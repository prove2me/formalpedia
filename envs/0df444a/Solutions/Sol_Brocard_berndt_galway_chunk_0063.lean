-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0063
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:38:45.054647+00:00
-- url     : https://prove2.me/submissions/6ba169c8-f074-48ed-9170-18599e0c55b8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 11151086 ≤ n < 11330942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 11152336 1250 11151086 11151131
    0x10b09120f010c0206060108090604050705060f040e040602070314031608070c0b04030206060307060201020f0304020f0f030a060603200d02010e0a0f0e010306050109020304030c0f0f080f031008010203060d06 91
    0x100c003c204012050340020340360401951482d0005404d50302040f1480000100c00e07000300c0e0081d026044043c0b5240c20800c46512102003400080024880082c1005d07020300300030300c504d0140b02c025954906a1071b000340f17403840b80d03003642c1c280d02814000d00c2424884540c0a02e41117526061118440d101c0380426a4403890682008002e040000104010194003081c1103005801c280c08444d24251115800e1307090340078809482d040050306000150252403c10740000d030001f800740025056100e9080401c0c00e02c1c010020a4944c15220f510030400c01c40390410a20865280350350380d207601100d400015110350142c1b58007070b04001e030303000342101c40d55a41c0070004000c08020b60300d401c9040d941e01c030304a0803010910042d6041c520741000000d00c4c0c0054000c592050745d25540b2032151589a503115400c00e803209005448174000951418000381d02040280103a02484280903100d190003952580e03800742c00e4000000c540d00610500c0402d4855100c400b9070f0a07801500424040c1e0a00ca0101000018 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 11153586 1250 11152336 11152363
    0x108120a0324080f0d02010501120201140d110304031409060307050d2a0207080c10050a030f020a0903021306030305031518070c17040303020a03050c01020c010c0302040815010b0912 80
    0x42c0c420006010320b002401c43c58281d1880103443c104600740c0300580c02c80d20709102d108501c100c01c0000c000150f00c03c01d44003401c0004400c140341496a103104080031a26480545800360400006000526800080c0150341c001e01041481ca0018114082000c41c040a8801400e115010a41d130031540e0468004c3d81c149a9002421020007071702c1c0e4a4500fa4959500641001d4090302d070011a07405400f0a40706000c55014050b0130028801c00d5086849a1000c0707011070030165910089080780400b4001004078143d10781d503010304030f800d50041103510259960305507000c0f440d1040c1000001d4002c000d4981c000001102d0503407006856010809510880e09210040e09240042104041c1c010510f43c602074054a40761821180b100d40301c118501c02e0380800341c051b90000f500c00700040c0c0300300028501381e038581c0009410041500c19003800d4502d04540d0744082038011500340142d03101042000c1c04a078900504c0c40c680e52401391240101e10030708040502500710306086031070424041200c10381e80881c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 11154836 1250 11153586 11153651
    0x705010504030801050f06040b1e1b0327030d030b01030204030b040605040501060e07051206040905060a0e010b0d1e0809130504030206010518060904050c030a0c0e0108120a03 77
    0x2060b02c1d0043c0380b07810901445100d0201c0902052160520209450a039401081c1c40c600c1c0107858039041809241400e028400000200101003a0355000c00c80515184150070082d0340311410622903217140102c0440300007142c4106803004c6032a0b0380001c0c2040058600e801c0024a0080e0040128081d00c11a000545400070190a0004022003980702611641c0204000c200d50381c0c4643c02008107500544040001900502030010003050504650b50411801040007400e003425940c1c00f0308050342110f8891000c2d80e510184c15080c0030a0042440d81c090071a07250044950b2a5036516800707000209460b8082d101032413071810050024219904090014900c203d902c24140b0301c400130308803c840032801070240400000c0c80e03040000003a40582680803014455988250501814400040080d21140701d1907503541e002c1e80303040c828244104e00034207000140c0350402074508200403040e0300030718007507001c414801c101840110a0720180c07116450089181100002c689000b1002413494640c01c06 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 11156086 1250 11154836 11154841
    0x601050d060e0a150303020a08030a14010b030601020114060303040306020d1805030703030c03020403020906040e120307020f010501050d0503030c0f04050301021809070315061209050105011d010e01080d110307050105 95
    0x60512201074854450f80006108007040d54003e10010029484020050380c00422200b00103005c860246038084c1c04e4060004581c4018040301c403c202c001c3e8030650314004000184806541d081c001c040014224100d9106a07040541c0442c0e942d2140c5c0c44050403040d4042000c2507000c040350080100111590070840d0410440d0a01d03a071a54003141c001c4002c40e00c0d00f80c411308618024029102105e4000301030b04802d64440d1305010251091441e508070324050031980028843d01d00014600410841d40100702044281030094211541a0403251158004d5284100042c0d0300100b129440010342d0556500d84000100d072030b1687c000e6404c0558954004200900300c444015030243c14410304032129204c54880180c240c00301c40301004007081c49058984140010340c00365285442c0d240782c080c40000c42d1038258448500f101c2c03081c3c02114030550304400d20325a1880c40342e1240d005d001030300c0c0d0b4001c442d454000c146940d130940308508010f014840c90b0840344000b062042e01c0f1800c0d0004020720691 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 11157336 1250 11156086 11156099
    0x60d020303090d0c051e0f0103020a02010b0312040f05030105042001020a0506010803070308070f021005060d02090c0904050106021b190b030708010e0a06030507091d0714150a0e01080601050d06 85
    0x2400c0c0d00400340106e00c0500d080a14007003500104840c201c0240c148140c00b8810001103000e03512504440040d0340d21041c203480704e510100820381da01618007160b0354495051051503003424046610983c031aa0400b0184001b00e2031072840600c0314403000030f011881c1500000140d0a0401508002d40140a80d1000040e126004401441064440d42e00d000c07596840001c240c0d002e42c818104400180d11204400c07120028591240b40c1140c030007080103440565540c00508000c100721810a420080401e98081905181c01143c0c0908580d00141c20703007400c40e4000100300d103403810405200d1024400c880340c0c18041411181c0141882c1c0d04d02d81e03928944150080c14440d1b080c814005440c0b179050011700c00311580e12903070040d2a030240103403c94600c0d04d05a40054451600c2c19020a0034210003820500c000b00903510081c100304a0707560740b01c00f018040040c110b22008404001020030054003809942c4180c010078200024203103000702d0344034000122070314040d100001c24a14900100480c05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 11158586 1250 11157336 11157353
    0x20c010e06013008090d060b040903020a050105070201050c030c030c1b0f061b0f03150a030b090c010e060415020a0501020a0e0f040204060219061503030f0e03060103030206060d020303090d 83
    0x2003c10146000390220101c480c214003038400002c2c0944142d0060041e9445407070050340840b1042e0149201050500e00c0000007000c9038159041240942c1c015201c0d03000b00f0030b0030b000d200c3c0d01c0071440c0020403182c17916800803403441c44010442e00c481d080000000c0c0d100d610100540c1d6410030f44054401c041c604e02410aaa2107084020b904003130700c6080002035100654400d040c0310600c41858840c00c081598a001c02c4c90341024141c42419500b81c40b00c95116151810030000950151070105114100700c45184d05081d424981541040024142d181e500e8540600311001c41d41d2a6029141e40c00d8a00022420000c03102d1000340030b54000149000045c1d40b04ea075006142d40219440e440e4040d04401b004100c0c0b2452080c1300260304220020b400d001c42c40410a84c0740c03405803001040500c201c5130148558209500200d011401900f46940d030300340c1c0000b03010410903003540140300d00d504640f000381d99001c1c010403052150581e0f21a600840d142402a90020480a0b01555640300f0300d18110302d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 11159836 1250 11158586 11158619
    0x20114040c031b1a07020307080303070512130203070308070303230603120306090a0c120e06160507030801051507080708040806060307030b0708040201090b0d06181a04020c010e0601 80
    0x4a04483d48440f0000d0440d4003550070403140f8031110100b0340d61030702e00b280e516504010400d82e410b02403030000081000c41440114402c200f1561820b80e901c2c5210310000d0030640c00b0b002100021140314807100181c4000503580107494005040e50381325400c51400b14040c00415050b010105d950349044503070950300c0011940918800c9042d41e0942c40903551004c054041210190f074407040520101d416181164803a40e0a0b01e26850320f1401c841c03002243c0c1c03090319185003001c05c5642c40741c0100000514010800040d8091500d4007510b08842520000c00c41303201070282c10303c03900002014007140c5040504595040782c0c40750142d0b4a0ba040ba0605954a0300184140209401a440001c20703a14022403a142030302c0e441001d4004980310f0420443c0d00f80d2005104178184060180003181c1c00300104083c148103110040c0105a00e81440034001c0d0303102c4111049c40546040401007242c0383c40d0f400c41c0c5140e900c030a550060b00e419103040418054420031500350300e0307802600c00102e01c0d5001c90480c2c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 11161086 1250 11159836 11159843
    0x9030d0f03050c120105040504080705030f030609010509010e0f0606190305090d05040807060509031603060e0c03030a140309030405060301030309170703080301030204050601030f06080f07081504020d03020114040c03 95
    0x14603a229a001c41c440d105130096160341c5583c03040140300070300e0181c0c00650080e009a4505040042c0c503940c0318a5944850801c01101d000401040307a546040c440c52409010140c0b00b03010740c1d514002120036105c101500042e26030b404c010000342c4039194841564044104d001c18000440c4812801500814050b24801a075002d503144011290340204115400c5079207000c0104003282c41c0450440b055002222621380c103019100d40c500a158400707001c200a54080c06002481440d400310322482c2c04000420540280c00c1400441d284640005442110900c0d0f807090a80c0e9940310075195043d84a9600456030085000c8000300070b1690100790202500c00355904007020512100d0115a038a215110041c09454104014001802c080e0409908000c06044c00310304030304905100003e84110f500300546035403010205500450041044a004007102c0c030186c03400c0f0884940b406400d6400070000782c0103030310b01ca4010341014401d6000c200c4482c80171701d0781e01e014101807804d00042c58203484140d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 11162336 1250 11161086 11161091
    0x20d05010b0301080304030f030215010b04080c0d03020c040b0a08010c030b010206070e06040614090306042603091902030708030406020a03030b010e03070611031e030a05011e05130209030d0f03 85
    0x70400300c20032401c4034141c9007443d0065052a20303554032903015040412044003140078841700003580b00e18810960303010303041c82404551640d04201c0480c0c40c24200700882072048143d0010103006caa00400c040c4000e6405503404200b001410000c07030014181d9a1003000306600e0b200f401c103602c5500d23900807480d088c8264282c03000c640702c1c58001c039461084100315541c0301d03004200c00c00229020307400940401b018400c410707003001074100009080c0001200d0659002c051741d00c8003082075001c0301d5100c401c0d003107000200f415801c0031100160386441a40c5808e0504031030200038001e558081102070300405c1e0140441e9030f115103d4000035150704020b44201d01003400c3c040c2290f002d60249030070040b4800d02400802d002d03803909a00325011101989040100e000c208110300c250640c00503201d82e49804541255035900300843c6010403140168800c0e10ba4415100c00d0807030000440d181e5130b00300da03011103850000681c1c12210400a00c00e0802260307040c810f0701100c001d081c0d041a40c4041d48903242c0c404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 11163586 1250 11162336 11162339
    0x60902030601050907051801030f020a020a051002070c030204090501110c010b010f090e07080709050301090b040b0105030a08030a05040201090f0e07020f0303070203040902130b0403031706040908030a050a1e020d0501 95
    0x5000840d0130944000c80424402d003ca0b03400c00070755030f0000c450900d05150101d00e0840c981c01d1031040347d002e55600d6005801c00c0002c0420300c03604200a8046064240d000c51805865403541d1790b0854041c040248200c0d104e485e2101071041c25046121103400c0004440d0b80c616254074054001c0c48644101404181c40c0b04c07101c400180280034400c100c03040e50031000615696400b0403202c070080103240106100c00c91034046041e031000d11510355503901ca0b181d00501400d260411079403070401640100d00c2940f00c40b00700000130b03000c8400e80e904020f001001056039103a0340b00582c0c210515400c51485c1031400c00d000603a02208130031607400740103130707030280c440d420380b075140c502d4881c881210f8001c0540c0c800c210070000c2441541c000c0c00c0c048004400350b0807540d1601c00f82000e5620a600986c0000e83d101c41c600302090001e852640c108000b100d0402001b030003503681d41c5080c00300800d018640c590b6071b0002180e105950b048094001c5060200740c4110720302d0111361001390031200743e0903e42c9192500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 11164836 1250 11163586 11163589
    0x302010c0309020d06050601021002030a020a0206161403041109040c03020f1905060f07060f0e1002040e040602160611190206010f0302150f03070201020d0f02180405060d08030406090203060105 85
    0x70302c40a254001e0901002c5a889880d4030001c0e11020b070000e4114411001481c2a140d030610180d4098002068096900d41841c1c00080c6420b03c080e204c040d03007080c002e107000301c00e9070001641c8801007031081e00142c0700d56440c20000520f8800301602a0030403c0c8400704001c00000c2c4040c90b0980307200701c03603101c1410710100a001510398081000034030290054800d100703900d0000050800721600c0f0b981545004c509644120640b0f4140104110355625601d2010070f0807000d0058008802d1807100c00c50a1502d0311790018124600170f80094a0b00b0b03800501001f840303013103c40220f03034070b60021400d115070054221a41000c0d8000c13054150b40d100b1524403a000948003140e824100c43c20711603448000d170709540030400380340100d0100345058a410001d4144884040020350711800d615000103844c0c450088a4000f583c103101900010349104010200140a03400304084c040f210640e00060603580f410085000c2031201500a41500400300c00c010810129070402d40e2824802c1e03042e81c100f41d0f41c820 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 11166086 1250 11164836 11164841
    0x70b010302011b02090606032701050624090607030e030d09031106090109090f18030207030b0711060a0f0b0a03060b0f010207060819060308071a01050603130803060604030209010f030302010c03 85
    0x10f0000c0d400450100400d48030701d000c1000d141c01c2002003404800c551568840c0b0b00b82425503180d072042d1340c0d440782e041003030501c1e00c1c1d41d4a1031210035540701c031111a4002d880d218003510403024014411031000c04c1200916200740c1185c000040c000d01120b00000841a002e0000000c501c4110780c00003400a0404241c01d01070152080322806842d80c0500f1410007030510060f209025071600d0203651010019607040e902c90700f6561480c0a80c010f0001c0f00d00b141000425418010080c4050100030014100216000125141e0008204100007080300200c40108040d019200c140780d4011a030000102c18405e2030340c0030440f805e100b103031559203411b500801a61500581c0c4901c00100780440001102d000e0141c20404100301d9210002a40b182c5070b40e190242508a00381c2503070100d4681c03110b01d0101054181c071038094400ac490383c40c00d41c0381000031751883c101042e03401055124080041042521070304c0030b86001e95401800c6080301d6856119004205c1c4040c4804c0c3c005600317012020b103200b402032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 11167336 1250 11166086 11166137
    0x12010303020609010516020307080d23010602100501030308130302010e010234030903080c070504022b0e0309120708010c020102091c03080604020306060c0d02010606020714060318030708070b01030201 88
    0x16000f230f600701030050315020760303942011000c41d40f000c0c1c48111600e10908003d1101e00710040100d40d12409505040b0000d213017581d451190a040e40c40c041c0140086034211380449d03880502c0420300400801c0c50f2500300d02410882c100d2508039800414040f10b07614000c208401414046480f0b449058007549034600385420307410001d008140090020300c04240303600001e000350000001110071a035910800b00d4201c5c1c2c040710f09103803480501d98010903054400e0781144035081c444075052040d5104240100c0d142d1051030b242e140305044030400302c101100300344990402005541e0080140354888030011f8040d40c0110366281c803c03035000c609441c0c4855821001c084e03954140e500e030130303140d551182400003c1d40301611855124106011103c42c1140812140c40d0402403640080382c0c00f03142010181c0381c01510341203502201d00c20f03c80c062486e2104000c0e66440100c454a04c1400400900b899086204054014100340d400203400c0090005140340d91b81220320030b030b80c6d1070207814034009003190f0708111 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 11168586 1250 11167336 11167381
    0x5030c1e0d020102030f0d050411040c0f030507020c03010603050d111b04021e0a090e100e040204020304020109050d030507030f0503070e0108101710050a0504050d0311120103030206090105 83
    0xc951062a5042892141400500c1801141e00c0e02d2101c0f041c80c80603070000d0340400300c0c098840007080b00b005100d4080f080310708030546051041e444801c038044e003400c07032407410700080554950000301403074420442e28050500c0074000300640703612030910035160f1102d0f02000340825640d04c1c110f424a000001c0200400b80d0313402c4040c3d1040e01d103804000c0a07500c40c008112400f20045104180d06500c5001802d000c003550300c03070942d41490003000001c103810040c00480064800c060401c500b0707102103419903010784e0441c3d0041c2d4075507031031006859055154000c03d82024030009080100341d0400000c1c03d00601030384501c0014a45420120303003511080302c0b030310001500e00c03032001001c1d401080419004400c003070901c00751646440c1084164100390510741c08583c0070154103110050240f19250f0000c1c110b05003800a450107448081c0d1f0307600c501d00c03203004050362680a20783c030101031010382d5206000c65100c82c1040d60740341070095541c1015203190031154640404646008000310100308403400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 11169836 1250 11168586 11168629
    0x509010c05040617091006060206040c0501020303090c011b08030103120306080a020604120303110a0201021b0303060a0e040503210a0e07030203060117010213080304150306080613020612040b0105030c 88
    0x710113581c0d8a20380000781c164a820b206041741c0088460031800b8002c0a400300760300038042ca260500300a04000e030035034819070554000f042800300303001d008a8200b03c500000e00303098050001d4010700144040442c0c0c4060300641002c00040b0400800718064036078000c03c0c0d40e051040d070352551041d40e00d60b01c2e103120007540b0040c104070070041402c003c41228003050107818000740d240968901340f46140d0000d102d400061354000b030000050a02811140d10b00b1110400542c1117140c10004510b4030301c502c2c090b0f6180081c2d000e00050402004100f02c07540e1074084082c082c0000c041100c59a003140064800c5000d4508081d80143c5001c0001041030490b45c0003801400940d10f404800f0803451980d20032044c59540070421000045548071441004090b0744004581c0c41e4504500c003e82d1281900302c420030181028003c0110800003c1c100d0381016140459044800c0c4030720000c1c40d01d11511014100c841d40802c100401c0c0309210500a0480780242c0582e01905400030400001c2444c40801051340359 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 11171086 1250 11169836 11169857
    0x60515190c02040b0a06050301080706021c051b070f17060403080403031a03070e09120a050415030207150b0405090a02031b030a05060a05071407051f020d090302010509010c050406 79
    0x30320401e944041c0320b0014000140c41c0ba02c007804240007100c1c54101300081040000100321000c170402401006011038806099070840c4101d1094001d954030100800b08075020070711207400c81c100c41d000c0700c24031901c608546010766110f600c603105e00554820000e080401d46080c1c40b0101c00480c00c42c0c452a8150396100040d9103540d001d5000f4501032556040703c04040180103401e440c1001a50003030091000180d03180e26001d45007628080d403801d0044418003090012840040e0814251400d40f030522111016100100804800a014400c00604207000403840010f294009910030010b29409070f5050040d5912589499620054044000e42642c0301d104191140c0000720307140d510f030110040030b03102c4400341625124039042c000c0d15440d03c159900e4003401a81500590001c122502c0714003c0d9040c0541a15060348079004010801c9040c0714600c1e10400b03804462b0b044a144207030f117100404c01543d04d810000d00070a0200da00803102d610b4401c403030380700d9806901950b0844606e680c4024201 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 11172336 1250 11171086 11171137
    0x302090d060e010b0a0303020109110312030106051804051306050709060c0209060307090912030c0206070801170a021201020901091410050d090602040e060108060901030302030412030c02100201060515 88
    0x81402c5202c409040d5600c0243c0c90f030f01d0751686017441c000e501030350022544480034102202007086404a06200381c2c820042c1c00e40600e8180290307811117009003040c685072005110070b0329607550b84001844d4003514080c20044001c040c50498820700c0e005400402683c0d85150b001d44071101540a41404100d40c07050b814014070303103854078552000d40a8256410780344d94030079017003c1d0b0f181e0b10703412076880782500d041c80607150f418821919180e40070301c000c1c0300a007048600502050b338103009020703405c0e842120300201c6800401c92144403640c040c0c803502801d402050054001c0d00200c030704d00c3c00a50f42d200b0000d98028080b0b560624010020720080502000c900142c881d44c3c4510b1303803c40c503142c6440c2194081403940c4040c00040c99805002035152034818001009020028110340c425950b4100500110798000161016502100c54080003c1c8090500b5140b10700c00210003940700c4070801603103036195410342120301111805e07602c8850384400c2d040840b11038007400c098886407507042c00c0c106444 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 11173586 1250 11172336 11172341
    0x10c051c060504020307030603120c0201050a0c03020a0209040506011e081203090a0b0405030703030c030203090c1909020d0c030b0307060806010e040f020304030201061701020720011701080a0c060302090d06 91
    0x8800e20040c002041d650b60000b1030b042e0f0b00102e40c140c001c26680c0b201007040c030108400f100c4031440d10b46810383d610000344d070000c2d040d4056280b207841001140041141014000c100140900c0e400514038096454280b030710a44e100801d01884a2a001d510a070005030144541000251034580340500f610300050030411641d0381004000680f1407203a071031301c10041511410624045c134090000303542d42c3c0d981400e003e0705644403e072070b072410144108200b210581010030358803580d04007240d036803100d07080c00e583c941c00602d10b5802a104903880088da440710144c00e0760002c80c82c07442c7c41c1c0f401d00136128a80205500c41c0c21508c1031038041100500007809a611402c040034000f017001f4070010700c184006075502d0480c2c004403812000360390349075014001d08d400c2112186698802000075407414200e0b80e18058a1030300c00f0300b001d40c0103190031411802c2d03070b0090500303100c0f400c640c02d042e01403907954504080d503c040440c0151011050f83e90046590b0348a402190228100581100300d40e00c1c1d195204c000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 11174836 1250 11173586 11173627
    0x6150503041403091f02150105010503130c0b0d020705060117070b0a03060906030303240f050105030406020c01090f0b06010c080901080402030a0230070f03030503090705030114090f010c05 83
    0x302e4002000069103507580c030129401180048000000c011800010103803909841d20600d040d0503042c200100626a4450126075100c1d01d241404055500d29107400306050469404c45e0f1030490020620010403c03882d406045910300500c11141e07180d0740c41d880140450041042840950031105060161030003400003031141c05010315000a046036144484011210359410031400240c072101c000c148000d01c9268080b000c6090500042054900206030b2a00c0c003151140605200300480013800780117042e03040e074180c002000004c0c004e01c1c60034900010000341c0f501d401c581c400012000f00d110355100d0f800c003215296104a07018a0801e605006540610000708220307070510440403d1801a00c035014406140000c140000c8424a40101d912000e40719516003a5004c1c1c0c081c690400c02d00c0d9580403008100c03501418000c1e03603600c1e104240b500300101c1d900200d4056003001c20090061501c1410180f0540d01c1000b901c0d0a0b500040d561400c0c4c1e54586d6441d000104248103104041410f00900c18 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 11176086 1250 11174836 11174873
    0x8030702090907030516031211030a030b040605060c0607020d02010c02070302090402030a12050903100b0a030204050c0c030c0601090b03030703080103020609030f1b0118150305040c050d06090201030615050304 92
    0x10991544c07907a40c2858001e0070300344000f01c840d40000810400082161b0009041710b04c0c00c00005c009041c46959aa90040c11088001c0645908c90061141c0b91648040c1c00f80c00083e00c0682d4907040c59104903507a000030780c4c01c04010f00c64542041080307803040c400c607a2003400707650240c060249181c080001e0404050000d99240c0104060b0f0000102e2400d6245000150340e11443d485501040806040c0b00250803c0c03a40d00d0f05101c29101c1c50b940e01d03070070b000a481c0d0403900020071751504036443c2d055004182880380707144000610501421400204c00e0b041b100340d10001e0000d00c8045040c580c807800f402000038049000d00c40144018a04030010f4080880e024080b00c001c1004c941410f8a80b01200040d1070614001d004044103d507404101c03890340240c002c00a6a190345800c125085002162480f00d040581c0c550101c3c0402c01048640001401c1c01049104145007904010001341340003c822404249001c078002003248520b16200c2e00c001c44c98640c10705560362911140d031200480e10800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 11177336 1250 11176086 11176093
    0x70c020d02040e063903040803071808030415030603050d08090c061b0606010804030f0c020103090c0801020307080105040501060e190302030d0206010806090304050a140102070302060a030b0405060a080307020909 93
    0x1030fa161081007000d22844188111001c2d00d0840031545102040204001450030085d0780e011040d005224126a0081c1e805a021651380ea2421021210231048006008005680283c0000c444600002400541d500f403d10600040c5543e14141c0442e805403000901603080030385540070090245a60941c00080c40701502c2e200c80c0090006007195001c4c0c1a00003000c2c2c010020802064020007a49501c50b00a0821600904140d103000c0e00d06850484880100301c0010450404c40e4405e8101e40e0005900c081c000024079110f082240c041c1d00212400310000b40b410000140c2d074503086c0a203504a500580300e6107a1801c12509100030080c00f4a03e241800c1c820b03070f50000040e20100240560b60f08581c0c0500120350501044508181000d450f84842d50b0060005002d01e50311184404105c620208001f01900901d40050b410700a80368000380d88018003054003450036400da045681220800c890030080c55561804000000d86203004140d85a8424003a44006080000008e60442c0104084 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 11178586 1250 11177336 11177351
    0xf060c0705151201050301090503040312110709020306030607140a0c08040b0708040302031903080606030712050a02130906030807060e03041502010b09010e04020d061e0501030501020910020303070c020d0204 91
    0x1c54858442c034081c030104110002041d61070040303501001c070b002d4001100248000f110316220765540340914040941504100d6080d415114014804861001d13078079001c1e104080e56500d80f80780203400c00c80e419402402040c0001d80014400e50011980f260041e91031400e04501079001c070340643d1410804c840c0c00b08108404100c0c40840009040014400e90020380d8540c15407040c035081c0b84075401c1d4420f03240c944232000b40003e5080251564051416904c0f90b45956460004a840c400c500394400d072594900000d100c403150940d0001c0620072403a80d04d246060390b84154110448029100240407010248101c400181a541101e14581032010480c1d08058071103100520b0072020490450140c1c0d915040e01c0040d0401c0c00f9417a004050a081c0c960300c0d460250041081d8800c00c4c030000b45002d90354103078040030b03040700c80301c5290603120104100441e41c2c4a143c034600030b50014211502c26120541d450036110701c00030840e4801c07011b82c0d03200d001c10038441d400e0021500046800326030060701c5200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 11179836 1250 11178586 11178589
    0x10030b0a030f0b040201090e0c0a030902011e030c0905150313020103110309150a0b010c060b0103060f0b03010e0a05010513020a021f0219020d0f08090f0f030c0105010b090f060c0705 80
    0x142c0039020340280b01040e0030303007407610001d450031409074002d1041001d490204514002d410003681e0480c602c5080124201c0000d10040311b9403614460040d141c41a00350281580030790590045401e00d02c0c03034490490694840c000c0040040d0f2a03d0f5803101e9500400000d02032011a0141c008800e106042c046228502d15190080c03603001241c00480b541c1c41000c40544020001030b80f550040d00c030600401c582842a000280b8181070482c024200f41d484151204040e4400e5006070028081580c0065034103031100e052801c1a4801c1c8125030f01040c03c0c801082c1c03d00e24600c00c0c3d40c100ca40080001484420044130312002c0e4000c0d00721a0194003c0714080c40c00c01401c4d142103843d12030040001681c900c401d04600c4024491f61000b80115401502c00012142d004162610700d00c0030f40c01c0c041c5490750f45500d4030b07242001e0510b602d01903000b000c051036241c900000207098400000802071059071f0325058125a41d0183c11901c65120285401d800c0103420460020300c045c1e0303030788825102030a49400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 11181086 1250 11179836 11179853
    0x360f06010e100605040b0a050901170c0702010305060a0501020c28090606030e010509031b07050d0503070212010504020609040f020d05090c01030e150a0e03070b0f0f070206040210030b0a03 83
    0xa006050042508040007541c01044a0702c03009081d40d410035500b01800c0005404660258070003107018041e000400b41c4443e030007a5036890000c42800030502c41850604142c0c441904200c030124046824040801e0042c41c101d21004196041a8020042594100b0070085820911500d40001c80d40180140b440c4081002801c0050501000045030b803038034254005044401c0c00704c032500c0076490b14041c000802c06c081b017201c0c2c45520354074145034001000d000190420425030310160340911980c01034020050007001501c0c99500842e844594240e01130050350a03540b00302c40095100c801005420701602d0540e201006400c0c945d4401410500520303250000c8940640b0f03240102e510026801c109580d0600031030912428000290001001818040c030b404123002d086800e41d180c55038841d026a031410010f942e40c89030030000e50000740c10300421070200c1d460241c0302c841d40c0c007803e00c001485090001a816010f241d004e00305080c40c10940404030000c16040d1a0b040c0d02603080d890000108a885 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 11182336 1250 11181086 11181089
    0x11030403060606120203040c050f01020709021306090b070302070905100302030105040b0912040614280806090604090209071101060b0a0201140105040b030d0e030111030903070b360f0601 82
    0x40c40c000034401c0c24603e01810b54144408440181c0340100300300b000113042144010304880060b1034450714041c1d0900141d042c00083d810400003144080380d80400381000c00d041c84200c400e56111103210540310b000760501c0e40704070800607015070301462003080502c200381d03c4558007800a140c0300700c009072a6400a42520b10035038090b940c00c14508141300315000180001e440c10802c4007622443c0c1464000c018000c100007002086a6200200d042524808098003000101106080c4640d120490080c0a007800d4000d8031000c2c0904040000228542894441c001daa40d4000f00403c55031781d6141400ca07011140c0032842401c2d5501c8440004481c18000d010308050020b64001140340805002e14110310101680701c0303071003982442c5018045460124175250801d107140740601072a0030b0200440c0c0900203992146040417800002c0010000b0b0100103002810320860394051280c94079403c0d04011038040380d00100ad103201072030130034100707081e000c0341032307000d034035403045c1e0f801081c201500300c1c1400803d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 11183586 1250 11182336 11182343
    0x5070c090c050c010b1e09040206040801020f0408010c021b04050a11040b090102060f07080408030703020f13080d03090305031303090305060a05010302090906010b07060b0402090307090b0102070e160f11030403 92
    0x4030700f0300c051080c02e00a50210010590f007a0301c1c204401c00d50b400c140484143c6a0780941d214030049810764407440b088501a0104600965541c815a0307400b91303036a4417500c1004030a518204880103407c0c8041600d180c00358024038030606071025031041100810010344148041c40e600c0c100456442004409003004040201042d610703900032000181c208000244414608011302c81000502500300445540007170f0040a41a12640e03644020b074024441d41c1c40c103100703a07440400c80301002800086440151a40303101914600c0141920583c19030300e1260008020503000e2000030319480d40d2861401681c1d005e4070309540c820340d0729100c050804100303503040310318035032114014401c3d414404055900120714400030303c115890080101e103503000384e900c014401070700c0f211103400c41e994580542c0c0c1c030403070024140c40b88180e982040304000c1c030382410a40d0142c001d6000029602020301d920354410f0412007a440600440b1b031178100c40c010f0341c0c680110144000c0c0200b42c00681c408001a03c0070f90312 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 11184836 1250 11183586 11183597
    0x306010609050f041107030c050a06050115030f020a020705010f0905090c07021206040809040c0c020303031305011b050f030406060b0712080606030c0a03050403110a0804050a05060408060705070c090c 88
    0xc040c00c1c03184500e60f152819004130304203003a2546910307075801190812a014a1700c032000e09081e241079810210148800703040142810f00129149495522002c14110a6103040000d20106192701c0c0503400350f001c1c4400035812a550400c141d50160292405083c0640f03000041d540d02c60000590811042d1444041440045441c000310709015105802c0e507588180180001d141640c1e80500718807403818014011381c2c980b18410212401386541500f40e642c02000e0300d88a190403060450505d1038501c09072055801c0c401c05070003003510070014200800340e603130380c0398900090301c0130b07451041d40003034801c880b0182d880317100003000b005903030240c210b2030301c03420803c00248050040100f040c00058503840c8180b00c00c00038000d0700b05150701140c0c4810340300c0c28017050b19641d504080d962403841c030013185d0b1240180a0203004105000c40140141c60040f1031582c0aa521401409058000c60161140503448107001c43c1c0054082d101030281d83e4414032092a01c02d469520070070660b003034580d07907102191 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 11186086 1250 11184836 11184839
    0x30513080102130f051c02040f0501090905010b0a05010509040203040c0801060807081c09170705090c0c0609070302090f0a0b04020a0503060103051803030705160b100602070603050c04091a0306010609 88
    0xf8803066503400600428030301840a500344000500142d4848a07800c04e031212219412085458503001007182c1460810100030309e696821500c405450320301011070b403951130704000c05824603007542190192081a5201c50038488108103010080d8005042a56a0038400000050b191424001c000140c209440600800c2e0300e000340b00c600d4031019045030303c030303158008001003d4664841c1e0342808450b0420403502282540340103441c20301d040c0c0d400168000504804120f103540350b600090002c850040210b5a85644000210351100000d00009510116841c0850307a0b440f0300410b0580c020088007000150402018001012648002c0246011520100400000f5038040c03042c0b50b807060a1920b1201051440140e0039100d100042c0070b030003440404100c485001c0e101032982158181e00c1910810308d42030041d410b4003016040e1085400500c0b51503070201e00d4a00c41c0c000c05000303031030010610703041c24204001040a40140012454079560f14035140006540c1000702500034000b0340c4508400e90b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 11187336 1250 11186086 11186107
    0x91b080106020c09150103091502040807090e0a0609021203030a05070e12070e09120409020705010e0f06010303030903140d060501020111090604050405040206040b1201150306060c030c030513080102 87
    0xa01050380800700350340050700c24807615103c1c40d01480e400154590071350000400c1c000140c005050301c1d907010300030351076400d0000598076040d801001900d45441c04c585005070f507005550b0a6030303c00b00c3d4101d0071380c11000e5120000b0b00107400c070403030883c401003c3c10007801114010350b15540007129408141c42d200c00078485202e4104e140420074100648100306440120680c06030b4400651042490400014000400d0104140007003421000e1603c1055170765550303102c5560294014442c19510341d403a1080320404404000350074254989031070302420340e9a18503281500200181e200076410711411400010f600b46007000240303445071505400140041c03c0800081c00c4500b40b20b440390307a03041c08000c12103907076803000290741c1103881c1110041556922480491503074001c03030f481020090408a80d40311000907076041d56061741c0c40c403240000e03841c4400c1c00440c2130750711610039000400d81c0d20403450040380c841c6401030b0269010b070502528150710b00d8014022000140d2002136184d5000c80c046998 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 11188586 1250 11187336 11187347
    0x11d0d080c061e0405031207030e0102071104050a02030402010c1202070b030a05070216120b060a080703030c05250b0919120203071d07050c0a08120103110901032a091b 74
    0x400280c40d000ca60320318141d5170301c81d524469280c042ca00f0080907400140b0a034460b820010f840a01c0d50020764031040c1c1e07483c21040e03194505007a14801d6040000003881c01c0801e1007540d110f690140c1d160481d85071103480300f20381201144416002c5004045c004500c16104c00019409a001703003030300244601d4002c000a09043d4460f106145d00440342c03808000c0c05a803010031f464070a8002d6008203298681c48001200041c540d4082100740c041e01d0000020b05800c51496a06240070f68283c40c0c1c001c8089490300f2048101001001501d402c0620901000004174040d2000e42000f5149890440e801d041c0f00803124102c0e441036401600b821141811820180040002010341010751000d01c3c40480c011004000014401ca04000c4003180d54210341c40208000030003540c104041d541c0e5940052401042c0b95001d000c107641d45098005102c0c100d0401601003030480e0340002d69002c3d044181241916401001590500710044c400c01c00b0030042c01ca485818401040d9001043c02c0c440401e80c0030f003c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 11189836 1250 11188586 11188621
    0x9050307031103060603060115030222030303020408060903040f060e03010b09040507050414040c0e04030c080a030606030e03071a070c0c0801060302010f09030506060d080441011d0d080c06 83
    0xd4001c0c2c1d0041260f844103030880e007508445401d0143c0c80300d0cc60070b40300440481d90002001d0600b13071181c0c0003080c59003603030090003510340320001d0380c41c0355484d481c3c0f0607501c0c1b103075214013000192440c5040040c684508402c408004004001040d050504000140b04074400d0b06e00769001c0d04100000c1010346000c4c03242c070050005801d5000014075050307c03078140c0e0780307458403d50000c000250005010035220b4040c1c040c4603503104103a2516020442001402442107005080119140c8864a015494008203507403241c0c0d0710a00035807001020b8440710700c010340003600460a010aa9401200042c03590b1800c0001c4c0800100006d1201d02d5800018000c0c140d05100f0070070300c1600d41341400840c8011451607401441620000d500032000e00d0448514443c950050700340c0101c076000c2c45400caa00240c081c124150811400b496905004c1c51940f0200c4120700c81030114110340301a95010360b4840d4400b40605000380b06803803178105034035440066401390420018a0300004d0400980307030a04c129642 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 11191086 1250 11189836 11189839
    0x1503030a021b1c020609060f0304060606030605010804050a060b0609030706050d050606030903040611030f070311060601021b0409020a08010204080304030c091104030803040c0f120302010509010e0c10090503070311030606 97
    0x741c1d564900054010843c0c00b10040d000d00b100013052010394441c1070131104d0080d61501a65980d18013401c00000805807409044002400c1c001d0015881d0320480186020301d40103005070a11100940d104401031101400f015000390041c0207503882541c3c18020b8400406081d140c9a9644455284040403940d004022170302c00d01d0144148008140000291010341c4d056080c580d28081d111819141b07140103003501c180708400000341403010503500901e40c0b043c450900e0221903003a1200170041e41c0340c00c0700fa80c3e013030340124502d003a1410034506600701c2801c407070010303000c1c6024a440360b901c203007a60300640008116920008007007003001070403151a030041c44250401c0181480408240e801403049110161903042d0110114043c40288607601e00205094088800c0700c60360303003900f40c0710f0710f602a200b40c02552030032000a40f020418043d4500080c6d0035409065511200000c124407030043d10203107810081c01d200f02203242d403010442100594000d442e02d0741e009100c0000c03d4905000208403d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 11192336 1250 11191086 11191099
    0x70b09070803040612091b170d08060118030609050102040806070c0302030f03071e020606030d05090906061b0303070201090c050409020d11180f0603011401030302030306091503030a021b 82
    0x401c0150008016181074400524190b40c8424000c08024040c1500d903130040c0c610205642c00f0072054100c001c160b000c4a003600120200b1489000400b0b441e00c40c00c2029001084e1001c00240e0191b00c2100341450703007460b100c4407501058980d00e61008445007804103d450b694001030a000f082d0007003102661103a15031400c151107001c0c6940080d140d0059040139501810080041502c00e0300440241c80742c8281400c4c0e0810b2026164402580c4c1c00301030ba4070360301a0040900415200340b08030111091350304040c0542015844007003e10205a000c10484040032a061030720011003030301800118040e00c000e500101701e0600718140007400101a920144c4540c1c43d0202c40340040c0c86101e0520030054008400045c0001018007040c0320110005040c0e2000c2c10120800140060a0250034000e040603002000303400c00c3d2100d0084904000c0c003015015a2042c40003030194a481088160320228013038141040190840110f451500b11405080c00341e00540c40700c241d180c0e041c1d0042a9403c10403281d2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 11193586 1250 11192336 11192339
    0x7080414060c030a030c0e04020403080702090c0903060106030501030308010501050307360e0406060e010b04150c06060b090102010c02120d0e0304211403270f060301080102070b0907 80
    0x5441151046114000444a810306000e003a9a5044103841d00100b5110541e90340340d55440c070040c0100303500c080c0c03c000b0a041c800300e4080303410244291415254001c0b00c10349022100d03000c01c22000c2c001805070319034040401c8040d1440d03c061004034000c0c21180c602056a50451401501040058004074100702040c410005800c0e408059504268411888480422261003034104440c6c031078824013200010040340041c0c14100f17465010312690168000f0095141c81310008041c007035082c4500850321609100030301c22408000080c0d0810f84007420020013480b440d54400c001e444080c0c0c010703210b60b0b602081d201d0130365030203000d004080c02a91006d00400e10030b41041d81c105000343e44055240d42c1d540c012540350400100f0844018003149480038000070101c1c00c01880f0b0400007201100c0d59030300050400c115140c00800d941c20070440743e11005000e440c0c0e40581030503060802c959a4060f0020b00b0401c142d4884400950280040c4000941d43e014a400e04090000c40503007610940d500c074460 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 11194836 1250 11193586 11193593
    0xa1e0905071b14030c0f070f050127050301050114091509070f031103090102070309080102040501020706030f0f0e1e0a080301060c0309090501060302070605010501050306210a140106051507 83
    0x1560002d0356080000c8060210315814035100300c001c6040c00c6901c0744000115455180c01c0002e80313006c90103481045803915500d51101850340d03030040c422139000c10300200410701030380c42003542c16008905801444014503902d000007404c0d107000381d00c0451000e03006000e000e070a0a11894803540595035019552483c4800b501007058850020810380c1040041d404403446644030b5041a00c5d000c0903505102c0d180d090801820307000750b00065007100810f09040c800280707034a040c002d0b03c04030344058020342a002d103800000e401503c0c1100034585681d6460380303d01c6854405114405032440c201c1d00511103500c001c000c0750590b01901d0f41c96102c5506c01803c5a00260140703084906440c05490024062030551030160382082040c4c0041f140d082c14030b000400c00503030541c003500308980113090612807a41d0701c0c4010740d0303a48410384c0c0c3d06810a1000c0c98a00404411201104030305101e8022940556415100e05aa11020301d84122207a51150f100f00304920b4035180c81880d185c03140f001c03140340070641d59 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 11196086 1250 11194836 11194847
    0x304020f041107020a0e07110a0302030306060904090f0606170f0304090c0c1406040203060714030406110c0102120108060702030c0303131b03060c02100605010903020402180a1e090507 81
    0x103440348500d44500c40c1c5003a022501d001c2d2914107a000d032040d0b1040b5201c901c0d070300d46000202c8051001801c00d1800d1b91882200266100d9107942540265165499603028440a41d1004040540103a241e413000c200140c0d0408841d5140c074066a0b0005103241000d01103821488003140038070040d0301c0b0310452100110080121822502d411000241c401c0b1001001d07a80c1140e080c50190162018010807001c0b0300d000318125100b01d100300e05030b03a1503546012050703c0700700d1024520511104248000380000c0c8081c3e0141c0b51000e420b140391130524600c01055401d9a0000c00920500030b41d40700108010003040000b0390300000a40055420b200d00a0002a5a80001440d10711300c0900c0060740e5083c4681a0003540b142003142c030f0071802031900d0303081107006450070700510300040c802c445e90700003071060038410107051300ca05a444e20075180c40c42d001c000281d004600c2c680c984140c0701c4001c45e0195201a0f4800003041c2d81d100c030780f841410443e01c144440ba1140c0c8028042410714082051865011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 11197336 1250 11196086 11196109
    0x10020d08100f12060b060304030f0e041a010503090f0d0903020a12050c01080a06080d0e090708040b0601121103041b0b03010e04140102070f0602040f080f07090b1201060906060e0402030402 83
    0x462240d0500d909504012018203050308406420410007c20710040c5580f000d03100c1d00302c10f681d49551301e00c10030381014081202c0c0d541401072901d860a80000290398458002150080400011507000c0e6141002250070078094095010105074040c0080045042a0164000a0503200000d061081d0651101e6894143c000a102d04200c02080042d540c44080c0d403000024007111011141044c200c80c0d009040f07401100e40c46031091840500045499228560a034460b941c000c0490000c0c0e16060019100c0100d04c3d0424a40c9684420008100242c88405584280d00440000c18091f5802104a000e1b40c9a0b8001c2d0940400410041c8023845901e040940c00907800742d05d1000040401c01c4071402401a098010f01c0c10b4030b07000000d8240541c0c0d402501c15500c00318601d000c86036032010f05a035034007141c0c0585100e42e008800200003a825a903c40b801911f00544041c0b840748062040d9421600c1c02d1300003d10296881000f401031b150310108891568909440442c03a6040580001e641c81c42d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 11198586 1250 11197336 11197349
    0xf06072c0607020105190302030403090509070905040f1805060609010b03090a0f0c030203060406090c050d030212070c080706020d0905010503040f0f0203120d05010e070302090904030c020d0210020d08100f 90
    0x1a030b800c216407062040343c0c0041500e60f07000c0030018009000402950042d81c0642c0020000c1c1c0c0e0100e618540702c007241d40101d0342a260113158620b450306000240c9040c18443d0036003965901d1004168042d07102c00e01d02c403031049011300310030b02d00b00c03003005005041070700710504007041441045500e030740004007c90580c0e0048444000a60f19181000400b2116000250180502420301081042c41d0f0070902c03e0b2441a807003020b445e5115400d1160301c4883c0b50001c0c0060b480030382c43c598550211070003402118020309285454a0315031401c0c0c0e10b040b44030340c49440180d0200001c00d60344c1f540015402d01030802440c0283c91401c180d11001d00c0300302120f1000d0104c0d0120188002155000c00103030401ea4011603d190301d80c01c1034190003004000034490b950340f002460001901c2e1911a10031203101d001c004081d45515120742d101150644040301c02260400d025000c2e0301d0159898400702c00ca4512150300a041c03050341d041c0000c09000d0060f05080a10641030401d00907800225514030907a101d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 11199836 1250 11198586 11198599
    0x60f010f0608040c170a060b010302030919150207080310090903090306020c0709060602030c1603030c1407050303070b09010b10080c130906030305040503070e06090123030f06072c 79
    0x940303062130850303044c003940410000350b050b052001c81e802e0b0105081e09828001c1104000000f8848010340076440704481240f10b94001c1d50090301c1c161314a465a41110f40101000b040341809201c001080381d01090b01500c41c00c50201c20449002000500980030b05413145091001003000d50340036048410318040201041d80100d909070100c8800c10911000f80102102401940c2d9074441c080e489621040d4014001d000b031181c1e401c00f4411b0300d00e15004a0390305036240e00700031901d81c65072543c4c504c0040c07d61031140281d840004042ea8100080c1400c1801408003c13814285440c1403400c50380002d210b02d004d0440c1d94020903007a908050b82c1e42d0f100c41d4294032242d0300d07800360f00001030125154007e070051910b004400300a140e800b80203172040d0b0740244d00b01c4061603212044100480c0c01250a5548480010014401040c000c205414030201401a941c1810a5600081d040261022014290f68005000c0210381a800340344000d0300a290340c1101510401c200b1031f40c1c519840c11106900408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 11201086 1250 11199836 11199841
    0x304050a02090103080901030e010b06030c0702121005060405091c0809010902061306030605091005010e0418060e01060b07050c090702030c1c030b0a06051804060504060602030c060f010f0608 84
    0x40103100c000265640203108810a43c0c4914000c601500400d0074940001d02e42207100f41d501c4014440c500c50720000515060842d5501140c1d588139502018049810442002020f00c0350710007040540300c45aa040780c046864a051010300088640042072400345a1002e69008006081d03400c40c110940c06e5442d01c1480380c6d1b00d520106001d01015034000707420040014214080580c002d1001080d640c0580c0c1c02d0001d19600c3e420400c40900a482c2d0450007104004204159800b61220080c51300c0301030008120861112042052904500d4017680d025469040494004200b88540c601600c4151136581c2441d11544a065442030103079a0b01e40202801c001007001117000700103440581d00541c08450201c1281100060b150441c0c0c505e007030100781000c109502a1406074031200540320356640342030603d5400f01d05480000c4401072000c0d00700759181004285511640201400352209800a5030364110b00780d1400c0c54001c0052001010540010050043c110000042d00c11a0390340c0c0303800c40458 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 11202336 1250 11201086 11201093
    0x3030108010618290a1203020a0204050a060b0301090f060b0408010b01030b010f12021b0f0a030314040807080d0603020a081501090203040b010501120e1e0c0102010908030a09050f060702070f09090203060103020103020304 97
    0x10300765504401000d000e46e031400410158009021460240709990a2200b611441841c50984500303000d881d110074000d1005220b180341a03405030000400303c500c00b00345c0310703980c203610035103a1311a0300480a46d0b5103400010140f960540a2015961000c1ca0300014009450600034401101c101e00c2000710b43c0c00103038400141111101c404280d04014080d200c1c01210780b41e010350390701103414040700840e0070320840101622024020601c11604110007610302201d0303584205d00355210782881448030b5076507900031025031101c451980103040081d00520840d0a416107182342d9040590102c031005004008200000e0441d2a8240c110b50302800c245c0b4212545200501c01342c131071941503400900c070f20043c240712450101045002c1403a1a02034920410141d07004909903022841c1c060b20100040001c500564202d502c20304406001e8803d5440e507040700000941490b000741c7d9000010b0f4085141802000140381c5954001c0004100402c030581745a80480d441d1041444043e040c180c1c00320005051 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 11203586 1250 11202336 11202349
    0x8060d110301020a0c0213020408030a03020a021c050d0e0a050c091003060e0303010e010b0901020a0b090a0803010308040e060102070f0905041a04060501080c0402040f0b0f0c0303010801061829 85
    0x8224008000395104d580021004014020114082e80f04803141c855040d2048250701c202c2d0103071a4000c000d0b62511104c0036058000c1d40c011140b5000310700c0f4925004d900360146079164150722146542e41a9610f03d0202c160f0299002d50082440c40c1e04030700354000004200141451001405440300c3c4104d41c2c4030f946400268070240c2c0003030045800c160168003403043c0440110b050394080414100c8a90325455914841c4c00748000e00c60150740003460020205030340d4840c1310b44c043c5d658811218190200e40c0c0b5070351140c20030f90040301c0c90035011505000c0f00d414030558980c801001c2c4014042203140210700400500c0c540b2603410540e0341c07240881c2c14400320f42c103058080300511808810f2406c061600000500b001d01c00c1c800b4074020308088003010320b058000c440c119120001004d00b018140380303da0b070780e40c1c4c070040340c40c031800c8010020341a440c24180040c0d80240110000040e9051038079440c0c600114450341100c0c122481c203085d4441c11104c80c1090070001a60f0010440c50035a0840030654 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 11204836 1250 11203586 11203613
    0x70302090a1d030c011514150d11130501110703111504030506040c0b0c03040603020d090b040b160503160c050708030c01060f05090402030d0c0609060501030c03030314060108060d 79
    0xc1c002d828800c0340b8580c00001015801c94502c001c1040c140505601c10510b500d030300901c0000d95540f1007962a41c07600302481c06215031306a0703c0902d00301444095000b2a8486c2c07610120309540400d641c0200f4110b9196100140001c0c2001a022244041c0050301c1d00410301004005c400022803850580e00c486100d400d0084d400d42c0e009548640301d04015541e41c0702103404555410590f440801ca192404003900d0300c03a140311004504050900c00146c2c0690005812000da042d40c5281d4013020405c4580c02c3c034010b501a1450f6940c0b8104010301e9074101d840d2484030b0003403050800911241c020021500d55400d051382c40c0c17075003030340815190140c14244994002c0320140f0000c6080c2d007403490107500060440d0012404400815521414401c50b250700303c40203540340e0058020707020200d000c0c08640c1100c510644c4009890860345d40c0c0c074401c99034281c106a03000032809030f00b4010550188505540b0085100c045045483c1001c002494a000181258000c0c03d00001c1c0c1d90401504a44481c2c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 11206086 1250 11204836 11204861
    0x30503030c13030b0a06080105150a2d030803090706030b010c020907050c0703050309030c0d0503030a090c0801050103110108060f0d11010c051507090b0a0503010b0f040e070c03080601020f070302090a 88
    0x1100380c109125050081c2546d8040c5104a51030400032441081c040b030f0700d2868254001d09009071480ca80098038203010032030142031000d5046401342000e80c891f003c0b1090051440f82840c1600d0f814a55245480d2075113640055040c140391000e029500c1c0c0e0001695200a503040314140c1c0d0560311000c08845c107025910304107480d4070402201200b0400084040e004c1c400085d000c0303a591101e25420040700d0320b61f24101403c42d81003040821900c440c00d0300f0944041c3d000f1402c12031400c7c0c0d00da40b05402c54909134000d41d02e05284014201c3d1569012150b20382056045444200740609d01c030014111181e1280003c1c4800300940300380e266039000c1d07004444120b07048404e83e0400014804006003180c0e00700c43c807000240b04401e01042c150035007010b441d02483d07241d441c01e007160300f40358943c5900d074444240705074895010302000034200c00c09104540b00303540315500c40200c40114079016180402c083c00003415504086030041c0162030001d0280c3c12650102c0360a28503444400524000b000c032281801d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 11207336 1250 11206086 11206103
    0x50d0303090605091b0607020127050a06030501090c0306150c110319020f090103080a03020306030a02040c180b04050d150e010509030a020f1609090615181104030503030c1303 77
    0xc0309110021a02c100b0090000c0c0504040c0017075038003080254865807400034040b0b503e12200e41d54003580c5c00300c0c00a1030768000041031841510340001070700c05031003a030250700020b444400611000625010703010005240b4201480110f003402d641041300300d9000d07420010800011915400c1c44100e02401115050140559a03400c41c4040050540308401c501030307026540c2c0f1801c2c14043d05062031394504032134200c03030410300b0b000380c0c1c58045001e0750010701082e501d4440e402c41d80016940b41d10035042c04041c16100d68040740c90802c1c448a070300c149984820b9801109200030403850b1148c44540c1101030b07200400c0c050300600111040001c1043c50407040381076280000b04441008004003c3c0189025038089581c40080c45071142d90719501031400c81c1d081604014200031400f0f142e0400d48005214600100d17000408180012005540b54001104000408d6001c101094540f0620f0300c4980217001c01e625250950721084e54910002e408015221400101d41501c0d400c4240c087d8051584000b81 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 11208586 1250 11207336 11207341
    0x60507060c090521010e030708030414030904020f04090b010315051306080106030606051302031e0711060f01060e03030304050601050111030403080d020304060e0d02070608070e0402210c0a09050d0303090605 91
    0xc8031380c80040301c030500d2603070741c6040d461240d001000419100d0031a841800e00c1e186544590b521596424442c0401000d032109004030300c010707a0342d400504130160308500c00c01e803290724003429041516600c0541a052500d07110b9000d0b0061041c0c0c5520094860070360301003103400034805050004041a034404107195282c14804420055950440c6081360070444034510000110b803c51012440290340d001400040030507001c1d00c1d11582040d5039030102c540d08044002080c0c2d50070f0607084c46022904422500c48040040c00740359040791503c61030b05000d82c011401c62400e03a9686a68130070600070f02e41070000280007090180801c10484000d10b0b07000c90400e40710669000700c2d1021f50810384003214190300303010780e00021351000a05081189499030080a10a281800940303c0000207000c0d00c0c00c1100c2c0c803402000c1511640020050200300b03c400c04010b80c5c0740302100006103000b60503c051070400300038202c041c82c0d000072000300f40c50040721100d01150080c40e040e0300400e20000c005100c10b081008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 11209836 1250 11208586 11208619
    0x120203061618080606041112010302010806011103030708010503061b0405090402041503050a06050a020a0507020915031603120906020d1101061203110708010b031b040b120703140601060507060c0905 87
    0x10b0540c00b07005c0545017444001240e00041d1524010320040a0407040b01d07a004002640c491021b40da005030041c1410700e070303100101c460b990659008840c0d420200b4108401003180342010003115901c4014442c4980741a4105010702c4482c1c40f0314803c3c1c0384154134100106095540d00e60124030400c1c029a41290519079a1a0850b11040c03004001c0c1c4030b00b45001c00081e422031301d6000312108200700b56a00b07440e10019a080107801c1c035014006040030b80304510550100d803400c00a212290381c8000004214520314072700400303c10898100b10707040010200c400c001c03c503000141801040d64a044c4a00b4241c031081074903004101d10780c801d882e13a245040380b030414141c00013510b0098040200984072460344481545080c0d800031113059406a0100c0c3c0340030320a0b00c030150081c032403440007803010a0005107000060419010f4818402e1a5000114200104001b034201d01400d9144d14018000940c50b20364060304500950f84080c0c15136032100c3d0300c01402d0b0311030300c0d05001401c0001c1000c40c039000f4505 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 11211086 1250 11209836 11209843
    0x10e060703050709120201030f0b03010507030b040506030a03090e0c0705070b04060e0a0f140f030a060507120b0303040e0406021308031902011104090c12020c030306090112020306161808 82
    0x40304180407929060100c0c200510501001c8203845142d041c200b21119a5070045009080d8500211210703543c0e01c5c100b1055660a000d9240101c0b580d035004181c1c600e004080100700c0b40c014000718402d600001c01040044d8000400b4400c840070700c3d00b018000d90740c001681c00284a1408000e20794010342002160210649003e0001d643c1150f4548051500a90503ca52a207140c0140d060b00c05e045402000f0032220745402080505010300000003180000c80031034070b0503500c100b04584241e19001000002944199140d086000b043c0c020b001400c00d40010136280d01c29401a0b2840d0f15010002409102d00c980490749001d45281d8080c10342581c0316111078503604003c1d2104000040e004030006191700c14010550090100610b40d0310301858600114020003a0080c4070044c4640c204000c0d021064506c0034011600049002c0c560f685440c608100200174160418590724000702c0141001da00e0004039942e201c54a0201d0300c640350303100c24080d9030500c2000034080200340c1c40c03000440d6950000c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 11212336 1250 11211086 11211091
    0x702012006040b010e04031409180108010507170f070c06060e13050708070f090b030109020306011e090204060203071103070b0c0a0507050609011209020109090513020102060c090604031112010e06 86
    0x1c150f20181039882c0e0715416030744c2c64240c1e00a00000c25100a00c0c89410321013004101c08040117254111401c411022040001c1c0c2c00d070301c0310495075074800030042007a030042c1c9003400140c0600103a6090740b402003503022203448003500ca0350400c47c08580c1306080206903884400a441c21058a90070f610300340c07000c412809441e12048950b8011200000f40704000011070304141c813070105a40a46c40d04040045000340718040e84a6815900c1d0b69030540540c40a01069010f4074101c00480308681419503140c02180303ca0380400403140c8100310802c4116804015141c141c0d80c410f140840c0c080004001901c6c0c05119000381014042c000b070030750503000340043d44503030351482202510382d8241d85108015650055150041c0414ae0104d0a00e80450169001c0018180b050421305002500d50307058100712041141c04024048500140c0700070342d81c040080700c1e48a140d540b490b41c03800348080040380080c003a9110052000032900e181604c03c1d13a452956818452405008203c4c0c80031503c01d10391380d604207 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 11213586 1250 11212336 11212343
    0x203070f080603070302130912050403060b01051602091801050109020a090801060303020a02060304031e05071a0417090d12030203061809030a050c010b0409030216050402031b070201200604 83
    0x10008032105990085151030710411008024001c114030303540a0042c040360b540b401e81102951125180c0000b429403010076103c2010b80d43d42c9440b103040d460908125942042d03003905210050210001c1c81e0b2000a0039055158156062071803500c6203024205a460040d400709065420b00340003140c0c81c0c44903409003110035201d5031000700076580c402007203089554901018005030409010307000541040d034019038110340300b07203000b940c68100f801e0110300c1d04040075810000100e002136100140482d040941e100800382440520050500355100301c03a4000780f25807030320b00c0d000100d100009541c507000c0e0381c0207041e04031590031244864008010001d600c2114114402e408140d02820202e01c0d41490710301c21b01d6a8402940f801c5600780c01540c1581284008400e5903417910707480c88040d101d9010f440c1801d4800c3d0024803050080c044105140d003020b41142c3c0c0124814010801c08541c01c6c252804019034400c04143d50302c0e224001200c00103640c00808541c10394904010300c08a4002803854441d601 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 11214836 1250 11213586 11213597
    0xf09020c1e1f0515040b0d0803060303040e150a0815061e030102070c08011803140d110703080a050109090f0209040201170405060412050a3903020303061201060609090b0607080409020307 82
    0x555000304001c40d00c6c0c0403011604500c0f00c0003000c0006e0090700c01103030449002001c1301d091903681c42c112401c6a50844a01080303480342c0c40c54035014140018408090110800504801c0030002c81051503603400030300842c45000d5400350801c03000c1ba00440b02103104000707002555500d4860500d0340d80740c0d1f103512134400158a880305188002640300804509603500d950341200703003404502e81d81c1c3c494202c42c2c0c14080681e1790794002080021340a0042c02036621a48890380c092030061080000c55005a201035501414011032400143e0044c4880c440b06030304a40c3c0302c0b0b903511503000490b00304242d00d5801400480e160240820300000040c40d0b4030603886034404c0d11003282581c40c00c80703050040922042c0400c003181e4449890000201036110500e01c03ea0a4500700380b20007207414074a40124a080d00507800000a000e040d0400c1d018030040001218000d1203034070310780200100800714600c1051f8202d5070b18110f003012607071144125100250014605900c90341c5542110f00258000e460000c081b03807 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 11216086 1250 11214836 11214871
    0xc0c02030d0c02011b0503090909010c091e03060f0b03060106050705070f050604090b0f090703020c0111040e0f0c040b0a050405040c090803030c18060a090f09020c1e1f05 75
    0x140700d00390800d80b01d50f060f540c03588030342d0100c41259004c203040320080712030b40000d00100740c5580340c4034221407046000800100b00501001300240c004d10003604100d8101c214814901078081030001100d0131668003850000f4426209180d0340000d00b4481c2503541d0600905000082e51907002014104180c020819203080c16951615940000320500c140340d0407202c1800204501c441030380c0004c01c030f00300141501844e046820005881d110040341c104010a5003c20000049002403048250300b0f0b4007602d0366450203007800b105c0030765124000d00c07200030180c118000030320f0100c1240039900100520001c00b9101c0071360320805003081c0c106004080c0202e1400130301540c414800c0c40350394100c50300728016501c5c1d034489034020101b81c3d20110f01241c014601c0304890a440d01d0301c7c4020030714040307580e0311000d840d41000402c3e18014001c1e8417080610303005108213001004041400b0940d408032002c00030b00c10103903906180c1480315082260400000c81502c555212444d90041d9102c0c03504105040e2101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 11217336 1250 11216086 11216113
    0x30903020307080d0819090605070302031e0903030f07021203040804090b01081915030b0901140106020a050c090402010c020d0302150a0c0203030103020d0c0305070303050c01110301080c13020408010c0c0203 91
    0x1030019010204c0054034030004aa8260050503107908282002e07800440e642c0840e032680c00680f48165807400000b60300004204040300400140c1c07883c101c40e000d50070214141003000c00e035280009030520fa4012045408107011600810524004001c0e4000c01900c07445c00e4248006590000d104568005043c0009080e0a41c800c2d40f0040c803640e96074034500514800d10040200a180d03507000c0c01c0800e0100940840800c01003003049200702125000454200302c84050102d030844180d000e0025544901136610008002207204e141001054034101c1450ba6a13000480d90440d6400e406904298a44405410b155021a400e074100d9095140032825072500941c000448801e404550010381040c0010300040c54041e503065419801010110280da03142e80303805041c41040e80c021000b081e030000c0e10185410080c05031511043c05104601d086625000714940c071101c0c80036405100341c00701c03800c250f0314102c10750690307024000d020300802440d040320174090920803074074800364464801c07220542d015 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 11218586 1250 11217336 11217343
    0x5040302010605040c021c0e0307030c0312080601050403260304030305060103110405100503090a020604120b010f0506030a09060e1b0f040204061b0807120801050108090105091e160303090302030708 87
    0xc0317168a82c02042000032071a43c2e040d6440030138070f021041201c0304041c60312a690400051000d94081d0410011080c0342d8586004901c148800134002d02c039840d410803546a03084415034013204c3e002401030304e4680f16420340740034a85001401860300e1b5008014042410750551040d881b8200a0700c04002c009803005202c4224025413140550008034140c01c000054403440c06160000202002c80d0440c3c1195400103056400c01e0b081a0b80c02e603c0310500342c040c00050403070280141740d40d14500c50b181d4208400320f101840b008000c41742d4241c94180304c0c0104680d50340405641041402600c109082003528101c002d948e01d04464841c16402102c159103150501c00c6030125152038440307480708804000c1690241060f0382d401e0300c4444051000c0342c08601c090015044e034031050f64600c1701c59030410b0005070820b1070240801e29a68504000c1110710540024010003401c0a500e14142c18600d9040b120710705403680700d034510039110306140001015040219002542d00c22015604115221800c040c0c0c0d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 11219836 1250 11218586 11218601
    0x30f061d0606040207030306050907020604051614040207030e0904120306060302090904021903060608030a0906030b03100f02070203120d14040b13141b040c02010c09030602181002010504030201060504 88
    0x110780c221001049007450540d0003041142e00c41e04000c50a150380ea000a0a008012105240540c020710100010410140444a40c009007044e10040050410b42c110445a441c0c104090085034000f80701d006241c018914020310420042400c0650300c1e040c540125106080e1409001103410001c010910310700038002d6803104c107000752000190365625005c00c208075004403640f03d980c5405110200103e80c050240d42d01424050000b941e40321201500100803500c2076010408141c5482c2d08c40049550214403104590a000b5002c41c1d0a810310b51a50002d00c00c24138000e50611901495a01c104003180240903402d0030407004103c948032000711291444406c480003000e84404d0000102c0c10403e190034585401e000310382c6a880502012251840c146522010040a0204210b020124174150003a002c03947d800f48024071040d04004406014103900703000050007142c003c00d60514504101009090394803009290321481d55003c0c0c0007900a01055405400550070110b0204039814140143c10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 11221086 1250 11219836 11219891
    0x20a0305090405041106031e07091503050a02040f0801061509080a03030203042301050415020a050f0c030906040308030a0501080303010b0a08060102070e01060f02060912040b0a050c07030f06 84
    0x80c40e01a0301c1003004001c0000034000c842e02030710b02074071520740e07260f0001031441011103030a0691038010f001000118600700130000400c00504080c1400002480c442420b504002c50601052544640c0059006801250020100702c110188001116401500144225610a1b184d04031014066008440200c001d00607004558020341d44080060f100c0c2c2c0c01150312030300a01c04050345440d00b0200e180040b00700040c01019a4551091001f0711480300d500340114003101504514040e904a40503004e80980700c9001140d040110340d460388000d050049902e4504001c181650340ea4072442e00d13024a4109482d4000041e02e4000040356205001080780d060b60285c0203500d09119400c00c08503000c0307400802d40d50441c061305800181e4500800c9600d4060101d6499107044040b0740c0b90000e00d4544020120750050b4090084100c00d108144211410b407451002107940e6504140c6050301d851281c06a4911540f18800d00003043c8001c5c0c41003480301c20712880e018482c40c042d400301061590361612409 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 11222336 1250 11221086 11221097
    0x903031e090b0706020f03040c05040c0305070914010210050103060e0d0306050307090504140714040c090f060e030307080d15050d0b0604020903010608030c0a0201110d020a0f030e040903030b0907020a03 89
    0x50244030304402c0a40b008502c80d580c050f10780004001003480503001507030b0031510b0040e9042c0c24401c52400d0302859040100701d2404100310316147c1c400405e640d4451242010944a0a0742c844669109118035030907040c1c0f6001c180000d507582d240800052041071104141801000f18a2200a01c04e00420040300e0000b0001c00b2018100711000c0b00074a0b0151007150070003801543e8010200c0f090291400030060307001d1032256a03601c0d4060005640c0000d61040401000c00410b1190341407003100c0005032600342c5401e1f041c01c03003c3c1d4046861441031a4000d4011600410f030900e0f00410313604040150040c02045407880c0b680c41d401d10201002500b0010701480034100000c03290b05003903001e80b0454500800100b800307561901c0082c21a4030079502d03002d0030b030408800d001c10740d40c10a04404004409000904026802e458025120280c80700020004000300c900d940601d841230039401c00d43c410040c400c1019201a190250080030425803040c044d00e095000070705591b001092442c142c0740c01d074a54 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 11223586 1250 11222336 11222339
    0x5060313080a09030609150c05040302061207030e0f0a020324060405060102010b04020c0102120c032a190503041a010f0306180803190b0a03111306150903031e09 71
    0xa0281c1500720021200c100000c00340000003042440c0a0303c00010300414407007072000140c090341030a68104004003c18004c04010800068031540d0807145810b0908080280580b92031604402418403030007007100e14803915038540b03452840840c980d035509100f00e040300c0c0e50201100240c550306681c00c3d4020003001d080c03c0050600d061a07046160301140520000403404011030004080760001d040044c00d6079030101d003000000503600c611a4000c040030f81d405045140c10000c0d420050660101c3c0e0440048000f0312100e1080210f00350f907002111400c50031400b940307002c0d0081450308200c1c0c0603140100303c04003801c0101044444541070760017002549080d84d0968661401410120010307402c0400f91399080c034081039482d006140903150130420a20841c91304800c041c140c6400104441c8210003c82c01000090007981d480000d4460503a0b448a0340d4502e8440000108003d9001c0001001985c1903849110b074401c41c21800e40e442610351800740040020480300703005008008101155040c1c10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 11224836 1250 11223586 11223593
    0x3090d030516080402030705040507090504150b0306010c060204030b01120201020c0103090507210b010e090706030b0307031e020909010b0418050c04020c1002071203050106170103080310030f0807050705060313 92
    0x740f00340c0c0140042c0c100c542256032003012408036942260500300082c20713031405104a140c613000d003a0124000c090a403424504003401542c0a100240c84c035818802c80e0000f010400c995034050710002d542000d0950455a9240c00c0d00c6822084401d00704e005018420010032158020f20803090081d401100070482ca81c01c0000000301c080b10056150b100c1c03040c034500d5000007001d00100728041d042c0d1440c11001800d00140f094600680c0750042d4080c503081000c03105003910006494400c1f00c3e080071a05440e1420110000030007001e001010f034201140c4410040d29810541000500c03460a80e030800600000152800b04071660f400d00504507008556104030914040d00984180e03007411041d507422414069888040782c4c400c0d041247c0c080359888505e00c000c0c4e0144101801030007a401d004600080010382d80c13003003913014000108041408008900108523001d0180082c550081001c0000190350501010365000101c085649108541011038582810010303a80500c034013180c2c04401b10800d03038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 11226086 1250 11224836 11224847
    0xa0b181003020d02030123010203190507080405120607120c090306050916150801090b01050702041109031b03060601020d0c0f0317040803100f05010c0f0804050d0803090d030516 78
    0x145003004240d02480840b40d03103507aa200850080045412903a003105081e40b0680000c80740d000d030035040d50020f105554886c6081180301d44a80d619241483d41e0344043d14041c107403406942c004581010209181c81107690002440718003451041e2100c5a02101c452a001e040d2525607591034005002490f0410020351a5044550000000e1007070720b6a805c1d045400a10040e03180c3e01c00c41e0628602c20300d4000d41e40d0088407040c003504180c1030038440c5424500001e04184a40c1000a004a50320902485c4844050050b03803098480102640d040d072002e1184005601c504000d017500c00d0003000c02041e0550700029201885031040d03162030120103415100c01c9620343d48000305806009156068111000f0b6541e080c0d8400c80c891208140c490030110010305504d074441e00240050f000c1ca40c4103210aa82005a81e2420303503111961204454031071405030b8550043d03512058110b00903442d003004001400c000b4500c1181e814084a40315815071008800307650095800101c85078142601108175403041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 11227336 1250 11226086 11226109
    0x201050a0e0309010503100e04080a0809010501060c0f0201030f0e0706091508010e0406060e010308030a0f050103080d091104020705070e0a090b0105040209060903120c01110702100f09030f0302010b0a0b18 90
    0x200007d5180f0350382d1400401c4200101d8045030b0060700001c500c2075407a08840c02e5a00710703140000800503903040017409444170444000c042c2c0036000280c0307841c08681c4240c00a40b8120307462a400c1c05904400354801da41c8104c0ca014820118441c1f00002c80c001e1580544035a07901041c0e0b0b0f51800c51303440c1c1201e007010311801030810358a031a2690408200303080240d00060003548039541155803498802005404c0310080281410b1050400c03004201148480050b03400b04100244000f0f140341541c0f0341000001c02e09000701c9d420a0003c15164103001c0080384040843d00d107040c49452550b03440f04035000b01c9843c4580100188540740041c42107041c9a400340c5801440030781150310785428000007910300405030420080c0508001070306074104000f0300805c3d4064080b00380c2070f4141041a4001141c0c0c0b5021078800f81041031508501e81c406200e680a44020f5401051800d040c00701803c0080c041c10300076084a00403064880001103000400e01142c1c0c21f0280c910003d10748250303503000c110105441 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 11228586 1250 11227336 11227351
    0x10504120503060310090b01051f27050d0b0105100203030702030a1202270310020903120a020115080304030b060f01050d050a06170105090c010e01080103120909020c06070201050a0e0309010503 85
    0xf0840c005d58003804a1003000201801100b0303144a03903240c0001c02c400c090b800c8510046d0354210f202d4058001e84c00c004201040041e83c410480869140500410382c05910b500c450340c0040019508001d01c00c0171015241a0782c000d036078881203403e01c0e040580c0d89205c20f55050005078401c01c03203400700e603105081c900002c00725100090303e03250280d11032030200c20440305002d40d0040d40710260030480c5410085050403100022095007000010030002c0d8071601e10442d0b10a07403130301c00503100200610030740c017034540b071b10f0700b002c3c40303440262103800303880c1c1e2030b0840c0c0000c48031301844030040b4540f441d011144d40c040c2c040c149d59851078006603c1000c00a404060042c11003203448150108400494040c10301c1010100000010a494100110380c41c050022903005d05020909408008c666403080c0c41e5070540342c021000b64007200301d170042107804440c141e0241000900c0803c2c903011a4202180c0700c0c0c0a180e065000b8402500c4c0c0d034642c0801ca546164040c1000d03402001207140c0355000c1c6025540c015107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 11229836 1250 11228586 11228593
    0x1d0d2a05031b010e0106060311040b07020604030c0b070308070305011802070507080d0c0204050f25050d02070b0411030706020d0f02030c0a1110080103020f041a10021b030105041205030603 83
    0x51600440c81040014400640c181d440d04210b00304084d0910500c1d004204074a402d0149030090020741c5035904c0b4a00902205002c005511015500c620044400460b80f10342082000b035920242119103400c0305a044002075603110104810798842c1c01218143d46005a80c80740711001440880000d51054100311094001da01002490701e805111810640c0d900d07440b10f40005072103104201c11108010814100ca2200006101c140302c18190204180361007011f00f40c542c005501d005a5141c059616162146800001c080b0f08204d1004105800789110b040c0600c4034603103207410552520946e00450005900110b050f900e003520a000078960f4200500649188c01c0f00b0560550a10000302c0068034602c0c2602c142d454581018007050079402e40a00d0116225411075000925800e0300d1442c0f03a20550721034074045c0000d02c1c030f03000d0b4000c3e24100400c0411001d260b580040c0d01d03215142965441400c007100d441e100e900301805640d01c160f0744940c0b02000e11038071141c240d4681d0800341c0702c03641511 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 11231086 1250 11229836 11229847
    0x5070c0915090b040906060b0405012c0d02030f0105041b0501030207200d02030f0105100f03050705100909020319050a02070503070221060906010509010609080604030c02131d0d2a0503 81
    0x1d00c1803040700c015000b008d00d042e640301d003054000341140058800c100000f0f1100520300c20392103d6944040c0704520110385000c44400c603800020314165088007004c3d2031303510b004180310401c091210802c0544030620f2440103110780d80c00040d4228050f101e000351248400340c80c802d15040c07890183c004c020000504050f0798405a801082c07816a040301005042da43d1754080c8060b003884070400400030040b8407802c000f40c07821070f41d4660b294032540c46650701403109007032000803031401020301401804202208544138a00380c04608584502c0210041205180c540840c4030b5010a000701c4080940290042d4a0101b00781c1c244030142941c10441c1c45030300700c0e40b00d201c400140d041c03000038040d4150030300904080d41803400704282800c0680c4404140581d54104004070500450b0140c3d0040d0581003a0300c400300300e170002c03840c1c1d58a00c00c40260303c00e00d41b0f1183c040b528203442d072030035030245240300300c0340441400c0000340e801c40d5408035180382d0800000403162001031100503801e1228850800c0c0d03402c24 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 11232336 1250 11231086 11231093
    0x120c09040215040e040606050d0201050703080a0b1c020f040501060c020f0a0302030609030301080d0807080103030503090a0c0b0a0306052e0c06090c03030206100b0306010e060c0d05070c0915090b0409 88
    0x183c10a0f00329481c155201018803007805514040c500280400320380642416805a0010b03102d132260350340c02014860004001580d81c046944070500d00000502040580b1455550551248000388c2080344100002480104d5504261040e141a00d0440e201e100f6103000e103400b048a80b201c005241544a0522000440161001e0002038021407280c0b00540e225414860303100d00f811491b41b610010000314808002a40d0340c003130605030440ea01420300f0b039500c0c3c40760100c5071301303045003180c004d4601c007400c04000882d0103e410042c601c4014580c1d00f00b003115100d40800c00c0c242c40c110311b041e40d000a81d50410300450000704031000e06445900340004400016524442990320050040c2c0388402c542c2020401d043d010300240354000c00e210003030702c1c40600788031136201d06000c0903201904000080008000580390141280e0581c0070300e0085541050b030140c0d004201c0e82c412036003110100800c1e040060b0743c0100380201451640f0114400740d0f60340c01c001d400001880c0807542950701544a58140780403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 11233586 1250 11232336 11232379
    0xf0c0111030414010c020307060504110d080a030b01090803090405060613120b0105030102030f010603110705070f0503010606020a050c01030b01031e09020306070903020d020d21020102090f120c090402 88
    0x1112100e15403646450b0500c43c003956044a902c4035540d043c150304038101d6602108452003164401c40000b41d5440c1ca0401007960700003134008a41101001441030144481c8070080c03d01140300b07603020310215010600460309040c01d4410140e9580c001d0061a02e43d247c180c00039507001201600403818014000125100c0c040c60354030614600e00344880c0300d41030201c2403800030301400e4280c00135803542c240040742d51341d0f0440502c541020141d43c5ea40038a201d400320411103076900c0d0002c0441707030825260340043c201d08609104072440380d8a4803600080c0d450001c1410902a42c010740940b60407480000154080c1803da401e141c100340e42c801e10300749642d084c03500303001d418402c1c0c0c5800500b44010f48145813800030060060018810f101e5001c00050751060150204560f058500c03418a261034901721084035801c804241ca8910800948035031181e0560191100c440d084520a01c41413081c0203001164405200d28505604805d004420b281444000903800c284017900a40c0310004004025a1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 11234836 1250 11233586 11233601
    0xf15060c020a06090303120506060d09050105010e010f0b0a050901021002070305070b0a0506060d180203030703080907091a01051602030102030907050a0f060818030c1c11060712020f0c01 82
    0x110308019a10400d41c24040806005003985090003800d10b0f04644000e40402d4624107405d5640c0d44540c0054110344410301500d0b81c3c0c800e16441840749907034511b03025003c0c0009024004520100600010f00300310410368000c100c1e500500205c2c905080c4020803190340c0e01642c42c040c158402c4405080441c2001d05c01000044d029a4415450700168504140c0e03089016104080d218182400d05c00a59035400450303260480c409000581100100b1549030f45104001c4007a6041c000410709000303240c0c001e400c2520603880d1106031002107440d030915000b203c3c0c0c40300c4942865000038400c0c540e194000c00003885040c00101074030716850450350010b0b00307990040f9400c01454221440030055400c0010f030710009031011114005c4c902c1c0c2003820040055100030b01c107008030304000d2201d81e4580d90070f00c1225100c002080598200c02262030010780c00d005181c064a00180003100344040d002c0b008100365003c2e8410b81e6034418060228a0008080c0d0000c83c40301810b60000c0000b000f5440c001d22601c030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 11236086 1250 11234836 11234849
    0x170304020d200901030b04030206070c0302070501230408030301030515040c0e0705130b04090e0f0c0405040317041a15010e010809030d02120105040b0d0312020318010207050c09010602011404060f15 87
    0x2c6c0380381514009061403406461402070040c0780c0c19842c0020b80104204050724070130f180c00403500695241186006c401410300340d550550000740071038048004030046050340c1c040c4007200c0002c3c25400094946080413500500566040c1500b070042480480c0c20681145683c90141c1c145800003d500764a14229400402d4400300090704002030a42e9026a0001c0110400942486840241150b40303501c5d42d801d8152041e507071100040c0416020702e82c041c2499000c240d4040242ca007614020707403000d82011440202c54000c1000642400c95446a0328120406a403103071000f00060b8015aa000000703412000d10303000c14000000c01c034510f132010300649481e584496515524100c20302c4201c82d425200680124013610140300031036000542c41c0d649141c1217800581d2650750040c81d183c6c500580a20010075400020813500380400050300a20040c4200d410f420f059076244000d03400c803070300010284c003041603040024001c1185a4404820203640840114031021100c0c50444890000d40041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 11237336 1250 11236086 11236103
    0x902130606090503070303050403060c021e0105010617010803090d0305160b04110a0e1306020405041b080105090105150c0705190e010b0f03041b090203070c170304020d20090103 78
    0xc2080590000b0480020701090b000740282d6070440c2c5009140e0300c200d000203010640c0b036000090015100b004088040450300b044005441115030708240688000c0c81802d00042441494030341e41d65000907034074101c803100d8000318944003205083c011082d0034100f09800340002031100b1001d190803003414115491281c4c9041e94541780c2440d1103940b0f25030750301d6820b02501c0c81210500c6800c01f04000580c102101c4040591102d0041c80c003440a2301c26a0040c60b0024103007004060300481105841d542d10317540f5160f45c8400c0ea200c10500c212040c0c01d07c51254040c2540782c03400042401705000b014844812400c3d600f08980b1140410011201401102d0003880c250030100141d880c5806d07403602420900044901e4090586070010b000d000151015040d094002c8250309103100050000d0003c107c0003405540780e04c0c04c0038000e000c41c2c03503000c2d0503255210820020242280032a085034403c0342d0042207420384048989503030946c1205c0d0058080c0281c1c3d0b44502410b19902e80d980c8038029880740d0040d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 11238586 1250 11237336 11237339
    0x1051206191508130c03140c0a03030306080d1103030703090309030606030803090f19020112140901050601020c0303040803030c0f0c0109050318031b0103050a020d060f0302030c0a1a070609021306 86
    0x1d020001c0141003144c1440c5064403000043c2e18110403601701c94004a000c0c11011403001c01c182003610251526601c80e41c4070728004201500340c1c008108231494182510038241008200780c0e8070030340d0f00c400503045800800000d02c6c0385000e6446032222501a00c6d00b40e000750780783d0740c5440840b06140c0084d103400340080b081081c40a01000b0040e06400d40d44044c00c0f1140c5070401c0d03074407103549a42c030080c18010702081100158080d070b030007001074a408100d0508581800700c00c5ca402058141c8020f030060090440320002800e0010485003201c903410003c601c2c40d0f554801a02d19030708010107060714500b082000001c908400d00030590030500a00c0919500c0010b07070b101c244000b060445442c001e404c03100405c04407518140121551a00a08003c00c9a43d0b81513501c0c0028411000425409454945e011030503201c07150611040d64404d80458074040a04402c0114483c014810303840040c00785402a40040c1e50007018150061049074082040a4545c1c0018018a503905920038410b603209030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 11239836 1250 11238586 11238629
    0x9030c120301080111130b1c0c03050405070602030c060a020304020409020303030c09010305060f01080a0903020f01060605071a100902070c03150e100209031203060a05090c03090c0102010204050105120619 90
    0x60000544680c020f401e01d02022002c8100c942019446014900e64012602508520201c0a40c9809440601e801c00082c0f1000c040580282f000b83c406481910401402040c1103000104072001d0004220081c142542c9480d540e0003e50700c0207204980040d21201008010703141003010350b0044540a142a89480e94000010119039000b0005031103841903c2c2c58040303698100100b039400a10415000c00e84801c10b040581c07800820340c0e1280f034a17600c3c0c40e60020f6240c2d403041c0a0402d83e031054581b00c15140121481c0c0100c0c203c20386020b02a0b00c032800d02004500c00c59402003000c24814201c07200215504e0f103d00c1d41d01400d024400604030b0319014880740300002070202e81812000c11f40110708000d22030700442d64881040b4807940071420000003060b082e50350000641d0041c140103048944ca8901050302e03010640003070f1094480c0e44140b0f080400258018000d0347c0c2590303010303514207080015803401d1183c83e4801070041904000404200745602000c103d510014207001d5850a201040004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 11241086 1250 11239836 11239841
    0x80d0e010201090201080423030d020706050901050f01060c060905120a030b090103030509130207020603131e0b0403140c071e06050301050d08030c04150e0103110c0703030809030c1203010801 84
    0x400990441e450154034000603a0000d541c0c64010350403a141003c600304000b0026001d0504072281c8145100206185000f20342507001805400d100312828011503d421005500345d410540707840301d001520400510581f031044030f40c96405030007607a011840b0029030301e5640c100142c8184030340b200c0f1800911080410f4160264a81040c1c00395100342c0c080d032458800905174001d0082c100c0c800c4481c950300c803400d1005901076690994004081d81d0396800c01350190441100740c140b00301c90303000d1010f07100e0186100850503000c0d11500300c80354034a5580d4644e42199072000c0c01000c0d1082403000d00051141d14030800c11000585100350a071004100592900d05249082d644200100f0004100510103511024038590409600c05a06030300c0c0d844004003100305004641065900d4000c0e0040e180c0301c1e9078001d8240700341540a0301c2c10042509481c0003003000f4070a14541d10b1250703000100c2040024401c980c60344c0d00100c803000f80ca04040f860807800c1d08200100f10407280b044008001806528020b2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 11242336 1250 11241086 11241107
    0x30a0207171201031707050c090c0403170703110706020303010603051305010e06010f09020405010e040903020a05120d0c03020406080609180a0302060f010b03010f031b03060f0218040b03070909080702030106080d 93
    0x205c04508028480d070b103e960300d8002c07d03c0540600390324400710ba400182681501c010b954040780b42c02448a61592441c11074101ca4002e40000f048000640500c02d40868800305441d52540550319680c20140160003500d00601040784c00303201c0e003100c2c102088081c400c603440c2d40004405400301c0d51520251480140355608031042c0988100020005d90303030040707460000840c09840100e003258540c02d0903400c0210080d406082c81c080c85642d20800e00c4000010948038602403c00c00604445d03100c100c0403400346000d5600414100300100e446450301c61903442e88072404114072008403403020b0189003841c401110880142c0d02c0031081c04040010072000d0390240404020950840d03141061400d0190514800030700144200d0030003200c1c3c0c4504008800c042c1da00a5020700a0f41c0718401444000d5011646100e4128298410800035240c540a00224048020020f00060341411412002401c0b0000c0c121842001001001c0040e1805e002e1200100032081c041d00560004480150013034054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 11243586 1250 11242336 11242373
    0x305040201030e0c031b150a08040501060e04030f0302030402041b0215011409060603070e0402130501020f0607120c020304080d0c0201090812030f090c0a090614090408030a020717120103 82
    0x100f10f5842060b01e00241c40034401c00100b42c0b03061241441404609107c401d10049040c50400241c001d1040d601b2016641c02203126000802c00b0303036950070741840102c005544c0103000580d10519009a24441d4025541050008000080100d18070000614400c006401900544c1051000c26040f810a0850500600743e105804c40e620300c810000556040b001003106100305c10220220302c465226120f4941001d0001d0002c550b1240480303489a05c0b20810702c03070b00b030041c49280341a0140c0b41d0b01081503800350310710380c44418192514111303190191115601040443c84140320019400004020100103040103071621040552280001010440e0580058501e98801e4802482500840d41200d03030250400040c0d440e40d40340c915109041c40d41140701240c5c404050380d8086645d04042d407200b000c642c010503100581140c40818001010300441d0060451002800041c039007994a40080c40c4040c07084039561310030b8282062581c21608074120344000700c00b40c1c400501c20414000d0030011780014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 11244836 1250 11243586 11243593
    0x60f030606060409020705070815010906090c0c02041a0d0602040f0609080a020105070f1202070e0a0e0307120201140a1a040b030d0c020310020406120506060a05040303030207021c030305040201030e 87
    0x1070480c0411103d118034810354941d1540000c120f0280030f0240543d1010304149000e581078a503d1124207859814280a0702400070700d4018000740032130043c8540c0364000c00d980c5507800600007036020400140030a504501c00907500050100655403645801c2883c10300ca0640162101d090400742c1d4280c68036608542c0070300c40100e0003400324500025181811542c2481d01c1035442402d850101d850703034004100101000103240b05104159004a0450242d40e0f241c0080e200d0b50b07440c0c00c3c203681598014400380c80a50820070150004c12034101c084e6a0203130301d5000124516001c40c1c5201860075040760109100d41e030380c880203d10300481a45a100004045a09003c2e0301c0c0400c00080d10382540c40d28103000e1103444180c80085480600400000d050a414115102c50b0f542c3d0000e48603408048942d00202e1038400000d4040c54400151040e0503450f9980a003402e0441c3d8081e0300950203020141e0707101011068444610801e0340c41d1a01191095a01040c1c2c0d04261001600341d428115001004c1d80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 11246086 1250 11244836 11244841
    0x60f020304150510030204020712020607140a050d060f03030f09060201060b030a0209010c0506070507050715021e01021e04080d0305012403140405150c04030b01050402070305090306070206060f0306 87
    0x4181c1c90302e012810b42c8220b070010b8a91601d940c1004d290000383e10003074010307001149203000c0c89680d100c044400f40042d000d480c070590ba400c60443d0500d512000500c620041802500d080d64410780c064017640782a003030001481c43d2a1031414030b02c4592548100c002070a44c207100000a035201803990000d00681c002800214241050025540402040700380e426030302040018003030b07128104200b412a000f00c01d071141828403820080596000e80d000340d03154403950100040400003a0388898046101e60f014103803203c403032600c070790000e090181100095902841b0307030280c810382035141c0a004003100781e180c1e595500d030884da9400c0014441003001810b142500410180c018004030300c5000c2a01d500c103070707400c41c483c4000b0790082c0f280f02040114048150b0030801080b07000116404a401080c8040003039a503040182d00581c07141c0c1c00010040706618004000904294003d404200e20a0904900307040078040400c1c6000401c452030001a800700c01030003070078140741e200d490603900103401030205032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 11247336 1250 11246086 11246093
    0x1005030603120a05070c030b06040c1103030606072402040906060206100509090102160f05150403090905061c03020c010909140610050408030412030f03020315010e01120612060f020304 81
    0xc50b40301961581890000400c003075254411130031a20301030303404100740d08030b5510303403d1640c2c00e94800c48085000d03615014031001010b00171903c1131400d0880700005c42c50b43d5101c0c81800700340d400080c412203a104840c2850303e115000c076052058400b41203e8016203c920b0004000c0c142c6085a0061082d90403110511020815287c0c0c01d4080c0da40665051225071662940b050080c81210030701c0040c00d065586c02020032840d1109414030720301820888401d00750710507601c02e03269011303034009000c41e03001c060822101c030503504490781c403560041a6107095890720000c01e05a8054200032401a0480c081e0008190703000400803000d0001c040040241030b0b401030b080c1a101902521651040545032034803540540700f2801c072405040210181e07a101da94407102d00b241848000021030200d0144004c4c480352a200e4805d580c400c80020407002e6150445c0401900c5c911400012581080341030714a0311980307111030042100034600c1000d1050404440e0410b901110f5010071030300c1290740100140b0010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 11248586 1250 11247336 11247343
    0x90203030d090c0b0703050c0f01022b0906090503030609010b09010f03020c0a05070e040b07030203060607020f011202031f0b0301080303061c1a01140a0b040b07050a021504051005030603 82
    0x62060811000482071054108040f80780368660044104200004000c01010384c4200500350400d01542180c91041a50180354240d01414050302081448040741c01002c1c900a00082032010542100080402070303611080d06480c0e4218058a03150b20000510440741003540c0e441d80101866190030342007848a5000030b0160050405040805401141c50368801c5018403120441990207022030340200d0391b0342259400b209040b103003641c4201d00c80d40020300460003030080781e101e45401048585440301c1503007000691009000e91504014100300651016440c42c40114015150120111004469000e20700e070001042e800002c5081ca06000401c0500400019a41c0001c01110f0190089041c00c2880d078803001250400351403280c0891b0a007550000800038541a645a00f07004004228648280034a0151714444c43e00b903403600700020010010745401400c41103118105549000503140c0005003408072000d42901d001c40c000608122528060407240c01840003802c1060540c50840d0010b505d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 11249836 1250 11248586 11248597
    0xd09020306060103140a020919090903021903050702091905040809031b09010303030e030f04090c08060d03090504050601110102070503090f0109030506010303050304060908030a0516090302030318040605060f13050409020303 98
    0xc6c601d4000c1004281076071400180004c903c00c5d09a40b2440e03070340d0b0300e01c07039000b8166044059000d40aa14007000d20306030190314074150345401d48c861b14504282076083c8038003190010a41059840a401a5021100340380030ba94041d07801a030036607444079011800c00d41071040c00040c2941d1464040d204980319114440300904480e0982000903089040620741030452090642000d098400060302250209090b0710040f00c00c4000e0f59901d90540d0b94000388900b0018840c0e010f408107a0b40d4204022070f10745500200d910000604d00714110076101c1c0c10b15800d98010040031211a04003003041c02031400e02d01c10480080c2424a000f07040c0500d0754955544556060001a040000010016051040701d41104110642c0100d07015501c0c6032001c400320040a00341e5241070381500401c41c01c50000c0c42103080c03e05a03a002000345141c02482d0840c0b001268071b0300b8807103070029240d41002540d56280c80203004841d24401c51141d035a01000782d0708210b402503400c0140310340e19000c84640540c0f8000709491 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 11251086 1250 11249836 11249851
    0x20d0206030402010306050d140105060105040501021e0705100c06050c0f030703020309160915050a08030a030207050705120303150303070308040204020d0902091501030f061413020d020d0902030606010314 90
    0x1075076034030385000480c05825030350809508841071420410820503240c1e14a203000000c4002008140c640c080110b81070301c10361094034016401900480f42042c0b4403004c00c280e82103444102d4070704503612400306050000140d4014007060054030424103025840c02101c0d0f020400298181c03816070000c1d45040b0600014005204040d03001c00081c1c04a10104481000341c00c00c030482117007081c0d80b48a10405040c88003980380100c944500300103001c0c203111108503b900d03e154003450503c4400c0004600035044104140e80780e1084c02000100c0352074210a20407540800320246560703261183c4010314801c204013505000b40c2c0100029070109a000f1400d9400550454001d6a40c070381e1031241d4000341c00d4200002c3e50191075074090050001404031521042074080c0ca0620544500000d170108540e0544208100b104103c80640141d01d08809400111a402c1344010f040003225a004d40c02ca0304911603d0b40c059683d903454500750716007001000d42c000000d00e42807040c0d500700240d20720b424030040c2445 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 11252336 1250 11251086 11251099
    0x80304061704060b0901030803060f0d0804050415050d060c021603021302030703020702030105010b0a0e0102060103021e010203120f0402040b040506010e010e1201020d14010509010b07021020070303120207020d02 93
    0x604001072900130110101c4001c201c0200c40d40c4074100300f40c542e442600c0640c03240c15030b00001030007414906216100c254011308124109443d0500340300182000e07520802d0400c0c405200410b2590700d0421183c01e5502555000806a0808030b02920341303041d41c0070360758500c091040c0c200010307682ca440c2c40b4403456290b140541c503625513110680181c044d84600039415401c2100102e850940000038007245079103030740c0702d1142d101c0e514016a210a001e000217500001c0010341107900c4010b0303484000b80c500040c03040b02e2a040742014510400041a1080c00c40c4040b054203000941c9031a000f00000c2c020125030401c01420020000303092000b405103130138180002070b0a400010b5640341c0001226480550096507a8039822074814010070b0448202500c0791850000484d05050155005040e6140d1883d11272501c9000c1e02048031940145001200704800e12012001306429501e091290031400801440b00509600d0081c01d080c0c00100380225441c418002c240160385d8002e200c03070890f901521030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 11253586 1250 11252336 11252341
    0x5091507030f0902031902010e06040812070503070c0314160e060103050a020f0a0201050f0a0605010f110304030f12090e0606040504150308030c0409050109051501050c07050a0f0608010803040617 86
    0x1042c01910054001075414014104001c40c1d03025440c90141c20f00380700340e0324468407284032010840140a2801001043d40c0242c581c184290342c50f900500c140d600850461b030074004241e503000400321031a04100c881000c881c4890300d41440401c500c1202e0b83c841f4a502e0030f080c0c189686000c80c220001e0566040503100c9012424440d0203504a40c2e1040d08042250399440780404080d010b4a0140d408007481c040c0341c40000c0101940d0710556084e220140e55880403102c259000710381c0b00c0c0408c2924000c50204000c0080015921901e0701c0d12a80705400c00c414030000000f01601d500b606600c40c000c90342c402410001c1d1079171010b080314182c8104560001c0c120000c1a109104810181c1001744400000002d101c80d241900c00980700304c640c44c0c003062040360780b122086025100107440e01c10701c06a04039124000c56000e6030285c249000e034070084a02131a41c40c0300003008044e041c0e0141954a4000170244042c980c085445c3d805009120000c43c80c00d807030198000e00401c940642c2525642c2403101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 11254836 1250 11253586 11253611
    0x60e100e010c0f02041506020f0f06010e070e040207140f0c0a0b2a01090212010903020c0409080702030604060b10020105130b04030908011104050f0d200111010e0f010509150703 78
    0x102c3d030a0310342d009041044514010b039041164090103004200152141d240320b8113182000181e10f400140040010704201d9203848516a4140d1007d0000700038020420034007070310380d100d901c081c208c002c4c01024540010003140c2010350501c042c0c100080307095000000c3c06200c54890704160011680e04d481d103582d40f00c5000000114004813642c4d180402e07544e6205001030300005400c11803010707000b1074200c1030110b9000d400c4c0b42201c1c0c0c00000200075030401146104646802d40c0b2069030310f40650029440c101955001908120049401f00e43c0c031303503841d2000c441c24102840500c15503240c0d8002048142803040030a00303450b0302083d004140440792000102018411441000204401002402080644103480c2e00e941c0183c003c0b58051030b500340b00c4080303a00d017014002c10703901d4100401d4480c20401184041240100c9403100c0d040c0507240703840011004007442080156446e01002d088403804800e081820b480018080000035802103071482038540b011212290040007500300060304000740750707 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 11256086 1250 11254836 11254853
    0x9050c091305010504060b18040b01050105030703090501050703090b0105030a0201080109090303021207020a15060b0a1101061e0807140102030d02030403030603140a030e090702030403060b0303040915060e100e010c 94
    0x200010450f5007044144010040c040d0461084000112810016a1480f072403503c08820b00300c0700940101825001007055500a400540d00204c0c90303d80495181070f551645404e4400a4070401e00185c0e4030346180003030141c01c1010074050041107018102289a9030002400c001c0d041c004c3d00035455035203102c0d10030907000c1e0303044a00300005030070108a145071100c1d01a444d0742151405641080b4000780d15105802d40740b06407001c1e42c51a80080741000c80c44802280c1d83c0c550044421581e41da100300125010380203020040c03550b9650703416148500c4c280282c82d810048251702040561616801d0324944d60f8010058030f80e00da4022000589070b680b41d042c110090b250541c0090001c1e12121003c5d1060000480d480000030302039180c1d00d6200314400c09200302c01d1011140100142c10510050000a03000d4019000d0080d00500f12801e00b1345841e01ca10403a04d502a8095150060380420040c03142c0040c84000040ca081701d0000314405400009401030006904030703410006402a03c008218541 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 11257336 1250 11256086 11256121
    0xf0b090f030604230106062115080102040f050301060b07032d0e03010c0e0901090e120d020403030207080a0206070b0a020d05070503061207080d0e060d0e030d0b0409050c09 76
    0x1021945030742042d00348100a22050484e8451240303402e400e0104411050180604598403640c0d000c41d0b034501e1903070056580251500b91a09203843da1043d50b45c500e0301200540141000030001661289003911540c514146a40401c0c000e90409004210800c0300c407007a26290303501030a1110707078001c0b034440e03042200c800c0d040c40580400001b01d200f40c101c0c1c1e010300384c1160350009800800510b42034802c20340d14040707204904d0b03900110600c0184400c00c400c0d001a0000064001182e00902c5104c800c1c0718a908403002d001203090380460104181541000441e00030481d56000d00000d41c07544d00401e0319880340c3d510181c0421000000301ea410305103641203554003682600b00700424101000001c0c069401900c10750300c900314008400010300c8001c1044800c554814000f000880c6409500b501c090038182501d50303000c007080c48249107120407400f44110805034400a5075560383c81c0d140810031102800300e9035014903d0b12103418005200002d54a001e035400715020310980d84c40c21140306205042 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 11258586 1250 11257336 11257339
    0x7030b0307080601150e030303040f02040c11060c21090607050f04030204050a091202070605030406051f080a0605180309040504060b041103100602060c1b120a05031f0f0b090f 77
    0x70f6400025000740042450300e41c2c0b000a40d1080c0c15100c401d41016582c1c04162009000010800382140051801d40d11200b08001c1604082009180418442c0d040c0074046440d881100070000d144010403c3d01d214810360b0351807002080c03c06080071854140e0300d5070001c01800500074006441c2c0045d82c03000040e50300950340180207110307030300d401e8156601904504004641d44005205415030142c00490007400350f40740d03655468159a281d4440801400300982840345400880f00864004000410700c0000307440c5039030003400c0280180c5849030864900521400342d0100d800007030300b500040030088821504017281d000c01c085e140c605000c1c00400e48004035031392091a101c2145008840400614455601f0456050a26540740302c2a6145c0e2012076000166087c100b102e100c0b46a64840342400003981502140c05c4440e001502d00c00a038407a151600101d1008400c104000c8032000c00500f880210000091f401c0d0718020312a01003500314060200f1a0a003c5a447c503d6100e01200d81c08202c030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 11259836 1250 11258586 11258593
    0x3060a0b030702010e0d050c0a020d0f0b0c0307020d0f090501080421030c030b04060317070f08070b041b0b0f0c0a020402040b0910091a0306010e0405010f0f1d07030b030708 76
    0x2c1220000e40245600d0319404158003c00780400003282c09802500c8901c00d108002d0b00203070102c1d03820800c821400401c22101601c15010b800c000c280d1280c3ea40344241c2c40708511613924140b0440191401c82010b0070f400410100708620400b083c1d0000e08841102ca0078200a201d13900c4518040a040b44030b600d800410742c60344410404510f0b8981c100d49246c1c50280c50402c0401295824007040c0c2d901c40c00050140a0b80d503c12000c442003000041c80d0385401001c04180742c60055403980d5943e0b100c000c0940e0002c0c42c000c2480284401004108401d418520704601440c1c9020321240c010701480b09424080440400c1d2140011002e00c05501402da00078030465907103071a200c0140c00c030b400248040d80550072803200302d8901030050031000151580d28988614802e0550520a240c0e8001058603040201d102500341c2c3c40d0b11a0300070345c1c3c0a0191150555192814207022600649060384506080c00006240001c1c03603580100785078101982d40340100348490484042807600450782e1080d140ca10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 11261086 1250 11259836 11259841
    0x30e0309031507110303010e010b07081306080a06051c020603090109020a0806010609080d05090603060a03150b010e0411030103020d080f030406020327030901030c14040e010806070306080a0803060a0b03 89
    0x221011400c2c3d200b074403c2e8955005040000c0c480030b590340024090101844007000041c0604280900603001d1103108100c6d046c40c0c40f048800e604141d80150744000082211103050020407445401440050503040c0c9142c802d21002100c00c50345c01ca040440073780154000400302e004c0c0c041c04e4001404d0b039a006440c02a0781c1d5501c9820742d0780c614091140304001828141c0200b44030380e010074a000c1d030300404c0c0e540b9800c101003801080019840070b80007035400000702d880000025059015540c490000e13200c00140d52800500141c40c7c44002040c0b6841540344c1078400c46459408426241981e4064900c0c54080c1c1c0580b801403c68440c00d800b200c400702c0c000c4104010031805800862280d51540606000064092005a008090322403c0205500103000b4614a94440ea2200b003140003140342c9041c1e002d100140b490307010341c05900500703100c940040042c465000e0800207a42c010740685000c1040710702e4079880d185c0b90b81d401000109141302c004045030b0b103551510010b0010b000150461541c90 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 11262336 1250 11261086 11261113
    0x120706060501020604030206072f0109030f02060601050d0f02040801050f010305010b0a030b010e060f040e030c07050f09070804050a02060409060501020607020f0318030a0501020706060302010908010501080706030e030903 97
    0x5400000084a01900340200894103502c08a84940500c1e4590001d00c1540c441752010348106540c12844240e0404c4102c80d001c40148003882041c00007607040000031034400038100100301101441401e415944414284074160342d112049954018040d40d001800050442c0c000000c0d00c105c0d40500807075030034603040c484d5081002d08403e048034458402080807a02c15010b0000398402031002410098108004000001e00900550361106001340256101d405d001c0010301110322900c07500c400c50b400031540d030800a9080061a0240008032001c0e000342110500144d0840d07001086d036020407a00101081c1040400c100c52140f5582c020032032900d890302c640302c1400401c128810903005118a00c08106400d0000c40c5001d280080e403401f45180080e2001c0c51007078900340500c020341520030f0380425008130310700303101410406201c2c620120303020703143d800018002001034000e80920f900d010010081098000744510483e9418203000c40e12544841085d801c40c05507000b01c42d054010001c000186 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 11263586 1250 11262336 11262373
    0x102120409150e070c020603060d1403030108010f0501030c030210050412080a120504050a0b07090503010905010b09071115040c0902070c0501030c0f080f040c031209030c2312010e 79
    0x360a0001c09100c5603565243c0d504222101540d4130004100e9001035900036080c070000655009901814500105440c0d0340c820a144001c419400844c2d007021005005c28802030241104000300d49a06008550540c5c030b80c9401e000540c40001c3c42a03018441180d20300d800798055600800411500d514580e82c0e034200b00c1410341c0252903c5001680008105e4204005413040602858000000748124840e540d40c00c205600c01901800511102100004d0903603000d0180d0048035118400200351082c04500b80041628090411014050300380320300d54034550001401c1034152124050700f04540c46500f40840c00605070b0300040c0001d0700000710301c0d082c410f9000d044002c0386c4003039030200039481d0000700488240b8030003628000010314050201e0380c0f9413400004a60440d0043c0c8001442c02c0d520380d00c01c900c0d69030300305400002c681c80d0301041040c0940000c240005100311014803001804140c2400b00081c19000035070721500c1c1c1c0441480360000254010341d000200641120703940707514907060300907 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 11264836 1250 11263586 11263601
    0xe0304060327150e0f010e1b01091d0c07020402040b070224070b1b13030c060306180c020709050907050f0303041208030a090606060c03030e0708030405010e0102120409 74
    0x540241c0d510310380d410511802045010f410003010508040d00c1003c41d0b01a04114181c401e81c0e20a1481c2c2e008003e100b845580345003c00b84004090205000030b001409a0704901c1d01c81c1401401d039030801520459296108100020142030402541c540112814178000e403003029400030b1000c907001c00d1910380d21004000342c0c3e008451110040307128415060703c02840304450a02c0183c01e000d4940095200e0140540000d0042000b0603004041c00106170725400030700765a24020303400310041051241042038480602140d01e01401042c1c10000c003030000384040c5c800186180c0d610414541100c0c406d01510014103140c1005101a09041d18401d6030b400040c042e55200701c829034402c1615107000011142120804036580594008584404185ea00300421b0000c0c002d07292000310001030070b07510841002e0003141d20342c80002e042c1410b000b4226007120260503070960089005000c1101c0002c25981219406d01e010042400700c900100d00f018040159404d46031030100f00814048000e400100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 11266086 1250 11264836 11264861
    0x80601060f030e0f0c04020c010f020d05010302130c02190302030904050702010f0e0703020a030f080c03030403030207030f08060306010506090303070c0b07060c0207120303090807150b090112030905060703030e03040603 96
    0x1540d1105003c82c0d464149145081c000d540c811000c1c0001410681c001d484400081c0d400042c20704107500d000000d1364405110340c1c0500d03540d40010320461801a41c14206164509010811544a1a4040c0d65074000582d042d9065145080c00820184200111424a03030050400c1c42681001d1002a028041503514205441d041001e112030003800003840c0800c8a400501401c80c3d180380d0345503160b1840d882001500d56003020000340280707410400003180528880c1ea40180d6070002400c006001d11041c00c00c0b2410003150205000311990300143d92410346008445e82c9540e500e1240001389188244c00740241020b0200200040c1d1a5840025040180c001ca034203014103072070410100d0320303581d81d402070400308c101c144012404240b09500c1049190720403140545402c2c40340c0c40f550043c4601c0e0482039080c944a8a4008040c01c052510600400c60500400402c850540c2c028003070404500030716024900c0441c5034410f041c03281d04449424044001500c3d522034613144010302602c642d00d9590b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 11267336 1250 11266086 11266091
    0x603020a060c0201020714010c0813080c09010b03041202190303051f0807060503040501020d09060507090e07020a0f1109040f0b01080d081504111b1009110105030709080601060f03 79
    0x12424022a0b0040300998168081e01c0800d08180c01e040110782c01d00e182c24100400d0702407440000c1c040c0c00083c241ca10320001c1070315072107291800031072920015142540c020390070240108a200e41c0fa030140e0fa04640d1240c4a14000e03200890704034a403180e00041e01c10f60083e28211202814bc040c0d0141d40640e010078840c40303900580c1c60007180d2404c09841101265403041c00104511480b4801454105100d030001500d0080b42d600403405441d58030809440c415621424000f5058000c3c01303034801040350b55140302441c5001c10000c7d450340241d0340701822081ca07004015003041140c0f0a24040303e171005043c01d2460409003418124400d00340e004941480744000007050000340003600c21428845035030b603201183e4800616581b411907805035560402c1d15000c5000101ca03102c0050300140c40292400b211411490352190b18203106a81e5402885140060120109103445040441010282083da9603501c580404842e44525580104072902a2400205940b80d10203d400b03e501016030f0b05 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 11268586 1250 11267336 11267339
    0x3060109050f0708040302070b0409050115021b10030e162d1401110f010c120501050607020105031312030203040309050907121e110c0d09060804080304150905010603020a 75
    0xc200e54042e207044258580d0b800000d00c80510500903564014030a106880d8165a1a080c41800340c0150f040300c85440d41701c100621000ca41d221402082c40c40b00e100034010144e40d8503000000c04003500d0b1503402444444d801e2010f15009070800c21012015030116034410f0018100200808140c2c015007000c403a03803698800c0ca980a041c8481b03170344050139211191141c80d142d03900d0382c138000c1040c8440c148258600030340d031110004e0080381191107c0e4000030540b4034802c40010480d46901004030100351034400140115107980050310807040d0f080c2059a40ca860300108000450b804481c02040304241c62404e01000307038150051400b95100c0d0729480c01142e201d2003041a440003c99114002465419002e2000145500314255950000c1800201c000380100014103032a85c10001103a60f07103000914104d125010007075045154024540302480c181001070081c4004000340004e040c11201102282c00d000e44110404086400302e201000004030328648140030b880c030b0344001d03845861035440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 11269836 1250 11268586 11268599
    0x303071409040603020a0f0501030c1409010c0f050f0a020907030c080612010e03030115140301030b0703240b0408100b010f110309060a0305040204050703180f0c0302030f0304030b0903090a03060c210b030601 91
    0x858949080f410200c0d10304041c04c02c0011941c0d0641e039041601d25201d1041d0c10808600c0620500010320b500001420540380c0c4c1d401446404070300904001c040505d00700513005081d40c41005241c11240c129010307a80e4044284a89014040820082d80d040c04008000035889060140078040800c051f240c5003103040c0c00c0548144180401d01c40a0141d82040c0d0004001c2846980a1041034050b071108ad0744440001003003000d11301d80d0380c0003207040e1140001e09000e54841006107158600012078140201112840020f00d0900b940305070a05000300440d618107601800d20942d444403102500c2c0302c0c0c952802402c024050b20040da0140e02a03450000030402c44e0b8032900a20b400d041e103407800b0300700240b41070303070799003151110180255440c43c3c8500001c00141d03414080c070712496040c140115101c2c0d066040c26500603001030180f5a80b0343c0100203030380007903c80340030700e00481c1c0c0c01420010714280e20745002d0301d000c60749a40c0c021410300082c903264000c0c81c90790720069880c40c0640443d42c1981c0c0707854 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 11271086 1250 11269836 11269847
    0xa020d05070308150a03140f060610090302060c0102040306050c04061701051507020d06050f041a130204090302010b0301110a110a08091c06050702060f07020303071409040603020a0f0501030c 84
    0x200282c00540030b080020640d403100c01d0801c00d41c05010349049107080d541c0c0c0b15254411840c05030700341290410079041e40808800c00100d5008102159215400c01002102820098940c80001c1c024400411401c1c00d2020079410b4800a50700071400303211524180c500005998007900580c1d0100f074400b11080990712248503010b040e1070010301000120541110741882ea500300200490b80000c01101000000b01ea41c0511b84c0140b61120041c00903042c0380c41d017400c524900002841841450204000c0268281c0900501c0141c0650300003800c492a800c3c2280035040c000d080313981540c200400c030754a80504100612048209590301c03904241221501d5031120300d0703070703002504000090002d01c100703281091002d00e40c074900100c0f900a40c0c9080e5100790559208031515800760f00900308020041c000d03082c51960214491014502c1e5103030090003d00740941b020407255161034042061001615190302a4000e503400070120a00325560309040100840d49000e2640040d05180408050a0252 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 11272336 1250 11271086 11271097
    0x108010626060a05060409090606170a020415031a0103120504050a03110301020915030f06010c030c0308150d0803150418030e01230315150703030b030f0609030a020d05 74
    0x38409038012001c02000e501107001c1c007a01282d0310900d8a10002003070399640e0024802000390a0f0007040749985130034104102c1e02d8551000070601d43c5040d1013025804040703400326000750304403070000c2c002000c11403d284c815481d80000b400340342401d980500c614201012541203030300c10b55107500f690b4400350003101d55004901c076542c1c001d203141101f031000544e50b40110160f0f0101400040c04d020091000502e5505034907041c0b2000b030800424410303603030b03030102c2003651084003824100780d070a00780e03540104800040000901005604004034540701d143c941c203225000705c010302000c040582402c1001d450303071055411401d81c00031081d45a4003030400d4010107410701c810000310020030443d61829180103c881c40e443c0d0411582d85440c004418541082c1c141c0d109000001c5610b80c58072614404003042c901c0e92561260b4881694074070b804100388110b0b00c050381e06103030203d41c6030b8040c40441e20300003230b905107410035000300c10820800410000180090035065400c40d084401c001100341d840e8481c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 11273586 1250 11272336 11272367
    0x11b050706140a0e0c190e0c0c03120106020d050405010503060103050411040203090f010b030a03020606010809010b060d0902010e090103170a051b010e06010f0302130b010507021002030a030c091202091306020d090201080106 98
    0x3090407c0149000f042492a40a0240c0d11102d00e490000034070b00e42903501020b1760300d004080030340c018440f40e941041410700f10fa086007080ba142c41e052200180c824040180320a040680710130018041042d18007410884180c040c106544a09007121402c0d294032040b10400c8030b9618180750403c440c0b900141001c2c000d80c054001c0c0c140c684464004403001c8900030300710f0000b5903e452403c442521881e00031704030080c0c41c03940050001c90074400102003c244450302071082038600010f2001c10f070b48a40711b030401200034071119034a40c030140043d1580e00071440c103001040860544460001019005554114400340c25200c1c1d5a880389081140301d5250700020790018022030060078480c141d503024400c5544141401d50401010307a0000e903505840710b96640050700007146c11802150540110b4813041c009043c05042503040c859446000c13003415201920480e10b01c00400c00782036891428044140d04040b056544004241050f0301400c030f5110300321f00041c0303c0d00c00080c0d92889400a541c10402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 11274836 1250 11273586 11273629
    0x3060f0a1a03060109030c0608011a1306030b130f020304020307050303040305030f091206070c03020c010e0f060310030c08030301030203120a05070209040c050d0c090608011b050706140a0e0c 84
    0x14511403580c85604020f08160500c81d007800c01001162030010490300818290b92003403001d60402c1240e4500407a02100031004007000e00c042c211040306092080240c40e564600003074044054000140000c00090a80ca859407425a0905000c6516002588078034000e50403111200d40d900c040c540d9921942c4800340841d04203200204c40450202c0c000d04480f0350003410748080225441c1c8403810241d081c0c9100340030a048540c030001b010380522000c0000c44003428440c6c458001c46000c80c0750b00104142c110720070100000081c00841109418201840e008001c1c41c420303d032030321042e6542e54020301080c0c0c481c2c40740798000d00c84048044202c640d88801d42e6a9a0b05020b07269003408585400075100322050742415201203680d40390400d2003001035000c3c0d5281d5184924100180c2c0071240d040d0400d8203243d041501c0756010102c0392500990f04400c918000303580d40b260382410380c010300485a14800c004101e80911060a03844d8124943d0310f055007060310201b075110802c20122050442d0f81801919 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 11276086 1250 11274836 11274869
    0x2030403051005090c09071101051f0306090804080604050703110603150603070903020301020f0a090e0702030403030f03060503030a1d09041e0201020a0804030f030809010203010e0f0a1803030203060f0a 89
    0x4007542000ba04800d4690803900785e21901e10000f03607015000c172903070800038220042103040c4400074019680c10410b0342642c1184c4a0107416010290352b503902015043c15154030540c41041146000c5400410051043e10382d6801d0524005489003280c0c44241d54482c3d02d0342e50141d451420300d0490303000c0c000182382c054100c00d80c8818400300350401040c040a00080003000005070b2000c1c0020710020050000490340d40c00340c1b03040689107454540102d1350321000101002049a0000b007180d0075640c15050a5441140b507440c22009801d0903000b1b280c15000100e00380310855085104600011078914441800d0050390050102d148070444001c0c01c054440c0c00c0d000480a0020f222600d031500610541e03040c0043c58031035188551160340101c030300510000c0000185503101a01540000005000b549594503041d5210b6224102400040006c0b842c0303000301e4140c8000e90300c5030310b003400026071056102c42c2505000e002900220340f01401040b90505004941c40c0c40384100058903040d000d10003803203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 11277336 1250 11276086 11276113
    0x5060d0201120b0405070302091e03060f061c060207030e03010b13020c010b12030a0305060306090a020f013f0c020a11150c031c061211041b0c120203040305 69
    0x80039102c01c02412565218446440e548a90083c0da125802c0f984000d41c0c2c2d103548906118002d424a49451b6000c01c4510741001d8580e800318946810007058248100a51a0900015040f020f04062101d542c0d10510440040010540140040c1800f27a00e42d264440301c024141030a03074410300d004c00d1b40010400141103401d81d203a03000d010032400307407400094408003040204640302604071844980e54004951b4049082d814084c0a0344104140c014203d14100b8590141ea51880b9410080c4240251008150301380d100e050308001d850030071690401402d4071030310380a540c003583e15030703044034850b11801c5080540054095400d44600350350080c02144c800c3e071900c002c47c1400740c4206034403ca45001c7d1140c0d0b002c55602401101c000c100285a0710001c00101d14281e200600c4040c4515040190030425540010010074150360460409040001c0e01000034004100d07a415840c0c06c110aa104500072651204c0e0404104c0d204031110710303c00720035910980e901c3c0100c0c407000705190f010340340e1050b14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 11278586 1250 11277336 11277347
    0x305150d06200403080705160e0a110d090303020705010b010203030603071406040b0a0f0305010609050d1101021e01060e102105100603060b090f01050907050a020307140c10020105060d0201 83
    0x1c00e088060b070b000c4100602624040941d1103a07109681502c00440c50310300740030081c0b2040041c0400a00c2a8041502d822404000e103c2c00801e4000c0142d83d40ca401440d804100c000c03074007003003004034003007054002d10b150240094001400656080d8605521098954000070449024000060060200ca460b1219101000070b420381601c0e042803007400b00061100040300542382c45c8495403030b100240054410000c0440e00c050b80140704022881c2e604016544928648107612508400b11051888213100181c0c40d249601c803400285010782000302c0706100040d4800400c0e5030019803441a1516004078440b000c1041d0701445d4100f849400003070441c003000382e80700c801d000c0c0b085041d5901d031044100035400319006170744182e07421a1142c2c0c0d8201d8510300000c50316401072061070303c0c1c40c40b54104400324812400007000041130007000640c0c911103a000300305440507184d01030100482d10b0700a00e9016202c06072071119a00600e001c50400c680140180030b0303a840f440028000800c40341064004440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 11279836 1250 11278586 11278601
    0x1031e0309051020031306110a021e010f020c0907030504030c0b040b15120a1106040306050103081207051608070c1706070207050a050a090506030309030a0605070305150d06 76
    0x18407250501c0028642c54110f40080c0380c0e00c45031100e54090a035044101400c0103803142c0c12106400c100b008a4006810600c918140c440c249030039403001c1e030004040307890040e4510707003e9806038032104103c0b1034036480f0303400c0501c2d200281d82d61803248420040a03a51881410802ca83c0041c9a5000908a51083e4455a4824000c0c500480c072402c0315240c04508410685054a003000303400c040102100500c940c030405220b082c0d6100c0301070703200f40500300c0c0c6650351814010300c1103100d8201c1c3c002079503450040d1806544c00800030803403960b4902e002c0e07405610000c100243c03a100c56002405c0c0038000d0782618162030000e4089550b40049035252112580085000c0707036504450400400ca0441e200d1099102070035860040c0202c0c2012b182c0a0714202c51070303020300e216064110090040352100007a45044501000001c10345460b0040040e01394010901602d80612603000010709000442d0002406030320203460800040d10340380041c102240c003000700d1b1500503e40c001100b000446551003000b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 11281086 1250 11279836 11279843
    0x60301031203090803070306050406120302031b01201903050405060a1808030f040c151b110402070302030a12020703050a050703020708010509100e1c050d0f020d0603060e010501031e 80
    0xb83c1071155a6006015001940d240c000243c0d00c00d000d1009043c14495040078203286400001c000d501a9002583c81c4140616114150041c1b00c0182d1842c0c825040340384130b80d000403044107002d00c100e074841c10582c1009241c84014220440c000300754038000d124050003690081301504c01c0381e0b1403911041c05460700e0640710b0750042190403060045140d4001550042c0e60140c50800b80d41030905000c1c0c90345e020358029100d60b034010040b110200390000c00c0a90300341a61103125128800300d0a020f40201d0510486580080c00080d00c0d20425a002c0b004084d0f0203019103030504000362103000d11049024101c0c0c01070110380d080144986c0c1d01d0090f00600b441e58420301c111403c9503100d4070b00c2425640207554901c0154003801d40100703185568040c814001c03407000c00401c00c000828260b800020100786200090100005421103601110f40005a800c8080d420035542c0321030b5132071124000e10880c03005445192821b07148055000040c09510f04807a0011210300c100c0710440485c2c55140c05808044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 11282336 1250 11281086 11281091
    0x41805011e360f050a05071d0f0406080616050a05040501031802030109050106080c01030b0a060503040503040306050f0403030c05070201080703050901020c010501030506040c05090c070b040602040902070510060b040302060301031203 102
    0x15070800300000002e140501c0c0c1580441c0c514152070002c81582c07009040382018605080c20442001d40c03065901c00c140b054043d000100d0144e11011508010046980580140c24081c000c107501000050890080f1850071001c80b5542d40424102c516015499070365000400030002001607620940144121041c1c8041901c15910958001385c00c54200e03081c200d805035115503003001554002e1284100d02142802c1c244913851039000020050003190094100340b21340440480c041c401c042041c3d401443c1c2c0a20f0401880c05c28101010a40c1c800711402c0300040e08080503207000b544100e00340c0d1038503681a182c8680c031741c0741c59400794043c2034010300f684090340d428400c60703d1240742401814000c500078005040a4185070170002c01065894002c81c1c001e03180c07c02400030000d0040100d40240d50000d201180e9615507203010b0000c0e01c101d6001246103030001c2486410b1000109060102c10034041041104550b9418100d250b400750344030195001710184010004030314926200d20b01500980b500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 11283586 1250 11282336 11282399
    0x5030a1104080f0106090c090503060613090b090c030601090207110108070201180812010b0f0301141c050f07080105060109050d020a03060507050c060601030615031d03041805011e 79
    0x350f241026080503c50107030f4642e001049078100b14425416030544602d8601107081c20300b00800d59807a0064166805041c00d10412000300b881940000134080e4440422049400c00f101002d07030311080e1441140c402c0c06020000180c0350424421210341c99030201075403409001400064852a40050200c81507540315084420269200c13001030308140d20509a00303845241e0091600b440700d105030420b01c0d481408001d0071004e20202e2050300c0c1140c8040c01d0100340c244581c40403440000318103002851405411140f9010820b002c076141880035036800403502c00c0f507901c8004500381c070429641035020070105c900511040c10300021282c08940054009044541e80b030b0364800c1200c07070480b1340200007200070985410b13000040c4021500f00400746414003410b1304014040100c0003414004009040e90744450400d4441c004010b80c550f0f0040c1d500307503a01c996a540705034131880721241c081030150741742000104100800701c64004203240e110744070702c1e003050038400310100e043c94801e0140cc2c0303940c01801 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 11284836 1250 11283586 11283599
    0x40e07080403080601271806050a2d03020303120a0e0601031101050702240703020f060108070e04060f050103030305100501082502030408070303020a021c020d06020a110f01020414030d05030a1104 86
    0x806d0018002d010444543c0150740250074101c89680d0452841504070240810904a104d10031945d0344c81702d0441d904102c0c500240a840040d003a038002501400f01040c508501c891034480c1c41c0c41911001018040c94503051101c0c2e40b102030034040202000b9a000d00440d265100e0b902800c030302440604510210a000340190111620f00f62108a006500140040402d0750510181c560007120a0051800354101440c5a0725a245c900134581c44448840004051104d03580240394002a010400c01207961a810300030003505003212003001076080c03040001391551055a0040c4200c03507045590200c0c02c008900c84801548003003101086110a01011030200414007040f8002d500c00d4000385804d030940d1040c0908510800c40000c80503c0e000380030700240e241c1c040b180c0c1c0c500d64404001a5030301d03502c060940e00d00c904036143c5000e07881244680148690705600410a0f5039602040588803007a842c2010307030b100038041d400400940c4c00c3c400305071251450f820801401d00c0c00d8800900b003688a0300d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 11286086 1250 11284836 11284907
    0x140904020d1203020f0d0617030703021506010309020909070501030b0f0906090403030605030d0203070c06030c0503130201020f0106030303050105180103051b0d0f050102070606050301060506040611010917040e07080403080601 99
    0xc8820801d643c0d9030402c100b12389043d000160100903040107541410f24549010352241c143c1c0022030002c400c4c100c0058070581c4254050784920750f0091820359203017800c00c58030355203c0303160007500d010030326002442900b0304e085002c00d00d140c18000c0c044981e982e10395041c400c00c950058422001c2c161618008076883d60184261400144150300540d2214a6403c14900400c103540c411801d00d0300d0414403043d1240d022041b030358030990a05074403041e254680f004038900550003244884039440c2c0b800100405a0640045040744d01c03c542e5444481c2030005a118000000e11004101d40d004181c0c110129400390401044081c0c01403403454000708649612850403885c82d030846050f50700151a1302080868440d090280c0303410741c02040310600704408980a403003107000310310130301189410510304c807102500440c104c260f02090f00d50558a005901e42e500350040d000b00440d02042c44001004584100c01441c86150195104a2a034941314015191110320b0b00c40340081c402c900860389007003030814 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 11287336 1250 11286086 11286097
    0xc01050913090b04030305060402090a0b090d08040605070c0803031e100503030a0302031602070e1b0c010204060e12061009020702010516030908120702060406030b03070f0b04140904020d1203020f 86
    0x158016400342c44c00b441c0080840b04010702d540d1145106100c0502d0036120800f142e805d0b61866040320355145415000240c00200c0100c000304807020000f030200b50b07150b021015000b128864000c803600e99403100603490704c17400201c4904003600c01011400c481c401c03c851303906410807482d5541c203080d1915000440e0941d80295003680211780c00109220360390051251501180c4040d1016203041820880403404849014044d1101601d44000e0040e4400d9102d089078810303840003000315034840c0d8561000e001c000d02908001d1154490040550f9201c0c0c0c04950140b0134403101c0007100b00780c5d05110a0703200075001400180c1c1080b0b4280101890741000c41140101603020303488514156240100280c58040045c2260788a40b8080c000d180c0141c0b1007a0965042e1484e904000c030303080000c1808030740b40c400251b00c201d001488515000488007503420091040d9981a510301c841410010107002c04404107a600030740003c15a640e58010030502142181d8228a600d401340c034040c045d211407402c98008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 11288586 1250 11287336 11287343
    0x6160501050a0606090503060613050601020304170705040501061409010f0c08030403031b020309210a0b07030509060f040f0b0a02040f030503040f080f030406030c0504050a0e0603010c02010e0c0105091309 90
    0x103900040c0403c98002040c0030040c1012401490030745000c03808501c41c281d4030400c3c4e2b2000d5172a6404280181e0082c01610042c16402241c03480d0526201401980d0b2001ea10419009900d03050010960302d01ca00c0a40c8038211080001030328000010340119410001c9542881c10401080c0001c000907440b00c00560040b40295004205000d1800ca6001214118500c2c04150741c8108840300054440b14002d6030400303041c0110003070384c0c070810243d242014090324006203041403081c104001117806900040c014201c00c0210b44a80c0c3c1c8001d00381e0717600141500c015100303a4800c000c00700042c0009196a82c04110395402600b4030b07595103c030b00412280764004030b440d50408681071101040010050000707080e500e0040010020b007004403902c130f114a005160805031200e2601071064040e1040324000e00000c0e2800f407a059840c0283c100b26041a134140d4840d5003400798003220203105000b202550409070f00039040390030340300006540c00e5001860098109c203400341c0c9252076880512071403140502 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 11289836 1250 11288586 11288591
    0xd02040b030a05100503010b13051f060804030807090515031e0c0403020f030607230c03070f02040c0f05030a0c0e030706030204261203040602090a0611100603080906160501050a 78
    0x80c04d003a24580030a641c0c000c0c40c02607241c0b1100c448107654a500d00e007030f00840c4d07010010700e035242c07005041038040103141100d8080780d007035100040d030302c2c1c0c0101414890b03401790b0b98813035860311030060031140540240304682c0d0101401101a13840141d8100071508007580100910407161510500020301c0d904803000c03240c084010808000750f041c003210300c440001048000d02001d00c0c05940c06000c410600f40d88004a06450114640300c0750600e040b0340ca5256a00b088031307116160b624124850034603a60081b4003d500340944111220b001e01003103486c0c600c85407159800d59450800300c038000c000700000882001000b85518030a17450612002d006410700341d0780985c0d1a8180f00d80611138410004403c0f00a07000c00910042e68600820f011280c544090011aaaa2074500b0280d02a01803414910b621902c841e10010fa1144c101d42c0e030b0001280088151107400507502c0001c4210341e807a100180090108003c0d80015280c1800205800c54410309032490781201d54449038210741044078114005175 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 11291086 1250 11289836 11289841
    0x604030818010b06030a09030c06020d0b0406080d08071211040f0e01060903080a0305060d0206030f06030613050a0609050f030406030606091401020a030c080c0a06050103140c0a03080d02040b030a05 87
    0x1d030180c5008148440ca00244001c0840402041c607500c00100351100303560769038481d42e08152056904a840c690890303070940d11174206804c4400103240c440340540c410703442d08800140380f03580800c00440200340340d1280c601940c0c550000b030b10122012900e40040c1c560300d14001c0000303c20940600701600c0b200c0000d544c014201202d0b210a414181c2011080c003501e5802000019200402c80380c004541385004505501e408010442c0f04120030030007503020710301200300040c0009900c1010310440301201203802540310302c0008260011282800380080d040003c2500100e0310307540205c020a44600100e424081d042c40345182540c1060300101c0001c2e450300d20400005a0002e481c0c1c000d0310071581c003260908003600c0080d584170202c5500805101800e400c08080c4210201a10f41300081d072020760722045414a0f01034000d18007404200e40c0700d1131110680000302e170001140b40189101409012090b400e40e02d0307404d80ca07044050340c800b04a408100101d0b045400e00040d50154805000104003030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 11292336 1250 11291086 11291101
    0x180902040b03010e0601060f120c0201020702030c0a0609090213090c080108010b010503060a090509010605030d020124030503040b030a0e010207060504020111060705030c070618080307120203010e01051003020c06040308 96
    0x441200c600c49100e44c0c10042210491240801d41e141150720508216140c4000780c00243e81c40c0c10031244102d5554030300250026a07680640050900e80d2080702540c6040141600b084000106030080500003060300c403052044600a03030042c100614145005500644d8601d810405d455003e038242c1c000816013001040188401d019a48103004d003420000e00310303d0100e01042c9070041c00d03c951440c19072640c0105095480030b6100c1e034007610016050352100002200042d02900b1002c440c040300204036801d240f941ca01191010050302d0303001010750b2405240c4141100d48c0c2e000a0046c0700819038030f0034020203900091000b03180e8980310300004034043c40c02d0300026000c4407010aa81d1040e81105040000065002040300d80c44441140c8d0140c40301101c1c01c102c0e00410004040f0190421520010b00602c9442c4003e5442038415a8a6000c2022510360b400d00707900080c4100300a0034450070040c405450151000e0708455130700d180041c2001078203c0d0140ca880c00541e0240e012460b0f1200740a0720 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 11293586 1250 11292336 11292341
    0x509040303151406030402040c18090203071206050d0206090a0902070501060306050105030303090607030c0e130225080304080304060207021003050105010305060a0e0402100512010801020901020c041103040b09030418090204 98
    0x2483c01c5041c008424407014040380325803100900c001d2040e55034070105803180c0c0c0104c151807202d01e10f00c200c2507041926521008000d5009882a102098010013020500c4840b030203004165a0f008e0812001e08000740d00340007030350704180b000680c8103908141c0031030a4505071005d07047c1c880c060350001c58518514203103081250030607013107540660400c00402581c4030b8002602508407600d4a0300117a601c1002104680c5501120a80c591280c181980301224000c95000b81c101c50b010301840004100380e0a02d64086014409001420b4041c00d00c002000300744060080c5030b00601500000d8070f000156030000b02e11906640d081c1010954074001803080e96818031032994007940548101c81d50703d00300340c0c0400c69070130b00910003441120703840007956041d442078017507483c460401c5d100e050716540c60b81c0b41c2d68040c3d046441d8650051155074602c892a01c0c3c1401008610441c1144039481e507107427511014941c01000348a030b45548410013001900b441c101c452180c1200240d000042d98250a2041205 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 11294836 1250 11293586 11293589
    0x1509030e0d03120f020901080f04030201180807050c01020616030e0a06090b0a050a020301080c0f040b0301060617090d08010510030603050d0507031b0c0b070f02030105100e1b0301140307050904030315 88
    0x3e104d0320610484940c2e0760491011074000500960300c030032581e02e500c5d049014240104190043c8006d10500d0020401d01780c014000041c8214265000505c00b08012640c41004070f07940404400540b642a08040c080d0303002c0c4d100c412500003510140e819944650302516541c05003100c140b91140200100010b0300c0c0b01c0c1c1d0b5000f510142d001e43c03455151a6a8542d6260b00240c4140300e074140e4180888150b03510750000b0002c0300d020f030007442566514a8060400081380681c0b10f080c15440c40003443d4400d011420302e03502e400b50744401d1081c1c1d08150500099080e203694405c00d0582d210320202c00304d01c041149544501c1d003961281c0c2c6e203404a2030010101913141011320700b004c1c12400c60300002032145546005441000456988030805400c164010380d81091000c1d406510785420f00203002203172541d0200303650800e0090002901d5000480c991001c0802e204620035400f40014000700101040030303104404010222050f20361030320009400310100b0342d000c0340842e944000380781c00d01d42016007000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 11296086 1250 11294836 11294861
    0x50a020a0608150f130b030109020a1203020615060703110a0f0b16020c0603010603050606041208030412110c090a1d010c03060b070b04110a0308030403020607090807031509030e0d0312 81
    0x40440c526100400c12a215080c111145c90344c0b1100d1454150720254012440c0c035400400c07040c001e6556404c403004440104805900502640380050800400004d001b18440006401e15203050201c0e1012140d0300b001030003104890141100320804200060039850906016548980c01410005c2101e40040c101a0058040d500242c441d401685d8400c000d0700e044842d90b0a02088540ea207800041c41071007503801222141c4040d0703450400744030301d94024510a40c131425181104002405081d61102801190081154007032845921305080000343c4031340201810201003a030343c81080003120a24400b84501016070764900702c0d00546681030085600a0095011061800b0425290718406001c01480079180e82e072000034221040e1220b0103d20015038101d140c40b40c4a09041c9402906d03280241c420340006406403401040104c1e0200b0030380e00b102e522103104218071800680c3c0c1d60150020346810360600040010032290b6849890410f814a0f200780e484010406158070200c08554080c40d126 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 11297336 1250 11296086 11296099
    0x60c02070623070803150a06020703020405060103020702060d0c02100609091b030507090c05040506034006090f05070b0301080f070b0702040b0301110417010f0203090a020904050a020a060815 84
    0x505802e03110011109020f4102075074a580307030744a0130301c54a14604100c2c0c454001444220016805501041034020745c0c1c401c507001d00031a200d00004400b81d000703101000e035001d80c040207618801d0701243e00840c1603400e00c4c01502c00700b105e2041e2280481c1c0721a80701080b540c1d100d090f58000c0140d03a600005811640c4102640310798190f8a0300d03907032803050f4025150b0065864566007000ea0040c01580c009140c000c001560f01d1074010b280c45c0004400c100d0b6a501140080900030380680d80c2803080750404a01e56800319950715603100c850282c0130420095481c5280f018140000c48d07800d00411000d08002d003180341d0340b0351400c12224644900c058070b4451030707080620140585e02c040d804542e02650112008110a0f000e13000007070041280080081990343c000400140651300c11907401c6044803200020084160703a107080505900c0300b298500d00c150021004400185402e010441c0c10034041c44c22203200e80342c00d82c08101c101c84079030080c6012543e14400c00c503880e880c020b0700301d00040e41a10344 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 11298586 1250 11297336 11297387
    0x50115020106090e03041a04150e01020c0a030809011206051c14061b0a03020d140a0e0f0303010302060c070306140a0605040e1e01021c090203070608010b070b040807060c020706 78
    0x126501c0c6c0c0114040c0c8482c0c1c0c070711084840c3e04802684d058030301410307802d81600e901d5468440701409000550888602601410160907550702d004007807907084a80103280b942c03a1122400046541c1c040e4400141c810682c0c0301c501090704d0302d817100d000c682680502c00c1c00388142140d082104d64148448ac141541c2d5004204010540c8210100c0008800403a0500c3c2c0c3c0350040000150041e0040084449020b031900d510480142071118031140103034441001001100070700825903171a60481030040046910401c010030060406000805080c0700003810342d80300035126601c100c140c1d82d0400e50070040d6811581440030448042c0304620013044120307070170018008010001c2e1740703507e00d0442010f07003020060482040e9010070b40444000c821052029002c6500d0115244000c082c004001d070f01038482c0c21000300b0101e00480a0906890052603c1400c2080d076030380344049000300a004a4419006000c100d000450340e00662081c0038032900545049801d0440040202243c2901c00c2c0825254461 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 11299836 1250 11298586 11298611
    0x30204051807050d02060c060f0714070c05090c07020d0302010204050f1c0201113a0f050403060c0302040e13060c0504061710050a1706070206070f0f02010b0405011502010609 77
    0x101002243d01c1030f1003000c4284071900004a884c060041c05c40447d005007400c006a00c601c0840c800d03caa403480e1a5000f40e504440c4449440340642d000c020312480c0500000c0c0700a2420450b0381e58001002c07101140340c00c20907408507029805030041200541e4012070305104c64608150710161104040c0c07841c02800305a220a20081d8800d050003906014000c0c0d1078500c114404e0103034408015802144602c40ca129603c0800403461000740d014059201150f0313032000c203220301c1001e001e8954540c0d5440c01d090039a02c640bc0181503a44695050582c00c00c40020320700c11150340d4510802021001004d524040e0620109841887d011074082110070003042c01030b280c01000480e6032034229042c85106640390300203001d10a080350004e03070f440030351000006841e040c401413401242111b10300380e92194450740e100380e903900c5007a6103034800310b6114241888040e1140300d5903001465548004541c0c0480600807404448013a0442e81482403240001104103409004004c020300044070200140c418004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 11301086 1250 11299836 11299843
    0x9030910030902040e030a020a0b0606092407051c0225060e03030405150a0f0903020114070303020d05091e07030b2a0c01060509090607140a020708010e01060302040518 74
    0x114810181a91441c49030151346942c1d2182d03c4940c000012250780e0118010060341d100542d41d421181410360700e0015090341821000ea8105407c09803001d407152480c0e0301c2511186ca0140c820103100036050198001041c01040304540692441e600c2c0c842d030b4600d100c0300a040207402a55107013010401964495805117181d007c0d41106d0080c40d240121805c8940000d065200d5907020a078400b11240700300c0000280a00240740d0500c481d110281c1c2c0c0c0c001e6680540b00581540b10207404100101600c0c42041c064000414480744207180061400301302003800800c0383c205440c108805e81c040310f942c0e06c0c2c0345d0f1031180841103007600300010000c0d070703181d541d901d50b405100800986510703058005802d881a410103d00706603442100c42e01d610b8841500a690080203548580c9100754035050200b14419004a03080f405080281c0c1c48080f10719100c0e0000d03d0540c40a40d8203003c61082c3c0000080301803081c42001d000e074903202c0022030000d280d4010842074030300c090480007004000c1b501c4a40440d0700003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 11302336 1250 11301086 11301109
    0x5060403170c0307140a03060b030405010209040b10020a02041d010c0c02010207080115050d0c050607081206010905010503070c0c12080d060501020325030201020904050115080a020903031e0c011b08090309 90
    0x40c3c0d10541c1c6c1d40b01054101c014050907030041140d2900401480100f18064020f4041c2140c282e43c01c0103170302c00d01c0c410050000210320728400940c0058800350090b00b03041c0c03ca0040140c5045405001d603021104090850301440702500002c4c29040d224021580c0c1848050002c0c01110000d01602501884e40d51580180d0300c00c807846221000c0d030350000c01002e81e520304010319008220035142e00a505044c0c0340b95122080304c0d10b078484010001034856001d1139960040d81c0e010380d5110300715034920074190342e00808040183d0300465102000500e503942c01403100c0c4254418081c441d101e07520480108141c1e0b9554000505540052203008029500501c1505046205080f5481007038840d05050307009110b10300803103820904007000410008215190010501110784c0c4202c19903481c46500c40890240c906001d601d80c2042014400c000c042020304890b02200445141c5030110003060369084038a10004044000c40781841d580d103c540140500c1d03032000d40c1001440c03521110b00000382d000d92a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 11303586 1250 11302336 11302367
    0x209130516210203070308040f08010b0301140c0309070302040e01020706140601020a020d0813060f0e04150504020d020408030a0f02070807030314030c190e031006050604090b0d05060403170c0307 86
    0x102ca480106554017000198029030f08452642e0740e45485918412103011319001d010400e43c02c005500c803003418144a903038114018840c0c526030301d2300e80510b025450390002d4500c6c00580b050342800720159071288141e181024036400011707500c0f4800d2a100096458001080003104409020841c0698001c125441c0072076040b100349002e400d0030300c0c1081540c000d8809200764a00e03090004a180d68000c2a080c1003076486031100d5500515a40c100410b440400c04911205199071030104003505050700a0070000d042008050301b099140c021883c6183c0195414000143d840304095001e02d4051000d0310103030442002602c0c456055880190442d180c80700700880100d03000002030710203080c1c5015142c407034000b0108010803a06004008045800d02c550b4144280158002114101218403a4800b110320140403181002d1a010240c3c1c02401e02d488442d400855500b1910300250003442158032981c030a0700c4504a9083c40780403080801d42c0208a0000c05000b0003d100480e90401030030b00b44080e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 11304836 1250 11303586 11303639
    0x904050d030509030c060405030406090b09030a02060a02031e0d06080d02030f030402040b09090709051602070b09010207050a090e0105060103090218062706040c02031204030c02010c0209130516 85
    0x80c3c86508034510b00c50b214039082c440c01081c0a010401c18040014001c655040c2d03039010a05881e441c10070b180b840b50440c80365060380002c0544005083c028064201c240460065a09100301e1190440c1229038804001c119588001039000c1c1825082c8070f01005494814001c003207401560b00b029549104080404100f04400300c001021551240c02c25a40100090801c0c20703107050401007960380d07000a01901a40609040001c0c0b1b1540440000b1050785400d5801090b03c0352800d80c82c44c80310b030300c4034039018110b0007542c101050726112019103d0007441311a40004107244001c0c0e00600310f600151403a07040608100c80500580d40d104200101000a007241001e15100c4100140203800300e1100089840c9400485a05101d1111a02031066900352014840160390480481e00e0b0b100c0c1e640c4044112900201181c0032900c00d50056901038810f04100044010382e0300040e004541c100c0b084022014100d0711041008000c3c0040d100c1013202c00640c0c56003d00304452038150420948110000c1c49 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 11306086 1250 11304836 11304841
    0x30504030b0604020906040b0909090606030703020904150608150901060b121003060f0209030c0f1f0c0507120302150603120f0d02040305150106020715030c1107080303010906050904050d0305 84
    0x1921941200d107039a100070b0103183c1d031f01d5681400026540103450228402c1162000003900c140c0c000c182c151140c400103024000060469080080e4850050300a03101081c50103802c441618480c0309403030181c503c1d440109030302607075000c1c0c020080000901e61543c60741090001c0290810400507903a400d01c00010000380c955030b040703003a06000400c0d0b10243c0070b242001c00381724030250180e00500200e901541940c80d100c144405010200f0195a0b0032078104900700c405040282d0040c01e600c80d0800b0070318028050980381c0e00c816281c020290003080d5070b83c451500e03241c109a01045668008082d0b001d400d007003482c6c030f00000303611450f010841480c00070340000c101980502110480b1480340c8010011500c2e29124103003103031340b82c0400700d554000d6100072001041107030000071080111824000741c0b40301010000400c8015180e8500c5100034000c00d0318440ca2641c0c010700c0fa80018140243c001d5450b03601d0030498000703907405640058040ca00510510020850200305d0011580060401041e140c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 11307336 1250 11306086 11306089
    0x50f1c0f030903030b0d03050306130203060906120a0f080301060306050d0c05040c120603200319240c0305090709020403020303030a05070c0812060f040c020c010c0201050408070f030203100504030504030b06 91
    0x70035507000d83c1e56006c00040740820070550030501840c0105010741e0341030b0300c80d941400314204a12041c0c850030792010081e00083d000f0700c1e05085500300e00c0303420419a10420b5141c2d960184c071010140e0111802c0c20040014000c0d0395040c4225001420122601c050004c00380e1074000c4001303454020903020f5a00c0b00720301c80c662405400d00d48101c02c501d08081287d25520305103081461304008141c1c4012300c01c82c441220524000500c80a44055205c0100c40300050366644442c0c1c0f480c0c503401241c940d101a42d20f03100c0100d642701e01c0703000205544011a09190103400c060502c000344c1c11940e01148144010b20150310f0003c240d980c440411200000c1640b01e245007a50001c1c00d406000380070b10000920320b0350340440503001d14011142a1100c48280700c44104020030748244030381010040c0c0c046000c1ea0115880341517030382038481c01030600919240d215003805040441d1030300100d0f400c0c0c20500003081107050400007809402041d07407003080366050603a4010040e01c20342c031015021035440001304815 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 11308586 1250 11307336 11307341
    0x6030604110f0a1805010207061706030a020405150108060108010b041802091903050106140d030e190801060303120c050301180b03070e1f0f12031209050f1c0f03090303 74
    0x8102d41c0b00c164a0b25440c812100404540c1074002e85100040c14800c00545540002191000c0e0341c0c0a40b14403c544000b546004000a401414140c1c18440e2004403805a11584a0035014030135910124512090b00380024245090140141c2d04224081c00100040c00e849801d9034181c488a29006207078400380340303024002e8010161a0f5600c04c0403102c0071041c41c2065003a050449114078000e00610f82d44060921004025044181d0028008402540028413540c17030049044001480000030346600c03c0c00d160881100d0300700c0c1043c1c0c6e55a240a0041c141c216124403601c404500c010320003284c0c0034074000c01500042c40b03480900c01621609032481e40860308410392260b4050211400c1c41d40c0c8160301040220246c8000100b22527050140000b0072010001b5800e44000c0000300c0381961424824405084141c0000d404200c1303e408912990303035003801405c0003540218000c11242842060f2213003042a00114400d100000c9240b00302c00541205031040120564140002e004085040c02d801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 11309836 1250 11308586 11308597
    0xc0203070305070e04050706050f09010e03030d090615140a032409060b09060409050714040204090e010b010e0102030c07060c03030f29030304030201020604021203070203100207120804020603060411 87
    0x226003e44480814000d030018040f1344124001c5007110185a0f640c2419501481203241c1301d08118010080f0101950082e5250310310418058120f0f0b00e8440c1c04090103048803420041140d0b003d0b180d00300c0801e1684102c10307010140981201d5a09403d03a0400011381013a81c602c4010f003200c0c0310003103c1c0c5c040b002d82000e00198003400325040c0044c51943c60544010070400503076030310079003515020541c1410075100f0140c3d6158040c00130700c8034a042210610b03919552581240c4d116800300808601d12100e406481400e24a1800206000d02c51000140402c0d1203109040d04550040c414070341c14500014800049880c1420511131404450508401420450202c003001c0307414001000b1405144603620048980c503022040c07100548141010344a2040d44406801a805200401c000d07240041012140031103079800c50f40342c45d0701640801d082c51007a05004064550101e042300a11980c681225010a84c83c03500e02218540750340010001d00019110902656a4105955012807004100c0d00c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 11311086 1250 11309836 11309843
    0x2010203040b1201030501060f061d04020c07090e0705040203040c060e01020102070f030c0201090603020a02100203150406080303040b0c09090103080d0605040e030904060803090a0308130b07030306170604020906010c02030703 99
    0x143e82d0b08a199544442d000d0071300c003c56947d03190020001d03142d403410030f1140990711965a505810611402080c803221614180d59501c43d50800180c8102d0004124410090802850224410980300c0344070381424500d80c010790041d03004004200c00070f0480d0400c44196442402c10300d0f5a0000000101e00a00030b080d0000c1080d150740d0074090174190800d11316641f55200341d07104001a42c803010220140d0180c4101c800141c0c0c45800207018400d4250082d503072128800049401d0b02032840300090a0b00ca09500502440e00300005000034013410704041c030360203d901d401031840c02c48194041204036034144006800e45001240b90313074030803090b1b1304090000c0500401c14419034200c02041d5889500c40f84065201d5032400c030b03000910407804800e0fa4401400207020340055807071a100d0210360f41c02000541090740c01e0882c041900d08a1101070040b01c2e00a980014481e400d001b000740700d560420011000c01e034000c0c002c000050b90b4402c010750b4032910a1070032031032558130713807000c28a00f0900d500001c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 11312336 1250 11311086 11311109
    0x90302190602161a0a1406010c0321060e01060306030c0501120b100206010501120905060105010e0303040b0d020a0324030303020d0902030a0501050402031c050d0507090902070f0605060114160201020304 89
    0x2681803081440c0305141c0070060484e50380c49601c035075040400310360481d554041c1c4032080c0d100080c59903018a5101e46a03070701a040103606080d220b8200c40710084452000c000351940c6200c20f002d0f0b40802071145005d0302181c1003c000c0182107846212160b0000e204070b90421a134274074520000820380d084404500310180400203040c0352140c010351152004d028850000c2c0c81c18890702c6684510340200744020381c10101914859003080011100448008006501030ac400c0100188100301c50f4000d100504503401d00680307590400c00d0040949105498841d41f207941e242000078240e0031000d1000440c0e0741828016035030310380030641e03e0142aa03880e010b5130602842a85000780003064000c248210b100b101074a4240b00e06400c41c511410a28412100148060120305a22000c0307070b004c260448540d08010310180c1c2d03a0360702081130341d0118104403081c1146050346410003c50b40541900050b090a2454800507940d0b030a250900a052200e01002a0920a60250f90003401194043d00000c510f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 11313586 1250 11312336 11312377
    0x1140a0909030206040201121808180306040303140109050108061f080a11150307080121060501031a0903030601020c040f2301030c0b04030b0601050717040609030510090302190602 79
    0xb84d1030f01011a000da022a56040003142e841c50907215040c7c0b9480c811046903442000b684407030016802c00d0021503018181c1c000c0002603503808008080c0f242d8441d58004c1401600c0031000a520001a441441054100300061040e034001040085d0300109210760300c102c21310803c4d40300d601e200055000c001c56009518442d02800031090400048050035076044078034040c0c2615140c29480101d5103c0700060310a0010f101314840f0800c8c1e034a250400d005202d03604181c079203422044617000e90085905044180455034000b10350505103030b1102420002d141107150080011b9282c482101585105a42d550450520200c403940401e24012980b11070015103000c9580514204000b0302060341c9000c2d00440000300e402e02c0c981101c040d81d5000b9100c03c19a12036000555541c0c0048104660711480c20f071000d800309220340c000d8401441c8550342c0100716442d40c00c080d4108100c0b4030545440c00e0400780090003103a000925514000c100251015400080c0d0401400038015500840c0d00c0004150b134 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 11314836 1250 11313586 11313593
    0x20a15110601050d0512070305040b030c0909060a050a06050a170106020109021219030c060b100203190c0506010506030711070303090e0a05040b0406020d0603080318010b0102030a02030301140a0909 87
    0x4000511461100403500c80340d0302e0f00e081102c0c1c1c104ca504020502d5102400a40c0c1d19902d00c4050f2070f0051080c1070250800b51580000344454008a400c0e520b155070110b8400310350318000213550703007002043d902c10904030b0403c00030843c0526580104001c3c080d0000d0340c60340c605d209180c44064000702054401c540e5840d141c00a0181181c14402d900c501a41d050705c0c206c0400c00f05000341c8804855100850840c1036983c1038078100b04050054441e0381e5100c9001b030b2292a4030b040115045507035401786944400b5050402100c9480f510650104084050004001140028800c3c15107504072041a182c3e0303190030044520082d085031070f0707440d4060600d0000030107400000c800f00303460050340ea000040e955443c89408032001103401400214948010402043e5981d00805001e0500d000200e030581d129250ba031031542c0f05a414010240d29014171415125080c880c044003900244040e40c900460400001e64900060241c24940d100c400010b08195403610038040042149001c140719043d002e04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 11316086 1250 11314836 11314847
    0x20c0a0605120c18030318030d05030108030901031a04020705010902011b02010503061315060c0b0f0c0306010c03020705041d01140613020a0e0904030f030c030c0507080706020f0309060114010203031012020a15 92
    0x440c90350082c820800030609c5c081c022000d0700c0c1a00c0c1881d004600f000304880044003e007400b066a024003100e014001d029688a40c0020090f0364060000071800c4005803000604010f0686095400c000e2460b22402c0140c1c3e108040303d400400841e800400c103c405c0040c48020994001d26042282c42c0d1030300080d80310f8128000b01951401010b0342511a510a400350b01c5a2008403441c0001d0316080001810b950702407d0000e007046d000e40304440b00540c50b00041400c4070740385d1000741d00c8510074000c0e05422038802d00501015526007542c000d154180f41c13000c91418150380300329038503903600440e0110070b65109803250031080c48000d20603489801d041c10050300643da150710300c00000342880e9031003113054024081c001180c070541d52228031300100d030344030195560003038a003c071001c98007000f070b00c3d2814501201440c001d0302c100002e0451545420405070209011040b1241590000d100700320110410f07100003000c0311032146a003070b1060b502e4400030b494401c86070002107d001440c0400c01c0340b1035000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 11317336 1250 11316086 11316127
    0x3020306041401081b01050a080106050d06090614030f010c0503010e040501140c07060f05060303040b07060e07030302030c0f061003080a1101050702010f06080a200a0f06020c0a0605120c180303 85
    0x8807180c031540750f85d1900448a82c0701d9104034a02080015004210203480f68004041c01c051031040000e000703441c0c42421701580c07015070203074000d414442d5944000746024800051151400c4008011300d0100c4000039000d07001c148510303190340c0081400203050040c02c0d00420189802c0081011203464074250070704050b00802403d49802d40750254180700c001d0f8a118075809200c00070011414545000401452544000002c4400c9900c4011912010a0400c88040034500c203402071521200c24020161600c03800a42c10070303040e1700500a1140003644900c0034025070760003c40c842c0e52903d4031141a24203100c41003804089602e08020403080d181e06601c0502000000754090090941d0f54481c1642d4100c5258060550700024403240c0e01c1080c0d500340103e0301c1a01a125550141c1d4803141d441174500c0344c0d0f0084016810555004205141084403100038101c0c0e400c3c2982846c81300103241c03010070304c01400c8850624001801c200c0400004841040000c1e000b000c513640c49681c800d0420112080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 11318586 1250 11317336 11317363
    0x1003030e0306090a110604080a080306090c03070e0d03140304060504062d050402150a12050a05160c0213020409060807080307120825030506010206100b0a0302030604140108 76
    0x105031590180d1401280c141d002d0400000104207108440d2203041c120b80c5140c0841d42e01405c10000054000018409812410300980c3c1e110f80301d01d0700d0824030444080c01003240300c42d1a000c00802c130103076810071032090103040c003522690340d0040702e0b00e416604030105000c00b41d00041c1c040304000c03c011190704000e104a109260071300104291075101c580014650252a02d0748044840e4a1401100c99110651050000b048803a8000c1c0b178000f2050035600c0b01001c1800038034401500342001d00305000d015081030000030204171600e0241c01c45d44107040d0303501001e400c01101812a100713543c0e6000640c1048003030000d00315039440d5180040b000034100f03441190703414061550006403c810100981d150160448a072050f0360b001d00c04201c44020700245045020080e18840002c011003601d4180e000d0311864400280e281407120002e45009001855803607940307055442444280c071712005985c20501582005612621104002009454060b040c1c680b0740e4168000041c40038800104500741c03030300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 11319836 1250 11318586 11318597
    0x6070b0906040203151005090903070602030403050a08070e090a02071a09011a04060501080c0c0109061b020610030201020d0f020708030f0316030510150c05010903030c09090e10050403050c06100303 87
    0x6502880100070300c02141c6c0c452a4550215040000381040c00886500c4807005040d680782103d02d5440d101281c00036542031b0009100407840c112010380052031240c100da000d081180318a0420b00c00680007810040000309000e4010481304e0800c1034880d0200100d8900c400b10031110b04d0581c04070350003440c1034004280c550608417500615428588110400d0702d10694400c40503590319845108207500426a041c4e0035961b4035803100204d4114803950200a94140b05aa100b1007d007100a20307241c0d025090211a1180041c01c000513a00001ca210200f402810300404000c0495421b0f03041c10565805140280030009201c40c0e1030110800a52150010010303040f81c0702c0c00c0c60f40840c00c031403040310705005070b9500301c800b8000b0801c60740e010340c44008107283c007060b0340c0030716614a425a001820110042504c60741c0d40b004041d04000b083c400342459403c01c000308044540400e070340d422a405507a02c81d03540e40011506062103802159074903030300d21007120b05c0350406201490f45245140720641c0082c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 11321086 1250 11319836 11319853
    0x91003050903090d0f08040f05040e0d080402041d0a05070303020607020601140108040609080d0b09070c0302030711010903020d03020d02070609080c130b100203030402040f060303020a08030606070b0906040203 92
    0x5019106803802020018010b60504984000f840a030300000d540c16920641071006000025401000820107451180905040c89251106000503101c20303403030442180e0403480c012100198401140d50b4800d030119008210b0451342e9090703602801e03605145500500032006458180a0001215400c50340b00e0750031507400d07a650220403038940c07400b030050a115451021102201c0d41c8101442508a8001e8a0010300b0f0555951103082543c0714901c40055943ca400000c80745103020f0740380d240c0c045202e0400c010404200d9a0080d103e20604600801000d0158585a00b503481420103e000e5503000e01602402c540350700700a503a581e07002d030510006219114010402900ca070004a08680c1080010844000840d041014440100c3e010f0380465a170307241205940c0d80c41b40c403035070380f400c4958020396a80d0a0a0060105981d81c80006940b4107040c0001000080d84c0000e11071039a03a0050091a01d03903d40400141c02032094031009000ca5500c4824000b616001207402c502480c1300310125041007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 11322336 1250 11321086 11321119
    0x131a030106051f030b060304050a030212030c0403060203040f080304150c050702011d01030f1503020109050d050606220609050702060622021305060705030901120603050303041403070c03030509 85
    0xd92080c0a034540101e40781c07000d8102c521820820840707040050902145c41071035503000c18415001203c050300e072940140499403d058040c07140d1904403455a0342d10b440c5203403085030b81c00e8030f104a200081845500000003400c0c801c0f101003461f1900e0b4040350301a0340c0d013414140118029850410f11540b03918054991100320700aa040319a990303810b0319240d030022103503040150310040140c0c5450503d911000d0503082e02825118441d400d82c4482610280c99041d0300005080c44040c0d009103010714554072000e004074400244043c0e00c40700443c1c0c9848043d0030795080400c1e03100421103030711001d4100300c6c011450084642105106550740e90031503005e5541d103420803901c4d1400c040440c0c4100394100307894050440c1d5030020036080151340400308115035111b0101d1100d90000c94180c0d116040030a540d5850741e484000c841c0c00c03504010051162500f15101c640d100d22011b00000e22002d01c182084071600b02c01c0c42075a2526402541a14600c2da4904009e0055806000301610034006268401100c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 11323586 1250 11322336 11322341
    0x4050a09050610030209060f180901150503031e0304050703080309060403170708040b07110304030804060306060c0b1f05030f010c030b06070302150c19091404060509070c11131a0301 80
    0xc0f13a400814102c09910313000c00f1320070f40505540c0030315007204540348050b840309001d58a250280c07400740000174103010403010900e58041e907500901d2090b0020003040102c955651250000c6420703040030703142c2d69104d070700d0101d1903d80d090380000c24101000c03040281c81440800d1442c440c0d0b000c2d8803801d11007004910303c1c009c115001c60303008012500c100041400300b491481d00342d03440f00e043d01345241c881145104241c81c42d0040d60040325090000182440a10342c503001c0e443c001d21550525019071481c55540e4a42c00c18010b080300d034460300070010303921460250701405000701000360561300d0850300e1300100c6010303014044510303002c82e0620350494440c2c149041110003464141d07024010213032804143d0500020003034440e10300c0070000e0020103c0c5402020900400c00c480f61078110001e032810440305a03940010800600c0380f0b190031070070860364848444480d40607155140c40b4050040d00c4c0381c1517401d440c0f0300e141160030000c2c0c0720038060042000e40c0201e18079401e0007207201c25001ca9200300b500b07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 11324836 1250 11323586 11323589
    0x1306031505040f0f0309050d0804031101050403020303030718030204020a05030405061510030209030307080309060708070201090c060507140d12050606030705070b10050d2f0102030f07020103060504050a09050610 93
    0x8a000d200f4400e030049030310f82000b20b00c480d200b8907060459035a03400010300c400700503079410f0360070190000e070070801c000c05500c0d40d02c0112005e003815414985141c0000c0d4503130000810800c1840f03141881e40e4040c00001c21903002840d4020011500c4c2e50410744024041d030821201101c0b544524004070303210711070741c820a440b2200c00404c0b0500c13420701c003041240130350440c2d1030036a091310042c007000e40000d0702d040140d0300c10f482c100c0051500e854004e000804407000601510150b9140a0380c601c0450b81d08022001500c005081141d606c14043c0b8041c1c221454500768808503013703620f901d6031a65070250000c200030f00c0b002420301964450000b0421705100903120000890360402802c0000740342d0f00b044035070040004002e0500345540c3d8000c6200c0a003c800201c40c40d6800e045540c0e1035081a0024580220031101004110848000041e6a0344601e28200702c2510001c510354046a120390040000b07040c01070000e001c0b03414200b4019010380316200c8110303454040c610000d580250900003440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 11326086 1250 11324836 11324843
    0x30512091609090809040e03090a09020901020706030504140708070f08030f0405010f05070f03030506010305070302071208060402130b09010f0512010306110f0c0a030206060a0506030402040f0b130603150504 91
    0x208142c0c0340010b030400a0841c4407044528800503c07096000355a00c0c4201e041e1844140e0196036034820160420081291941040011a106002085041c0d90014000b829621f0300d0400080360f48132400c066245440a11408402d40b08000c404100a500490800b08581c120100040744a4071484841d0300d03801205a6984000d000380002c106640c458200390060031064109149002d5183d01c49a040d06e1110300c09401094a5600b80605d03940c0c54410168404564541141030103610398581b028920703941004c0080050302030206e10b03603035201d604031a41e400b03905464000c881d0751140c00300c0041e08410091804105074441070010b041c020011901910032500c0c0105560303086660f001c0060202501c04400c5410500002c0034024a41d00144070703026260009007070092441c50001d00d0101c00415960107000081c070100429241e040c183c0e81c00036411140030500580d01e00807200241a08003009070b2106081904100400b03159010710241c90294000540c0a0424000301003511425a4000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 11327336 1250 11326086 11326123
    0x2030a0e120c030f032212020c06040302060304170c01060e010510030207030909020d020d020c150a0204080d0806060c0a08040905070207050a0303030e0a0501050106090e0105030105010303020c21030703051209 92
    0x4c4151510b8080116800207a140c041401480c40144210a0181080d02262000340280380380785a02d80401844006401c1141c821745040c1c29a07000c1000e501010304010100600c0e040c00c40540380f0984159024040b400000f044003d5642034002c02041081c400c031170041401c2e880e8007044611034022038110b150140c54189035240303050782000095005a040c04a090360a006a500f0342081e40000d00c10300401800030080d4104049801042000c050903071501684100420007240c8004101888000c1550070214019594400810210310441104424500603100c0704410042000054025514598410441c036600d000042ea51074000d40a442d0b400303110020f0402c006481790308294488401401941c52058161351114207544082e08410040f400c800c8061003485007002006004060440083c00654919100030b5105c109401c001406406e800e8900388a0454041030309070510789440480b80d45017100e0500911640200c4841452004414045841a0000510f50420030641e0200c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 11328586 1250 11327336 11327347
    0x16150c09080105130b07090503030a0f0305060102010606020d0507021807020102031e040b04080c100c120c14040506090604030c030b06130b03070b0a0909050103080d06050a12020f01030b0402030a0e120c03 90
    0x11500382c11740c0204400d0410100000201e980c0c1c80070710107020340310b0850312105c13112480c0701000740c241c80c4014085c0b03045a1410f03004208195002901e0030130b05466003030255a428450011030341c50442c4078515038003083d05109024010354154000c5118001c290310484e108007250304680c010703103003e4902130104e1120101180c0894400c1c002003d01709251000c407035106059414480c01d90700300b0386104d4007080000c42e28080d034110601944403001c00610340040400a010b0110580d400345025590242c840421403000da91030340c2040300d001e941c00c40000392099a40c1d03c1c018000501c1115494040d869003006031088165502801401481c0100646501c5040065100350794101d00d03040e00800c00d0704400020800310a04c41e4078003a6005814455a85000c0002d4000340c80c0300358003650040710702010800062004240c1402c080f503040300c107000704203001001200680b03002014964400e1000043c02041d001c9a8448c00c0c0404c2001c0980d2408a846c089410084c00ba046900041e40c004001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 11329836 1250 11328586 11328593
    0x7030303180506090705030c0316090507090503070311180f0a0504060b0a0f1d0c0a05070501090606060e03010e01020301050105070204091a0f0a1b0905040216150c0908010513 77
    0x1003001114a8440501d5844000e61a0949848000d8481c69419044100148202e080500010441203401d400038445103990301c1400d00381041602c5035000d0b0994900110b4503961182c01c6200080070010211001961a07003044158500440c00c00c510501201e0390200403100345500803486500c071982c414510b41d86030200000074210040040f42d205940302041c0b80c4a075111101c01c0c0207000b129045003021401c005c00401c1e54140101e0804107800303200700308118102c0d00f0048a071030801c589003a5481da80c243c5400e03405802c5d00040100170904254001c60859070040d10000301040440091019064050440e0300302d21080c01030300c0c0010720400503e405810550401d801f040d00c1400344140480c00702070000d202280c19150015100c2225007402900703503a6024401550480c0003164180b01a01040a483e1240b10f12516019680104904910a01200c03039070380d510b500044040400d21018241c400241094000c1c4c0001c2042d50001207007159051040503c03611414078040b070455210b44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 11330942 1106 11329836 11329841
    0xa0905060c1b0c0f240f030a0b0103060e0a150b04060c02031605091303121506140933120403030605010c02010206010b0d0603050102040e010807120507030303 70
    0x583d40310240d5500022080d03546040341c1c0c800140d2140d244888030701010480324500c04001080640024400b64019841100500801c0010f594141c0041d801c0f03504502440b4000300742c040009401c0840d070b500007141c00301d80d08081c54450b6a20004000c95511540088001400202d560703800c41c1410803402c0c03000d256101040c48181d040002184001800400000140101ca0081014140200a040a840e10b4a00144051600301140200d0a074041c4075110002e4a0507003072020103118001a100d0040000745502408000203544214400d03c1c800704140d030001480d601e10502c0748803401004901e00d400380708006807030241005412115254000b43c144038941d090000143e0303000c584641074070901160907440d03070000024413000300040c1d0801859580f0000b03010070602130344000d203412a81441c0c00c403004a40c580b048100c2000800100030301eaa405000140006070003078 = true := by decide +kernel

theorem cover : BRFrame.Cov 11151086 11330942 := by
  have h0 := BRFrame.cov_init 11151086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11151086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 11151086 ≤ n) (h2 : n < 11330942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
