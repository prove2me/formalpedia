-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4950
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:15:12.176218+00:00
-- url     : https://prove2.me/submissions/5c5d5141-d10d-49e9-b4b5-679bb45ad29e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 890107913 ≤ n < 890287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 890109163 1250 890107913 890107921
    0x6030218060d0906060f0b040519081e010c09060503040b25020105010e0c0918091513031e090b030c04030503040b1b0a031e120606110601090c05040308070f020306040308 75
    0x106120317900182c0198040a142c403450500310303502c144224054940110100d000c00d00d1744c21082c2c10110007800030942540c00e0102c484c0c10740030b140258119000d005609200e41c0e00030150103440200c090312265612685981c1d02c0c0d440d00d0b00300c1203000e000c2c00f45100200a81d207e000c40701499252400105038004250340d4034190034a05101c4000c0c00c02d80031510100440c210503954180b00c4a81d82c4080600ca101960340d1250150406c0c03070445502e500c6040860410111503449040c2d80c609910a45030307164541e41100c02c4c0252420200e001201240c103003070090100d6900740018542c17241c184414a446c2948035170700c80d030840e08550710100e809040450610024010300d215840c0140014004190310066502c008100b61a4541040740380c0c040301200b900d280b407150030031217240f8032089c03020300c44aa65024010569a071f0501e4101c403a014a00001c030f000c005c18045c4101190459441d0350909095484084059006074000c40383c0e10030302c0d100b031401078405120b12841180640c4600c001450 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 890110413 1250 890109163 890109173
    0xa180b031608070e06040c1e0207030219230f0d230c010908240703091a06040e031207050a210207061802150f0d02030f0a0b03070e0106030218060d09 66
    0x14090000c5d03208600740b142c01803403594420f940982c04150031880141c481c50180d0180d00b4100c2ca80c00c06034100c0d01c032804221100307034069030755411034210a81d40101004801804021507034640c01d19035004440110101e41c91401c20101c5030600e0190700c804040c4072030718807150700810101d14a40748540202c5520a276660300000c0340001011030102804102c244008000840c0c10b0082e038580404160308046100144241e1121b90f5456011041400c01c07503103402d80510400c0200d03801e41c46241000382c00f0300804000700690720564920703c1214510b40f1881000d455641221386600104801402961444002079030b5120200100710701c0180e80e03005074100322003600d0841c00308507000540305090100603100d40115407980c2c0070011000e600c8191100ea10040e9129032100b4003060750010003840001854880711500034505002c041008040a10506448203000c1c412842842c0240004001140c0250028590b038135464000c40d00c3c581409000865a030070502154168a580d10303001405c00c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 890111663 1250 890110413 890110439
    0x50603100f0b03040f0b1302040207030306080607090f050904020114030406090201020d360f03290f011503020702041a010f08190207020427060b0a180b03160807 71
    0x4541c02d0410351542c5002d4480d00200c2181c8080101022151b00002c3c05100400c1c400c80e0004e64020410741d40d1304400e08000300604080e0103040340030301a684c04280350300d01420312a0f045800700103d2019091a003000c203d280d490041080e07052026a2207228000103803c00158400d5100f040d00190801c5140002071500078a41d14100c244030146401108079a041ca60030550f00e10070000215947c500f02406508a098030340c0300340340c405c0400d0404410480d01030b0104400700d4014001050081d59000344c04418601a110106070340e01c180f005110051002c2151030ba41e100604002d4904601903006c9070440e0038041006030700f428103034000300082d07074400100e01008202d860000c080d0700f40580381400c0004040c000c4002c09600045007030464403a6048101703180340b041320301c007200041d082e1070032001016680d040754114a044410300091034264101c00c01d0b81c28080710301c19107420312408500142580c008081c0c1c07501c0340703840082842d50450345a10140a07000081c0144502e02503240c8440c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 890112913 1250 890111663 890111669
    0x2060409020c0610270513170c010b0f1c0807080f04090506040e0606120a140705010210020c0d271509050a0305031905042102120105040b1609050603100f 68
    0x41008a0b18900620b018071480c00b82d00c1008103800501901c4004d80300188500040006082c521441c241b14003066003000502700c294034001c0240500d004800400c40c0004816421a0780038100141000320703c81d250007140421031050041c986400c1c126107a020080d00100700240c60608009010f015a01050140320307005002034500b484105412904551a84001096103014849121003544500c404006000300b942d0041c280c2500708000074180ca031107807045e0050f03c2c0903104408000380800c1091003200c1a03519490050300d484010f00d4800c03030720300d40c5020210112140400080b2214900404500010500007151003602c42c6950000303094044590700c483e204200c1c581d0100007180000c011100500031a042940b0401500c2c02c1c10b850358042c94100b41554000360900c18224031340d018200c1d800900031035000781861000c41180d8280d642c01c80c0c00403c40f920380300104411a19446441c00140070608201014545030710208140d500200c0d022034a2998040003004050000c008200103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 890114163 1250 890112913 890112929
    0xc0b04091112040201050a020a06050f07020c010807050d0b060418090201080a14040f06021207050702180106020d11011b0e04052208070c03020607031d0102070602100902060409020c0610 82
    0x101602c264a10a03558030042001c0e05001c00042d85c400018801c0c010b030301c44903a003d90b003003046e82090482803403031030700c2258020003511690b60343c19215801044110b224282994945280c060340c0002e282c041e04d99034a2042c0c00510a000201d17016408190300f07080714854090015041141c0d00006100e248050314400b8014500107034050b65030780564075981e0164100030f00bc1c00314211841d08030000c1c4561800303070511102a0382480b104660020007000118003ca541c00000d0f01500342800320b21000b032050340e01580c49400b40d210801c1c000c0c2070200c1000610000095004038407448811911031507440c41c0001450702e1800f1986242611603590402d00040b10300300c10054045494010342e401c440050b10100000c19094100402a64100040c0d540030304140e403a045149009045045091007910440701c0140407090766510000380ea000b1211282d0060841d001146003c8004141d800c0302682c115031b04100100344c05a8030b0006001202c2030b003000f00304501c2c00c0c10b004030404c003541d004922 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 890115413 1250 890114163 890114167
    0x403080a0f02060114030705010503060a090e1b10200a0b0a1515050912071d07110604081608040e0903040501110703020a050405090c0d08031027020f070c0b040911 72
    0xc17036100000c052040d12003e00b011980ca44601c0d00044200c00c459002180c0e06040000030b102500f400f241c1c0c00e44011034210401c4081e006070003009904a00800000006090750b076003841c1c2000301d04161254010100b091b1030703c540750340e02d590005d56000c445d40d010440c1c4680c1464405041c0c01c422900808442521804950384180300510034400c86210070f2066040071002d24411805100103801004809000c01d8200d003822018500181c04079100d502061000010a80e4840d02040a5100396401066949441641031780070912980740d24080e00c607481e00303020216101c1003c08003640102c06440003151200d14080004007034a5640e52032041681000c0340c20001601c0b081c0710302e82034031b03001c840220f020b588848086180c00305820069520514140e401d40c14042c0c60710080d805840b081c4441c0030203c0e150138a052401950700300f400d000347c40206803607140c560264050001042c45074162480c2c01a40d44624503030820540044001100004003001107030260320884840c11410880c240c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 890116663 1250 890115413 890115449
    0x315130501052806030c0212040f1d0f0103080c010209150d1112070f031e0b030c040207030c0807020109080d030c02010b0d0503091504270501050319170403080a0f020601 75
    0x264081c42c0c911801341815145c0d080d080701035009000310401c04e02c040c000d103030301c4681d00c000b001c54042552150000e07040101042220003000d0009840c031481020100f00c1c0c007646195101c1d0085c0e40440c0384034050355400e02003a201581e4012041a03041780d503460a948400c010a50002100c88a100d180480c0301e00700203240040310f1401402d035001280d1709201400344421a000d80240c4600c4205409510004d442c2242400f042c1e44103c0c2c50807015400c0313a84000c0501e0901c0102d120701100980840c803281080710004074150004c010442c81071402c61459943d50810030b01d06014000d176040407940300d2240b0042d460b824800e0b1654500d086441c00b554900a071580c40c0c5038070032469102c8c010526840e0710440c03106030300b0454000b0000312408803640c800304805a914942c5a181c440b8803107060600004943c0341c001101018412411790030b04aa00159890349510501903600e070716520320900c800008104850042e0051600e5a240e40310141c100c4400241800c005030000c2e4000310001d8814 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 890117913 1250 890116663 890116729
    0x1524081303050d020f030a0203040303150b1c060f121401050103020a15030b03031614030f041712072009010b040b0a020a050709061a03090303060402031513050105 72
    0xc404980d400d0304150340c0d1008803180d40390180c80781c00c17452a80c5000c00024402488000c1d0b00441c030841c020350b010407064020020031079001d500b501c20001c2e055000e11500301443c0070402d401d4000c0b000040c002501582e16001c0350741d00c6c0540e40c401183d140f441882e16061044405000000541401c02007003258150b0340014120703d80703800f40d4414409075142c1c1c00b03900c074041c0d40070700d007100d40003000c0b0b035101c2c001d02589204160400174103c0340c2e80c1440311054548480002500c0031003422600b80c42c2824108174100c1162541484c440e000c0e032140c0c0208542ea40c00c0e01d401441e41c680030b15240030002d640d07441c03080c076030b8445260601e015030603200041003680c0c40f900a980070b4074130381400036a544049032812854208146e0001d80140103400b400260000f15600070305c00c8480712007002919801407610150180400c85407003006400030000a040d52810754020340c0c0c005400c1d44a001c5001054000c03880b29020304040080556591005004a1a182d00c0405011640b540c100340242d10142003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 890119163 1250 890117913 890117941
    0xb0f0a0b0a200d051b0109051f200a180f0e070c120e040608030d200a02280b130b06040c020c1e030307080310061707080a152408 57
    0x500400c104010030303c80b0841c0200c460080c05c041030030000b800080194200241c8a280001003000c50321022501e0b00a03240c054050039800c3d60411401180705040c02c03d98008581c4840300107000c00940e0091101d0b54180c03400b00c1009440c6212003821200d042a1414011038009080346060142c500c04000000e60320310314219014610f03203000070302c41046401090141c100c90300405180d000c0800c6007a8541000c0c1c0c800d09002242c071a0f41c140f50300d90001070742110312800603000010380081030402200e03524031105821018001c0c0140c118100c0e02d4039a004c21603416922030401155248592040c04120303e805a080350040303404000900781208080d60300d000d4400f0450007462540408000e0303410303a85002c04144030140a0f00d076507003c90724140250ba4000c03280003242c012100400302c0c1c0148541104a5030403004404a8a5a255500103850104c1c0080000701c1d81030b152007a400c242d070f41800d10301c00103050100111030b000112031807046020410031112810404208200001c400700303680 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 890120413 1250 890119163 890119183
    0x6030e0c040b03031c0b0307090603030f030c0207051309030801050906010c0f0f0501020a170f060108180106150903051905030708030c0c0d09080f01060b0d0b0f0a0b0a20 75
    0x20000341c010302c120046400d42c00313a0640031061490300044a11800c034580c015034405482207094a25241c3c42d502c035042164034030b01010340040d08802c42d40304203902030783c01848210814011940c07107d5664000030800c003079006080c0c00b480d881e64a54020140c1000b07183e409400d04032251203051070144d0000700b20150005000e032a512000b40140c050009080f00a400035030403400942d0341d481c2810b00540885200c2c504115600074a400150904a00703200303150140034140c1d0792003c3c42c4c490544a164281e008004150306540c0c8120001d80d81401c2c82c03041d120310089031102c800d03061441c1042c0c3c0c20094404102c010b03203403210b01601c0000300c0100071190302c01e038003004407034598a9400d001c20042c0207501a809051051341d91100103140c00c03290880032141d2500480d060503105450042c01d8440e94400c20024501c184280100c01025400440e181c4802902c14841d44102e580083e14098103035002c820040700c00180fa000c0c1c95404404c506881e1400a40596210703192804656664091700c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 890121663 1250 890120413 890120419
    0xd08091c051501081915091406011410030c030e1c0e09190915020d06030c0816030b0705090904120e0a08060f1e15031c02061f032a06030e0c 62
    0x400c40802450052101c1071560b405c500301f001d015946044003543c40701803102d01640c8611800007401c14401030581aa03501d0184c180008405070300d400343c0c007038441e040d0f0b6601810b445041e04500c6150800c4021850604040b502d5004000840007401100c04200143d0186503940200b200c0000444020000f40c21440c00c0040c80a445003404584001d008040c0b941c0203000117040d440b81d0240d5008a001d0780c3c0562013029502c0d03036514680d039a99210840c281c004805c01901040412030000e5010b0b48020b050410614001822001441e01c100880d411a0689105d0181003035007640038215141c50307101517541e084003074201000c40d0ba032010020000c85a00360740f4000500b0080441002c95031007901c0c008900c3c81805c180d94444041c14031000c605000c0e100f0a1030310b1010040310048600305041c66000f400c5181c4400b4249142d40210300080202c04020b0352001001402000307001003c2e800483d1182c103100c0c000c80c180046800158462410181800742d08184d02030007160015042c0320072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 890122913 1250 890121663 890121703
    0x1091b0308070803040c120c05030c220b0a0b0d320a0c050702040c03050604151503020c0102191e051305010f021023061008060d08091c05150108 64
    0x5e442e05025240c542e401140d4a500160070003010031210134500c1040c0c035412020358401020600c248451a015200c0c2c3c05040700040c0c0d05840c04086540c0f000501c00d90241c0f980c2c080c541c544074500965481036070740310b04507030762451542c0d4005030300c02c0d008004003003c075101883c820228a9113020240003400c41a00c0b1ba03540c104801d052030048003207039281940540240603560129a015008010407184103000c1d50404200c5a0103010b40a09001510407024440207528940e4004800942000ca0310715200c1d9402c0290505882d41620144410714007651200d84070002e008614070b51b0011040a0700500c0000e1084000c034800e5104d24206072607080c070340041c51740c5040d041249070142c1c0e105402141450a0041d00e100001007040b40c44080c42c0c10150b030099100c400c1449040709101d10328100241c00ca00118401e0b1401e031144640c114001c1d403155090600280c009a42c14000100c110061140b100200042080c1440710048500e40000381c0030f02036142c101240e07242e0180192001c859010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 890124163 1250 890122913 890122921
    0x9030a12021c21270326040c08031927081b0f130203131401050601080f0f010605090102160e0105041503050c090c070f0501091b0308070803 62
    0x30800c000721492900e0100c1484000203068090140c40091091144246545400300841241c2e40203003c50200d07488004c0c644203d500003082c26016110108034204025403440003520030201d07103a9260341c856460f44814a0034140f42001c000c1a00d40d124952581040c07091043c0d03c01c0b052140403101d2480e040119410005ca0390000847c130708910320a54160003003002041e01e03840065804200384c00b0000c0d0b1441030b1022001c02c1182c003400c0310099448800f078182080080714540182da00071141c00c0482c04210003e980300e6043c0c0361000c00c81c841d160b540e08100203d6607440700585d80c108103540c02c03189003410243d036800b0405038140681001e100000501c12540d1348204a14080000c0203000380b0285038885500d06244003080c8141ca01c214200110000711448079202501126440401005540c100800303018820710000c04102940c0000d0180f00041800c0c40e01070f50b00340d8070800000416400310316007081d07040c0301d080342e41089200b42d05060002826000881d402a41c20401c2e09441c0c4d47c0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 890125413 1250 890124163 890124167
    0x7060b030120090f04020408030d0c031d06011a040321030b011e2007080c101713030e090c03040b0c09010c0605101203021609020319020901030b04020a180b09030a12 73
    0x800c036070008210744000200c496042444bd40100c0000c026590140000c840c17003600d9180034003c0b0a500744542d00038000420240040204503040b040d4503004160505070b41352142c440c20620074220004003c80720300501c0a240d41031140c03140020302401e0503450300f0220f40d14030a11900340c1c80398209109040621100d062041503003660722650f05400c54800329110241245c443d104a04c0c080d01880074a00f540f2030003801481400c907204000e000a000960300c070a100321706900c5251041c0c3c14044000d00302000c83d00c40d80140b41c46850174501075a600d04003482c4c0000c0a6200502c0b0003600c080500010100d07070b07444019206070940001010510f074580c40c83e0842182c60fa64030080d14051520a14400c01d5008030b0324442e02000c0000e40300c5559550231604060348012102900610741d01c0a000309106900d0340501841103061500050040203079004c0340c202d80c040390070413004c00c100421003081c011614646a0183c440c0302e10b842e06280340900071a5840c11505030040504801d1400182418 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 890126663 1250 890125413 890125417
    0x4020717160c08010b01110c1008040f0c0b0415030614061b06070903030f09120b04080c152d0601032003010b09040c031505060c010b0607060b030120090f0402 70
    0x3900070b050312021580e11000a80204240305005020450b10b20070200e9024021a82d030341f600070007800038500760048280444030100c1c000c0049071782c040040014004500205442009000d4490503070b82d60701d0030304200d4050103070409600030815041280034045180300c4a50b041030908140c1e002500c68583d61030a80448072031462188030b1344a03080c00c010082d5030125034541101d0298a038020110707031035103044640c02c800b40101f403894a110150017000a101c007001c0c5502c9400340b80c50034142100d0b180e2203800e1050341000c0749020104002401003501c56030721146410200b60318459038108283c084020301000041049040c903a40c3c0d42d11040c480321010300c0c007200b42038202c0900d030780b0b40c1c40d92050100c90f00881b0034107015030700e000003000241e40244610490495032400030700c0903610301410884180e0003190010810f5407100c8001000d030307d850010705480c62040c88045410124101032508460615100042e81003d060403003243d0240741c421561441425107080301c80c1118a000b0401174 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 890127913 1250 890126663 890126707
    0xe0601090503010e010902150f0423120601080f0a030909090f0803040605101505090d02060d18120e09131a0c0c1005310218041104020717 61
    0x40d42420700e40005540103500458982c4c7c821115407030800500600b1032858019548400b006003000c1000f404619103003180700c1040801c0c20120128021034a011401182200d0180040c1d58000c000512008009101c0941d0144150008207462245c0351001410000b451055030f52440d510a0800705014101100c2c000c2e060b00a0310322580d9090602e4064001d0804840050420078040c2001c5039400d04203d40e840454102d41e42c0a051801c00d1040044402401d0012a4440030400c03400c182c54450340a0352003140880281c0b100308590300d0821075a01105910110300b0811000c070030302882d5841c00c00841c2c000300c10341d501840380c0030303580b410710901460034580e20344d00c2080c0020403c2e51610b54000704440c0042006584130504840740f0030741603c100355004c580300301e010303042440c0290500c4c03401c03d840c8680b082c0300044030b00301e6004a43d59003040030301108607904550070403041c001c507840b10b543c4101c07080e14114542a00c640f54545450344000c10340c50190b40c0002e40344032140c0400748903444 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 890129163 1250 890127913 890127919
    0xf020f040603141603030c020f010306170c010e0f010926030f03041104110307052214012604060c120f150602010501030f02040e0703050d0c140303100e06010905 71
    0xc0542c80e814100c1c00040c8000d14902a44100381c41e006a40a42c150840112540f5845604800102e9804c00c490070041000719410140d03240c1d40045c42841e6005030741c08030b20041d4007a0140345a080f000409042044100601a04100c01a0000c2c0c1c0d80c000024800c031071828070f505c0d4180c0c260681494170f80c229070481e25181d120109440d0b003403521000040d40250300c41e000070105200e0010a0205442980c1c20030710030032009200180401f402000101440c243c41e201c6000482501100c00345851401d4220186920600c102c09265581108400700550030f880303803041250b81010181c140b42000240b0060002d0385600200c0a02801612039004202201006100c55202c0914240040c07805c419141d0600d1b810712000182540180301d418117880d0003502510341403032103409201c040c20b9810300035281d510400d10000301180c0d05000c9071170000003c1d0303a2080c0071115402c10f1261841c41d050160015001001130003c2045100030105c01c0701c25140c040100c550f43c0200581d080d40d860351120f50 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 890130413 1250 890129163 890129171
    0xd12120903022407020607110a0b090709051e24100f03051b0316020304030c030605090c011706120f0a05010504060f050106050409022a0105160206060a030f020f04 72
    0x10181c0100303082003402d0b00d0208588074048408070860f03001030b09450107030140c1c2100d00860b00b56440b0f25000c0c1c030311505610855004005d01da840c080740b0242114148400e03040322005011080782805010380028841480030309410710000075021514020b0000d0411180a0000e1204982034103400050890001d18450312041040005812a00c45040881c0000e14000028007079100074200c0030051002e0140e51810340c0e8544000300a0703200c00d03c020105610003803000100180074440708a020318420040400c0da802c00710603007403030205410206030511000f6400d0106030020203003010b03400718007192400400318a5095490a0601c10f080b25255030003101c80040c2840741c1500468000c0c2e1050304104820030492407603130708640081c01283c00203a0104010461010607402500c0320555646004406c0007020820010041a82c032584d1442d07515802080202d1240741c0ca021005101c40c00a001645401c2000441140c0c56010042032013200b4030050044d0f44490314801e29000001d04100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 890131663 1250 890130413 890130431
    0x101b030e0d0503092e180b040b1c0b0105161419020108011a1218060114010305090607090909060f020d060f14010c0b060d0501060b090319020d1212 65
    0x99100c1c2e0151010303078003414400d031174a10b6025503400c055001941c103040c0da0641004d091000c070788900d9840d40b0180d1111500c00c0110f4021850320007080203001800065a03a171151500d0003161121147c0c0342100c03949442100d03400c03a60420201c442c001001410300b41c055186107008518240140041403c034840c00b220701481000400c11200054002d0320340303400e10303aa600d807942c3c110040300c0182020b40c1000d00030403003560340d088100788d0801c40c4840c040010440d0126640c1ca4100300340e00044070128800c104c0c106958240c443c203a00075840340094400c0d45460a8050400540e506c01d41000c1c56807004c0b404d0078800c080d44a5a860342100c48159520121880020040c11480c00742c2c00c0182000d42000440c87d41601c124820080c040e15040002c4005440c0c6082c1e01a0041001e07400c41c02d04400310333000a1081c071608000d401c80250b096101c20010090528000c1341c2c82e004100076004140d520096039500c0400741e00294014984899904080ca04aa00b68090f4402d61640703030070900c9003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 890132913 1250 890131663 890131673
    0x309030c1a01090e01020316050c07091406010306090209010806130e01060b18010c0b0c031003020315011406091c0606030b0a0b010f08160e030c0a170c101b030e0d 72
    0x10720304035041c20500348034480c03c03495001d080344002d60700003401143d10a2201521030040000c1c003109001203080d5081e061340c0c0c0c00c21714156030b454002038100f152400200051980c0510400c4007070454950114142081c54001920f0180060f00040c490b213080110880c4c00c880c1a000510355040020003030095694030603e285194101d203c03000301031080c0f41c150f0100340d4402d0f0440315102e0303000043d2030300326124511920740701c0d80083c003060301d4407001c02404009a107081181c15084585002d0340c034081e615044c20b041d44803a0140405200c0e4404002d1405242c0e2503110b50305240340d541c940e011402c411803410310018491a4030040007600303850204240c1c150a988001c04148080e2030348c000c110005d5400300c98a8104403090303041061400c00c0c0035081803103440c01c9101c03601d0140840740990310020010340b000580f5400703030200c42c1c80040203c80c00841032000b44d482200903100e01c11506a40b40e40a003ca102a0524007180c4250b86040c00c01d00d4400ca4034000b50070340c054103001402d0000d04003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 890134163 1250 890132913 890132963
    0xd080a0e1603050705090c12060609222a11102c01020307080411151308070b0a0c0b0903040902040303082d060f01140301120b010e0c0301060309030c 66
    0x180c42ca07000d03201d0000b170141410741c2240d1207911014007191900d22036070a6041032003000f0305001d03006a003d0000d1141c40e21001800c07412003004090240803141c41c0c0d2104070564250100c2500040f851507048c4510040b200d40400c168000350606d5480c1c4012100c125140440c03042c5403c1a80781400c2589101000c03c400c0506098401c2c105100c0f610f4585d4840341c00d03448240c50311000586001c0000340400c0c524010004400d0340107162103034040111a0720500c5420030000f807454541c0920b0100051801000b0781d40090140104440c00d101d40500040c084901820f03014141c2035880740001d201550034400c075400317030004030702c115111910307810300500071241211075000d1400c501160202d40554844505115140440c44140c26a00c040a11606d0340030103490342d040c0803003501108556210b85028501034454405c007220f0070001824040c40b0060181c0c00b81e000003c1c0700c820b02050655200449042d035442e4100403d0254007850211190400010007400c80c0610495000e034000761001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 890135413 1250 890134163 890134169
    0x10c0807090803090102031803010e010f0213080c03100e072c010605031006030c0903020d060e07061407021903081b0d180e15030601080705010807080105030d080a0e16 74
    0x96103907000c030788484020381e592080480c00c9000d44c0c0184508102c05d000640c204101c808003900121303541010300d0115082d144280c141c507103c540c020945800c822000200040104070110080c0010b05412020a44901c039030340c0b00448030340d102c64500c40e000e98100004001040c5c0d108130107890903143d0321000c91810105c0445010341124034000140c0e68071400c181c0380110b04450165014500c3c14109800501e05c1c0f07440881441010300001001d43d444940c0480c0d01d50103203d02081100e880101c032424040150070800500c00718041c0720000502d4403080e50034080c1d040c0da01c02100030483d00c2e1040192441c2d0300040c1300c0c100004100b80c2e002c0c3c0b01001c81c07222482d400222080075001000a580518101118003c0050140d80801c80c1520303084036150000d4911b086801c07090410303404641400c00c00d82040d4807981c4000000c0040f56481052558003021a00c1e00840300d5040400080e10745a00c0290385040010200100340ca010300e66102840034418031086507203400c0103404952220b00c00348 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 890136663 1250 890135413 890135417
    0x130605071106131502040803040e0c1e031302060a02030a02012d0f060902040308030915010308030703200310050f092710050a050402040e1f090212010c0807 69
    0x40214144600600007452040d480c5809403800d640c07003082465070a2092002076030b19074902008240e10300d969100400c080c0400c1d4024590392030078a8004442690301901c0c222000c0c6007008021400500c01009a00d50b101d0401c09994a441c0d4181c1d405440030300681c0694400d00020382c9001c040d400100510f000741c1c0341c0e0000d000c0d848034034401403402d42442810104800340d844903a040700072154841c004c50158203500240a035250303803006080b44c2003a08125a014400030621a64003005c00c29079140800c4030110010960465031041500d01000e00003500341030712041003090056500c1c0d0b82250342c0c0d00300b8400b00d45900d061103a00c0c5544045108950154005061400090074140d1034607200300042c641044420b8502c0c0c0034a401100703500400b080c14016000c41e0030644010380a028002c01007030305c01284600301030040004455003840002c041d940604580341c4408811402e03e8885030298a0003c1c40c20410b00116801004030a45042d8651803c0c80481e80c0d141c0040d5113900540090f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 890137913 1250 890136663 890136671
    0x241206090204052e0f03180507081c1e2102180436050f15160207052202030c03311101120f0605121b0906040905061306 53
    0x4c000d0102d541c484a9040e07803507042c076004000d0742a0702400c030742440045140b90010705030403002052842407001040494494100c44800c0100d10410803d10012850351211840c2c01d8a0414014221600c2c480158031400c0252040f103055500a12207655080d40e06c650500d0800c1c00c410002009520071408454001c12024000a15043c90700c80c11850301106006048081d0034000141c044074460001040d1724a0124813002c0010000c0c000c80d00450600d80003007249690512210402c16001010554407000c40d0003503044080c1d0001c0d0400842d401030319a100c407610680c402c50000c05c2010130b180c0415000100380b001d00e60b100e400851007981801c0714203030700c43d4a2000c0401c2d0b249501c1880c42505500c0d200490200300694154008068141418849107200055030070599440c881d4088080f03a841c98204002e007000311026241d05600c90103080c4140d14602c603000420159080c1502a0004000254171618ac590105800320f810a0482e180e40c03822181400b503c072803985040f1240c1d818 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 890139163 1250 890137913 890137939
    0x6020c1504211e0c090207050106170f060c030705031f09020f07050c15030103170d0504260c031608090603160e0303090f100c1b031b24120609020405 66
    0x411010103281e80028603030625417502074540d002c0d4020400a43c1c507075682d1000000c6600f01e0380b2034281d00f0050f1170b0203440020001e5603010308061008000780511501001000b0026900c00d04a9600440d01107400b14100c41841c2409180070b407581203803401c2ca1001511015500c2d00b0b01c003400680c0e1041c07044601c5c102c6080280400e04080103a02d0000c01c00600050000806a41d0581c844081c410201410030303895041381015580d050700d05446041628078680001c03200e5050041154203680c40c560710704411500701e9541d070700c52034284000450349043e02002304920342e0119410b0900c0103101c6901c034148022f582c240140e5000c03003000482c05680d0828a10304010090b210310007001000c901800c030010003440006c09030401d200e0b081084054500e0006144081315409003519040c00c40000d60075440d1508194004030307611514442120000c0060040c04040c51890002e58020415030492415003036451000070014450760509080021590450b2907015100b03c8008484e640c1d034440c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 890140413 1250 890139163 890139203
    0x30f142214010c0206030705090a090204140d020f0409020109120321060806040f1406042405010302030712030512251805041e06150201051006020c150421 68
    0xc0c1d801c0e40c0d40802c41c00500c11000d0b14200001e140c0c800400d0400514009101c800508401e81c190000102c143e4041014412240c104000e41c0203260140c95259000a9640001e00003141c1c5008d080d103d107071504030940441e441501d0402c010240c1c51a000b00145984c038001d0449910011521345603039024841320b0420041340030712403c07900c010000e441907071201d48980074a070714141c1c2d050311964000a40a0060142040054456030041400d400c1d003207441c127100c4c00d0050502410140842c10240180f015a8000c5480011100300240719540d0f00c00914066626004030aa0380304d81c500c0070000c201c06e190042d001c0700034140380c00ca0b507541c41d10702100307050f9004e28441141310311801e100c0c4410300550525a00503403401c90350a40031814100004110000c0e1401500000c20554500204940c0d840d024054182c018a5010f80340706800e080400c02980d910311412030510610300940b9851021a0b1981101c000e4514140e06800240000c503142407070f4840c3c400c0481e0902102010009464 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 890141663 1250 890140413 890140439
    0x20322030611191409130b04111c0c0e13050417040e06090a06050607081315020303070e06192003040609090b031c0804110406060804030f1422 63
    0x290b41696440201c030482142292031010104d51980381c22810401d005590355803c03c0b00703402c0c914049000c165001039a040c84181c800c18018452011424411100d00c5900ca20003000d0b91132003584000354030000f01700101c840e4180d20a0360380e007024000710b1070040c0e2000c40c0c02c91881076000d8400007464041084507202c243c0f145100c0c44a0a5403044081641441c1c44801c281e0824400d0740c0100c0d4064803840050043d0340100e004841c10900054410001c01c00305510310b00a008004031815500f8882c1c0c0041c0d128800102144c2c10072031045002515540c9003000c0d282c088000718068003090f40500000f070a200d50300b2480d12080c10700f40c000c3e40c00701000007040758280c0c4d005a40d4030065038a0449014098141c800e05030380d05000b800354a404d140d00d4101c140d1540c00003507494420a003068180702040d14225140d09009a040c2281072100640101140e070b04164185807410300651100c1c811242c44044011402c02d24030001026503050310f40d80104070301030540e4240c1d00d40300342d526803074180c40c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 890142913 1250 890141663 890141677
    0x1150e180303060d060902010e0405090c012c1c0605010b040602010b1e010f0c0812100b2511090901290904120207240e0f01120c020322030611 63
    0x10032160034451303000030000d410243c0c02e036106042035035a0341c5000b000078040d10340c110340480c80e5a1000049074855a8007451074402e07401c83c00810b6045114042d60031a101120700350103070091854429110305000c880300d2003101c85421600c104040e5071a0b500c81c01c1c4903403113846900c1c0103609000881403146071201d001d001848c08a810390035016040740054031051440030402003801000a0340b140818440401031440441c903610101c541d01d085008440602c1e125000007201d101d0500c82c403020017949a034070b54500300c00c414880160280c01d1a00900c0c07540000c51131a04591104103100307103000150804a804051140404082c1600b16a00c100c3c01c9144010a40c0c0142441c0c0486e001c02d2140300d41043ea08154410384000e03544410420b14441130b42c45441c0301c291000005d5204e096031000103160141c2c003c0310700306031010300b41c4002810361040c00300e80c80400780d0303c2040b000c60318000c00c00c4810694076000c4214072800d04038010b18048080d4030040c0c1d40107040642c40c0d0200290b510841d042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 890144163 1250 890142913 890142919
    0x60108010b27060d0204150206070906090b030c0903010f050a1a0108040204020a051b070609090b0d20130207120507031b020409020607120f021b040e01150e18030306 73
    0x240141d4401414864440000301c9600203c0c01c002e2502003643d10300042000c3d084400d0b24144050300f100f0020b01c1c0c03040040001c0d00b0002c2003c424891942d12040f406c040360402e6141356101c1e00d07000781560080c4a8040c04590662a0011101c5c910240d50015841100340000402044240c4001480d9048141038410300041032040010014501a40a064410f200340b61aa007070001001040c1d43c0d05100c401070040d10b6001100400055a10480310005010202030a02a400344100828140d54400b200140382d040c03542499842000e003004100d4014200070f080c1c1101c51042c584c10b0000b50300000c4147c5142046030481d40d21140100f080320241ca0f0b0540d140d120b0140e0860000c5000c00f00c85000320383c002c0d2101e5102000d0f94071000544106405203c00d100304032204603002c0d004590131442d007020364000481c224042c0f0b68507a000c00c0c1d8020700346c6020032141c00484040340103181144580804203003d10340400c0082c40d140541e4410a211070070318500f040c0f5108203a82c1c074081102c070594 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 890145413 1250 890144163 890144197
    0x1504060e0105090f071e210605130c06050d1e02070501060807031211030702060a050a26010b0a020c0303070303060501080a02070b0a0e030c060f0901140c04030803101a03060108010b 80
    0x20114442c0e064050717802c011448170f007035521a2191f520402001d00c524200800c1c5042d6030040c4100d0b4803070175400034160b1101010040c1a640c600306209032a10500e4203010000c01c1c0080c4a200c160001c404851400f4000c0400455001c0c02000a41003402c00f690070350318141001c0f44207440064036405594200341c0103000395103408401c481c01c0c03105221055a5000074000000182c40d20310281ca109821130310341a44900b090340b4000d20b0744800c0d0080c403910401c0c60700802084100002c0d03840c10358100059441c1d848800c2001a442d046000fa00d481e0540f100259541c145681648498103450f82641d898603e922070116090130380c00f520402070848010080400c4d07030341c0301c03a0340410003004020050b20308044450758039500303240046455072220700c01081008a0350302c4c284261692000099107925036414038803046005d5020780d0100034032303111002021800b009108031804000b4507182140e03032150b00c24607044c005c89410503149107000c50449000840e08540c007009450700503401280c462 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 890146663 1250 890145413 890145419
    0x50a0c020705062d0d15030201111504030f05130b040e011a0a230d0e0f0712120306030209090102040806070c020d02040b0604090f09050c1518031504060e0105090f07 73
    0x30710a14480754244034400340420540345d01c01c942d80500c1440c0d0350b02a280d80300741d924500000d007440b201c00004940039040030640803e01c0b0000240f0f5500240c0619106052a60300e00060740c45100d00c0c40704090764400020001001a580e0004105550702000306001e241d9031104e651076005012515640202401c2c40005100303840f41009a0b0840452890085195200c0c508030300303035030700405d50b1241c01070700d400660410f54000c00402071401042030080440344d19011400e202107001da43d008040c0c24100c4c00310710219110790844005150000c000c074200f410b003014514000c3d8010700c2204541e000b080c001441765405564104c400d950058a28041c9a18940c01c0100404611400c3c41d03000d0b0b001e2001040000c910300c1441070314240a54002521021414114500249140c40320712802203142284518060b4505503003465034070700c0000e00200854800030b0b0419060020254501800d40704000900640c8d40001c2d1b2051004002007020707481e806030440d1500c1440d82642c000750b05c228420 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 890147913 1250 890146663 890146717
    0x60902090f010945050a060f050d03050d020c060702060906010e070e01030f1b02010902040513020d0b07020106121a09210a12090f0c2106020306060c01050a0c02070506 74
    0x81c04001400030b10b618910050182c1c00300d4908550421036007507174076420060900e40900c1040054a0000f40032164540340c2070000f09641e10380e032001800c1080104058125000580540300380030010300c151829460032500c001d640300c10454455980f0b10a680001134542d601d02d9049000e040f2a64400841030000c02c01500a440e442c0c20313100e00a41d507138254ac0701107030305018100c0541001d03500102e804645401080709030360018088151301414440600c00580d00c00e010320b40c4841d4000740d07000381e036680c0c11402c0e401071689074486030a01c40400701080c1002204072070070800a003807444078501c588540c9920741e503442c1a544c0c0c441205481500502550602d040900741d81c6e40780c0e240c49940d030f1014480c0c45046d18503469003200c0000500d001c040c02c104251185070050140b02010848041010421f0910000c0400001c3d00d51a40000442d10707940f07811048521504000009102504209440c1001010385859402c0140915100425145801401c540e020b180744403803c1d84070503507a047d07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 890149163 1250 890147913 890147969
    0x40f0e150a0c02060103060e0309030a2f0d020f06040b03070e13050910050a1d011505060a0e0f0114031006110a150c020708070b030702241605090301060902090f0109 73
    0x480746480c841402b0004403a0350800c40d40070406d2140f0141c040380d404c109620070340c282048060b1071010804420441c600c1c3c0b50f6442c06070360180c04542d041d0368406040081440d620403500f0080c2c0c058000010400b40d1a0041d5295401580c1902c04030b14100d114a40e000840b00141c80b035208a4101c90401400c0d1560354001c103800103025030000070b105800a0034002c00b0101e105a551881c0d46031601c10341d10003420900c800091400341c400e14a40400180c004011400c80d8140510880388051012080e9103d0401410304000f90300045607281012007401c0c030079402c28440d04d40050840707864140443c5001c24001140b9034402184405c120078822010080d240c400708000451103041d200080401c0c3c2000b407900200f0385001c01942e60b041150000317003410321000c1f450110300030951044040c410311500a60b440181c981c03080c0001c81105208480c00c0c0302d040082607042d800c00c00c0100f82d550301c96000340041e001c01c4a41c0d80c01c4a0f00c4000669843c0e8081c4102d005689420f42584508014004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 890150413 1250 890149163 890149181
    0xa1815050604050d11152703010509030a030c030b0607030c020432090a08030c04060e1c031b080a02011a18070c080d1401050f01020703050714040f0e150a0c0206010306 74
    0x24120060031b07000c0581a41c001520640081e016480d499120f004202182e070849403059000340540c0c42d05c440003075607910408400a0030140d6400c07032414058880c0e4400d4502030002400e1540e6500d190400418644c1d1102081e4821441c28102c0038903500b0141c640d0800b40701040c80340b480328100d500c0907008a03400030301001140c061851243c000909000007588554400400252a83c1c18a500185900d5a4103600f03030260b100382078540360b030040b040684400a41d141c64103041c10765013420000184001202c0081c801d01c4042228078515406400100511100420f590050142e8000300068402c540c171070101c00c4401c0f8030108a031680f08824403443c442c00303084000c2c40e21002403100340448065006440c640c2c03840300014045483d0104150071445400d10041c421141140c407159100d964030f201d00006003010b0480c41013192241c3c1c20041c590844040c0030002c5a408000d81901d0703542248400d02410304c08000214010782034410303114810265801000d00e60300315901c500c010305880c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 890151663 1250 890150413 890150419
    0xf060f060910080f0a05060d0f02041b02010f1107080702060a020304030c08031803011509180c0315060b0406050414060408010531020306060f0a1815050604050d11 72
    0x34008035202c6401d1250b101c0e40c1d0707542d10314142c640381020f0004850064220f6407070b41d04002c284141c40e5690307180c0c040b03150f81002200b40c614001e0700c001801021130038149101c01d0507142c42130101c25010341c082c0e0802d0100c01e40c140301d0940322640e40f10301403081e5000200500010721070200503050003405041282020b00483c0d10f080d46a0703c400021800680c0850699800068a2060307000713400144400036505800900c01400c20103010003c1c00554014218060703500da000c00030184c5084081e0300b5494201c8000044692603003030043c021052203401403a0f560800000240703001c00103003150216805039071400d0800e414280b00800000608401c03d52146d0207002c00708480c002071003403600844108510031001168284410f8610003140c10041d0741800040b50380c00543c5001c80c0f02a40200d044501481264081e030024050f2401c5400404403000c91090300e00d00039000b03501c07000c0003c4011940081896607002044541d2143c1d010b890f82050042009100040030b410803140150002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 890152913 1250 890151663 890151667
    0x503150408180a12060605060f1c0b100e090f0c0a270b03040303060b03090a0f02042406140418020c0c04050709090f02030c1e091005030604140f060f06 67
    0x1c00060384011203401861501131081030348801c1103018891174005000541d841c41c10300840400c0300041d400386808004400e0404485042a651154000311104400401070302c450a2080001007001c0c0d41283d1060013035070000007040c502c0003000c56551150601d100716610f01424103d0031120409001085c00e400001c004844180d9603105100310040c01d55003c1541d103a162500f8003c0944a00b50b1000fa8280010402d1010400000c220320400f2500700082c26001c0c003036407021400903c8041184000c0c0314007000b0320184018941d1503001141c1903650b07000034028541d218040580325510400c00004402203d29030307003204030f801601c45000c0803000e540400000030080f5003034407021a20400020760001045c01040003901c920b0200b0900ea003403c41c1589810a00d0024a200d04c00e04404d00794480f02d81200120844411500c42280281c0218201c4105080140c00d076002030321024411820440c024110f00c02606401d486541155120420343e10317020103000050641200703058014a007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 890154163 1250 890152913 890152957
    0x5030d1206182f090609010504050604080307120e031e0c040e070501140f03071b06060f090c0305090c01051608040e09010b06030403020312100e0702060406060503150408 75
    0x5a10103800c44440c680c200480c4044040c4228051103a401403080d4541d21032002010321110110b003030300c4003a24103988841c3e0b21b58120005941e01d001d00da10140d4018400900842c0007140400a0040c8600c20b0500314440009a00c040d01c414075614a1590103510607843e11016400348906080210304a1064408200244011405a0f00c4000610045610020382000b055900030039030003031412901c280038200740030040305080342e100283c20f000410048484a000c000c000c10104d038091603020204101482d540c0d0701c416104c06651040d40704980ca00800101045e000b402614800d0725401c0280011403480c00042d101a00b14880360844070803da00c01c00002800c0800405c044d2280e01540b0b40d00349070003040f1134251100d0102050141c0e000303106002c0000d400009031441400d4200041103a550703400c3d410151500c082e401615041e85034000d0103026600490614003450040d5424850b0036110010300d6a00c3d0241d0840f96864001c0d0000500402e281c84081c01c1c01d401405c0b030b4105076401d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 890155413 1250 890154163 890154179
    0x1b0702040b030f01060e2a0f1314030115030b0708090c040930050301090209030102121315060503150a02040e1008010c0e0607020f0f10051b010605030d1206 69
    0x114014002084d07036480f18240041d40310201d40130b50110040115500004007508007c4c16041503040640c000c0001060382110440001c003a00e0000c100c012a40d020a5610300300c55100614141115000c1d501c0d0803004919045090048015690868900746042c0c66900c400c8801c0d8000400018590040c0d042d200c20664481c003804468a0054100f68038440b1850b01d010400b0864020310120040710b1900f480c0c11540100036241140d10001005844241c1500401d02901c5042e0403451015244401c0107075032051140b440c1511030003500c072403210804001284040725000e000e20303941540b04c0340d48050640301d4440025131203151814054149582c0301c15003015914187c9401c0591549480d003442010300034072030825001d036140f5014241c419440c009c1801c03440307100406401400d608807900e00980b51020805544000500800c1640c0140d141c0108550401c841080f515038250390951300c030310414001d4070140c0d14000e000d0140d01030200d0043d01c020002c035000007015900c60303200050b205 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 890156663 1250 890155413 890155423
    0x1081608151e0306010b03090a021002070b0a1e02010c0206010b0a0c051506090903130b0c0a051b28060305041703040302010b040b0913200a0f09060e1b0702040b03 72
    0x1865040c2c0580124081804250520105800a0292a00c14400c000f6000c0c800201e45001940540344080f0101c4605022401c0059075044443e260400050002205038000c0f99404026844110b10307901c140714200072400c0c0e5080310700401c0184e00580042c0003d0b40c40b10014810302079241050f081d110701c0c0d652114104034840c4000c16030b61401c5010400d80381030005905034441ca10b68003651600d511046081500300584c00350011818006c2650480d8080810003120190703045000c8822441e0031420101180020900345c0e03001700031109401160041180342d4410b25251034070401101810480210000c2c417004100782d0b1802151901504071808983c000d42c06140a60300100700045610140015158940403450003051040100100c01d440310202d8581c8650110b030940c00c00762281818842a40184500c1c0e0340002c032607a0000d415404100f5000072038904040a10010355902094102140d0444800c5202c1e0b40f09040100c041c036030ba4004055091006000003450007220020138908 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 890157913 1250 890156663 890156689
    0x203090f120901201218040912110111090906010311040f0306061406120c0d140603100b100c08120a0207060540020612010f050108160815 61
    0x4074800141c60309495900031007103e4a082001d204681e11691a000e0035075801440800072907880300070883d4816582210000c40c0c00c51001401070003010310508181c00390200d00c0700307001c01181940d440d0b08004141030040c095015030300715965040114103010300030301c030800074030031410140d80b882845100c5d6078900c0640060495480101c0d2481c0c11880c04c28200ca0143d00000c0e40301e800141340903110b5032480200c503121541c008441c0c1c581d40364524101070a020350243d049106080000181507503002c070400d58400c1030210210741004040c401d0780401c0710080d2512a0f0400c881152120b03910b070003011181c403940e100d02c1119180081d03c103d00c140d07800003554482c00c0241c0001c0c06005001680c040c030382d048000d5044410b0500c246a240342d200401c841d01b0342000900c42c50401300c6030601000c680c10a42d0300541800d950b0b41c841d03080f190159030b0034010200f0340900d11801182551103903103030768826000350091a255155a543c16203109400600c1c404003501d03c03440300006626100e00020107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 890159163 1250 890157913 890157943
    0x20d1422050a1a09060c04030c050607030c150207051501030c03031b211107141207051e0916231e090a0905040215161b0e0601051204060203090f 64
    0x541040742070182003400182c00708201b860140020b1002c030b0b060201400841e01c080328142ea80d80d072917103016100034001c40c0001d0b00346480c060701204443c0ca10b40003000740314031410941c0c0d142d00e1070203012000100c00380005403e0101c012030034400a40200741c01b0f0500314020130311000001c45581c8445207070351803e0700c0c184080c107a05800c2d000380d60401c05050851420b1005056041d0420f801030030240750081c6d00c203115412029610791101414800321018180c061700d00b01e91030301c800070700b1140201d4040b00240910003c00c0010814056100360309100c02107507403070914050505640030000d1200c2c2105402a250810013060f0003201d5100380d40f6481c648610340780d1a91007039401c0003510344595204190207400c01c0c00308801aa105140f41520818501d0525165500c1d4200301a01651507203000300ad20380d00c6045807244410000c200401c031800e81c007d0713410b6940c441c3c2c0110780c41e004540804070002901c001081c002403203600a5507205002800329480001e0031100c0c189010118014102 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 890160413 1250 890159163 890159213
    0x110106080a0b0a0c02100c0504031403130509150d08090316030302070f0e16140301060c0203011802030307030e1219260703031a090406020d1422050a 66
    0x1003003001c414100c0d0343c442c040703203c10811080d40410107034940704100340f0b450009554189544825025034140d5001e90342003c2c4074000030740c9110300d40342c0e6948283c281f441b07907003c00d18000031079152082c100d500c50b030180c00d800d03120150340d80144541d808a400301114040000e0020390300b944c404011038080040e940550030100d03440d504019007000c5003a08a51401c00ca50441441640c0006c1a2907411040080024184040e0013000b01c48001c140240314031002d80c000000500d0590014070001128001c4008112120502015014035000c0410094045c2c00a0081c1e20100340180d40b08000c00070094103283d0481440c580940c1040003218540c035040e00700700716070010700480c000381c108109508000c0f40010100c00325000e00314040c42c000201096200d40c140003c0310942e044040d0320f02c1011b019079034203041c81d1400c80041d40204000800141c1340c29240c1104d0302c01c1607d035038014042003401102a001c9607400241069102c0742c1500c251141408040001c0c94001c07442010f0b44084003241 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 890161663 1250 890160413 890160433
    0x20a030503040606091815020a0e0f300f03032404060801060602010f0b04050405060103080d021306050a030c0e01080a0216050d020304031202061603050a1d0c15040b0a03020a11010608 81
    0x2003861142d45421f414441c41809203400181d0031078089005044119403140511201c90009000c02009416081d56241800702c5e802c1900b40d00d04140503120031000646595071401d40c4000ea490104458000341c039409414a024101343c0c0c041c009080d0200540b001c60b8150b140e10149094503525800440140e55580c04a6039100840c859202d240508030380620003070501e6104e0558810042c0400380890200141c0380d69079420507811a14100c0300741840100c041d50300d25010f0318a4200e00c03042400700b821300c10300548051164030700080e010016101d000658582c031807510b0003500882142c0b0b001d03c110003c408045038040040000260030380c1d00071603a803801c500d000d05a2000910503803003598081428000009204103101d502c4603010300d0002101d03070f196110040505803200c1003410801d901c0e6118928101c0208800c00450f00c180c5845404c10200704030403c0511480c030400e14100400d00440c10080d02c0380c0c0062455070058900107402c01403a80130507003191107544c000201980141e8141d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 890162913 1250 890161663 890161673
    0x2d030b040e0c01170f0a020a050705150106080a0b24070818031501241b150b010906020c122514180f1017010b0a0f030201020a0305030406060918 64
    0x2c4100e04202010000050600da504000100c5c0702030101d01c0600d40100344040307094450703029502c055801504580038000032030300100b45203000303005d030100003100c400001e6440001c50044108000c0d01501680120780c8079a21a065482c401c0700c140c44c2d0b0a810405800420103442c0505040714404840968600840c41003624085214034860136001d03008c0010050b10f80c1074000b0820142c2c03440c0c03407219041c003d07250481341406000800a01010145c007144188521844500d01009201100300090301c002c1c0c00654034581544202d00041c0e1110660f0103a5090001012122a26101c200d400c8544a201101599001c10011a030f6149081c02d040200c41508903c0d0302a005040e200c0003008044103181c01d0441000509240e46900000003040c100000c1c100d02c20010460140c2070191000d00194281c041c14500c0e0717420b403083d80c4106000c030721215600104011254141c00900c8004060f035000d42e0140c000800580740280e0f20040007a2902c0b980c0109400c01500e41003040700c07001c0714904 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 890164163 1250 890162913 890162927
    0x4140a050a050a140d15150611030703031a030102031603063003020c120304060207050303131818030f020d030902030d0e030a060f0e06072d030b040e0c01 68
    0xc1c0c82499400d004000546950811105440c620702c502060600500c0102d00300c0b60905000401103910501e040151072450380c0a0907c034250003025201c1c0550f196400c95021009900064032a00100000c10009000e5070041a140c903000400c02e00a100d50340c0001d003243c1045030704611003042c405040314050f92511130f1002030400c130ba00c1a42141c1d4060040111a48072a481d2551850103021250516000b009401001800144040446086444000d499801c41c1c440d00d0058450301700049414a804400e0360b4a01e810451400519842c0004030b5107a003544285544510742c0c8c070302804400ca442e80c11001d500901039262200a50000030000780ba00c020442503204042c1780c8070407000140e40101e002040c40b492890007944c42c000c0c23140001e003481c4411200414140c5000000d1176205800e070062814405100c0507101d040d52968002e5503080d00b8190450001500c80300740f542d007900b0720300c1e4049071200d003071a000038005610004a41110b103100c580307a000e54411140301100f0f69001c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 890165413 1250 890164163 890164169
    0x180803180d0c02010e0103090506150312030408030703020a140c0304150f020705011110020d091106033303150a0c0f090909062d050a0e1e01020f04140a 67
    0x10000c0111140000b0038204003804004d040040304042c0d08800e0f8031a404c50085960405e05540003403c1802c40c01c146505c1c1d084c04103006c0d0040308160104294254150791182c0c2d0080582071a555441c0f400301c2c000e600c40c3c00010b0500841d80964803103060303c04003910801107910000d61b81c850410000078a8100c1d044602e00402900000c100328060303010030244211202030900c1d60000342d0b426401d42c00d00c001c41020003c11031020800c0c440211541e0400040980100d0b0070420320100401408070341d101c108c40e042c006000d4204c0c0d08000c500004040c3c51417032041200039143c90842c80c00642494046c3d60040034441d10f45023440b40a01c05440b030000315881c80c4c03c010b401c1c8d80c02d19034003600080f8107214036400580e13100c024009018694101c2d06280b036080302c10030409803407a02c90494020341400e49102c4036160100061013600b0510485c01c0b05100a801010141c02c10100b03002c074000b0058540c5410b540906c25460000a80c40180024060300f15001762150301001c10301418514541c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 890166663 1250 890165413 890165461
    0x60c030402090a0b061b03090319020f1c15110d1a063103140d0305010b130b030403170108010603110904110d08041a071b23010201180803 61
    0x10b030b20320704180d445c030f03088855400d0ba40c940034a40000003455607003940039000c0000d405026964081111694074031100e00150700c03c444090950b490a000e00c15180d81000806c0b40740320b03d106290700401c8110403444140742d008500402d049410401e0b070081a00f00d00304241043d03486450740c0e0046851801d00a440c040151032050400901e005120000489508503a100704008001c20507200d141c2c1894002640e0000340000010340c981d08459942d6060701d01180010340390a0010070503c00f98000c9940d4680f03540001d1018904041103500543e0020700214240501501442500904d05604074024614800001034161440c03c11800541c501030640d80718001c00ca0810000400361031606040b030901781e5588802c000180742402d05031290381c010940c81079a190a1901e00c0318280024180d9603c141060220210b6218070440f900100b802980e01150342e1030100c0142075044032740c10340200814800810a540000c411072800f0a50f070b02c055640c5140001040b07101110030540c10000100c7d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 890167913 1250 890166663 890166671
    0x10302041d060a090224031f050f060a03020d110a020705010507050d0e060d0f1b0c0b07030b010c022d0a060206011206062409050d0201050f0d0e060c030402090a 71
    0x8281c9040d202c100c001e200c8080190340c1c288a00075034071021400c081c8803101c40800d02900081841004171500210f528024003001001c1040c010841240a081156005401e010460852001704102c503008030078100105a0b0902441c096544e8500403892401049800b556903031240010080c02c00045420040c14401d0070401240020700c005000e0b11501414500b440358540c0d818001603052040040d800d132402e003809080405140c2c3d80d84822500d05003200740200d0042020021b50314500e032904083c01c0071301c20100083d5414001d030015812414140350200030f04403154001500d60120403d0203413403409a081d8401e0070708541d00c1009040804882041d4107902d0640003c0d0384603014000c0c014100d680220340c1040000e40d4000d40058034440003500240ca680c0e0740b006985090b560074007400154a41800149402e04051203100c03a60107035205843c15802080b54500c55200e020300440301c55903a1560000c0c2c0000b8030049020742c43d80100b0315642e04042c010003004c1400908039030801450 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 890169163 1250 890167913 890167961
    0x31511160f021003060f090b150703050a080f0601020a200303180f010306052b150e061609120f0b0f1503161509080d09081b01080712020702100801030204 68
    0x340406c0341007110080c0c00e001c501c1d010000e0201c0e20040b590100034102c50408908142095041406041c000907142e80c0c03140181d071034040b100a110f00c1034034150b015801c104c600d00c000c80c2041c4600113000b00d20100c48014843c500010070715680c00803c0c5076100d504000040c40f41490310024142c9001401d2030107001160411002440707009488005541c0c80c40560001c0d402107040c5d404d425034094001e02c207495421028101c040142c0404000c004142c0181e03030016503411a403143d54a0101d0480c0e03106e0070514203003000d09015501415083c1c621a60b128450300008840d03000c214401d8581d1200c500440c00c2011034034848030301801919209402c400054004d100104840b00e04542600c1080031012000d168183c0b0501250303000142c880c01404c0307481c03050f2a08a03190b0000c4075044002c9403048844200d14812900c120301e181d42c0082d03e0100800c44c0140305507503282c1c00500c40b00c80140780c60f5080c0c3c0064000100308145601081a030070041003546450b200c1d07585014085103080042c502 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 890170413 1250 890169163 890169179
    0x10f0f0b011e031103010e27070909050f03181005090f040c0c0c0609051c020d020906030721060609180206030c0405030703150c09031511160f02100306 67
    0x4507003150b07854040326200c115003900744244c004110313446981c552541d40703503140c04008601d080d0071109050b400101c0d17294034000c581c54070901600142103d001c1c0551508050061000d40207070354083d122445841d1850000b910140000d0500e00003800703031225400c050320140401c140081244a050000620010805440d080c0b40008140c03c2100c00050300040d0500a403540110303504041c041c084945804500c0c2604080c00c00c1c02d641044550140b4122005000c81d40e0010304903000b5049070303441d0002c10040c10300445203a00301e0002400c1d1514a6240d40035001d40e0bd0559995088540c00d03103102005101186c031030701c000303070030140e03014442c000590030b4588515883c1c2c10001d001750b000200160440034400291005050000c064030301c450385d02d051019012081c00b220b540d41d10711f00001642c1040c040c06196003203da2201c5c240b54114042d0103d10002c02107441c218030007400800080d415010400c401e002500d03c01e2010754104420740c01400440310f40d00104000303143c644401030054132 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 890171663 1250 890170413 890170427
    0x303140c041e091503020301060b0c12160203060a0605090c040323010f020c030d050603030901020601180f0504080c060703020f040306090606030f030917010536030c010f0f0b01 78
    0x7070602040882ca940b26000110b000c800198050359896191070714403588410a40f100b402101c3c000c078020310286844a8468005105140c1101400c0c0d00480552900d100300c100507003000007442c1c500101c41e000300c0e00400d0070b0810032a02c510406039a0902809245401ca00c00da8100e03101030f600034100350a55a414030071482501000c0b07115065080090b01082003501b2141803000d0040d02035440b100071041481e520340007101701c011010f050000280950400205480860005034028605071740b030050140c01c41c0300d5101c00551010349071190b84a10303901900895000741e01c10352807583d55800396490b103420503a01500341e800305401000076420003040350054400307481e0456400610381d0f0b0383e85021001040700d94801410b401e1803000035014180c03c5030b80c2c002100d000c040ca140306202920752aa00b299012964080d0302c00401c10f01030039480904813560094400b030443d000c42c10b042c001d545855500940401e0400741c0d12000141043e48850003900c1c24180710100500c000c40f1040000b820034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 890172913 1250 890171663 890171669
    0x31d09041e020619030e030c03092106101401031515090e09030c071517150a0b09010909050105150325051b03030420010e1c0303140c04 60
    0x503400199007a1a5040c0c003074900c0308078035802008581d41e00035080080c40e10080c5113000303001180c82c10000d2203c194005c0700f00c4511010200c05180f50540d031800b04010301c114150324103c3d148024080741400034040080a01540341040598036080c5480710404410a40c40c411904041c20f0001d440364007003444416800b41c440d18036007260400146d000442c0d8540b11a0f01491014080301d05215400310080014018407413603609940c1c0054854582c828429480c540910010b4210402c00003180c810f091180d800ca0a10b6001e06404100480050340314170294024034520400080c03000d41035038000c289000100361604040c01071b0761602c0006036030381403041207422100348000000385c0440c034084c007005405181340070a0560020b204030020207a40014082011401403001c13020701c0c1c4c64001040da441164000301c48441082d101c0498a20881c4402119060003003a9107640010368500c144d08900e059408000403000d80503060040a41e11600e0060600000000500c00501c249030100d41c02e1f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 890174163 1250 890172913 890172923
    0x140111070614090303040e010302090903030c04141807030c0e0301060b0d0f02090909030c07320102010b15030f010509010513150f0608070f14070209130209040f031d0904 75
    0x82c002e005400c0c1c080368880c070440c481d41800b0000c0c020405070988402a03040c0c81c000c3da0b01c10304941e40c9942040c0e80344001e86000022035424042000f50400801d4800f11101c4d01612000e0450743c0f41040000c42c00701561884003198403510b07148600c40c2d0002c880c1030443d100324000d201180c070f050000b0700725104541042202c280c8542e442071100550390102c8040c0f040141100000b880c20740c4d82aa202d401c6400110100e01901e0b40003d1001061801e0f121190030b002c001300c440c1100f452420003c4000041c650b4195500e5004100044d0b880480f1400341e00c0000020b56901d00c0d0000d007021031040145c1006d0b1040070b0600040c423294aa074a200d51440c000f0000000d0b0303080c611500700300040d056034400044072030002c0020a4071580029803c0c0140360765201d0440050844100740c510004004400d050701030305105007000f52911544684d0000d2148040d049104c90036008500780754000c440580300071425001c044205070380446509015070402c80b0ac00c40c1e0311340200004030420350161000d01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 890175413 1250 890174163 890174177
    0xa02090604090f060803030f180c0f060310080102030c0c01060f0e0714161a0a06050f150c071706100b03040b180607020715020f0706110f0d091401110706 68
    0x200c402c1113070300c1140542a580e04481c1c4038070789043c00d407241440480300400d40c00303c04c040f01d000c0c04c1c0380000d42c007000a10060100103942d00b0507090000c1c0d50802000d00c0315203100d214001a04c01802c2c8015070050004614803560340c0e0dd00b100203402d45500350b002c3c0075400e00241d002c02c501500505139a410195a10344090b00441190700c0c001240101710041c802c418046081104101d0308615010200b02400b200580640d14040c00c5030403603401e0322420350440310314032070848a45041106030142400c0c00e5034050a00307846028044c80d06450b42c02c2606c9401d501d52540511920400c40c460f4412160624141c060b400d144070301c0014000078000610711a280c6003c100c4072041490b804070030782d2a14086810f64904110029a40e9215110301c46807500090071502003640b012582c039800d0100500140309052425234221941501000c1c3d4240c240200788200f80c2d014400e100803030381140e83e5902c04003501d045c11550b05a075540840c2c414184106240b00c031480b1040441c140007100c80c242030001c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 890176663 1250 890175413 890175431
    0x1f092408070909150e0c03040f060509030d09150533131515020d020a0f030306030206030403090914090d0804020f0a031b0801050402030303181608030901080a0209060409 75
    0x3850b0035500e03400c0030b00224146a100e0000d100041040021903500216241480d00c4404105405102c240da014244d5900f03d000040850299000590090241001c6130315241c2d81400750340c00c6079a810001c444204803000300c0c014584642c01015007044d180d0b81c40080000c4e84c003100030301040c0c4d0750503005002c55183d400d043d41070f0f030f901e041e0107006800d801d024401040c41c440b140f200015540500e06012008a940f52000c0380300040c4021a607a40740c0007000c810486403289208040b03050412400c041c0c035140c000c1b0068a45a0185014521036104d0030581d9007072440d030300141c1c1d5080010f045120032800401100721400202a16442a0b504081c507140d101e50001c148008052000c00760804440d50000007000079100b02100c0d800208828003d003035444d404944e0980f181542d010758140d1061004c924100c0308540c4001c1c0300700c078910468100034504c6070380c90325080240c3c0c41441c903078101003545e40165822045843d80510401130841c0740c0421038001607034501460149010345c07540c442100d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 890177913 1250 890176663 890176667
    0x2041512020409020c010903030c03180305181210140f04030c050c03010c0509040b1e090a14070c11010804020306190914030705070b030402090a0207030507021f09240807 75
    0x2c82c0a42840f080070340d505c291100d40d85000e40030000c0124000303031810301782070714451282c07052501101c0149445c41c404280340e10210780070340188c2001004110b400280c154181e55010303400d0f001d1002d074400707000d0340c0d441080c01d4400c440c03590019000401c420300402a086641c5a582c0d0b41c440d601d0300b0110b445504500300280307440544400650158a000004115103822001816403550111428081111054140b00b0070b99181805c0c1050007012242e5400180342c08410300f68400481c0900240314501a40c0d4005050b00903502503012a605908820510040042a581141081c240344280d4107080c5c0c0802e69604005050128600c0952101788101c042504030440319a0010b01c0b082d10702d0286c80c1440c2c0c0340d03030101d907080702c0c00d215018001450206910a40e8842e0740c0040001546d5641c0020320300c007039400003000700c04104040104070700580e182c1040c040e5504200004159094030700402421032100c3c0d42000c070315407042c2049040c2290b6000e042c0750041c0407a26118116442d24402 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 890179163 1250 890177913 890177917
    0x90b0301060c0818220f1e1d060408180402030f0a05090c060408060f06030f0c010c020f0d0f0b0618041e2a1403060412050405100908010f0204151202 66
    0x1225510405403140451a8101002d61013540b00140c05c040209045080980c0100e8038016420380c40070407032a100c3c8030820040d03881b11007080030140e07c2a503020907655101c0c1c20090111400c9070410004107080348850b02c0700d0310b0541e1100007038408500d1801e11048690750b015000300840460350325100020116501880040003083c8040c0c0015100c0d512410410344903030084a05032001090400020040d02c4d00141d140084604c04001d080c9101d4001c0044403049840002aa00b080150f1790440d42a1600282521a0b5005103468400312440e840c05045414000d401c039486958450b9040d807080101081d9140c003c0d502400e00f0000701c0c456409103028203038a820240c822400d10860340c40d0200c2c6d49401c4105458220714820b04661601c000151003411800655015406140010001991041c924240004505015041c6a0f4810010314950189248000007404120040242120034003500f0002e400d15a002d50801d402e08121801c0030303d05101700e03401c216540000d188609403640c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 890180413 1250 890179163 890179207
    0xc061e060303020606030613030504090203071808030a0e09061309020a0e0f040b010614030703020a02070b0d091a0c071217040303090b061f050f0c0f0d090b0301060c08 74
    0x14051041030703070301d060281d142d0340100c2e4458000c0c0586070004441104200f5100401c41d85503c070306040c0f03420104a140250002000c000520044031101c0300c0130030f0b8a4030881d008180c1d40004617501e84144400a010366104c00810713011b00444c0d4140700e03c0d5610f0007070710011508a040c3c0011100d13614000207501100130341c403051540c0c0f0a0703420710012651242545120301c1c022030080c2080e90382d540c402c4a0120f000c51188035903403024008203007018030a40003000d00380703043c1c8100c40990352107075060700346640240380e02e680080c4c1d80e078111010414010514000b2061040c40c60b02e0a18140001100d9031003599801040f0112b800c1d03070f1614030f60260f200c030081044e119282414524092034058000c0c2101d8400b40c1c0d210440341c0000e030580ca00342001805603c0340c1c02c0c01c803a9002c0c035528144c41d01c3c2c02c0203d09041503c1c0900c402e403102c203800c200307030b03503801d002d0701d00074043e9004800010b1b00040300c40d0070208055008000500c2026000350307403407030601e0341b016440d40d40d05010a640103070351101c05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 890181663 1250 890180413 890180471
    0x906020409051536040f0b09010e0c0301150303050c03070f05010507120207030e011d060d02182e0302120906012607120201031b0c031b02010c06 64
    0xb038240802807004044401d04031000350380043e90f522242189850220516140300b610845403ca2071405024424805410600c103c0c00081010002d5440b1554640c0c00c0360403a034140c1d034030031464012890402040e0308980b0190300070000c03d402440c0030100c030b0007903000280a00ca800100140052800c200f00d60405411082a4400000324039005010f40800d8440c4000175001178401408403d151003281d4100380e260f00d030b80d00b119400c50010f507410490001056100f0300051040c0c00c1036280d050003440c11110703600c401a562001b0710180804007a904a25500824400220509401541a07203401c0024400d001c500705950545003100684140d05840c42016510710a01001040004000d81a107118a09504860742e000c96041e40f02104c01c1c0c600d2205904c0100c0c2080210030207203081c5003150040c5000305500864450110843d175601c46d40c100040d602d079540106040d4000b10803a000000210b4441c9070880c2a0002018001041c4010382100d81d1100180c0b4100040040400781c50810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 890182913 1250 890181663 890181671
    0xa05010b120c06280509031501060804021011190212032d070609060b0109090e19061407021c020307080307031a03100b0f09060a03080a05070c0b0c1e030a030906020409 74
    0x50400100031ba004041018040d1180144642c1181b0366840510705070380701655409078035a6a902000410b000218241c418001c111102c1c0280080500407107a48040c09425007a65140c1031052180101c203d010480b5540c1060040d410f4103505142d0340c24400300b030700d115003581010700f030040041c41c4030b2000010811440d010701c8000700301264028048a6400b41c841e41d0696079641d17400401e94800041c0f18401c4d412410081129802e00a031000b40300780584000030f000c685040580200310816540f02015a0001d00600ea1a0310481d03203161503054148065410031f10180d96800440c00084d112105040e2540441c40422800820442d502e1500404840154000103000700c01031a852450038000c0400d50102c807040d00780001c0d0301e405640b014011801280c0740d40c60341180f64000c000d440040182c2000f04001040001e951600940551140c41e0368451100b00303034034904440106038641544071012107541c3d03042c0c04001e854105c401c5040109140845140483c0284101c1e040300c1041464 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 890184163 1250 890182913 890182987
    0x3030a03060e150f060a0c080d02070b0c070503040303030506030f060406050601030e070f09021309020310090b041a011206030602040e06030f19110607140a05010b120c06 75
    0x31580080e022500d10b000e0003036075500c60404081ca0180c86002c880d0300000700b2440c618032400c0100040460030f80758038203a40d0100255035148d603503500c0320241d02c0c2075640114801c028415020501d44d044552517010714500a40c036500e00361a40618071002d401c1c10755500c00180d45840030b0204490b54020790342a5000ca151515041b0010a82550220f0000e440c01d21154165100000c880707080c0d4000205200304030b45495580c402079071080100d00c001600c0060001400c15160016502400030b074600d080949040c04501c0040303c0303190300031510803070074510000b00c018000d4082986019080ca012440f25112410240141460b07900091040744000340008050400102c00e90040d5001c41c160b6402044113883c8907a600300c4154110000c030384008042000811444030200c2090002d08058144506503c2c0c02d480504001200c1c4c0468200301251700400900384a58408498120760711030300c160749884000d596110089a0501030500018903c14030718401104c9118003048502d48111414 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 890185413 1250 890184163 890184167
    0x70804080d090f0b070201050403060c03060b070501050f06040209060d050702010b03030d1a01091809061e051b0f07060e0f12040e0106091424031e010f0302031e0c03030a 75
    0x1014481e0758642d43c002503000c1820300c8a1000c0743e60107a016074980e4105815900e0340e100505200d071590302815968000003807080e82020240c00100d00038000081c0b54036203052b04460703181c001083c541c491441004100250740c0d45500351b500240d00e100c0e002526a450020503801049200009541440007085120800540340c00c000713941c4d0a411303641080c0071050300054070094010b0007155034850900c030380943d01d410300da4003980e03203540502c00c0411400c0f03d00700310001804070b18042c1e10340c00391035408000c40a404482c00c2800054084143d9180c0500824550801d0013095801400c49403154440703a5140b0081055140303814150b4240c80c070610300900040c8065000c2d2142124060400c000058101d00615441040352038840324009a0090a020080e0035020300140340d441c0345540280e1682c0b82e001001942c0310344000c08034400e843d2510902c100c040c0d00c0c168007004251030240014001a28081075039105c9254005117503402080d00c007641c90912185000f50368140c03102050b400e01142e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 890186663 1250 890185413 890185427
    0x70503070b0a0309261e030c072006040603060503061030080307051207020303010303080609180706030b18220f120f030b01020609250b0c0c0909031e070804080d 71
    0x4030300e006c8107402000700d289885140c041100c0740d900d008003c0c030184012860700814a448054040e040c000000c204000141c4590050342122000a9440c241400b65080403c01940c21803030781d00700d011500d803500283c1d081200c100103103502140c20020700f0140d040c03441100c004515074440c2c052500e9141c074440c02043c5410031542c20700c403200301a0200b480c3e140003000322816240c240e52446e00e00e40e102014010083d4001d040b0000c6110450320307403226050107000c441c0c040d15040c2d5010450f00d03808420003651030604000c41196581800900940288400c900e01d441803005161224100f074609094540201003440502888602003002c0c03c1680e0080f03e0310711110351a04d0030844841840700481c0d86403012203982c0240d03800400501c480e060401d10550381d480b41c01100c4c00c26580c030303020310100c113400c0440c0040c42d0340d008082c003c440d0b1800c04841c985c801d01078401076003440c2d046402180410744d10305a264143c800000d41c48240304000302140c0c050620081100c0502607110302c014818 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 890187913 1250 890186663 890186677
    0x110708070203070b070c0303050a1b030306050306091219020106050604090507081b0a0804140115030b0718060509060403060207150606090b0d150305060f09070503070b0a030926 78
    0xe0040c0f60000c80e4201c411420f0310481c0790452244000c0f9415550f0030740303031980718400c0f074030a12a40ba06d5852003002c105160840350b034429a07010030214a004145841d080c0007a0102245030040d00340400007051880a443e0070181d48402032a02c0084200103900412180c1c11107030300514005804540410b07681c000d14041d0465983c0c2810784d030340e07040f05c451b0900010b00c0348040385030040082111462251600d1600107024001d0f441017450452002030840e455003d882d04405d191640801c103004100c54207076404911420a86100504402283c001160310b01500080c8007010030704820f43d0701ca030800c1c2c801440e0321400440d51008070f03013040c0540c0800d0700d8501241c0c504041022801c14410000d01080328412000c40d800c00c0703c90300e03102c0f005e0400c6400d441410b00394844000b0114a040144601500c070702c0550407000d0402030881810003200d130f0040b5010380e1100c40204000c000ba60202c4003a10b17820326000444514602d4510710000700c41c2d0000d2810150350140740d0301c0d038800e03500400e10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 890189163 1250 890187913 890187919
    0x50c0309010305150409260f040b0d0f050727030302061b0d020a03050402030120160609051c081501080115021504140d140301050d0507080a0b0105010f0c170c011107080702 76
    0x1c1904407c80d803031541d1086982200100805200c100042c07801c05001d01010a0402c40200d01c040040f02000200c4904883c40760000300071030b0b038040e000c4804480441403003e00c5492805017504507140a1340e0b4400140400000b50150503040c15200000780950711038051005c1c0943d40c4002003034004010b444260742c182d100e5440d005e9880084015101d0a6400310101d201081c00c107400c20001d200d40050140003038403010f0301d4041c500001071092048501c01c58016040000c206803002c402044510020700351011038440300307090b901a0b0707040b100c80e40c1160049201225000c190090407810071070b00c11040c0044810300d5003800200600c04103208603d90350700003220072540002004440c0f80c40c1c000a01ca20803e000c0006002500f0801c00c0341590a0141040700d5416541e02081d80c81c1c00140002587d100c850b410051009d0340c0e02581c1000c501620380b4004c88640001c1d20340010425488012090503c030004010702500029000408101080505291101c013181814040d5920070380080744 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 890190413 1250 890189163 890189213
    0x703050c090f0709060f02030c01020c0601030b010b030106080402040203040606170f2a1306030b0f060306010e15101b0b180102130b160804080a060606050c0309010305150409 77
    0x20801d002c040125114040541c2c4140d409072403c2c0041d1750320000c0e15a4101140001c00c000e40660303c09000074682e004141c40140840c0d0314606040d8149841a0007078900807004000400c01e41b6448681c003034001341c04550041e5a5103681c5412030040c90298003107114030a24042c0390303114a4002c035881c040c0045003026180c00600480a42d0002d82200e8181c2c10000c02c071449030446030a20001200400101140005416480380c658407049a8110b031103071100040a0100a07a034101403002c10b0041c28841034500207030501c060003940d0703000c21600f443d010721500ca2285942910442071480d10105000c00c9260080d01c0e8140003840304412142e800540c5041741403008166414801c55a04601480114031920704150a80100f03502a08454000480042184000c107880c00d0051000b461018010120303200300e0b01c1c14a00340d841a90240c41402010710481c8070a81d008001c4400e10304003460300203042d90f1144000c0c00c201c08030407806078015203012921010402d641071217102e25004811429 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 890191663 1250 890190413 890190421
    0xe1e0f040b01090b0904060803030c250309120f0b0c210c070b0702030d23090d140903070305010e210a09061220091c020607030516050703050c09 64
    0x599403502403650004000a8081004e540301c003004d05990381c802040811025500c500d035071b14542098440c490386000c001400c1c0820b660140841684450700c0c902c100e1030701e100345c6000c1e00c0d824980c420381d096150092040b8003081280e85400001c50790041900341d10742000c101c04101c2c1c0d001005c1d40c03c0704d00d5007100c0715006801c0c6041c0d210311444035002c0316444c2c510319913142d0044640c040c04850641c44180644180d45280b8000d110344d014407904640c0c01254044801005400083c04c0000c03140c01141e42c3c50340c1903034481058003d60307031880c074a03603550706000c00403c1c40c048643d44054541c0d4a406000e030814040407031030120115007582c20000c007002d0100c01c0c001c2c40c8215003460012075186403041080c0c0b030050545410080002c8400503d41090b03031003241d00e031010a889180351000010b20140f0514144a06815401110034080c019825960200b0868481c82101805021000c503406001180d0102a081d00c0396021040da20300b6642ca1819640c0c0b0034040042034407440c070400000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 890192913 1250 890191663 890191669
    0xc0607050a03110909150604080708060714031302040209010207182406020c01080a1d0d0f0e061209010b0a0b04050102070510020d08060a050d0b01090608031c020a0e1e0f 75
    0x203100700b218010100011078440740030664510721b610b40d0054011109010001c2c03091001e00103c002024144080c21003850480c0c4020412040c800c0842e184203024820300200d00541c2d150810090350690700165602c000c40010307450100030781d10000f0002c0030307051800c0202070a03400019041d0354590310003082940d0211b00c064051b14501403000168404000301985610850303100c6e8103d00c10010008601c0101c000c40654811201c2d103241250340a07181118a046d400b46180300244404e142042c1c48e200307030307000198680c07051092200d800d60000e80030407400c24081d4005039269400504c0c011000e6610071110000303411910465000d401070303c00002d2581064044040c01503141c0d030280145901c00041514031110241c20103800041c003400c0410706481d90581d05000030b01420860820b5850300240300c054584a402010702a001849a03102860325a13405800341c401c0001c000d81c03650300140c0101c07030141da0894416070005003054803c050000009000c0c440c0402520507000f12581c10041c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 890194163 1250 890192913 890192917
    0x14060406020a1e080309010207050f0c03030901051803010c020a060b090402060904150306020a0e04061d0c1b01090f0203010b040501181802090412020d21020a050c0607050a0311 78
    0x144005600150003500000d40181902000c040b644881115100c24036103542c4d10507003007118802150780d80000c60000b404020460b0311181f0009074010b100020f2000046a100c0c0100702d00c15040c80b001145440c406100740c1c1500301c51481c0074008102e0704448200c000c0d65410700385001d03542940780408400e854240842110701c0ba980103059545803a00c000103000061190440011491140d007401100080c1980001e00c600e0f03071b0702c0d82c0c1c000002255400700011900c42e035000c0b403040f10410785100d0444540440c071540c03050303401c40c88540b120185075400413042040203080010b5441c00303101000b004800b03c01035107030b2070081e8000c106501c0c0e80c40c28441151420f0180c4a4005070350070305044015042d81040c508065040b0b10402d0310308240d0b012a92205c006d4070111004c3c0103000b07120b000184d04001c001000c840034034003ca200c0e0f523520f400910400124148200082c0c00255800083c0d010701e046510440342c074401c5502c40e24016200611507005000040e001070304020a1a030303484c80b030f00d003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 890195413 1250 890194163 890194169
    0x1061101050f010b090d02090a0b030f0601050f09270604030e0618060d02070f05010c0e060a0f0c080705100e0f030f0301050415080a080406030b010c03020a0f0525140604 75
    0x18030382d480d43e400c1804c0a207280d000025000d0b8000002c00082006071202c0c071340c40b030150540c40000704038400c51008160130200041c940030340e150701c1000100030303036580c0f8000a80c110340143c60075130035901c03080c1581d880c200c034240c0040d2804200401c66003c00c0c1e00065840d1049000c1d80e40e143c0c8000e2060b003001620302c528604110741c4803115400c00d10f01e141c032000030210f505010100524208040c1d4403441c1001250006895596403041c09444454000c98004103843c8203c403c1c0b8501448100c02501c11101650300a08206047c190f810420410400701c541080e00301040b101040d010400d0a0007a00c940b034044e001600035050440301ca00c2000064681a9003d0001141183e00349818003000b00229039490012050880002600010600c9184007180c001c020040d5034a00345400501a5402030030124104614410343c2404290f001c20107907406684801000b84960050404502e401e85079082c41080b0100d007116600700141c0585080704031100c06254604003103c0c0d000f0800c4500883c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 890196663 1250 890195413 890195431
    0x50405010605120a0f09262d041212182603070602040b0a27120501091b030218010308031602030d18061401060909090204140f0106110105 61
    0x4844400810303000790302c3d00da01c000b90100c0010030142c030101803010303200103100660340300091003072815021552030400620903ca255416103080981c288112801c0001218014004c0a04c07203580f8100980c02d04030740c0103011000380c1030a4a00c0c0381c1000602d4500d181400c0010071000b8040442c0303555040e4051341101c5648012104540019042c20a109a03030010b48030540030420004d0001892440900040c04010403c2a19001590805400a0134003003400c0b51010507a0040b140c48101c034030303005098600c1c00044a2030030006291041c0581099500103010002e070600e2502c1481c66280c092044a0088441004c0c4050340f203441c4003294002e000140880004100041e5111003801c41c040a082c00e52044038030f041d400c0c107420f0040b5020b4088107201000580b01000a1090b07a002d0030141d40e441b80a000415458104040d00c2980944203000c0310790340b20503540040d075450754020041c10490040e003a8861074a2240584003007001d0140101150099010b05a11401480340501c190700711 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 890197913 1250 890196663 890196667
    0x7030b0f1803030a1505130501080607030902130e10060b030907050d050309090408040803040b12182d0718050c040e06010e040f0f0e010e15010e040f021002030c07050405010605 78
    0x10b0041c0d8030103850700103200c054814480000003219155060b07d505186003d16002645506000c0c04509040c405450300e0f0800d403c01c0080005070f540e06065402203070706880d0006010894880a40c186007000c84400c084601d8440002142446a4004d6109003060826203275030a480b07004104082240f03c83c058036903402840500c280d4201081d0445c0c1140c024801c103400c1690b50f9880601d103a1150b01711466004001c22040b40d000b00b034a00064210020742c11280c01441d081c0c08107640c403107800c4142d03c1c480381c0803001b098503106249000c3c0041c0d5100360a40b8030250326404c42c034241d80d04612829240a107004c0005811505540c00da40c1a501101d454150a803641d04c0111000924400f000780d02030f0f0303607c4200042500c280f159054600ca8000702040034880b1303007110781c02c441c0d0b44118006103400030608104403506030051075040d60358040c9003103d10380b654103001604042b1010002e411040e00380e0752280d0550000040c00b4905a078400712028240c0319403d00c01910401c0c41900042241 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 890199163 1250 890197913 890197921
    0x130801050a11030a050405071e080615062704060648060b09040b060a0e070e06160506130b06150403300509120105010e0105061b07030b0f180303 64
    0x130507000360390428003500c12190880d480300102542418002606418401aa00304010140f03060021550100c0000e24800050000e540441c4483c032036440b5030034104031080c5074108030f520f0101c0e000ca02510050420030150351500c5000e0310000b0255041c0402813130750b00303500314440160070030003440402403030002150408103d0001d84810050f14112046525025101c1580c4c8480c80c00510840c01070b140a0914140481444030f20804d640100800424035000c00c40d8a83c0c0241581c10b425905841269440b50b1180f0841000c55410000800c176001b818140041c0c0310206000a001034040c0036545519150071041201d1108900920002001c090008001280c0c800200f11940c07095044882c100f44150103840c85a0103c1c07040f803d0218401203039540c12405c058a10102d6202400002c00265041040c0c0d181000360522456105800c0000c401604c1c0c4802804107070b200d0303080d0048914494a80c64529003d40e0308640800703003a440030001a0300e040b00954216008804500075504d5500c07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 890200413 1250 890199163 890199181
    0x9090403050f1207030e061005101b080301080d0c0b0601030c0e0d060218030c0a12050a05011103071101021206040e010209150306010f0216060f14130801050a1103 72
    0x4009905000051100d242c0b0807698500504204244040c501c10602d0805009012151002008804c0d41d10190030401501365030100041658070840b16550710041003c001c07500941b20421040d0a100001d0241d020022110080c5044e42c0c541016103110b0540400c01300c1d03000c0105140540440210030104000d07500a5000e0b14820340c1900d05007007080444070204a440da03002034202c4180b580004d8090b406560082444117940007103010348081c010810001c0d0b010000d90060030380011005034540100074081045100e074941c030000920800920180d8020542c0088500c000410004070303110000700c03018421070301158210140d444150b15040240001400c540c04041d540d0740d42006161b00c182d940c1c3d5012000d5601f0a188659a07250900c00100b0300450700c0c2c013000655010402c7c00b04100b05940500e8180c030180d20b05601d003800c04140c2210420b00804255011000018010701201c8a13142c0341da0a6803500002480b142c2c4582e29404101c1c0c60303130804c01c00c1c44c66040c004030394180 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 890201663 1250 890200413 890200429
    0x114030a020a200601050301050612030301171603050c0312190807022419060e07050306180c03041a100303030902060c0102120a0606030b0f0f01110f0a110d02010509 73
    0x1149a1401e41540c00140c0e0b400c525024000f006141e01d98131250040020b85003d0003040d50201007036881ca00500742c0c02009640d607000c180141420b4401c1d8010800c100b500801050a1030340308503545050a17592814a0307032b00d0380d040c9022107001e4010b141c1c001604120f11005c0314400040880317042c00f040388020702141d01d400b0160a90045010b046501d811408221440d040190240104070a0310b0400b4003080d14201c05509812074400d040107010000018201003881d03001a80e03042080d035036034400000a2503500b6403000c15461078150342c24415940c1d002806141306610070000a90341c1c6110501000b100720017100e10460101182c541030000038420740018201e184083c04072402c1601401c045401e90b0040c00003d86140041410800c0c0e006042c00383d10b0060902d03007001c01010720301d0008a40180f415038540340c090011800e202e40ca691150103039a0048030b01509590034980100311554403802695011740700101d0a504406151903c2d4110683d1554161621031412200e481403180013 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 890202913 1250 890201663 890201677
    0xa08210a0225031e18151b0c031b0602060f0603120c100203010b1909060509040e0c04091101030621020d051501090b011b110f0604051206090c0114030a02 68
    0x1400300d20f03d481800c201e00c1a140080c04c945400100ca50b00e01c0310030030304020341e5114050140711400d640b40000d03004000074000300d0540480418105d090b08080c6180c07846540000c0c80c05031385014200d0140c598203030b040c0640303502d5403d5a4903522090034280340c0c01410341c4c103140c1c1074000c44615078500103160020600360320164281d0b22500b942c000391404a8009134450310000a001401001c00e1800b0318024081c0071007402d00303420003414010000c0960140342819400f5903940e0004d440420410011a281c00d8002081880085030900d0321410750404080300e2404617007004004100001040c0030314109204182501c1403c180170b8081113241407a500055540b405040481c1034a204013801c51806015004400300d918000b5030001040b507601000c112040c08100c1030164001500e100d01920108000c803031005890340c8050015103944101e40c840b50313000715607449540100101091035489900c910050790208401c2c54015182041103101c5016018001c100040c3d00b1041a4060820 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 890204163 1250 890202913 890202917
    0x420030c0402070b0609130506060f060405030a030306090f0e2a0a0e0708010e0f2a04092003070c20060a020105041403210402030a08210a022503 64
    0x80d81800c20086000c80c0d100d42c4054904003807903020841c545c1000880540c016038280c0322001030b9015920384948030703140034000621a843d40040315409960340e00aa030050b240041c143c900760812480c028000700388611611041c42d08117000b124007508030f4402c0c921000d0841020f02404400e0902000d203071040d001c4038007401350b03c50348628101c1c0c07905809080500003003280b00401307050031400070b0b24041c4140c0c01111104091000c101c0b400d080141500d1b00b001400d00b070040f1400020060001c140b10000401241c52004a000101c428843d0070030a01c0d684401d0280160021b5a07000c82451b101c220398030801704075164042800109030303081c41020021042000000300c20500009020b9030300141c00080140c0d1103c052100780111203120f4141a0507841c0211b2414410103c40407a041c3d8448040d0000001c3d01c0c005819520140110010a503008685654031494074184504240c1c18007201102145813500094604030f5074030032a00c4101c0c0c266028050507012440120a00d8042101101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 890205413 1250 890204163 890204173
    0x312060307060c08070c080118211e0c120e2704080319020d0c020c0f152802010204080f0105070c080a170c0301050f01140f160f0510060b03042003 65
    0x801c7d1000b84206405200c90340c10380201c80c40c460030038010140c07c2c40910312121017900f0401d407166030010140c1191614203d01c0c030a00074454201611b1042010074081d01840741d448508440341d902c021180780045007101e40384610036602c0d00c0d003006598114610001c80b0045000b080c045180b0344060359201506e200003840380d0b0444003c03541682c02c1510181485910f4207800d03410550180000382c40204d043d2405204480f01e40e0005080720031020f00d81e404400c00003202c1c01c8406000d9450107402c11240350f200005000b44070028004e500038400c00813903000340c2d446440c0006043c0141070207080f050f84d8401c0c0f081c510b80c40d0746403641d02003020803050080d0301201c1e070080c3c40a004218421421055020340713940c90f1005100300e14080c04500e03810400c140d045480403030401000d560a1b42d001c0c0d02e9181d16003408510f07000000405040152401d40114810020041d00050f010b41041038042d06011055540c880544203020540e401400c0c4040b0921821462841034102e403a034200c0181151 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 890206663 1250 890205413 890205419
    0x501030902121c0e06090a0b030907090504121103030f0411041407030902101b15110f0c0c01030b0607110a090f05041e0f0b0916080312060307060c08070c 68
    0x549880b034a98040300f06241d03409103004100742c00c8140d00c034600c0c10070380e11342d0b2a240c864800290600018080c42084650100c040340c1014030401c466405000d2114042180b8101403c044003101c5203040c907880000da1001018020100210589010b0800c00107403a2030764440341e81d80911550f212001c541c00594510710600440b520403003040c0101060380b4000b5072011180140122208200040c1d420311018050300746103100c50200310b0281c0d0380c0065001c1c0c0442401c1e0400f0000d05111100c40340d201c540400e074900c0c42034000c0000d0042d4036480b4110340d116440400150b00351a6280e500c3c0d0f80c0011306001c1138020900c0c556102c00042d400804600319030f13440308110002c4030381c4010510343c555039400c204810428002ca03602c060340305490135188c0350201951804000000107000510424034000842c080800030045020b00d86010192210b0542e1110191070381c070b42203010207107024035110b80880d0305405d02007980300030343d18036949541810900303450b550466481190700301e80d8801104000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 890207913 1250 890206663 890206699
    0x2060c031906180e21130e0c1201120201082d07050d060504022b0209152203050d1b0203030408070e0130060e060702010507021203040b010501030902 66
    0x1d07100c550000003a10070401d14007030071944001e1540e003490340705400e805c04200c4c680950800c46017503e0078055603614070381460180107450754411034080c652101480301c290403e601800024005a0110b138140e0782c0c803c0d030701c1d60110042c80c01a0208404c0004600c01e80005501d02d02c044c00b4a08140024040040710300c02c0c003c030308503407840c005a17000c030307000c510702103e40100402424112001d60a1101c04101806010b00c0c24076540c041c600486000009402c0310b406980520308000c00c6081031591384130107a815640114084900d140c054010903001504e01c080800c01e40390000d00030200000c5100e01030341c01070510b052002440b1101180100180e40410062000d400c0e028003400f1614541201800f107030798103800c40f2202c10b4440400414000c0c2c6c080d803c0d81d0340301400e410b9041c4043ca83c10300000078806040000224020202001520b0350150051030081143da4210b0b04408a0b428180400c1e010588005007202c1c41d11004200c10343c440d80128421900080a88203841159010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 890209163 1250 890207913 890207921
    0x6121b15090d030207050123090f030a050a06090b0c0a0807050912070308041514090609041e060e13211b2109030b04060f060f0f08011b02060c0319 65
    0x480041c1e02c801070034001540c2c4407010f28200c9280c030302301c101e1031407480c0d155075014000c400301140140c01140150010b55401c11200e05405e400100b80c1e485200c00d41008406040030601c2035540720f0441020030b1801086d40308a035055000d90362400310540390b04c00e0071a404d6112400700c5030b10000c244800c05a020060200318011413086501d0b40d55503190a15541c4405560b446c00d0013030100e118458061007102c1d00881e9140802215881d40e2090359034009801000345000400c0300040481800b40003054581c07203035094483d0042c4040c1203984070703c140800106004d1000780340c040750f80340301c1c4800c0c05612103101c01c0c0e100310f040c00070f00c0303840880110004011510064681481041d000b40c241c1c5401145481541c3c800d140418480f811602c401018050242000740742951b204c049aa840b00603611510203030403011816095195224641e1003030000781c6c001c1110301d510f8905c011407000d045100041c004400c50700a001c01e541c60400b090b90a0300001d00e41100d02a10044c80070b003501143c85 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 890210413 1250 890209163 890209189
    0x1306050a0b120a0e06191d010b1203031003020d060b0d030513060806090411030a050304120b0f0f0f130812090606010903030e0613050d050606121b1509 67
    0x1000e034440122079981ca6100c0c1024000040b03151800c1e00c0d07101d200c4400700d9031641c44105a040101001c103031b41c000354001d010062496150b401700380d03a001c10055040d001000c004804881e903030b00d408094600d0030340300e21040d02c280d24035460302441080141000d40310721414600031240010101c080070080b03003082d000c3c0d9208400085d0b0000300c0050000440a00313502415061504208516050b00403544a940140c80504050815114401559001c00c010242c4503840002d40c0e48803941c03202104081c2a1003c0d0807502030b140240002e00086071034540611a11a2010300c540c02c2d114099104003549000d000da0307400d101c01c2e03c0400086000c990003800780003460305a0810300c1c54a180e02508000002d4101410007c140d202000481e51040c40c64010300e80458419541e032803100d6040203007240c00da0066070003203a10762a00f000d0280200e001c40c4070b2902603900c0c0c1000018180c400b40c0312050541030300c190540790794414409042c0243c0000c014110303c1151303854640c1c07400000f242d41e08649 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 890211663 1250 890210413 890210429
    0x6040e060a14010c0204020c0f0d08090f030310030803040c0918030908150411011106040b07022b051b1f1a0f10090e09010504020f060a0c021306050a 66
    0x400c0c0400340c20809200001841d503000440200e058010000302228100750019109680221340e42072605014441e00400007803c1c3c00710355003008111000b0b4100c18044804007158018a005944004c002000f00c0707100d902c0401064034018110343c1d5519003900003401c02d91307022949081c04501004248175500b80e15841000d0018030a5051500815400d00d980001400342c0044000055186000403440d400c19401103685200e80102001210121f070031100404503071140c83c2c1440188504081d445014010603030070b0b15810042c140402100b418001c120002c1c05140382001d0440601c900041c010080c149000c0142500d141a1060b00d003c180d0282c070340e840c65a549034030943e203207144600400d403981c03046418050303003140e40040d200800d90701c10940501030031510000081c0c0700d0007821004e40b408c40d000c108582045c1c003006008040480382280141e11411072240a403800d50700b501c40403402c07562040c178000103940c24442041400c1c246240c42d030751031780350115aa81da01c540c0e0700d014103029 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 890212913 1250 890211663 890211689
    0xe19050a0c1d010234030311010b0f0d0b04050f0a081803070b070809150a0201140718030f050a0605010305330109020c0a06020c010b010e040608070312170c2a1011090604 75
    0x9600c0340340c01c44400e40c100c14031403c0700b1607042c0cbd42521034500d01d40c0109d0300026402c140c0d03030316814001d0a1040f1501c442d55035000d01d84617203003003018a0001c3e105098480300a50214009101859a01c80d0140101604144107002e44000580b102000b0603044c800940403100348101d540c07804100e90020888080540d45a49084a410361074201d500e60044803442c0c4601241c80d8040301c500054010700000e0840c1a00c143d60700d09004041220034800303503100c24204025a501d0618680303441a80c070303481000710382000c480301d03a807e031001004403122080c3c00f102c3c032580d2030599250b009500000042c10b69014130b44060012694520182a002180340000708058120000040c603000c2e0b00c240c168482c5107021401e0004100010b010b005480d48108100b0400a6900040c1e5a058407146c01d150414404010440c03641c2012028102403841c58a0025244452000080c0e20520309405400360b075004003900001e0b42e4482d0452154444050201860420b103a030105249174080c2d0014441074140d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 890214163 1250 890212913 890212937
    0x2100215010b21010f15090e180601080114011202010c050d050d1808030a050c070b0a0f050702031e210129070c0e19050a0c1d0102340303 61
    0x20389814030400282c2c1c03c25400640d030400d4140ca5040c5264000c2e00c0e068030031040800e0205003c2c000c040040c114107102c4c0c0000d460258807000e02512000662a01c50003884000585528140150000070404d043e80070342036030800404902d4001448405d904101c041141140801c04c103104030303040b40c50180e489980c2c0e00100100c0c00190b0700c18510180c04000d0a0042c0c5003ca42e99030140c03500b0075443c10020a450300c41d299134141c240604a0301501100c540c100f4059203145030b520000322003a000300700b0320666507444001e0f40c803805508020028012104050b180340c000090041280c25402005200c601040400420011000340c2100001c0c5000402020402c24420412201d009410580360f03d040d01e95658407501c180c0a1050f1010304986c003000c0380c51401b020038589902c20000e4800c02051900d01c00c0c0710050316241540c1d0f0045052000045040ea80e0030900c105100d506800034211000c0f0303420504410045218500b090403c040324030b5840c0703a00c40e850607000314001e03a1a0344e21104 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 890215413 1250 890214163 890214187
    0x110a0206010501090614030412090506040f090f06050603041203020c01140f0108011104060c11040f090209160507150e0f0601030516140d0f060c0914090105060702100215010b 77
    0x80c903402020074050300c903080703911506c4407400f10390707001d9884400e4040011443e21305445488651700182e0b4843e10106000ca07044450482000c00c484c10700400f440585408032141040300c1090180c2d1ba00301e2410000503000c14541c182c41c0000040a290040c94640349083d11800c690303003401c958107040200414800428000384940b80504042c0c4003c1013030388076600410b8224400ca100740c909001c1000025002d11028004038610000e0140003405040070b00301d0050000c0c02018400ca206001c0d850100d2201c10418803410040d003d50f4580620700291900c0b0103c9010080010b0a03849440d64604950140d06001501d180c0c85803070300401e01541140b4002c1e0030090800e4240c0c102070100a001c004000500d100f60403081401d03606004e101d00c0317a007080c0108209034113000e0b185500340607092054580c40300c001402c0714548804032001d4400c402c1003201d03840081c0b09455212005001c0c880152501c1d1028a42e41201d1740100d54100e15000c0f030b61941000c01b6807007100e10700008541503003142 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 890216663 1250 890215413 890215427
    0xf0507080c0a0c1413020906040e15091005030d18121b030b061804020904021c0c0602060a270209130b011202040516020703031d040e0d09120f1104110a0206010501 72
    0x1a0985c040d030801703084002042c0b17240120304c54016240380c03d13400319072901c1e0301180522030400045c056081034541503401442c445042d01c5494020312235440030900c850f1042000c1802d0f01160300c0d035026400e1400300ea00d04a0300b683c202c107035403100301000b9400640c646510b11030019803041c0800c0c00c162429108202c4040f00341140c01034503d00110030400140d642007103d5a01540c126107202d400c404a54424880f5909014020b21003801503d02140e451b400241040c85216100d2060080903192081d1403460728017801515111090100301e2030040c5851100d981d400841282c1014011140d0340b10340340005000e03800040314544910781207040d0309003030003861350182c8106c0c9404e40d03c6c0689a0021340e02d481d5480007501308902400441e1005100c58841401000c00a10500c00e411000e41d00c00c0d11a2050300b50031002c189a05400101c04404440c000c00319a08024645010000340c6c441c0c400e682e944c0000654041e80d44c12626900c421100090503418203144d0003054598107100001d890300c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 890217913 1250 890216663 890216689
    0x3110c03040305281106030403030b060309060105090105030114220c060c03180b0306221416020c0a090b0a05060a0c060506030304180e0a02100f030506010f0507080c0a0c14 76
    0x1201e1401071513404964400070000000406440107692907940342011801001e5940c0d101c1c2c0e1068001081c050031280004805050356401c8070b4014940e40d80c0c4003018200d41200314100310b40f141480004588908100382c402c03566607404243d40b000c40c51030361484002c0000c2c0c1c0100c00880c42c80d5450400f4140c0c04130030403007104d90700e01d600c1050b907050514150650000401c194403c00c6684072604141d04003001500b42000600d20910805090042114021030121303408102034104c50b00141c030321031001505203d0f074280030300300072001400c000040380500780f0000c070203421503d5020005480d0b140d0100400c0140016035450300d480c402468240c050314805014140300c1d92040c001400482c40501000340034400c414800101c5040c0d81da2031034141502104065803000c4040304403074842d5008000703881c800607541e070100100d60301c203001559042c2c800f00c0c003440010000d001c003c0c002501c900042c406810003000301c1e072004070079569411812250b0f4110040e911480800905141800b905069075 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 890219163 1250 890217913 890217973
    0xd0608010c091e08071710150e1e07080603010b010315050f0f06070b060a060c0503030601050304260a0906140d0c05160b01050f0f090703110c03040305 67
    0x14003020341e40200b07503001c0c41c007070640f42c031010909107041512400382490081c2424030540da986039550038400181a508610702041d805070100e8410203010502c00c0039803503038594880c442c24900301954044c1100009000c6050524140d0307400303007500303481c3c00181e128003042c0d03075128407502d4402d05140c00c0d596000c0126050508040007040c4210010f0b204006692082d41d81c270341502404400600f040c4001c89083e500a84000f490400388000f080210344290020b503440404540d41d003804031001d031405034021740f154009002107803142d0710070f4005507001030240c8002200e41100c0000344c0d007642441100340100f0f005c0002c01c0480e45420400c030070024070441c1481012021180f9210b0407078450484100c8005580d014030f80305c103070b0180c0103880010201c2c0004440c801d0092421350764260080c01014441c55070940c00c44080c1c41c1901d003620451902030204105610b03207540980152007070054041060006101c4003082d200c00700040c00055005400524240d540c80001d45e419080c0380c00030140c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 890220413 1250 890219163 890219171
    0x50417180a09230703090c030f0303050c0403050307080f0d1e11040806010b0c030c100213120f120221040e1609170712080309060601030c2a0b0c0d060801 68
    0x480f0900708500e40c0b81d43c1e124603903101541c2d40030f0110010100e45030003c10f030700525034020081c407114082e180e1549100b51000c2025859482082c03030395004034400108154410411075000415403406084429880c406403400d20904045140503902820600c3d813803031407020303110042a11940544041c1e00d1074015024501400d2050258481c581400344940d08100040c2e03811480f801001141c3d65820420150740656407046000c030042d51102860b80c803800000040814021801818094082e5000c03604204e0034029590f5084441c0241aa24040d40254140108040b08400803080c8403000214007903034950034603141c0e02c920b12014103a0110201c3c9519103244042c1c000445200b0303503400600d44001805078035144d40ca0101c607034000c0989000a06400d8041042000185008074071545c1921001e0303641c10011002c1320396062040001030040c40b100301d19205615094a003607142c01415054150352611445001101903c0000da100d000141d0950782400e18410720000d440c00c040244 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 890221663 1250 890220413 890220431
    0x130b220f0507030c18081e120c03130e070c0b09010608100b04050a0501050d14010b031014070206150f040b032401060e10120213030c0602010c1103030a050417180a09 73
    0x195641f41114204655101c002d1444207002c004006602d0526045510349544049040d02140c59401151084850a00e8100d001c15400c031000c9800d4401c003d1030780d0310309010301640c803004408a0050141a115582c80401180c6004c00f0700858100e68142c190100d446402401403004841005040f43c00c0c0700e18180060005070f998030307982010303540c00ca42e41c140d041050050081c010b0885061899142c41900e4a66425a00c5604143d40da80000d0464060b40da0346c2480c1030340c940c0e004440340c00310201144000d00241c50314203a0340d03940c09005800014442c800c1d0001c00c3c034200d40031055581c0383c0414485609000c1c802500d80307001d0f08091804212a290b010007240c000203520300c43c5024061012510300700c82240380d050351510100340c500f0322141c82e5207080040000c2d01e42d01812005500b01200f200b4617602900804449500c03210041d4503555550588200500002d40215801e0100030300c104c08003440400074004505d400c132520740c484108441080551405035028010742400e1a4520b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 890222913 1250 890221663 890221679
    0x10e032502060405060919080a0c08031903020c030c160305070617070e150a090326090d020409150c09060c033e0c130b220f0507030c18 60
    0x14070120b82c820350740e160306e501524002440b400442c1c1c0040750300d5540f000002460700b01c00141e5048050089113411041e82d29016000d40383e00c900d0040b42d0001709140600305406120754000e202501046090fa030810041c002403a0400d42c002d000b441c014442030005100b0300c04240b007900000c06007810140b40c4140d13a190081d590150003072010b420b00c04032004003045a00c030107000322550349543c440341c0d5440d0341c1144050030303c00c8240401e6680c41d62040110041c0c0c07074041031044a00324416445410440d05008003c1000ca1241c800c80e0007503228411034002410f8040c6c0c810110103042400b01d0090f0302c0701001414100da0382c1c011010481d0040401d8040fa40020806a00110f00c0c001e103003112503400e55000c44020a41803e043d1074810912074800c00202092081544400f1904502c02c3c410f6208010251102d01071510317172018101c52425500104040043d0102840d000701180035410403800d4402c844048078004003090312840b140110340e07400804040300c1542523042c404002d040100c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 890224163 1250 890222913 890222917
    0xc12020c010c060b04110403051b012307080f030415241202150d020903070e27010f06030b010302040f110a0509060903070311130501031205030612010e03250206 71
    0x1e03100303030b07613821800085031900d400082c1001d140e8040103580e1652450f2079942c450f80007a0b80300691581041c480081c0d8815071619106403101080d03111a405022420011640110740c202c40c00d11080202244860104000d10301c528090a205d5100701c40014004064a4051100584a0780b0010b081e026050000c104841990941200a00c811080d44041802d410306480800d21440c2c000c950f030010110117400502c180348040d000e071004180c1c0d030b1501e08980a02500d82d50500d1a0f51400342d04c9131040d21032250032304a8400e0000c180a83c4440040c4101c4a80342c00c240d030a42030f504010b00540c00e05000f444d030541c015000801c0000080050a0041d018024018042040c0025003840c1b1340d440f5400c0d01c0341180f00600381d81c210303030f5a0f14045001822054081e0301500b0700b10400d00503202d542c0702e40340c100c0c0c0d00000d0042c9000500901181c03950b000074140307603201d910101c0b00c070b1348000f09104020221130a0401585d864031200c00c900d460362823100405c1c1010404412100050b210441 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 890225413 1250 890224163 890224187
    0x20f061b0702010e03070b03010f0503070b0a2f06180f0a030513091e0b060705060a090c08060f180106050105041806030206030a050f0a02120414070b0a0c12020c01 72
    0x214a41c0c950341c0510040302d8009019403455858862450003064800c807141c0114102c8280d06401e40c8502e030f0352028503449401500c90345250301000d000710f160325806103c000b1110304481e1441300c0007884a401c4070007603100d8041502e00d00c2e8000000c01070081d00b20040b02280a441383c00420301c0c1c00c41420321300daa5515440c001403c02401003a80701c007103440e0740703036201c003401460f081841340c2c6032a04179a08118004601e820102801c01c2c100445505241c0e00711260a508107000d800c0c290b440d202c8240142000507012203007031806d2032002605150611a0318021140072903828554280582d40a0030b00038982c0c1400303020b9140c80c0e001c000c5680c018044500310b6100031840d481004a0458400082c1038541c00650402c600000b04410081268095031051120346950000c6441d184025000ca0161002c03000759088154007113408520a0101d039100b1407000011a262075864024800d49a040020342202152861801604006042c80d12001240b95440248002500a0002082c0d01e040003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 890226663 1250 890225413 890225461
    0x507091a010f1b03020c0f060306060f0310030b0408120c0405030706031e090b0f13080306010c0615090905190c180207080f211501050d0f0c0f020f06 66
    0x1101c046103e0103021400c01048220319000007103122400c0181d11020054907440c4580178000e03468030b40e441c0c020283c1c0d004000140109040c8501c009120007103034409040480001030080f00003001540c2d60031850303c03441c460a03210392a1041d02c0e000211030705010b408042079220a110a1065417000601c18045480918004c540c2c64403628a28031a0391948105500c160b050881180a010000c481c05000d40602c0d80301c5502d035662541d0380c6a500c100c1c0d80000b410001c003040460b00b150b1007418104201c034020031002903419400080320b122200c0326071000c43c1040c0c0b10700c098400e010b803c1c0068200210300e805120100c00499075031034040202402407980c80100399590b05001545039054546003513001c0c4519130b45202107031030b00d006504010004400d035611038800062076660b60b80c066005600c0f44041600d01ca00d200010741d400d4011344104000e03203980d00700e10644e4240c61302400c0889081d91301c8843d0400380d40c07803009040c240c642925010726880501802000141c0b80c41c01068440340c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 890227913 1250 890226663 890226677
    0x3020f01051b160e07020c0a1a09120606130504050c330d0b010c050a0b34110a0b060603041a09070611071a0d0209120a0507091a01 58
    0x21070070030340b812000511049451060580441d0340c00714481d0000705481c084480312078150759105003240d40c2d0f03614002d21b90300302817900410452031424090b810101809210107504200c64000400c015a013000b80e0031280b41e1245080c00228100103214071b034020440300c001d100e07900e400d440e05a911440141c032540900042240d401c0078500800d000081041500050f8000011155480045030002000c03604224542581300807998010800c10307203076a5000015200f0f8644588503011100001080e001c46119640100c6e00c64094020300400c3c0c80e64203250070714118800020080113800301d203107140c50b544d2000e1000c00210b50540280c50703002030200c40d0780707036039682d00e1500d50752922196060ba40d41090701414001014004903c02082c0d074056518400d020014000b000e540300c2451081e441c403158003c4101e4071510845004008845001d0405458004800003050034000b280c440354079243c100c60030741c8040001c01c1c000c0c600204100402440b00044005090a610701a0202181070080c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 890229163 1250 890227913 890227927
    0x1a04052212020109080d0b03060f060919060503120d0b0108041a13120f0e010503011503090203150408070b1302010e120703050613051614120a020607031e080103020f0105 75
    0xc00d420651801750300c9201c854480d200044d0754005040e60f02d010a12a000c0c81000a450128070005144502c0c8024012031a40d04c5501c0368500914200340385203096502d075940442d45441c10026200c030b240e00c0d98001903459941c01003920449201c01c20050412400f04140004144d140b0700200804504070f05d07001160300c0344050000c0b02c07000c449000341408544007078981c1050300181303105030014081c0c40385002c08106600449182c40300b4004c4407000f014402171f158200b403181c1d10032105a4070250488201c0d000104410706078a004942c01c4032030440008106003084005108541c224003050b4013102e42c608150700280a00e0780d107000c0c4600401310440c0e02480207404100c040002c43d04a0161800d906000c00f501c0c2034008070800a031050310807040ea000d8281c06e0030310200e0072600d140c030070780f5442c0c8800c2040000046245003014074500c2500319050150703440c030004040181c0b10b600c4030223481d4240100c804c402182c00300200e0501c26031000410158840e1201c080d0030840034a005656580 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 890230413 1250 890229163 890229167
    0x90b0a051c0609080d0b030a031e0e030714120111030601033201060311120103030f05040806101706040b04060b0a0906080307051510120602040503011a04052212 71
    0x82141c5014000702e0404546600741320a0800401442100402c2030003481d0444081c180c3d64203000308010700060141c012082410305904070050b60455520b00a0108206a00041c0c03900680f500500c082c1c100e070f031806661500e410081d545811904000034000ca40d1025484070840c0401800541410f0700c40e01a0034844c43d070b120030400c82c0c020048004100c11011880f15655003801d00800c0046807030071110b61000301134841a1000c134411305000d2034250b070856401301d0790505500d4514081c084c0900020032101d90600090744240249045028034901e0400d0f021400b10b03000a01d0f0780c1c1904050113005c0420704255034654000d80029001c14540c904402080b00003199902500c9107a14100002c03450032400710041c1462805603084458401d4903803c04014510207492030410071000c48420001d44001251a0f981903025070001428035941d80c000c01e003560590151103040c0744440364114628506885220b40010800180c43d41c801c180c0c0301300c0c5112806070000030b844a440c0381e500800b814 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 890231663 1250 890230413 890230459
    0x30507050d090308060112110f0f0c0304142e0c1403070302011509140a0c03090f0b070207081b0d050c101805010203030f150409080f13090b0a05 64
    0x1d07803001000c0058415a00b40240080d00c16103400340000e8401c044078401c68914007440380d040d103018886c0307031400300c9580d071011481c0c1c00764032801101e50050103040318000e4248003400041141c01481a84c0300c5504040104840d51424412000091203850340d68441a00c1003a0620070114102881d9607015824000c4180359030140c14400d9200009420042580c10f40000b00c850340c3c00d540030003103541c490510304152200d52102004501d0300c1400282894040d0304070b602148560700b000101850035485000030203d99060507544400041d0a115003030740e040280390010090200605078000001c0340c04120042d07100c800134420079070f080d988011b1100c00c0c425040c00c1080101511a8801c81c404041c200c40d0001302064081001520009aa540040100ca01c9591451410a855075135465070251100360f9418080c1c015036290903100000d4100b20080a180340340280d426112201000110a05819900030500540c10300c4800c43c602e0312450065805d403201102c0d40d080000c14000c061080c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 890232913 1250 890231663 890231677
    0x702070b04090e1605031911030106030303020a020c0a0e15010314090706180803040b22080c0a061b061d030409140604050609150f031c03050105011b0303050705 71
    0x14803000500003441d40c0d03442c1d11500383d020940c0159440303c000720034600d240030401d100c0c05401d074110101c045407001050f100c41442510910b030008208a8120110742103d00b22380017180071070360006a208942c0e40400120f2880c1208980304240d084c2051045684d07100080d1141e0886129543c407031102e81c0c06504103a9582200310044043c40c40c1142c0c07040d544400f284100307004a0100312540c0303121904200010160751024004515103464142180c11942c8110841900032409410403030741e40c00548020001065084002d001c18080c810030400e000c0901d500120a00c1000d880f00d4500d49041031420801540205000070000303242d100d90110411400312070070887c0400500404c01d1240b55020752800710119444800d2070ba145428001210300070b5403070561000050323002170042404032030346079511680540801c550103105000301c3c0c50080c020140e04441c0a07079003141212140e043c414107005203001d18195007104500a5060092000c0b69409070400d03071030760000333500140110200c03080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 890234163 1250 890232913 890232929
    0xf02040b0114070f0b0c1207080c190207060e0d05070302060c0703050f0f0d0801140d08041a0301080606032b020118061a030c01090501050c0a020a080a12030c080708070207 76
    0x10f51619480c00c2504800c492400b183e0800e0302002054400d041001603440e0040b42c41c01d8001c0ea625815400e40740084000c10041180c0410000c190f180964140c0154140007150020a9442d051131806000e90010b4242903005502040001011480005070102140e405890300350381e03426030075481406c0c100b181d04090070b00c0c403030411390208441000440c8a000407601d0151003807000701d00310480d1050700a10402c10081100700780081c15280818485884a20071180b40703282c07965a0088201d410301818170756086010120040003070507400d02a1030340c0800102c0280070810200080040e0724101700d58101441044000e4111034107000f513002d00c0c02400320004c003041d514007a01d005000303041c5002080031042240f502000050800281903000c2da00c0584075003a0550400340115100c0e0001e600c0726000f03104901d5082e016881d802d0005000e0600d59002d01000c04481c242511440ca100b200c1104051404411109942d4460b5000360804228a4402c00d2502c4541c5c0c22481d0608541000d16 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 890235413 1250 890234163 890234167
    0x230109020a092702210609103501020d15030c0b030a0b03030415030b04110307030e0102040509010303030c0206090d120c11060c0a0f051903020c030f070c030308130f02040b0114 78
    0x42c0b1070304002601080d000e42540d00d0f4015a103140500039403500584090079443c01c0c40c50709004040600c1450241c4c0b0b001d803202c51a501030b200c0b4540450f00c42d0031102c09d285d40d50005495101507024002c0703044000c0f0781e10651044900d15079460001d00304d6440b50a0800320003001090718420300350044c10a1840040c04c8a8a0701d44414840c0080360525403000d000c03d1501890340302c6410640150707204480c85584c0b00742541c1d21004103402502c8586d079005d245541c00c000201d5155141048039010798000c0e0340018a81903811406031420b040074105489070740c041c10309940450707801410428162900c28021801b130001040540f4804054904121240612020095440c44030001380c100d55041d603071000a10906d0441c103035054070441026840b00340303a001c1010f07615070107900200b01c3c0880d004101c91034820300d001d05240b00e41060f0380031101c1c0402c20740e080040c103607c20306140e00501080c080e440c2084e02c6587c3c0e0300e080074203180300900480d151b170034100f0568000c0000d07018001c0ba0341c0381d0503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 890236663 1250 890235413 890235427
    0xb010e1012030323160503091e0c03010c1409191215050105010c02030303041112101a060c193306140102250306230109020a092702 58
    0x20b0082c01c0104c510f14188031036001807150400400c4040ca0060800c01100c600c0d40c29006811962540000c106040d1072044490904498964840308007400320220701901e410b840301d500705401d60300201009410861400c2c9075030b400500130f8080700e04200c7c00711400d94564440c0c1101d84500e0039554007000200d8001403181050084186400e00400b100a008018036070b2504010742d62404540304c042c1d0590300c2400018001003034550400c5030400300a00c0c003a240c088088030350f850703d06452642d4203903980341c0402203078000ca610f80382c4000f024200c90403800c01511411843e234841030080309498800301c0000c0202480004100c40e05c040c407501380608508001c071a4500351003407100f0501410302e4501440001c042140050301c4509050590182c0311100c0c658036581010345001c5c10740604003038000300c00070000c1c183e032246107101498810600c0c2d040010401c00c10000105078404e11000f401040a03032200741e4001065000e40b401161b01e9403840200f50100d481d0300c60083d050b0b0840c10304c001000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 890237913 1250 890236663 890236667
    0x102616090905010e0712061a04290a0e04060504031206060c050f0a21120507032309030a3006150306080d030c020f0d081608040b010e101203 62
    0x301c50300300e002d0402072000d58000c04802d642d03151140724089181c102c4d08081e030b0004240350400040040d00c40c1d94030820440b2040003c0849010006034441e002248501c2c5075668001040014800811903103404090316118035843c15031402480201055681d40002c1d082600941c08102d4842c2d00c40e9040000035140d09002d0520520420103503280d01c1068a24410b862001070084045940461041c101c280c1c014a000340042d08801d0320b5050051001d0200c185003520b101c2e01d0703c40c1320a0343c1c02241c80e90180e01030315540a0300d1405841464801030802c500d10900104903030108440340f03001491414220b024032440000042d13010f10300c0c00703410017544401350300c4d4008009a454400b40002c0940281106800700d504510525440b5009290007201041c0a40e20000b02c401d2180195941c1600c0c019069003000c2c000600000483c1a00c024844000c0741480c001d2254140c03410040100e0500361200290401c0512401000c10f002d9400070340000c1c1c0302e807030800c010840000781140100b418580 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 890239163 1250 890237913 890237921
    0xc0a0b01170f0c04020c24010f050f0906010e04060321030605010810030602090a031b0e0615070f0f021e09070c08090103052802040e10261609 63
    0x9003445039402542400740480041240301400708a08014000305540009000107908440449040740c000c50091039041c50780300d14002040500c000103000d143d81008000c1181909a0308400d0040340a0040c0c8002a1960400c46412000174200100d001640c030300040c0107072070280c10060103500d280e1241d049070b0012800d41508480d00b034805000ca152284011254118100c0c1e4180c00c0c0e4400c8042000800c10b15402485031035006880d80308160703200d85a184403940e41c1c050f0642880d22004040050040700c4034056040b000032108584951444d00100780d89000d0540c010301011f00c040004400c10811070728000c0c00582c050000180d038060000c134010500d035118141402a60303100001035a141c1f003100c0310480942d03c242c05906140c0b80d03a0045004180003000130118620b810101c0e0103210003c4d2038203540300c0070404056a10b41c100781018811580140403071100011449041c00141012003034507060b0320241072840340000020300c52515004120010034070900c5010f04c0400c1c1c0c4019504 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 890240413 1250 890239163 890239169
    0x17040201031e0f02091f020a0f060212014113020c0d0f0305101214010608010609020903100e0616180e0103020117010303080a0c0908060709061b02090a0b0103020c0a0b01 75
    0x61404d41c3c002141c60004902d0743c40c2c298002c016000000740d040041e274031180c0d880c0d12500805005007005419038030125019420b0300300c01c08098900c00f10000d0040e020000e21422201e47e40751b0a85800040d540840c0302c001c41400502c200d452401704092200198150b480a40061088a60103640300d88060310f40c0c07030407000240c0020f08000024802000bc420a941114080356007074220900c151a9001ca15005103200c41c095500d6610004000d1400d0003454050403190350f0060703035071503c202090b1600008240d201c1085003008000701145001103442c1c0c0d405540c8151744103415291010485031100074021604070b50f02040400305810fa54029401d040e64800c0e2a01000722142c140442c9030030209102c003d00080722240011005601c41d0040b5100c2a803908002c00c2081e02c500e040e50038900200c4140c00002c0d0184401c0103071680c008811401c01519210044c0d07401020380104c0c1444000074a4a204e80741c490704c40500d0f0b64032070f0703048410340c03801c1e2070984584034103516010342586820300c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 890241663 1250 890240413 890240419
    0x60f02120708090a02040e15090106090e0a0c06050f0d0609020301091410170703140d0806011103040603150e09060f07090503071208130b0a0f17040201031e0f0209 72
    0x3030008400c1d030301500d4802c0c000d1804100404070141c0a60800016001c90f002c450600d020f1003a101e5031280e12600103501030304018002045080c10884400204d0760f480d070507419981d03c9042214007081c59440e5030010303a40759251007590345041c0824000f4074400d0003190807103e0303d0104002404181d0b940a181030b41c2940da0240b10b2006103010742c1e10140d905458901d1440c142c08400c00c07141500e84031281d1a240c990301500e0f003850392916603080d505001000701010f504114a2404c00b03c2d0300c4040303607910941c242050081e40c020500d0050317070307400349010b01800d15580d07007640c2401c14039030b40b00500144404075000ca8145015100d04d601c805045d00d140b452555101c0101c0c9145006610f0314064a90140040c00490b20b0415045a51034401200380c174008000c2105c030b40c0301da06009045002d04003c2100959409100c42c000b01181e0b15140030a040082c000403c00444102426030b68100341c0920b40498440080b042406100440c5501810198602480481c0d50403c0e600901441d12080b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 890242913 1250 890241663 890241697
    0x130c0e1608070c020108060906030c13020304020405010803040f061d210c01030216060b04020d051f0603060f14030f06010f050f0a05060301120c0f03030e091509150d060f02 76
    0x2400143c0704880c0094000b0701141021000035168200306071201d90084000302100c0c408860400411024648c03c00c0882c01c40d0b03000000c100c01c0d0b0070940a418010404a401103103040d1504102050318440c0c3c1c0581340400c440004640f040f6079680d0105441c0320700041011242e41060010142c400e0103510b00d15040d4007400b42100c0e020340c02072003960250214000c0300c0402420b65a00c1c10024110441c5481e80282c1c00d005c61072440f0b4152203168880c904a03241c0488000281c908082c0448582e4442c4042600341a01400040554018502183c84056400e068143c44600190070481c46d03812400c5988107030400081d401781c004000c102199401e0f01c000d00d00104001c140036101d0b046006198009100304010400807403440049079041d801041c04503030741a111510a6000080c80c0d000b81c0002d0301c6080b003501c01c0c0c03900905094000d0a0301c190900e00d4041200802c03029100100540d0844071040c1d03280503907454140c0d940c054540d00c100100071262600d002d440003500590090030441300a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 890244163 1250 890242913 890242921
    0x503040f0804060f08181c030f020723010c0210051302042d020f071b0806010f06140304051e011d0d02011404030203030604021309050f06041b0503130c0e1608 70
    0x4244026000c0340ca408014200d0714141d03c081510004020800c1c0d0101640c0303276004000c40d20544007401a0a11901d9450300c0d48003030b000da0302050301c0940c44400c00c1b83d250032405104980c00154284010b804400040780990758101111000070300380348041e410508045002b5091003071086145005029401c1030f00c203d0130700300c0c111030890049003941c900c034030400c1020101080301160002047c500104560303000300c0c0c031a10b040b42400703400e034400c0f0090510004103218070798110f48510210000000118190726003a11001e030344454207204d500240c00101102d2074029000c1d0040000000307a40d0103d12165180070000d9511075007030007050015442e0a14000d00400005491409a81c043c0d00071411a2501c5080000950111033b58052040035054001103998990051503c0354010003458070a6140800078041525104240742000100140e070340c81120350805c0540e900461250622440000c279480c2200c130240b9190403541d1032803075034800c115801000303211300e075041c090541d1100b0741611 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 890245413 1250 890244163 890244181
    0x209091317070b1803040305070b030604060b0712030b04110a020f0609030304030801090e0a021305041b0f060c0c081c021c0f0e01020c1507021504030f02010503040f0804060f08 78
    0x1c42c00018401281200450f0a08071300d0401c215020302d0103c25246883d503241e46141c94010140e010990000c00402044464507080c412140207001110f10300c3c0c0341000e5136451391003017420006400c041c10b40d591025141da441d20783c090785010070044103040d924803080502a58800e0400350f03030304841c4211400640428004030036240103941c180c0b10404143d00b001010b81c050400140032903524841c541410016a481c0803109408191070980092142060b080c80c0100f01890703281800407000820040003240360011554084400501d001510808645841102c039410380c1e012107094070540d6481040d01c0040b010812584e1724a400300d6802c96886c126134000d00c8103102c0001c012881c1090b0010315203004031107100c0c480c10141f05840c5000d0329400020712400300894010f800070302c041041011410603244055064429110642c2032520f9556152040801800c0017810000c010000c14100a83c01ca6681038107031b13002d8540f94840d92204030080880f800d001d1070070002000f80c2c01094401e8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 890246663 1250 890245413 890245417
    0x15030c040b060301170f0d0816021c0e06040e041109072a030c050f0607170402130e07120b040b06040b0d03050a050c0601171522060209091317 63
    0x280c000b6003483d007982e10f04101c100c012108001c0320002d034019034005079101d002c07d0141c46072040541d201c034061400c008011401d40e050600140b0217540c4041e590705100700f076100c20059560070034900006076002f8400450518003039070f8003400e86d40d0071110521007003140406c0700034820b0300141c800f4049540e0b04001100c1d071070245600c10b015801d006880380e01e07000c592015085420301a041c4082c08005c1540c1c1e403441c003024140d503002c1c0ea41111051250f66a4041c4e80c000c010300324102d00d00124107281e0009402c40b8442030b9011000c44d13480c104000c07000400d1103080300030301684c01070a110b040a82090681400d003150304031032190030707040011044d143c28807c4400c076050141a0a0030303e0856034050300e04d5032106074428244807007401900803e6074100050b9020706031644c030040b07442e603800186034604100205401820f00050f400c103c6040b8204048400c03204c0100721040d42504141000c500a20034803074a10341050b0310704100850b50f0384505205440c941300e01644c180b08580d6000b044914 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 890247913 1250 890246663 890246681
    0x60301030f111507030801050108013219030302060403080f071d0613060c060614090420060a081b040501020307260403140106080705060f030a06050915030c04 70
    0x840c180018601181980c10404410a005441c414201606145010f8650854181107002502c1c21006000e00d50340550803d0051994036080c00a0b82c240e10b803d42d404040800c1001000301c05a9000788507565030740a4032420006003541e184207603840e410300070340316102203c082e4081503c3c00c012410303191101390540e100700b40650b1480ca4080324049601d803c099507001c144d90140051100c502403c0e10070b51850700034203442e1900701c6540082d192580070381b1516404202d51030030a00c0c0400d803d0325426001c80d8800e501140c602601440182410001c0d03070400d092680000004ca04c0d201c00c9038201d07181c507004000180d801841a421104403801760701c40d9000e00b900680050290200003480f1081d55000110b115824002c0306002907603402c4030303402036401560084248100e01ca05050203104a2002e0304640d8003400c0454186000710700c02c1c0c1303e62a8041c60b801d40000010b03011200640c0860040c002c0209038040030b081c003141c411840d45041101e14828010b011000001d0b143c03501c500070030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 890249163 1250 890247913 890247923
    0x62a0f1c030c11100c0206160f11010f0501060327050c12030d1a210604081c1b0315030f1202030d09080711060307200f070f0503010b06030103 63
    0x15980c03548000c80140035000d00400a01a041c001d00c0802d00c4240a1a40007200c284400101d91980d01c4000346042c3c005072060a80302101500f01020035800400034003180d00c14103203401200350f01b4483c076004002400c01e01c55a54588400070401da541500540303a400718225400b46404007200051100d4008500001c10b00c0d8043d040d04140b60900c9040d800003270f909281500d042491400030304080d5800200c0e144406030740325805200750701d442d06111607107840c031061001c5a002c941ca4420360b2420064005000f550010072032001040d641c000247c00301d90180c40600c00c10209000e222035080180803900d02190404007411307052010b00b40c98104881e04802090f800c000300791100001d1401446020381140020020a5141c100b54007419a00b144101c00142c0d80c0c0c019414540300d0308140540f0944101410018019542e5100e1084420b03025402d08150011552100c032134a00b035415101d65400e4020084000b90306440710400c40222842503000348011401c50003040002c0c802400700030300e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 890250413 1250 890249163 890249203
    0x2061c091b1710110d02030c04030c081501091a100903020406090209010e04090c0503060c0d06050409120f03063c0b300a051e160e062a0f 61
    0x1010402c0c84d0040d13410b40451500651404404510038400c1e6441180c12010607100058100100107803084014000c20003180640b09403200c140c02c82c0305d40d007010f00ca04808245c850503100000c91003411031181c440030040c4280803100807002c01a0202e10284401d9101e13130b05d818800540b004003030086981e1450140d45802e0031400800c201300040503289400ea408898442020400b62030130044640200751400545403a9008a2020300a40700350390032490080341800240b0340054040c1e00a0010035010303040081034075040600031801001247c0c0800000c83c0c1c1d4090054115502d81281026040801045802030f0800e409248007103211348280d5a80b1582003080007001510b58030014201c884091010f0303002910401740d0783e00003c0550741c0d01800b03940c030b805010444540c100c400c80c82c1a5910300c1d01c0c96030301d007074840e10b80c449203507000c10001c2c490101d08200740e6a0302e02040f10340520744c581303c1c0d1100c12100d02120401c00b88205480850b4031480f4920300220500050346003044000b40f18040d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 890251663 1250 890250413 890250433
    0xc040b07140d0f0221120c04080c150d020c01150902130801111911070603020a26012106090b1f0b0f0c0a020a06030e070605030f0402061c091b17 64
    0x160f5664110740e800c8170600d1041c00140e2402c0040c0c1540b078043c0b96103210068540d42443c0c02541003102c0c04100a04c0303a0b204000900c980041d000c00c0d81e1081c98580e100507191142256001d000d4403c0440b07890040048010204000d003041d07016000070050a10b07403146441e1210029807c9600800300246001001d204481c0c2244030210803880c0c2402c3d0307250145030b910084182d189403034000d81185011903008140600410390090040e84c1580810f25050030b20355881085003503038a018007030f00002d04c0c141c0c1d480f11549501c80d9118820564000e04c1005402c40c14100360f280e03548143e9541c04480c5002c84c0c950b04603201c0065100540d0701c40c00805103080740b03071440000180e002c001d081e502809014460000350f0748130002403005040c0e64030041901c119403900c0c00d080c00070070303009082440002d1050240320310040c1c100641c031a80c15200b281d81d0b2611901c64007120443c0042c0c0301071b8503061414690410800140103800e24055011070301c4000d440c0c03c0d058910131700c001c82d000d4840d0b000403207036 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 890252913 1250 890251663 890251693
    0x9100f0207021309020a030501110a030c1701060f030621120f0e060d110703080f06150403020603060117010308042303060621010c03060807080c090406050c040b07140d0f02 76
    0x14401c4d441c801442030700f0040d0b032952154296165010058103264000c1400160720342c240c0a100c0d884102032901e10b084c0c5071000c031826801501805140b040050103401d01c6c0f09a03020f030780802e02822040c4148002507070000458001048004000c94072000c61036466017540f40a00c64802c1d140940740c54001e42594241d0911810340c2105030f00301c9080b6210300c0c4040340f0142e04030003007018070f000b9a5144a6450004080d184e03809014041502418a42162052010210301a5415258111282d03680d0341c84a9004903100c1d030300700082d101c050001600000400441d02c0c0104201e03500352191100004400300c00c84103242c014007a040e0540c00c0040080c0c0c241c074001c0244040c180c1141c00b03150050a04408035421155410b24510109541c0e04052084280810001c1d0080c820700c4001d1101750501004a428494090b0000300900d0322032001c82d81c81a0800182d402170862400ca00380c898031507040500b1141c0e103003450403020b80203440c1e00103015403040300c400342c0c045585c3e001004221916854 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 890254163 1250 890252913 890252921
    0xd0e0307020d11150412030906140f030a0219020a060b1e0907020709020c15061c03051303020d150b01030e1c0201022203230c09180609100f02070213 66
    0x481d07228070207040c2220134000c0c0902800c090541a0721445550050303240150082c040c0340c10440a00c40780e4007416000030a20400c0f1090b40e0b00030141c0c0f50316900e40c400c2c2c1c2e00c00381c01140e40d034900300c8103090522240c4980c0011700440c40ea0042d00c050000e500c0c013000317105554540c000000301540c850648a03c1c58280003108a4010700703684112510240c0e030340c81800880e000001c0d013410399000a00814111f00044075504d40120088482e4030f40320b0040349840aa00300c02c11401000e21901041806805400d401c0160003550060303e03c0400010b40e1a110080c05c41c88170b1111051803030124141240d511a00c5600325040e0008010814011800352a042003211080c074142190f400300410072240300d842000100381800501c80359211070543c41c0940814100c1340e00300b00040d0b00401c0c402c000c00c0001a00c040d203540b085c0c0341c8484a413520b41031824038000c3d0392250441403285406200c502e890024008644c1e03600400104541182c0e141c810341644560782001e036200219044000781941c0c0b07031b84 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 890255413 1250 890254163 890254193
    0x90a05010c0305190302040503010b06120402010c1a010e0a110c0a1106070c030b09010b060f0904150801050f060108130804050907030b1c0209060a03440d0e0307020d 73
    0x2d083e8180181d07064262208850b41d0700c024000703078021504002a080900414011020840e5020308103d11281043e89802e0000c00c00f9040064900f054410f118508042e44403400e99000307018419a101d510300b03400c4d5801500c1d002c14003850610105660581c031b009071080d0f002c3d0b0030068118014940c40701080d0103000302c0f03007603448041004020b0020720b1001d1108004d40c824840b0712050700e03103154918210b0791078451850050b2800c010700c1c802c1c2013040c000c80301c01810403030380000e0f00000a0f2a00c03140c3d900941101c0b105618090902614030303603180d410742c4180000d03601d08a1035a14030516605031892050002c0107580103100501103880c2003500c507540445135140010f902000000007548040d24040e10b50300c0c120040c01e00c00c00350700b0400f100681c005c00584ac0358002c03c0c81e5a40f060030031070400d9801001f9a40c2c1510101c0c1c91070703495a5111204107181c050b0124214940c0fa0816103500414030100c20901e45020883c2810000c81941e06064008194a9805c2c2d040d460351248105200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 890256663 1250 890255413 890255417
    0x5040309080102070311071a0304140c060307030b09010618291b010c03051504020309010b030d03380607150f021809010f061b0c1514090a05010c03 65
    0x20041540c41c0d00344043e005040c000c2d0ba03198000c4800b8004d1070b007800540d41104851940036610749044190000889801130f030321210507074012840ca800306080c0740d03500a0155201d80000140045035516401040c8405c00860380159280da0301e1000f90303000d100c5c02c944a500580d403100100100d0031208000b0100400c00c5044041c88043c00008030b07625440035081040100c4054803010f024070f02440b0b12008403d09040400241c101107800c5003246410072100d922440e00040010380e00c40d800c0d0017404400d50003034212502d42c6002140075001d002048044800c0010000e5400c074040180c142c16074021084030482070000e41d00c0070a2244c1a07100750000c1e1000a41242c20b1000314985109071407011040c070301c0058881c8401c03c040940400c8512101d840703080b050006203c0e84142c0c820000485096041540142c950351507100c40f03203025200040c0c01038101a02c00a042d407001000c1c9010408241e03140d07a021101c60508079124010800c1c1d854014a000c1014015540a0b50794041210b0081c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 890257913 1250 890256663 890256677
    0x6091305100e0c0607060203180a0c0510210b01020f0105040213090201090e04080405040c022410170c03010b0603011a1e2d121f1d0f1008030d050403 66
    0x12400300d2042ea004c80c1707084a005a0000801055400d40364541d900720711040d01602d1403a020380c665003168103031401600d100301d1240c4003a06890340500b4010f801a4405200350311302006100c00d00c4011f100301c42896025000f81440c0c214500340610846102d281e0041c1452400e05480003c50020004490b0403810711803824008610200f000070920303c0340b072082c001c5550b1981450b02b0302c0142e03000680c000065603c03840e10172008080d0f540c5420503000d00c2e074040c0f0240d44e58400d0040e55460095101001252401080f010b1415000c201d003003d40c1c500354000e01506083e0001d000c5244003d20030300706a5482070340201c07840380c4800000c0545912044a4400d8105c41301100100d03503000341800c11409203440d02c034040b50b15240741d858280740c034142103141c24110074120704402c10100520b442c22411050f09100b4030052211451400780c884001a0002d100090000340c400345021b070342c0520b00d510301c100000e000c2035041194030155800400610700b4442c43c42c0210000d800081d108409025034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 890259163 1250 890257913 890257933
    0x271a0708030903031f050105030f0912070606030605010b0712031e0507030903080702032502061603020604031209030e040f0f0527011b260a020306091305100e 70
    0x800c0080c500a00440000d075079070b8204580e509851003c134010940801c0ea9030303007041095030781044c00d0720351013804015030030190b80d9199076141c2849112130f01042900400700359a0240901ea91114054a00c80c26007000166282c0300301240f1400303400b9008010b8000000e00691b42c070720903040700f0718840e072160100140b01a032540c0c010a441c4121100000240d0344c40550060542c0922819000744850020f946410206c4007140f00d80c0614400c1d04001d500e40020080440d162a001c40300c00c02c2002d40034160785600e601c2c009440b01c0301a10107500003006004001481040c61003240172680e811f403200a2618078210030312026001074000080c1e403560303031591142d22584a000b0307148211561183c6d886031000d928083d908004004603065500d07898590b90246800d041c2c69002622580c5045c25202041c06c040d101026443c211012500700c0820342c1842103643c0d2a8010710b00400c4200c420241c159500301c0080c0002c044080064050341c07105030b03061000011584004014503498081d2050440 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 890260413 1250 890259163 890259173
    0xf0f1a010c030207180905060708060105090d03050d1d061005030c090a0f0e010605041d0d110708030409050106110c15031302031207020301050609090703080a0519020a03271a07 78
    0xc0d07405d000e00e150365120301081040220038400c2980c802850300701141d440c144500000d003540140400140590b0001d040c0703030280b600072403c2d10842d400e03140c8107000310360b54010304020460f0401100f4109200351b001240e044140100800d0965038040d000b042134924407000c01c8840c004c060000c0d210641d884100f451101103601681080101c41ea00204a01c2d14101c144821151481c542c010300e180000074040d203d604c0440d0f05140f00311a0325284005501d100505402c280b0780c1d42c4410003601c00000c00040c21841e5400c00ca040b07404c0c50b15080021203003903940640350014241d4007035010300307580b02101034403100e00055074010044c41c5611070464601d82c003180c6021602c06143d190207001080c2e030030841c0307401d02400340c0c058029a001c01003820042c42c0541c0d200001d020042841c0c0300031450844c0103200c2c03416640190742019500240c2e16001c0d002a4603194200003d40020300031528445507800c00003c10890007a01700180fa40c0d26140c045070007111401e09806540c0c011041103410f0202d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 890261663 1250 890260413 890260439
    0x5030c0d140f0a06080a06020304020f06030f010510170708072010060504090305041a090405150102010f02031006051b0106170f15041b03020a090f0f1a010c030207 72
    0x200480003040075030a080801c0d00c101c600040035804090304146090044d00d0b40401c01e0b0021700c0d80041c0158807a207591000030405681e600c51903821082c04420060700b645020040350490300240c8404043c860010000c5924400f0464582d0701440c4940108802621540005500c50380a180c240003412144a032001280b03801010b400060344001ca00d0b080300312075880741d44000d1400311010071000300c1c01d581c00303087ca008500c41d03a40d0070341845a038030b21211100000c442100f0710080c0200f140e403508401d80d440280c5006126030044d03103041c0070340c0320380c03011842140c2c0a604001c80c1d400925191000071603030791340114110149031818115034800000240a82c0f0094103a0100a40125801a011500e420300004c0e542c283d03903104403a4074500440f000010b80c0c11580018200c0c140760301c5ca5074110300815050340002d420845550001800340740d1035000030526042d178101445050907042e42002030f00d0800001030800e001c0c110a0707080039030080124082151180c01a207210341e9488205060403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 890262913 1250 890261663 890261681
    0x6090d050c060d061a040501140304080c070b07150c0e1507080c0a03320702030a02030a06020901110705030705011116080d1418060f0c1b031603080a05030c0d 70
    0x4242ca0702c00910805070b1039000642c005803001c170001e0a040c03808000130b00d0000a008105540310000001c0f0b82440002811548080da1000403a20030b035544808030074180c1d1007018180c8a03030f01d070042441e8000381e2500554078040d96035a143c0d114002c612042203180c441031045512210401c000000000d00c0a20141084000c01c8018001a000c0c1d41800f03003031045003043d03554022528001c4140340101902e4400710f4044604001500c0d8189440840d241102c0108043c0d8503100b0081500d04110f280c0d001000401c00030398410103a0403003148803540c1d50381140607080d03158100f0001071200d5440b6000c00c2d44041191380450710f0290303450802241008403500030204a80003588415429504107400810011401d00e00a00e4640500c48002c0f10304101c00c3d585104079400541800e01d244400c0a5508007460101507804a021440b06184080c9034084500d0190203191418030803076101c020307103408480c0c00146031413034030400700d01c101d03003d502c0201314100341581409100c041445900c03452500c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 890264163 1250 890262913 890262937
    0x60111070f1e06050d020901050405060d0c11010218040b03190308060315061e03030c07090f050903091003020c1606020d020c101b0215120a05010e0606090d050c06 72
    0x402c0c1405050b00d00c0103110078859006120031241003210b00e0784001101e1520640c0c0c1c0c030040e11000703c000129007520075a84040d070702c400b010507120440c0e156603001c000440b5854031201ca1784900c520700c16081c1d01990b01410020704140f50300c2846402d0035000101d480c90000d090351010700c2651803ca8240012142c281d00180c420020880d1600701007080001e080800ca141d580741d850210000358032a5440b1000c1c0409070340c41d03c10070030244c42c200140c030806100c080c1a60b00302616501080000c2c0440f07051100e00d64101408030305c1440002c0100c1e400198003402c08043c1d0a051760b03082e000796101c140e02e400603201d40d1980400440e01c9085040c00303042d00c0c4c0c1c0071f1728408441c0580245802c68883d0340f140b29040701c8240010440c2c00c11800f0001010b5580141c4502e215030000419280845140e00311101740002c81e0f040440500000510940202d00c0c10003113a40c0f1800ca100d40c00b8011030b02e46411110400c0350b502607140032031000603000c1c89181118000e486034404513416130000e14800c29 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 890265413 1250 890264163 890264189
    0xa1d0a061a04170105040c140a0806070e040b0603070207050105031e0f191401050111010605040504060903022401090207061d0309181006030203271c03200306011107 73
    0x43d4500d203241008107420001e0000e0b050589668404405500c41c1c40400201d2115035020340c3c56007640c0780e00404100c001d907401c500d4440e03805008407280460b09407003145070004444a52420401307907801030701c0540c0104041d90a100065941e54009011251844103080905650600e541d440521850415031981a5401c10610100582407070350390404240c0d062481c51481c10f02c014a1082c1145c00900e0100c5140d0309a140301401031035a074025170341103800d00d01000103000c1d15030040d06c0854400d500703c4001000301401e10b0004010b00301440400c400c44001040060840e030080c0540c0e038001c80b8001603014084c8a405c0c6003142c0f24480301003541011542203101d24281090806038941140d25400c0b0b03140282100000e982507008113828035a0100c00b003002400d0005906814030314005541c40e1400e02103111a07552040c9444c40c42c001d042c8505e0305001ca6109018141440c1c0d00303002060100d40c1c0c00d02c0540501d420003132540c0c1c104201702e20000c0c40301c4020480b1100a01e01c0d0381c00c0302 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 890266663 1250 890265413 890265419
    0xd030209011101020a6b1207140109060b0307050d1e06091203150605042909190503011d03040905040f0b0903090109050a1d0a061a04 59
    0x26042c400c1101c072603640c50740305103d0310b07060300c0c0c01070700d05210901e80ca1110345050740ea00300c030010b180d10200a035581c0001c0d0340c4502c0d002100c90b5002070000c45801e05408401d504c0c1c250040c04081482c81c45100181c209035001160100d08070040e010a9210340c0c2d409a02c541e41c034608508642c1244420344046441e01491106801c06200c0140901400c5e0f03440d4000b54195159001104403403240304011805038010001030205035884016055801804180381e41c4400e20010098100e4560300786100c4403051380066281e00034400c80c0d0460710400201c0b41d40b103035016005081011100c0710590000d504210001d09581c604070038064540800c83c544401500b00800d00d03086518040c40c0300b000300c0540446004907607000007034404035030b40504c3c041172035640d81c940348c0400200315500400a0031218140f040022022000d40380da04800e17a505101242e0310420001e41c1c3c04288608160203441c807042c5903000f2161024140e2000c08541d000c500d41d40e5400d25048002050000a100c00d00042014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 890267913 1250 890266663 890266667
    0x80a0e0106210609241401210f0507031a0a1506032307050a020115032102120d050103020306090a0c150302091306230a090504030e03070e0106090503011a0f0604080d03020901 77
    0x180c0074540758012103ea1b07507041c0340c40c020300e00c004071440b034503402411580c800810055800d04107419034040e007a280074558a181050180b030314500002c407891511030004a05428a103c1d0320a000c05001400e08050328000b010707030080000043c02c0340703001e0b501007039245100b6403641898040c050b19640d141d660b02c0d08002c004d003154205400c9c00c600c2c1c61000740c02c102143e580140c203181e8501181120844c45140c21003a0725106044d100740d80b03600300104000d07070044859440281201d0083e0240d680e981e458084460b2503002d000801407190b54100c00034080e074250804c594447c25920300340145170020706c00000d1140581e401d42529042c0c1c0f214014001c100d2510311600c025403e5034241c00400d041c100005003030f0081405008030603075807240020300b410f2203103490b100f00c0e42014056402140e21440086404242405024045080148000f41031b08052041d1042107061134024007840901c4420412040d038140a0b0342d41c08201808049520340040c000e81401103002e450040e6039440003000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 890269163 1250 890267913 890267921
    0x80409060602030f07030e0d0f0b010509060d2307030c0905100e0c0901030216060e1006060e09040f030e060a12050a0204030f0b0711010606080a0e010621060924 71
    0x501c11500b09000600e410b41040094804da241e26084c048890000f60003c140400c00380940680203011010262081c49198050b00341621025070702d003046652040c007031250412201c0030040040710030b504a0f420440a2003152040c4000c4041500d0416541b03480e0706982d401103800501d003d566a81c20b1081000120203078030020485410100450720340740380034031010300402c2c92442c14150002000c18411801d925070072801680f0000c204460b07880c4480450303480c200c0c1540c400c591440d00c02d0125009008402020024600524030f44c510703500c643c1c0e1800c0a9240349822411f0000d40444001542da4040c05403c0140c0265200480384c42c1ca00c0300d410580c1e00140804800c5407042100348041580115100c14040d0020300c0d400003500c440c5011540840c2e03106146805518190001c102140c1c4080d03075901404200030180070b5050115505402ca451a02c111096020348624400102540701f4024003118001d81c1c0c0001c0043d01ca0b01c400c040c02200e0006101d086099a02c004884441442 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 890270413 1250 890269163 890269169
    0x90705030a0b04082b090204290d08160503030f01120c030b091213030506010f1202210304090506190614180409030206010518091902130908040906 65
    0x30322100d860303078441e11204000500040c2c1000d4000840d45c1c03e0002402640115440c040404580d240218140d240103106140041344101c0c1010718403d01008020984413800b21981d41001100203800104044912100401c0703920b504140a641d03c42d1109150300c800d0907010b40e01a680e42d1a180d0000c0c204104160007803a2110100c402500100388000c8010050341c3c0d2006410642d2345072031082510706603031441030741c4024000240822140102201d82ca0850b4868800c4842d682d81782c0006040300000c03800380409000b0f42951402c003515100c9804400c005482d24a2106c0c80c0200080c2421680310741c0003000000c1c2c0f14001d11205007850040c000c0da02d440c80c2200d00380d5506100000f003c1441c000d21210494001141d46240c0c5018a0508603040740010410081c41c070ad40d103800ba458bd03000344a42842500400b820390020856141607a01c202140806071035604141e81100500e45000f480c2640c1110400022110408551282d020340303a001c2c1d4101030302d9901d403074008401d80301550 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 890271663 1250 890270413 890270419
    0x6030222031208090c030a051e03160204270f11010302070b0a1a040e010c03050c0a02100c0314090601051c020a05060a0507050d050919050d030c0821090705 69
    0x403000c00120780000440d44401c4014a00b80c4210b40f41c00d092103142c00d80b411901e41d410300070b51a00604001000480c0840400044030f103410212240c07100c5500d80c01400103e11111042c013400708014a4164002c005a56403e0b6581c05c1c69090402c1c0c04080d0301c0340d003504a58100e251114441807220300b00301080028801d203820b51401e0000c0d074406410010140a803c00140c5030300705401440d0082e44d40d03060340000035004001a880070072266028140d2840c400380801d02d40300200703410002910856001407041d80042000c200740420a10003400f4044500b02010ba071032410044012420fa0154020b80744200200b140354140020410088014500b44020601d140800c1c8010b0312400000030865400b2619103482c4c690002003907800744544200117009000d6028000c1c209600320020740042c21096421040c00814088210840d10080c02003641c8582c081d0441300000e48980c4c1800d1220f8414020300d418035840340c40b1422554030407050310b03105120710000c001c9881e03000c003ea0f6005100031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 890272913 1250 890271663 890271727
    0xe01030f020a0e041104050607212c0301062409060e0f041a040507111614040509252903160c0f0803090d020f190f060204060302 57
    0x40b02400c001c00f4402c071507001d1500c13080c0c5903809400080640340240005000c0c165200654070700b040c0082c0400f1092100e0140306510009031510030704c3c0c40d08500030101d105418a4900039110f22240d24290042c0360b1564840502080140e0030100c2d0b404482107821056903841c4584801402c8554075400800801c600100d6400b9503503200c00305065000015500000d82360141d620841140004100d16a001400c103028042c0c1c0c1c43d480540d10b008094442d00351000200240780500500c0034512940104448410134284907151540c0240e411040c18000c5841542410965035107144d02601d201c080e007da4070804000081d4602a1007007813000303608055030075002d9000c0c0007219020103044c0c460603540741c2c455000c01c1030140300c240280b2500020201d0740040c461400d0384080d40308490651a41c0110f581180d601400040e0381300045010201501c0500c40c000c0520b009800c0c0300100303071169600300000303201280d102d00c0140090280ca580160b55000c07690102c0000c07030403400c1024206448 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 890274163 1250 890272913 890272927
    0x90c060f0815011b0816050a031403040c060f0c020d0b0a0f06051c15020c060103120f020c101202030a150e220809040c021e241f060e01030f02 63
    0x10041c500d01070100800b0b02c01110404c01c1c240156540981c0100384400300c1d82848007028880d0001e58080624401d0b542c000025260f0842404540401c0e03a00402c0825400c02c06d1003068011a1140011409072610b04d134502101d0700052081c84100506861442c030140a200c1507260718020200c100e07070007400500003140f801021502040d402d40740f02e01d8a071a603c01010421451001800e410f404018003503407110240344e080d40c5c07074423001e00c0110b41003d04164103101d40d40c040c0f1640d044100d030329009010181200000e0044e58482c03012074104100c1d04801c680c80350702207407000c3c500880700810b0020341c07a801c0b460b00c200d9411264200b0380061042c1000c10060b441003540108201136844262000301d80c0a14101105028a1005550107400c040c0d819241c50780c00101c00640c01c2d1310340d00c10020800810440fa0300c41a0041c0d030503600d00764000c800c2140c01c500c00c64094000c000f900c1542c424000d2201e62030072450702600810001a0070b13441c0d61200c0c0d0b03450300840c0d001081c2c1c06800c624040e6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 890275413 1250 890274163 890274167
    0x108060f0102121305060c070f170d0f141602120f061f170a0b18030a18030c0602030705060f0705030103060c0309061d060a02040803120a090c060f081501 68
    0xc3e40203a0262080000a00310403402030b02c4c00e28100804010300504e4a802904900c0c0b42c40c0c1029005a4004415011000408101d0a0103101e00300c070900d0003515803420705d100c00316426858000000103000c81061161114039024000b4224000c142c500b0070350600142c810001c501d0594641e1011650041c442c40000341c101040321070708100c1580402004404000108a040321907500c06032403040c070445400d080f24070120308c1500313662140e041050160740d0130380402c4501041071320807503030b503881400800c030303168050343d5050305a04001c46142c43c100d683e40c0d03807420580c64642080d801600042800400c0190400540790010880e071030711805407410f07e0b0000c100e8001480090f102d183c6540c80240380c60b0082d40700d0010a50400d5060003002e0410703503103803900d80000880d03245502c202000100c4000891084e03805461503440910711b0007030710540e1031300811000740005d10ad142e0350711407120000c2d101001c0040240f80d55211003210010500000d4441c100083c00c0e80314036034800d204100356a03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 890276663 1250 890275413 890275423
    0x60b040f091112070807020f011401081e06010605180402030c07050d05090f09130b01060203090f03070b16050708010e15010905060109060807091e08191e02121b0108060f0102 77
    0x81c541c42c005c02c00b0ba540381ca040f0f1803c0011142c0c0c0156518180c1415003108100c03100c58161582c2c041150048617010308143c0e01c6005212400c0c4454201100501c4098460002444100f26100c030000c60b40e4843c0000804a03442582c080402d4800040c003041003110600c090b140c1c04000d41840da0402c000b40d00451031140d00b4129051042000710002140d1402c01010ba2150316044a0325070919038407560040e40d0707540301141d03540c802d088115003607080307180001c0c000c0d041ea4401100f0600307000da10800c003d02400c1407901150240549200410316140910907405d61540150003842a400c1c0141030300c00610b01a0028590130342003004000c403590b0800900d0b4100c9500c2e140c207004698940b038049030502c426410020808a9644200c0500360080e0702103401c5d41c400000f51050214860640d00191140c13000080c01d07810016044103030114601610481c040c00a011f910092420100103401c00740c4013000310082071340000702d00f89a5640201340c268018815201841b80008a00c0043c0d919 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 890277913 1250 890276663 890276671
    0x5030a0302071403030a0c30020f070b09150109140411062104020901151d060d05010902030a2d24080604061a0d0b060103060b040f091112 61
    0xc140c000448500708070340756001c800c581c0d0600d01070700e407030b42081403561002d41480c4001c10b00264040d00f80784010310708814407203a040344420202c16078a29440014001c0e410080d00c1d19900c010601c4044c1c04a0040348400b849803207114003801c089842e0405854024178103801070704030316251000d100d078800d10941c0c0940e0415000750f607d039143c48241c00010140e225040080c0e02c180103140ba540100003580e01d02a009510844094610382c0e259494402c4a4000d00795400008465000071200d00c22018501c00000310054402480e20441000b224140c500c02c1c3e1280c03e4140d400010130400a00b42d00c5030014030790030100c6402c0c0f43d1201ca02401e1121100f000038149807651498006080a501e54a00c060a40020b10710a8820b40d914685511024210340c240d0b541e6040403a0700c900300b603032001c450103500c4006080c0000200507448001c041100240040d0605035580008142150b0420280c801001014056814903042200b802c050b80d0340c442e80d01c0e121900c14414500c02c011b010640c0c0307501c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 890279163 1250 890277913 890277917
    0x30b19020f0a050d06050a080c0102060a090c18020f12150301060807061404090501030f020108010906181d101a01080408090402090d0b07091409100311040221010303080c03010305030a 81
    0x228521210301d00d00408151b8040c660203459654000f41845010404840c481c40907000e48813259240b0014109139000d240d070080c91a9410002840340d2140c0300700b40c0d41203840c11034005041c41c8049020f0800340d03004118140b42ea0301040704001049506100c10402c00d84254001e200d400d2034110607039034a0040e1b0280f42e080c0202c410070308150800010980d0300a1084007024042942d45c0c1c2046261444041800d070b0010744810300108407a101c0340500011a4603101501c4004a0388802d07001c02480d100628020740c0041030135034260030f1820080d0001c0703c0000030300010f41c0f01c1c2503110a0a038400300380d000e03418040c180023008041030301c0c070058413960380307065a0160b914190381000984c4003a0351030300284111882030034012103991160321841079585441651140618444c00c10040307281c12102c0e43d6010702220800d000160007040c04982944010344090700b806a00036003e604501003503050700c440075103100100b062550041d0082d401c030041d00205840c5505503140d15449105011103041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 890280413 1250 890279163 890279167
    0x207261e0c0109050a26030c040519080a150e0706120f09080d0b03010c1706011218061a01030b030d081b03040506092503020d0c0f030b19020f0a05 65
    0x103141100f0f40000b19000e41c0301041e5092040240303800d000c0f150b42846a021050406420b01c2c42002980c070403680201492103515081a24020420248080d01404965103800480c00040e0200c4108500840b880c4111000c1261046c8854440d04940c404940c15480ea442820200300c1d01d50804403c49040701d041502160a8036071140404c007600c1a83c0008100c4100042c0c070401c00300312039002d00e0a100c011030003440f9054000008076400b9002501c1c0d0605103040c100854451340c003e01c406520f6008140010801036a401d188501000a45006403141d58440c902c480c014080300e81450b0070f10390242020401d024502c4080381d0b51344850183c910500c022980840c2e00440040b00748400094801d9203030303549262030300d0101d0f240c840039161903442d84181100d0b140c5555100c0c10750f80c940d500d001001d104440c507540070000d401c03070307030943c10b482d0700c000020007240a5040b0090240558068102e036045e5007014020340204030181800084241e02c1404048220501c0d4022110301e60540d2411340d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 890281663 1250 890280413 890280427
    0xc3f02090408041a0a0905041b0302070f150f150609060c0327031a0417130902070f0203120a120f1d0d0201060f050d020405040f060207261e 62
    0xb9009104942140204001c41a41d84200721031040017030141036140d5480c102180d580d02c0500c01594003130704548861740c0030140003500783c92180e4050503640e401140d0f140c200304c00b603031990340380c0400c90400c0e1141d40c0d45466400c00c21070007900070b46007941d4200c22030b1001c82c0d280030b2004200c034060b40540c10402141d10344840a061140c0510030151075440c424aa90f210400400e424143c1e440c0703c101ca101800c140d80c00708094a040c500e0b8499500a610020001d5511200314010352106040003910251030780f010448003e54400740040511464201d200b181041c01094500107a0300c2d01030300360a1081240e0000164004580050003810340001700d030780030441c07110101410b12052480e0b038299000000001218001034070080404c02030b00200718644d260590f681410240740211a0002182c1d9110401410258401a4042d011384464a041c5204c2da0710281a80e004500a4644244566403c000d0014602c1c0c548030701c0581002d0076140002d0f082461002d41300501141c0b0540b20017040034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 890282913 1250 890281663 890281673
    0x906040b0a0306050c03060a060509010f0f091a070506011a0d0209150d1a01030606021e0106050a080307020a150e041d121309060605031603090c3f020904 68
    0x7100c00b071940b2810a02003817030030300c00d01c0c5282d800444030305100d070b80340c05400180307607005004541c2040c206a550802035083d14a0a4a040c0385e2104503104200043c0d4000a02000c0b05c1501e0680d48142c00c42c0580d070b1212030400c2c0c0c0c605071068000c580e14044004008101d0b190f1081240da43c0c80c034518000d0303200c1c1038140000b000492121841030300c0e4100061090400002d80d4814035241c218001c3c802160b60401004504450710340c060031000d40e014107540c0d00c1d845400da150740207022486001044a64036100458520607066200040c036901c085283c800f18078010100030040c243d0140300c003801c2c2d0f003031060062000c0d281c1d0100c0e600030b50f994001c42000c403640c140c120144104480031121750410618228140b68441e03591070030201203500c40814981001d02400040307540999420341540c45842d20703900b4400710b07050b4140030b040c0c0d2074202c1400031315164a0440140440441078400e9101651001420383c41414250f012406004101ca0100070030040090955016160030080d5641c61501c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 890284163 1250 890282913 890282929
    0x30605060d170c010e0106181e0603081903050403090e071e09140904030503010b030c040306090c09150b0d230405240906070e0402070b01060504050418020906040b 72
    0x2002d010035401c0c0b00303400355020250009042620101000300700110081840e44e081701c000d1f010303131050081450001c81e0b1045c01d07a0410340f510159402c0d60303504209210000c00c11541540e0003241e0850b004200c1c2075044002e00421140c08185003030520a80c81c05035001880907901d07004100c45400c1e5080271504051040d06900307400d988868040d185885d02480240c20141d441c86001c1003400081070b6014581000050940615856202c076400c590030104042019000108034001850b81880b0020201d00342e8081d0602d028042d02048020505002c5220296941e89506c40c69640c03100d4400c01500300d0400890342c03201200140003c0d103250446c0d4980d11580d00c00d8034803515040420521051100201d0f401c400081d0720355070b4001503103100d81382c0024640c040f201030040b90054070025403c240035030008820840e008100500c0c010a03696003c00c419400c0c1c000c040000c402040900280c00c242c403e05c10000910a1015903012243c0c3c001740382c600d001000c444c0101c1d141d030303150003013a26402e031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 890285413 1250 890284163 890284189
    0x9150f03020913020d06050307120323030c04030c0506130510200f0606121c0c1208070f05120a021305030d080a0c2a05100c030e07060f02060103060506 67
    0xe2080f0007400d03407400340a0f400c0b032203100201600c2e03d9800151454002055004c60f021034155900c140843e07201940c110f43d0b0041c1a6a4100d051402d45040f110700c800250703c10499812619190f600794182000da000c019002103004820420490804210301c038500e20407103c04031088140942c15250803221070303a00d650780781e82d20010010079400f44d05002c00d401c103c1740340c082e003281c0c025656441080032800c803604400109401060307000e070030244080510b04d084943e9041000d2641d41e643c1e40c9030b2800c01991000d100040d402c00500160517405141840001403500d026410241080d103045003c1030068001005950f000442c42e070820301c0068180d00810000b4296280d810300503a0181070f00c13004854403030782c0500c1e100b04040102e008584110f4481d80d01d080070000d003582401360030503903440b0681c00e8a80d8814000c4410315002503000c0d104407542140e40201d86241150b0b41c8900d0410650401400e2164004425038100e60010740380b0b0440c4e41203000492035803107803004100442c811031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 890286663 1250 890285413 890285419
    0x210050711010c0c110901050117040317041110020f0d0e1504060c03030b06040b07060507030b030303010f05190305030f070305071a180703080316020f0616080709150f030209 77
    0x408050313400241021003103004094010042580340e080000d149424050640419882d800c41c11601402240442d40b06109007000d1400d100031000704861b114085504448001e000600f60400c1d0400310803090341000c003400100301d1000740070a0140c6800141201c2d4082042d50880320110380e0315208800c0d00f2800b00001140c2d070315251030005140d04070f0700d6070076004030382042c1c005106801c106040310200c0e40718541030343c05d01d8100da8660300a4040503111500301500d600140c40301e40e6083c4001c600800e0341000c010000c0e844e10b000d001c1c43d11505814010000b92600b400c0001c00c1d400300032030b902c01005c1c02c0141c1e80c84449103070945050240c4a8094821109000900b10340d01082c6c40240c0254140c0070384403424440088010780c1c81d000c5000040003410213002207076001c440640150707114002d900595003081d01940304586002130803a5a0280ca0909003c504500740d080384640e03400900501d0103020f545d0a12118030707400d61160610b08108200381e001060f0240c0302e541620712010b402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 890287769 1106 890286663 890286671
    0x1141c050123010504180b0f0601091208040509091603022743121d0109050f0109030903060b0312120f0a060501021005071101 56
    0x5a008480964a070b40c2a280061292440907000b800c0c4450781008541c03400e002c010685503200b040c250705480344400d41001c1585185055403141210f0088409900d40100481c3c0031240c1d03900004030036105a103a40208a030740001041205c078202d605401980300c40c01c6151301c1304211403071420813441400b004c0005042084100807584500b10b40210510360440e042942041304850759061000c8060007696880ba05040c00b4504441d520080ac5504000c0988609810b42d585803070410701042030402d035401c1e120b41e0041648040c0b070012031070103e81300501050281840d17807021507440c0107454902203410014403a2010710b81c3c25545140702140340d42c45090081c15245031450700b501824221403910300d200e40003004070400c3d0701d4040c40b913443c01c8201704200603000b40030302c0c140b00d08110040000b41ea001030210b03811001f80c5400141a00e907039500355034804034001c50030800d50030 = true := by decide +kernel

theorem cover : BRFrame.Cov 890107913 890287769 := by
  have h0 := BRFrame.cov_init 890107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 890107913 ≤ n) (h2 : n < 890287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
