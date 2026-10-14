-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0990
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:41:16.412223+00:00
-- url     : https://prove2.me/submissions/d5429ec0-aa20-4982-b362-2f7f34769248

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 177877697 ≤ n < 178057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 177878947 1250 177877697 177877709
    0xf051e0c070f02150c01091101050304030806010e0a05180109060803040f03020108060d0210120f060602030904020d022b06060c02010f2d0809010f18080a1b050c011403060604 77
    0x50040e01000c54940d00422034610307901e0030400352a114103030f51790385c003a00d10004119840e0409035140305540d070141054034002e54055840390b14603629840152010140441c02c140c0c03045409030001120b50300c56841582041304a2001038541d45000c003424207840c20350704001240d400a00c0709122800e18040c10504072270302464101c1c02910f418000c1000d0700d444100180d0050344042c04010703c190849400505014500010401c01c0d01240c004e8080b1039040c0140c1005801c00c012080303c5181c81d0b0041c0c00c0d50010200c0c01482c214243c001590321070350310028121006407400d10051100001d200b42e000a12803401c050310000d4003603000070000342903c542041845040050750499010368100c1d0f01a0005410087c0da00700b41034980900545c2c4102c0d0811b580d5800e0070000d07680202113000b10000c00255580f0030400714031580d10f030750180c0c1022540c1c4082112418000000c81c4078903c40c807090307034000c0026085580035000010f21003c884184100180f504005000300307519200c00b16400c49003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 177880197 1250 177878947 177878963
    0x112110c0d050a1d06041706070206060603130f1403040f030c05060406050702120a02030f010b1c0506040b0403020f010603031e09030206031801020f0c0c0306130b0106050d09060f051e0c07 83
    0x80303e400045c2c8038011904940c0010f2043c10b4041039107540090080e0144069070215001c2d030f96400c080061911040340c84220716002d81c0c0c5410000350702c0c82109040284200c503050904200140d44507d0750b0001c0d0f100d42c40000c0408000c0050050740c0d20840060003080c1c4503545800d0614402420601c0760010003402448070401000110b0800d01070a45a140d0040554241402c02030b5454081c203101d205491080e20320000080c0c0e44081707114095881d562100140402e69140e40360b824284400520a605600440140c81000c800a2081c1809180b0a4a4403258540c400581803241c189001c0030809108203d1400d0003d0b0b910f2070140d03507220401c90080b01b00b0760146138059000e401980e44001c00c20801140841303003400c01180104401d101a07080b201965141b6080c242e21111100010308126102801407100c24451001802a110381c290049096130380d980c4d400c02110b044294041019581c0e800f44050411015080d00da1000707808141000c40c1455010941148901580184044 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 177881447 1250 177880197 177880247
    0xc06040b01321203130e190b03060705070807170301060908030a120b03070801140405010b220c090506160c0b0906040b030402040b0d05010905060a050408180112110c0d050a 76
    0x720420071102c11380505c4005d045207079600c0d4003200c4140c6058a100101040310070030300040f10380e14407802c906400300500503e0386480d1b03800151517540c40440260340c596420484c4c0300100700b514a2203c07060340c8122800e030b5607601d03280f0b00500154840d041a04290420442e421410f980003540c0c0d80207290802000480c00c001070002850444103030300000d125420000c4805e519a450405544198090301c0240404405002088000e180700c032041003070303c208d19543c5181520785038490090070b56682002e040c103503203600024540f500881400840d0514802c0d088041054201401e001003410084507810f201021000500d107003e540920748171382001100140c1555940d07003003030284940c05804a2103814440c1005400307000d1a100c103980d10312840f404511152018460144160340100296041c07000403001c03540954550b80c04941003003000707825101c0007400703480b0362080b080c0c00c10302c859900e6441030161410300d043740e01c1443c00e00c0000d0148140309608a0021703d03800c000c05490f00000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 177882697 1250 177881447 177881479
    0x8060a0c093614010312020f0304030b09070902041403010c1103070b0a021e040e090309010503040b0402040b060a0509030c03061e0a0917071b0b1605030c06040b0132 73
    0x144000d039214035a04014110700740107000050f10b0b042c1c0340036003c0c18103860341c020010380c2e45807540f2007074500b5540100410000300d103106040c0c5400800510503240155a1503480c0410398100c0e401c0518040056400d8034118a000d128030303001c012183c1040388411038207212082d20782c069074101800c4118060005001c40806038116140d4503480b00c40594042508580c1c001c05400c41c1c010105035140a6001c1540390798004103650010a05070340c1c5078078540e41d503034038441c03042809070040b038104d5117072000c02d20310380c1c0c4800290a02a00603030390a074407401c01c40c080506c0d051020164034002e401070400e2048001403200341100c1000712164900241e250203a0300c0b4000c12172420060503084a0441c129090501d00005010817409190024099203c4861014147ca09482421950401004141030400021030140e80960054090b2400c040c0300302d14140c2020021502100d201e02844014010710800148240d0120f80400703d59040440c040e154094130444030714440c3c0300b140c1100c100035030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 177883947 1250 177882697 177882779
    0xf01180906060312110102030c0f0702041b1107050603011836150203130b0702012a02060c0c0706081302030f01060501020d02010b0105030402040b04021308060a0c09 73
    0x81203601603410042d040c0d480c100074501c042521804000200303001007581180c00c0500a1b2400b541d80350300080c3c0341c49004140b0007903c1c1c1c807900c01243c01a8640800d0502d99801000c207001c80d00094176070f951407119001c50380c1d0a01515400040c400e88042c40184141c5020103410310b4408041000050321030079501005865030805000ba00034860b150900d040c0030410910010078440c418145044000d901c0e49808043c3c1c08219141150100c01c80b60150210300d03401040e58110b40103000010340b4141030300704e842c02a071088544484d40c00d42c52821041c4d1130f0341042281d91044440482c1810701012800b161f48940e0b0302c3c465002000f500303c02181c140e01041c0004843e19074000d040300c0c000d4102a031034074041c004510039140940500030028040c940103002c2c190340b4034016580c5520755501e550821008086410300103070007560921003000d61410740800540540002d50042010740351202958041d541c03000803810402061480400c04100b5021240c82c100380c0914a24103209003052500ba5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 177885197 1250 177883947 177883961
    0x106080c04021e030c0c010507110a1b08030c0c090606070804030807080904020a0201150b09030703150902030a150c0302090d060504060b03060a2f04060f03060321030509060f0118 79
    0x83c2c11400400d020111114800030a6001d100900038001ca13a150700c0c01340c52041d0106140d01c80713900b10079030850000d02c8540c852080d8400007150208401d807a01102031440d00040d2841006a0041c121500e0500c2d00038041c03a032190046840610300100ca984080487c010381c40001c2c000030300402c0013420021018195510f1240c080d001b15111185600002d020f071401c110182d140b0714814001081c00800c60084032814880034000742100c9207150b0b59001c41c4141d9a0000b40025651005c1c007005070303401c2c0140b200650107940070990302c0d803d1203400022141980d20810606d8070401280d00700d41c03280584541c0c0c00d0f80010b800191980c1c1c6051074005032412500c220391502411040020b1350349203910011f805104040c468404c100d1706022001c03003046103026804104024070040124621030808280520014a804a0b0030380d51303641d03400c0e00034010104c500391400c1c03d6501000b1031079040c4034182d0301c40c0001000b01528107002c55003550650b01030060341d844040703c10500400703034a1500441 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 177886447 1250 177885197 177885247
    0x1020717030d02130e0709081b04060b16120c0201020a030f02010212010320040b060d0b030f0a050705040f0207020f2103120402010807021612060f020d051005030106080c0402 77
    0x50368401131030100000161450080000c8035502d44085288284944202c02c00d03107000100070140742e01d0700d4511181d03240012840e20303402502d450b404a40c0300084000b4140c101c001158420221881d07207007400403a660120703a0020803802c40702d0350000d40c1c0c0c00615071402d03503018101002c0c003048440c070480c060b205e48129030000c0800400004108040407110ba510303608005100c0a6a001d0a01000f0586030210003196100c2e20511041c5807403601c42c0d1100d504420010220b95240d07007001001410801c517504240c50f41c1d0000710081007542054003441010031400141145000240c1e400206c0c102259000e081c00342c1d4114103d82224400800c07041d50180c035050451f0307100e40100c0b04100384c1d8901150200d000411003404034100c01c3c00003a46c605c100c40e0407980031802ca41040404070700203140e00c00a561054445040c0071080000e4402410a0b0a1080010079146403900101503c2c0d4003561141c7e00981c0740982c2040345c0100400c6007420b1201c00c607005a0760f08604084e011941400c0c503011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 177887697 1250 177886447 177886451
    0x30f080405030604120908030906071401140a230108100c050405030a0501091a190b030102091c0219060e04090606030c15030f0203070c02010509120d0c0611030601020717030d 77
    0x88000d00004114883c10000c5d690346560308103840e002003a03102c1c000e24880340c2d04000d05000d070354000317102603038180b18440120000148484e0040d001040d006020713185a4402d541d105406a803030059940e01141c403002c09042c50030994580030700c0c59503a510030400b0108140e91011450311040c0300d5812640100b0009003128000482070034114020644440e084808407541c44a41004200c1401080c0c424008011144c3c000c65030071070302c44c0160000d19005036043d5400c2040c18807960782c100a402c2c66216600095941e9059803040c0400e005c10701c0e10080003160700d0401000100e600181d21060b001e019140807803900018a000400780c105600024086c2003046c1c000f049841c030b0300480d1381d080e859507a0144040004a141c0004900c03041e07400100042c1209466005075010b44001d081c031070320141c0340781d040f401d11324043c86c01e10440b00d4070040050b1814050809011113070159001c5210040700c01031450603c580041c1d40e88500344940c07030710391071038006d8034100f0328050003920790003e814042 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 177888947 1250 177887697 177887701
    0x605090f041b090f06050a060f050c10050c040303020105090a05060a09030e030304090b01090b0f07170c100f0f0e07060f020a05011e0c020604020a0605090f04061508060118030f0804050306 83
    0x5010040d01007200604d00c032a01c0d1100000b100e14010700400100c0d00142c4540c2081410850202c0780c86e48000311243c21845007802200c94900b0621400b07104140c02005140c44070308500e8024255400034020140c5684510307881404100d010a1580d000000200c4c0065035644038a0142e0340004d50b414003660502001c20001041c40c0070360031451030010240e0350000129160780090741c0901501800c07c2003000d043c07050000145c082c51060550700070030314149062480000c0d0382840c00510107000070900340c0b1400303200a114080c1c0648145014106070600001000700442c0f60396511510440c42007054158280860354000d101101c5206c0d000701c001d100c1c40c110300e520040300031402040c0310302c141d02c0c011110302014804a9014000c583c018134061a80d446c141c011200c6801031300769a1760050785000c0800709542c803071044a00800100c00801c070340e100c2d9400050220b05000701230324140b08040b0320401c0a4420310002a054980c0540f0b84d00e024401c0b803e140c51180200e4000513018800c0702d007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 177890197 1250 177888947 177888959
    0x140f13050f030d14101e030212010e1216020402091c03091d0106080f04020112061805060402070812070c1403030603010f061413090812040b010503010605090f041b 72
    0x2c01000e822079492014080400000c11565103400120342c0c80065001c203010501c10b0b6041c5510400007654820034a1220b2510b03900022403104c000d201141282e0340d81c1400701c80740203092007036062080701400c2c4c0c541004c0c41450390000804110700002d109580c0000c941d001d07035071241010140103c150745070005040b210314014000000c140030b81e110200c2004414110211108641d034181c0d140c83d0b42d80c0392961a40000d15142c240082d00880c1444989105540c20010a101e204011300fa620008030f5082208030f07000080b21009401d080c05a40100b107008085802d0804407401506400b01d2880b165440d00412201a806104014000445100042c002e00c00010195002d010100c000b0003425248504032400c032000c0344929250710f5038241e400c2d01c1038580600c4855503060400f001040000482d40d80a060354002403181034422649802d02040c040174079065030240c401600208025420b01d40058141e4a009000b0443c2010750800603040103c0c00400c19032175283e1007002ca44598441d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 177891447 1250 177890197 177890203
    0x30c1804110c0a110603070507031b050d17180307080a0306030615050306070206090c0d020102070f060915050a08060d050c04050a1a030a0c1e18060e0604140f13050f 73
    0x903050380c2440242c13511045a10f40481101d00611141c0c65252400b84903176030983c1c0c44400c0c0f4100c0460300d10301c0c3c486580411400e205802452009036520b41c042c202c4000340f4541c2c20301c0545240260035070f00c8502c10340800d00008841c0c0c000d4001c6622034650740340c240b007240a4110354000801d0b035070800c0918074100d00e5000e1031a09554003207050751203c0d601c23035400303c0e59110211044400c95101340180062804d04214500c091030041c0b05450115490340c05a020f00307682c99100306c001400c603002c2085803200c0030010b0ba824460a28000d407404400c01002403510b507028081c43d124007024000f543c200641005000806800a44207101e1031810150050003040068400c0c09510451032100c102032501054540031160b100d90b800008906081090301e6125540070035203c10342004001041c4071110449a50032868007070300204071181000010b10500c2070240c52035000701e080c506003400c80403107056202c1d070180d800d15800013140c0d07511005c280c1c00c482c10700c2c01a20b94003a15000e040c0024001c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 177892697 1250 177891447 177891463
    0xf010b0903070b0c0114060603100b090f0303070507061e1202030a02071b03060b060703020318120a05030304030f03021c0b0102010609060b071412030a05060f061b010501080102030c1804110c 84
    0x1ca406c40d822650340c1402c0c81060711080320f6803016890555014001e296010000d07140e118005450004085d4405020901d10703800480d017030b01c0d1036106070070411196034005d44281c41001141113144079021441405404c41c880b00f0140c05001d500840081c4803041294141c0316402e400410075000b40c02d0808800c05081e2090100352462410054070b8036490a2110071902000d07816401540360080c00a01015004560190294491207003051021115820010b0304c074201d0003200915540d091500d40502003103103900f0b20b042414010b1010f0440ca101006172a00790107091480810354050040040380102259008000c00518141002c2191aa03501c05403064500c1500c5071522020200100e40d1340300d000342407000e0507000400000f42e030ac0199800441c2c01034000b03021030410700220400650b06070000310f40402120040050104406000d018083c0140088c0000314607505080e5a07a0400c3d01c1542c10005001601146480050700d840c0d01407821401260036a40c1c407a01c2c20f5011079166401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 177893947 1250 177892697 177892721
    0xd0303020c010b03010c0215060a080a080307031b08040201050d060306061e09090b1f030c0605091c0c05040c0e0915090114010c110f04110409060b030f010b0903070b0c01 75
    0x43e141c45608141014403405410302c80f40d80007000d44488a410724a2002d13402040c0b980c10203400d10b000103801e181045800c1741580b141c41184d0300d9140502000f0103c80b07080030120305990369030114100712038104081e55041034080c40d10f01e079030b444808010b6002e00301987c001800a4908000001d8074400b0994400e2508141001000711030b98800910059903010040038001102d408081281d5500010306404880601d29a0000042d62500e868104184551002012420000700007404e0321780141c0410070b20b0306590034442c001030103480300052808103004050040b65a904503030704246c06000c0d11021f10390000e04411040c5071009000d0120303030402941034000d4100600119241c6042c01742d0140e0a02c060b520107030741000c40d84a900b02c5681e205403080c1c101d80840b240400544845c02441440741072400040d56aa2801010504640d9150f001d88540f507024024002411109026281141c0c1107480041e2100400750002c1d007001201e90204078000700020f2003400858040d0410030001031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 177895197 1250 177893947 177893951
    0xb0306040b0613020711040b0a0902040b09010915020a08090103151203031407080c0703051c050103020906040603023006010801091209270213180e2a0105090d0303020c01 75
    0x25a43c1c80590290600060243c09050800d040606041d40100e0303206a0003441442560750341e00c0e10600f04c2e44103402803101e29000060b011f0041d40c1001240c0000e00300c456940c0d14401405400070344620b0070305802488000c002901001c1c5a100707400c00020b00420f481a11200d40d41c07040c0060215070940380071000300c1c0c00d0018200c620128440054420b05c0e19803540a0306540306040340311554400b4404506000040c03007825003811080341c14900382c0790f24650004032941107004014042d180200303003900c141d080840520040e215030901d110705680d0988071070b410300900b007004104e01c400c2481c41c0e02d4522031000000399001c01504444292030241404115490607503c040724104100c1c022950070080d012100c5880707101036580450511002c000040c10261401000788401d18168002020b48a00c00c0160b42c40750081e1013070000b044c510400904840d000d002c14600590403200c500700303403181000040c171000d90090046403481c0c1f800610744280c4140914000d002500402d2000001c0c1d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 177896447 1250 177895197 177895219
    0x6080606100201090512090a0b030a09050f030405011b020d0b090d090602010c08240306090a03110303040222020d15060f0905031e0c13140c07020f090a0b0306040b06 73
    0x42c0c010b00c103404c2420781210240c541d28540300f0f00800140d001c045060b8101051010000700220460b0117180500c018490105200c0100c0c248280703050381403d03a00c0c603117070800c000400461380c0003c9400050040a0700e062110300990001445500c40d4043c050110340099040064100e800b02d030304c4007601d05689a600700b0513103515080342212268076420001c203d031034000c10f18034541d0a00008980d240400c80061540d10400446e04142e0251840041640512031000c00c1607084081241c6130b040340b00c015401e520301a000034000500c60704805801018100312401c8840e0a501201da2920080300b0074807240b04001c42c0c0707121512180c0300700300000c0c80c49901041c3c180d00c615841c20403600b0043c001c2c80c09503806901000304050407044685140301e02a1030b098582c841085070303011203104090010740403401c965540c1210400502d10101c1c00c608000314401a5654000c1541c0e1003800ea501c1d03003080d1b45400750b1030014075a40c4541d90f031600c00e0748208010040300d400c1441c440c507410386d0101e00c02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 177897697 1250 177896447 177896479
    0xa050a090b04030b04060e01180516063e0703080d2306060d0b19030c0506070503192a0201020c2b050309060301030602040f1a0901120b030106080606 66
    0x5008900005016500c4c2c0c1c00810040768103500f00d000031400c8030000140b0040940c4420256251010341110310b80c000351604c2419500d8114410700500c110300708a140b03030031004031814144812001043d140b850316070480940c1c0c1d99104c00f01d81a444031400311000c440d200d041002c5190000710300c850003c0d01f01f40312101411a02c41d40d514a8483d40d01001c21951a81d44c100506500401a0380604654619161704140e55521400710305840c0748034400078241c15800e041d454855507402440c007a2504010040004c0c0e400400c9402041010100c460414003001d01221b6000500002d00952078000000b41440301c038100c04480303407034400d0b001c40e44540740f120144110104011001d05040c40b07030380b80c0209800c4a075840000303a90b2040c0196460110311500142d0290800c2c0c200750307125580807800380900c0d00f19050540280140d0034400b02d0000c011408001c0602c40da900c0c040c104241d0542410034043d040e00030b01e04c80a4008c000380100da1b15400c07a03e035104403c991062041e0049900f000c20 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 177898947 1250 177897697 177897719
    0x1308120d0b0d030f141c151e030b0702010204051203090907020c0d0602090d05060709090b0904080a030f0605100c0b0f101217070f0218150d0213020a050a09 69
    0x403030755040e02c800004001c0400144d5010034041502c0c00340c0c02c0200034076155003103c2007415000c074800e0710300003c0c1e442640a1f0200060711540007015400840700c213000c4940307000b6004804490f0700c101008010381d10000101d0190240d42d10983d00404200310f488280100480a400e4541d420384994002c0d68400c0803c90343c848400f81b5031504001c0201c4002d02040d180d40090200c0d101c05858012a43c2d401c0ea1200c0c070b4070321304072896800152450f1f0240301d0110305004543c4610360440d10300103035083c15201c00c05584200c0c00c000c41071544c1c407003e07540c1d0000d4a4001100600d0001c0645a07490000c00d0040d10f030260750700d070844101100c900001c181e200c5050141d80030324109983c813407085050400c4251000c0c2e1030101940c90903100120381040d00900c070700510f0850310869031841d4024091051000b074050701040c00810048038010800c22024a5020b020b2280081701c1d008610340c500d0002c100059030188440c156240000b070722103d85908540101030040705503441400080e0b41c1c90008030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 177900197 1250 177898947 177898969
    0x21090516180b060f070606050915030607030b09130f17130e040f02150d02030c07060b010503090d08150a080c0109060f020a0305180303070b0712060503121308120d0b 73
    0x250044051103400264081d00000e003043c1c51181b400000c4040d190000507200000c04c85600030711994140d0304071800c1c2800d2008507001082c0e4101031110240d40070000b5074642c00140408401603280281000340301448411409460300710309005100300b031b0030300180c0d030b50b62180c1c1e252100500000800280344d50002c952a21039030300701244081084c050360030441411840c1261041e1103000784541070794400d10b8401507008014109000381e403070401e807420009480e40c0c2e0740000d051100070704c00c000200502081078100503d052811841070b6540b5a4400084000607120a4000c120850085111040054881c034104000d0700c0daa58840e64601080b548080c2c1380300148016005a0f0010300001c2c0141f019040406c084240b90318080031140100b844c603081582c1c159550b5110b44184284560050956110703c024928113008035401c4c00042030b80c91103101c003510404800011640001445000841c014124101c01c0d50f035100181b0700c56001542003070503042d807003d107040c00360200c52030403080d820 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 177901447 1250 177900197 177900199
    0xc031412040308100f180c0201021e09040b09070c12020f0109080309160b0f0a02030d090803040201030f06080a111315031103031215120f07030c0801050721090516180b 74
    0x4422442c006c4080c00b8011210900c3d041d99000d018454149000b07a280a1700441800416501c03041882c04200545105000c1e49000345428814801d9a5622080d9010000e800c0480581c104003841c1c801c0b0f01d030100c91090a6101d529041c01c1c8010016803c00543c003c11070744040300c07800c00d8094000c58030010207114846600d01c4c10800c081d10102001e01a244003891401524100011402c0c10425540e070418101e4030050000308220031980c140c07160f003d00c8241c03000c00b048050f0030015099a540c40d0039001403d01d462070202c000701540c6c0c00702c1500142c54502014071034545245085080c2700443d02084880502842c1c2c000c529040001c00d407480c160b0303104c04140040d01c3c0c840004407a03800081c142030300000042c1966440c2c030020019100307030107040b900030121503195040c81841004140c0280d91140d042009009800c5e6000c884000340440d5404084240c40890f101c0340000c05000200234001d000f4400140c000780c20340b500180898a5101d085080d402d25844400102e03840031b07180c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 177902697 1250 177901447 177901469
    0x3140f040e060a1203180302130e1603030e010311070f05010603021509031c0c02030d020d09050a05030318010519031d0313030305030622050105030705100c031412040308100f 77
    0xc003002c039115918441642c8800b1b20a400c0c03a0b500da40100b0300b035000d685c0c00d10803a04d03143e0480c0e10000c1c2040001010f031812038242c0c003102605541c0c00806111100d1006410551503444110406c040e00c4116000701d0b0b4488480504802c89180c01c1c1e01070314040c401030344115040240c045010076604203c611407003000303000c2d0815400c2c981041e018110a6698101003022a50788840181c40c10050f03001004140d4004007084002d911005240e400c60f50072041c01259000350402081d1000000e56034004059003021a02c00728410040b81c2c90300440b801802c09980300e500c05407902c0e405600000700b010004601700c8010b000800a241e41e446800284909820400b10800c04a44142d0295400c0700005111584140132844204521108500e000c0041540ca00c010000e03031404011941c0200400d07281070742603200c1d1030006030041c40174000c00360038003030501c000c591058014012a07001b407010790701c401140e041a0074010701101c000c4403481c1c0003811128010610003a0b00c10f03414220750360f041c80 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 177903947 1250 177902697 177902729
    0x330a06140d1a0d0b0103110a05010504030b250e15030108061302040e01060e0f09070305060c03040303020f0d0506040608010608070603020c01090203060108030a020706080c090103020703140f040e060a 88
    0xd5000500c051090700d455012515000040c0b50f60703490551244500502c00c00b1110750660426880310300000c80058411003c400c4104100d03600001074030200c03900300602070490f50b91400224104858105208180c3c1240440e200342640c1000c2e5210079110180d600710803082c03070328081b00400c1c4828002d20701d4550066002076041100019940240c3d440070704046106099440b501d8251007554200344100c480c410200828800f80c140da10394030030044002004028950340700c0f1525141e01070709200c2d10510000c0060240b40c0240c046442c0f03034108480c055514295400704000504040d50070301d00c11400c003900018204014014042550f100d0300203005590316103c0250000d600094940415540324000b90300907035801d000d194000d001e14805140e40d01c030b4071000281056000e805c9070062041143c10310038104000c1c1c3c00e4901441c0c1c2803c005a0b1000242410303540f118036401c0642e404080000c00c0a00060903d0180044849601030300b0403548952080104124803401112610b40700380344 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 177905197 1250 177903947 177903967
    0x14030102091309020a051903050606270403140318160501050301140a0f120b070203070f020d0f060e01020d0c03020403110d020d1406041110080f330a0614 68
    0x1200c44040f620040c030b4410380c1a51100484e181403100400e92401000001082051003800c0c40115401202124071100784400c8595405108141c008604220050030000a00301030188502521440c04100059182d20700b4194409041420700ca91707074450f00a4602c400400311003020000140c41c0140c46031750039a805c2240d8800d5080c500b48120341e020308101d50008841101003190005071100c070400b00382912142c2444595003101070000400c552003044440d0120700900c099204041c5d044481800780011420404120300506030f0181c82c541c680000c0e10440d0708158010801d500000b1000c0c02070589145003681240100c0c80040c0104040d800c08000c1407500c070300c06a00f100e200400e401c664880380c0d1903000f40d0000054110900c4d52101c01880144200d42012488840086034280d0480e05843d200810b840c1c009031901301804170321008200c42025511070719464001072a103000c0c85a001c2c000703100b55004c0125201d0b000d002003003030100710320b407080c4034050000c400f541010340780201810f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 177906447 1250 177905197 177905201
    0x18090a0312090c1508130f02040209041e05073005040203120f03040c170c0d1104091505180303011a0f1c0605100e120a05030a09140301020913 63
    0x1000d207145640c0c64034020002454000000054651900d009040119010b00500450005011450300006c1d5017810340000d62030b00300c078400390380d1b042e680541c503a075020011401800034803c081005a504201083c1c0120070703540414450001030752902240702113a060913221000f0920190404000343d03045802035111a0001a0032a01c05411262404d5000410400e203400c05201c1103001d180000c01e00080c010503d8a41010f07200544031407515800046e20107a544141c078180d2401581d4400010040c0012138207103606512018006002e03420042c40d01041010b002c0c21848130304c5203440f0100b203203a001d125016a06241c000300942c516428003c04076180d0b680040e4031301c042d804c03c228800248160f036001d403c001141803074200d41c0c900710080b000190307602c1d80c110030700406014410b00c21940e80700d9481016084103131148060142039200030307402c0480e505000391180c0b200003003002503241d20445e84400c9415a15a50070908000030405080c1d1003034003507031a0b00c03c00e11005d4040b4a2226 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 177907697 1250 177906447 177906467
    0x40815070e01230f040602070f08011a09040f02030d05091905010906081b0a0e01031833020c0a020108010801110d051509010306020408010e0102040b12100306140618090a03 76
    0x981a0f14103010b10480d03000d0b0590b019800980058200c0c0804001001d03400d100f00e000341200e140244005d052005583e41504410850688030b0108000454140082c042e1404151074000d0180c4040c0f5295290242c00e55021101c0319000b149814010311201100443c45000e03200140c0d0350740b05191030142c3c101e0f00148054001150702c4001144600014000f100509405503580c40b104100105a03001400f00d890319070401c941084c03909540c0001600360824245210000c1c69044810700111084019084e00c0c103601d07a18951002072264021031000991740c0c10760740b00b42e07540b040b1a0380b40e080180c26a001d0148110201c00280031040e0440c4441e0407040e03101800c540c0110911040d4000141d002c5421f81c402c0d00c4640c0e00041c1801420340a0140e43c0c1a40c2c0c03900000d41c1b5141c035080209419104d088030080981c51501d000c0750384c07441204101c1c401960080b40600c0000a510250402c03000191000b500c00c051034900d205620b1001c004580c402c484400180248030703031584095583d03200b6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 177908947 1250 177907697 177907757
    0x10521061003090c09200304062003092a0307031b080f0d0e01030209180103030305010803040b07120c051209040501051017042102010504050d05070206040306091502040815070e01 79
    0x6d44440d14504101e0901a42c8200e004a40108040d01d000d02016040040c2c1404d59082101c01c20410541c4080051261881d030030101071044c09042e1400c0b0f090101103103841d80c90b414010008000140092410308940c800888200303602d105542c0c0f000320b40d44001284d84141590400c03103090300d1150045020740c00b03513403060601510740100c440c0080e10501403441200001801003005105042d454814903000d13240fa0402186040c1c00c0c4508000d00c0d00800000030300d503600c0b201034038220034481d0090985a41c1e0002c1240c440409240b4080095041840514000c0e4034100001507146041c00e02082d0784c8016840d015200d041d0311080036045400104161255240026103900c05601c4c404121a00085503000148500b0645042802c0040440703601040040522003103001d80d846408440480c0d600c6940014121520710380304800140800034001400d102203000176041c0000700d904c000300f03880020340082075912039000f41c805146041c0000d00045000c043c40420039900d00078400340c040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 177910197 1250 177908947 177908981
    0x2410050d0b060c06092808070204020c011506030c0905060306010c050708031b10140117100213080606031605040f06120309050a080d02060a0b010521061003090c09 72
    0x1415401040030b907804081c96152541c000401c22030700b4801404200500c207800500c403004824000e0006603501892507020700035180c0000c41e0006c55403141c2c1201c0d0f403490030700300901c02c99a910050b48a0f4000520030200464103228019080920802e850380c2a204000c0800341140c549000448049100070030171a0b16100303030040854084410800380025405408880a014000b08203040c282400d07a0394810030241003026840050a002c18014107480340c1c2d10b050983c842c1c0041c0b02d10324246c0d5105001041a1001596040e64854141c0301c030180ea030560100d500a4641c0c1043c15580d051b01c1111907078251140c9414045481c0c250000c2d4241d4014400103d40703035440d52080340808145440c01c4020404048041200b418805812001060b104d800361039208078001c0084e403100b900030300042e81641c3d0398890340002e07806441992010300d5000d8008481400c00c200f1500f183c1403d40b0402d101d800024074541c0551700c41e000c1c0d80c0303516510045100e0240c3c03601d20004060071501c4403a2071f09103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 177911447 1250 177910197 177910211
    0x1801061e0809031806120f060a170c0625290609011701060902040e01140a06140d110316020601090e0c0f010201090212012703020c0915060d052410050d 67
    0x3e000b68585001f81407048000c403035410080d00300119021164080c0c88030391602c6016108445c00890140d4050300c003621529569031858844220203007641246d01e0341e20844100000a020742650319441d0030307003614110342d84103010800e07503894100102c40c1564086441001403060216038006403501e01209800030071403e4403061034100380d03040740e0401d94080c090708004000080c01d0301425692014185d891000e42410007a00400c60005e200c00c04450a0340021070015170a4182d0004100c8901c0c0842c09441e0705280600402541154060718014407800002107580e0078036110351040140400028007211542d1400d11200c01040b286c074905555a41010b4809078031184606d4800d0041c0c200000b81e1210038444c140505542c0c82000602d11031407000c038900294000448000302c100c01ca554804559400302a60104203204400a40001b000305103441001c010f0f800942c09280019440c05804880c404800701041020310010f90018200f258000000c0c003a8000341451400594086503003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 177912697 1250 177911447 177911467
    0x411040e030c100c0e01020703080711090f091e07090504060b030604050a0501051e060603132406080610180605030304030812070804080a0302091801061e0809031806 73
    0x10303004403105450a8002a200703085a20f103611820b40c1031301c00303400e0414142040c00d0000399154200d010040180303200140d600c0605c0318540840030164401005240d180c98400400664400700b40e403050242c0c480e6002c444805000c051903401200f030103000825840c1d10307100880002d0705015200395000c0d0b544812078107854806008507441103020f030005000030356192a00320b084031002459004100f0040c1c00507101200040001784c0c01a004072900760700c0e5103030b025102c9000d4802c6440240034002d007600d0745039024455240d4201396038540d9420480301f50f443d460b490b11002c080316040c81140b645a4107014000c0d81d41c1a14403c45114140001e50fa9110008289180c0c4079820580d100103011603940780d40d40310050080d07404103882c0341018081c10310740e07210004c502034189120181500402cac490b019072203202200380b4000c183c0d0030030410365030f4404002d0601600104140111814107810000980c06100d2460142403248000c51078a00d02540850095064801c06640820100000b03412 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 177913947 1250 177912697 177912703
    0x507033015080f1608060609010b0706140f010503010606140708070c0308031f08031e09010302070c0b0a0e061201030611040e10050a050406050a090213080604080a030f0608060411040e 81
    0x280d0f003a64001007501084070040321200202c541d000c50344a92040d02040030b60385a855041d81154980404c4030344032103003840d1140207888441c01380c0110f07482c2001004100c1ea84a502107040380c40680007048901d803102000c481c046494581910380c0d4000304100c50002c1c40303140080903982d0041201001c4140c4941d0343c007030b0a0707106445100c0020751007480080051090340811000f4420940114074090740003800b41081507220748010b0380d400022559410607400780d011500410317805090b40c00d1254403082850041e0300f1140760640060251000a01c103424100125001d10a190082c40b0300e90f841c6581e40c1015000320203060290a400b44400501038041c60a206e00a11542445003a080d00301b10900800384034a07400544214180712003008280c980c042c10030152039080401503903901c0042c0010101c420658020465846010200400d106001d00a4043d9184a5606101400b2020303c0b407410b40d00c0901070703064039030072520104001503060324101c05180d001034030101d182c1640d8038170b243c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 177915197 1250 177913947 177913963
    0x31b0d0c0509070201090b0a050f060904050c060a0504030b1612050a0f0c020303040506060901060f08060a080f06041106040b0f0306120303090705090a0203040803070810090c050703301508 83
    0x10240c1c0d19030114508000407e48800d03400090110100710324985072000c1d103c08180076200c0c1d80200c03607100220701031100034804001c12038400751000e50f44045480008080380d20602c4203461103104030b80441c5440800001e060040403281e6214890301022041e402c0062038013500c090399455a0b411034401d10962802030307100000440c3c0156840c0e280a00700b550070300c1c05c010502c40c070800c000c00051001e541c106080f4411010b880c54070023410313903625000c0386001d50795803c040745520495481040a5000007038a0b031181e88900045170051205405224040c000c2d0f01400103611001e00c080c140ca0b03103004010b03640c07001008000c1c2c085003442c40c1d222411948152180a080e0704402c00504c45400c15061041d00245004011499880c04e925864200e00000d00707440c0403c0480c0000c50300c042c0402e98030700046d0101510410210440810150096210b40c000f100404e056005142402a405580b1a074580004042c5940348114141e01d50080001e07058100c8807400302600401d003904204a094 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 177916447 1250 177915197 177915211
    0xc0204091a0a060b03070f03471311120103060c030c021603020409021212040f0b0a0c03030f110403080c0105060d0c060804080c10050114031b0d0c0509 67
    0x3400c8908028030000003407000810300c484150802a04011500c11441101d034058a01d1030100e0801104c00c1088002d04070381d00e903d255a06d0b21030f600300c0c1d400c0075444145400c00103001d00300759000d4044c008400a42016906203034802c0104446070b0300f01d000c035040000c000e2031600a02c1c0c540070410b12406500ca40a800580300e456403800c0d1190f00325014803d442d105022070000740022401e80c5018181e83c1742c0c0b808002d000c3d680301e03400c41d005c5450b2202c441c01c1850801c0300381d48403c14100071a15403604248580c0285001d070b400c0000e020b1b004e400c1103960008072a0340300f40f055121504d00b90040c200c540c0800c00025999803960544400b2840600003640c4240f00c0c3c1c5685590042c03213182501ca021380524400c008405e00000094140d1a8002c03c9a4147c01d2280e40e6540f181000c40d014041c020420b50780e80107603011500034041e079511250580e04552010f0256401810a040d07841d900c0411240c28101c81c800d89059070b180c080d00d52034009200c0d800080c401500e96001c034a910300296400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 177917697 1250 177916447 177916463
    0x90411010207120b010302040b04020c0d121103071707050903030c0609010501050a1508090a0206160c0e01181a0a0b0301140d0308041101090e090d080c12160c020409 73
    0x65806503a060040300c0080c40c01c0d02c02d980380e2152948682085190601c0002c2c844c960340c401d406265180c1d40c05803a01244400c00740c0d81400e04425010306240c0d904203140020501d8000c964440b010f600702030324000d10055480011040300c2540000303070320303030080c0c50701d01031140c1880a40d240e5030b400c10041001d40309201c090225414015111403d403001a0050b0b880750649130b40031f12800d203d5040b0800040054501160070f500c81040c034500300381c807009010b904400c000604d54028400301c0c90102202d84182c00d095411641c40b84415020072080c000c005c2c9414190b0140050f079034182c0c11001025003041344024051900c200000d08400c4240d104490a24012004005c81c0d8408510015001070075503003249a00300f1680c0080180d00014402000d0042d034040c05800c50344901580c0380500304510501d49181060341071940d503655180c02a00004510f94001104003181c4001e981002da00c2c0c2c081510140c856414036515151040d0050040295042c0317142c0250703071a80503040311075005103c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 177918947 1250 177917697 177917723
    0x414010f141c0e0d0512040c0905040b090c09160c15020c060612070803040b0a1704140f01090507030b0601180e1b0313020103021605030d020918010b03070503070e0904 74
    0x1c03500035500581d44115158001298851600d9040001c54521046e45107545400740e8562400e90328809982d001900b2182c500001c01c01040500102280a0003e9800b110180c01080c001c03c0311100b07049840fa207503207036107020440341c040c0100703c0440c2c5180300740c4901c00b49002c0c502240040760404032070442a6404401401100e00742403403401c05140c0c10380d0162100d9420070841c40d94034803440c031a20300812400117885000360b108408809a000c0700314402c54070743c103090900c00300300c0b82180710942c52401a581c1040340c0400521079500101c0d8024080d00300240b540d01c889054960003810141400f02007803006103400c1c401c114403405048502480e0b00f043c202110041c48040c1e00d007840440c201d20030002d0140704003052180744013840d0b0910700036036140a8880712114040b03480d10010014440450290994007058010b05030020040d01c1200060300d449061005151007072240044802d410400308074418070900007903500003141e09003035024003100303008a64140e10403501075031006100c0f01e03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 177920197 1250 177918947 177918997
    0x1202130b0d0501020f0d0606090305030a0e04020403021003090204061e030b0a02090604121a0f0604091b0605090f030303190507020c09040f02010305010b0a02101a060a09030b06060414010f14 84
    0x8544800303040b4270b10f01140101e0440e40c600d81e481c03183c0c90180342884401d01210b1f1442e91a90121406554003402d1901c0580c504500500138001181e0201c1c4142e04005012070081c9207200003150882119000000c000d02e075841d6200104000381212130340b203070208050041600c800008000034455802d11304158100340c105a104030088400d220552040202840741303d8801d03e02e0b850b003000081b10f001031080e1a43c41d00803800c0d145014000c2032510f14400020350300303800c8400392500b03803010f40d05a070003450341d2820140c6a02c0112410304040d40741c150a6807103884980d014980c009010300449544040100c00502e00c241c0c1250102c0c0e2481c03140310080215681401210b00501e00302c1391003403d04500c208060f407541c0310080000c80f047c6d40da60240031001c004c15001484945c02802040ea41c28900400900004540c0000e44114030880c000c41c1c1c65041c0310085a040b120720b00c84160300041d002d0011030b892041a00d40c80304103c1080041072550410790000c0a05a615030480885180100c0f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 177921447 1250 177920197 177920201
    0x7020303070f0b2d010e18010c02030909010b28030b130c020c03060702071509031a011a040b0f07080c0609160e040b070f050c03030c131202130b0d0501020f0d 70
    0x100395240d43c03c0c0600c08070a80c503d0340c0001d80c1d065881c010300780b071020741c1c4801d003c900c1c0030f4000e1f040e40030560811005440440c0c0100080144210a561081c02d60380c817a20036014611031103502964010103a41204102140e04800c00803c01c00b518000c955081002c1c0040c00028540401d420065503860005052580401181c0080781041e00500301e03920b49454043d40302c60700e030b12034410074640d1418141160b5102d841014007666120000b03c60318050741c41c240310001024001d8054012800c13015135500c44210701500c017214500008a0b01e0b2020140041303056030042503007203403901d0080c03080000f000014005280308007580700080c44002c00c00001c2c5642e614450b88285030720100107044c040411400c040b45680200241000108481650350817a207034451583c40310482d0102005000849124a0091000c80ca0315203030b07a42640d85651041b5046d4544040095015200d0103885400e1051500506100040103007104901401a200c40e400c0e070380100402140301000040b803101424040c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 177922697 1250 177921447 177921481
    0x5031005180105100509030102040e0906010807031205090105120406091506030f0803040219030302070e010b16022b0f0c060801060f080417070503030f0c03060f0607020303070f0b 79
    0x1115690104690307000c0000d81d000c41801418092401490480b040b58042d10440700102c0f40a00210343e2642d8070740154506400541c1c1e1100aca00441000188209001401005a0b50040f50b242d4800560700c800b9a44c5510003000603040c8417080c041500c0100004000b1740c41180180c5000c20000d00902e40003d0081a98107840e500d0780c0341c00010f002203900c0501c1030300030f9580b120006542e07451740c4c00002c0304500070b84100306100041d481e01108142c0c2c0450351404a4a0140a40600f81d17216400321040c1d028021104d01c00b40346011a2101618111040c092030682000f501585440c00140c003e0014480440545104204000c00c03020000c5100e00403001308004c3c5040f2a140d410020014580b44401480804025000000c10144480d406000c0306040b0340c00d00d4641d0740d00c80e61400f00d441c0e4200311400c4c0e0880342404000348480710080e003124401e24004140c00c500350a050208006508050400d9070548824000702d0000b850329101413250a0086803c64514941041d0500080c804 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 177923947 1250 177922697 177922699
    0x206150303130909020d050105090a030e01021c1209140307021206060109030b0405031204031e030c05220e0106030615090f090c0e1e18040209040b0c070c0605031005 73
    0x420000e1000061420040c5803ea0700b02d0403000c10410340d1800000c0ca01512048003074160b51801c002e10042d51000a81411100e109803241654290001c0040e030311350010811031100204d410400200581c4039820056411150410000700200aa03e910001041811074481140e00c005a000d0561921110340c2c550041840c004051034588000000e0880e25039110040030407090300042806c020041c42900c000c64a5034109512928082c1002811410388041c1140b10440013008c103008284203000d906061403054645928100f144d0700500600d51000941c05144c00c1120804519002c0407120a4000d103841e0f03402040607418031840c024031010152640c0180010b40c003080001c00440c60084086440000d000104484035074801c2e43c3d90702d48a04426030044500d4840520180f4071006280f6205043c0c441d41054000705801d201071400554000c4e5001a40400003000500d200c6001036000101c05902820060700c0d0341c9a40c44d1086540100001c1440402000560003001103068001c02e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 177925197 1250 177923947 177923953
    0x21010503100e0c0910121a01080102090a1401020a0f05030d05160c0809040b03060a09060f0b0102100216080406050301030b0a0606050901030b21060610020a02010f18090c02061503 79
    0x10214500c550f550070341c030f00e02c540184411000101d181c2841d02204000b4000280d0016000b07460b0b160900c0302c844070501d013802820104002040021051003a50250326001d00341c2e214503800c2540340e00c140b040c058031540c118411400d0050000b1580c0c20080c103450f00c11401584c8074098101040c003990b40052826504011804400030300c1607010b001c40e284c8a400040c025902c841c24804500603140c12680701e0b8151094509004400c007882d0700c03404600740218803c21560b03008601002c01c0c0d07a603420f80700d40144d02c03090041c1c00f0107001360300402102c01c0c80c0e4400c0c0759021441d0384180391500f01c0d40c0240041100800104180003c440c0800d6012569140c01c005e15818218040c01501440c400315040507603640c52038020f40c5404200d0355451540c44580b240d242c420000c01c0c0e6440038116100e602030245100740a01c40d80c00020a0350b00c2c240c3c16100c42082d100050411a682001080d01c040e00003080100050080b402d0320410081d03111030383c00b400041c0780c50007030001106e19404000d030182e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 177926447 1250 177925197 177925211
    0x2104060e0307081e091f0309140609011109010e1c0c06020a03020715090e090c04050112140c0a0b070606051804031e080a0e01020c011b08070c0b06090405032101050310 74
    0xd5200000d01900b800021010f11b28015180780450042c072011000401c102000f06141d01034450004006100e210300800078400340d070203e54480c000d4001c1d08412800300ccc132074041a000900d40003507030502d1b0410748916070364800140d84a2010111560b4030160141c3c00140e1a40c003410b40c180b0890000d090f518200f04420041c0c900000e141026034031a0060a41c031000128550f0340c2c0c1800800c0e000040100f0503c40340d42c60b02003030b12214945601c00c0328400c000002c3d486003803401068408000c00001c0c4645481468191000340d6a072000204603071450b603e04010400c0e41d200c081105100881c01c60000b06403410703260140c103402818000b4400c0720b8a1280130407502d03a01502044d030203034030780300c0110360415803900450180c0500f4580003265400c00c0300441d40303445043e40c0c40c8641c4805507101003607a04d4070305095031000d403451005842d41e200c0000180d0349051114a0a810501c24800c8034540400b10203032202c06a04d642d804414034460b43d0040095280800c8284060485200e00b084a6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 177927697 1250 177926447 177926449
    0xb03010308041a070209180d0810050d1401020d05010f06020f060703180209041202061f03030503100e10060e012d050403020603010b03060a0b2104060e0307081e09 72
    0x940203e00c074a00d014040100c0d10a2408581d006485040354098910761281c108808111650000c94a44100521849100c0803206101e03c0c40303079000c0c4007400550f42e10603003008240540842c1c294002d543c010040644403070b00e600701744010200c3c06450321000465504002d400240032420f640428110750014614468040c1c0108415811041d107003400a42c202c8160025429401d60000107075010701d4810810040c40181c00500e25101083e40c2a1106940c4101e08100042803440407030810042c58182400000d00070b50040d40c0042641415000341d9a60343d0300f12140c8002161088546440c0c81d00802203160402c860324030030042404c0100150340800380d0f80c40102c5101180180340040c2a058080a5010b0320444000e150050403a070343d1382d80c59000c40c403219401983e605000380001300300024010130b5039041c1c40800c82660301340710095400ca2105c505030782000d4070a40300141ea03505813130718141041005110380d070311580c45c26454003032030115410340001c03009000c42c06500402810380b003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 177928947 1250 177927697 177927713
    0x1009080607030e0c03030a030f06050414040303090606090f0c020d05090609060915070506090601080607091e0b0c070303030623010c0501150e040b060a0b030c160b01030b100b030103 80
    0x1c881c0181c6400580440c81c81c5400d4940b85034003201a8240c00001030b210001c961540101000c0001307007d0502c0780c00d07074880a11045500800700c1d255a00e400002040010f0321940001444a008110104400740c07154800021140e00151410380359607101c0c0150103041d01031248101c0c203000c0342440c0f0f08200b00240416845d110f82c0641e030384211400500b1052076079850b114100303250000c0814a4444080c0c0c9000ca6440741e095440c40224410799000094800001403424490f0401d6610101400d01c0d2505159244428801c1100756060008002c50702c507080350041c28111a60400a0a00920310309014044500c41e0300040180e0006201c8580e4246104403a640c04010a10342241900007609240b0300610792030f03400d00e5019041400c00a06da0b0035840c011405940a441c4050b035a4441004020304501c0c2c501c00c10a0040c81400040e040d1020031025085149903004c140340d0f5070356199182403000e030090b00120340c00002d83c2c050050903040c813074000018203a00300d0000d107554115225545 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 177930197 1250 177928947 177928951
    0x712150c02070b0c031c0207051b031e01090f08040f0e0c0a0c0f1a0109050c031302040c11010e030408010506010f0206010311060d0903031b2f0f160510090806 70
    0x21250f800000c6071020440200219201c0d03645140c90070040c0550301040c80e000e98001c45040c0c90b036205441d0300c0a0001c0c100c014410032040014000c11040c1c5402c04000795150b500400b5818555a901c40300e40400d4000d12895101c62240c82c0c080d03510b03418100c0350700c08803a150300940340c105802c3e0100600c420303542044800310612418000c0c0c010030f2924002e5203009051800800840d18810001401040d45203200d042c1e0705800000e110079a95042a8074407030008a8034001800001c420101c007508007503020010458207860086d0b030300000101c141c0d0075a10310144c8407005500005040100c60000c1c40351a400c81e90910b0b102c000e20b00802c80095982d50f06010140c040917594a03407020a80c1c6000483c1c00c000700400c0203008411140c00c000e00280450315503540c540c0004200e43c2241846090650b400c040b460341d8694440d005c06014582407500e00c4c001c001144516a01052900800c1211100806a6070745080c10302d818442407141e0445410020701c14090060343c02d010322000803c60796 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 177931447 1250 177930197 177930209
    0x10c030c12110f0706020702010e010e130905071508040605010501020a0803150d060e0109050c220b0d1b0311010305160f02070510020c0a080c030a02100e030712150c0207 75
    0x3007645126071500032414441d00c0d03d0500c1849001404904001d030075005040c00c00e0003600d17240300080c0e07014010341d900d801060225501c045a155141c6030b010042c0c0c80b600c801409a0100c45d140341d25001c4904800c1b40448030800801c105e40700304010080c032405505c0c05040c081c4050a5094403940c1e03a0007503800301420720100c840c123521000f00b00340c4407152685d26441d001401032060108142c4243c5c000c00c82c1103400c0e1214020b0000001080c1880d0b01842024a0a00c60080900038070304400801030900450203a03000f0002c080101c041544241604019a0400c1c1448107561039031034024580d40001c1c5807541450f0506081040d00341d4413859001c80c0d80b4076801c090f040702c480420701f01d09002c0c0f81c0c0c00165004141ca00c0347c0000f1607002401403000342c0c0c1a00e280351031a840d4a081e40d5502400d240c0e095150b4050038000e0010304201c4000c030f200705440c0c10010080d114280000b8108207854101c1c803000d40d6074406c81300034425024822840156095801c009540c1100c03002916040b190043c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 177932697 1250 177931447 177931451
    0xe01200a050a18030b07170403020c0d1e050c1008071b050c030604050106051c0c050d0c0906090b04180b010317040f120309060f08010e19090f05010c030c12 69
    0x2121030040a0755154408120f03000d180c0141c9a1600c07501c0c41c4001d40f00c00c1c0024100510400200e54141d10260045030903070001c1c003072210071500700140402190401c458540e44201c03880c6010a010643c0c4810341d20550142181404544c18400d000d10000c414104002c00c03901030003040303500322488640c0c000801ca8103854960803420a207107020b19154840f81c0511803841000b051003011340c020415071384200d41d980051720316500b6603518008184000f03040078802c25001c02980c40c00840003244140301b0a484101c1958443c1c11004070754080c0e01c19402c05460f044118400c1c6070512036040010500b5070824401f141989411078001d005010045c418551034008000c4600300b00c080d039000b405400d02c04490a601c4504050035066081021000b041c80a1030100b4218043c0c90301010795586980c522502ea0f2800000f0400d54002070524030601540312985000d21f1154014546040d000d031202c2c4e156010149461400c45191440420405181060080e0740ca40d011702a111044a01440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 177933947 1250 177932697 177932707
    0x15030c0203160b040303111801020c190e072732091b0a021501050a0308030f06040902100201020a0e09090a02090603070509041a0f0f010b16060f0e01200a05 69
    0x6c0c1c0007071420100e028a800b0000c10520703d441081c2c405000ba200b4203130701350303104104c80c203090051807403031155481c58081d0728210a210507000807007071f15030004840c600032010a10b4115031071030000c242403425152041c045c2c0140b000404e10b0103d40c02060294655642c2d800d8031184180910301000452441007110b400403400c4501d0140072508400c140b80550f40e550601c0400c0039503108400d00042000c036402000004036413800411103011070740c104038181c0c650360303803540c0f80c0c2c18100c0d00820286d17000baa10020b032405603c580c0110b03045054180c000681d5689050720282c40c800e030350010980b0400b03c07501002082c03000800c2d54545294140ca004182d41c48040c00241440f015400c00d9030401001c80c100018080068503017200e1107100c81c9032481a484d40c0341d01540d1440101e949101e00d00b84c1d40010070034000c200c0010103003610039900e0081c4a120320307503503101910b0b100b041400c0425107070f028451040d20280314bc040b019030700541926005150480c1002c25025a0105400344540890 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 177935197 1250 177933947 177933953
    0x6070201090e1b0f0a021009050309091e010f0e0a06061e050d11040e07080421050d05150406080303090c0405090708011b030506030d0801031b0b0415030c0203160b04 73
    0x1410070140e4160040c3c00e91942800c001c980d40507003001c10038100501c100c102140c0050304510403406060b40100155152451000a00c80c400002800400d00c14104030035104507000c0d0361450301d001c0c0580e400c4c124070081c54507042d00855000238140c0c44d103c1d03141c503204028580d00610301d507401800500400c4511211a1800e440b94000c003000042141d0800e6110f440c0d580e4191b00800a80303c4000d40003005071950b070070485003a042202c4c0140f0003071032010b109002c1403081140c0d1114003494070300704e031910300740b00d038420300360341040d05c68400c040307141d482480081c03400d8080c10340a000c03190015070440c6000c0c4d8100350366130052049140a10350b200c0204003001c1e81404490040c1c01c40c1c80084c0001d20b680a0762441c8040155054800039280a01103600c9160204d80c0b019003514070b9440c41034503429900e815074180100054001e80d104c50100c00100c180c103040240004210b1002c010000204190004d400d490103a4030400441d0020000200d540c1a00c41c2a030342103641019004d072060384e85203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 177936447 1250 177935197 177935221
    0xd12050a0207020a08010203060406060c0c0504020d0905100b030d02150c03040303020912101b08070e120109050f0d020c010206010b0c0115290a0c2006030708100506070201090e 78
    0x440060342044d0704070700c0850485815001180141d030107807810803626540da0b208540c400d02201005010944002040189207403a802a01e20701b424803030001003140165440c0d501c1e00d00700722891011075032600e1b04440340d458140700070b030400c1d030007400a4840041c01841d6040e0b000c40042424480d08404800700e400d06110b9816241101005084031059560100010341c0e9241c60840c011b200c203040c80202c221101c1c90101d10507280c0c0c42c0303888440c3c481d151940141c54a01980310707403030b4126503403001300c90240742d007401101515802040500101288501c0e524142113a233810b003019544100a0a405664001109411200c0381c840b1151034200350f135510350252010343c8078900351081801e0049262411610710b121012040c07802c0c4544015401c0d8410f1550040a1003000450202030101c80414280c190b101c1480501c0341040c008400d0307280002e00c1c00c2d081a51000002442441000202c0030603609070301c00341c0340131030700a0704042c0c407603000802407a2680a01e4416102550100e10381011207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 177937697 1250 177936447 177936457
    0x6051c030c0c1511010606030b06070807020409060515040b03010207030e150f120105040b01110c0d0503070b0703020702031b0d12020c0307080c031510091d01050703020301030605090d12050a02 85
    0x80f000408160f40c21000041400d0222400ca511a510b030090001d00c1c18042e12441c0c54590b030103410b0505290f096140c890064121400580c0c0064559100f8400035a507445080d10600352025000c007402141d409100855424882c1f242c0640c1c81001200007180d0030540082030071400701d03440300e14401020791419050180719244d812700c3d04045280913070707000706660482c16520b0541c1d08000080c085401100c84220031010201584c00c2858210000d003884107283e003101d4000c4e0202c0380b5080c03069031007008444c4c8c203d40d80400030f640801d42e0b50852030144980c1d80340342440c00f40300102d07035119000203541b40b00c1d03648001e1517200b607139551b000d10500078020400041c000030160f415040d40c0c1d4010603100c20010170342c40d20a005201070b00320759054044005000d4060310f40b44840f100d08080c441802049250303050381a800c000c0307441d003401e42c909002d241e10a0510782c0d409604c07545545040d100fa941c01600b50209500034146141189901000000c0100807841e0080b0b1107466418441d8028450 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 177938947 1250 177937697 177937709
    0xa0504021e03090606010e030a0b070f140c03031503060903120a14090616020d020307080f120709031a0106050307230f0315010504030c0b030403050d050103060f06051c030c0c 77
    0x408820045a4640840d0807071041700c081e01c0301d940c44c034042010951507403042000284500d00d0100401c40c1584115884c6404504600b0300055402d01d18104150b150000700701c03d005a44000b0400c910b1400c2d03041c0c2036442d07200660050070141407000784103441303010b1801c41c865060351900015040301990b0b044100d1b803003001c00740303292242442c218241c0c4844003141c84020007144440b410110500c00508003944080c268040c42c1004165501c00c1050341c095031100501100c1480780045072515058424001c211036210b4580c0c15140d031510000d407846200d41c20801c90100001017064076044021030750f2011140c41d101900c058203500700046d0190711221040c1100000c16481c400340d10b183c0046028108030840c405052002c0001120349114500000f015500380ca002000046405400b56821030720a0034100c0c00d0008604042c021550309900c1a951242ca5512650780c004141c400c00001e0310040c1c5290b110b072540052840c0c101440b0190007800c11280c0d41c1c180090040cc54860006000303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 177940197 1250 177938947 177939007
    0x60e0c0a0513030b07030c050a0e0d1a0f040318050901030204051b030c1c06030f021e040203131104060509011502030705100c172809020d032604020a050402 69
    0x3840c2e0610005042040301c2c0c00700860300c0d03c844401f0041c01207096900e5040950b03035500d01c9410140034002e0304000807104840b08048054001002c1d440300c0003145c400c850300c0340302800502d41410300a1003210340c2c886034139040001741428481038643e44041410343e601036801007015203901b4007003c603145105114000411000c01806141000f9a00034600d001204101505116050000344100c43d400d1000030300c5000401012401800e1514001d21450103401882d056861880c001c901660b00c2101c0d1000ca0280c625469000c20041019581c0185030594007000280e00300360210380405018046c0040350a550071300030450a01c20000c440c05194000c040d984c00745c02c03c003900009000840d03a5500071509407281c2c19440ca42210f082031041040031512120f103d00c2400c0c0f410a003080340441c021440d01c1c0c0a4460158881c4420080114401c1ea01c501d0518080300e00080500c3c20f181060145007125030520015a5a00910307400351101110010399521103505401008400d00010100d040c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 177941447 1250 177940197 177940199
    0xc0309040b01120c200102120f0c040305070303020717030306030c010e040902060d0207020a051002030a0c03090e040c030302060603030405010903080a0302160503030915040305190908010f02130801060e0c0a0513 93
    0x25601c0668110000700e0302500100c20b0113070440186c240d0290446680e144504000000c0110028004072a00010703a10308207441c180e02c9845860400c0c0c019007098015030b116a00800c0141086501a060114504080c50440c01c007000000e403030f10a09400c0c9410020b061510841540c3d440e80074444c1140d0042109035241e10354030052005c2e40080101f0307803003050740c0d00d00010181051050300400c443c05902075031070b1001400040d680c0019203070b4140c040041e083e5003c03034001200c01c40366008502074450030004034614a0700900c1d0580041c034a6000b60810f010810450b600702c4170b954166a404180c26444401c9075904500038003418142c500e0b00c4024003184824041c002c0b00441c0a40b030300c801034596007100401c03404412503041d60010001581004045010358a41c80f403484002041d1406d1070504c7c0e0f07111f0342d16003540c29940352001c1031a800150710941040ea00d18102c010301c0315000901040d4a0200203c0405000402a0559110006039940c07140d10850484c0c2800948401100f40070f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 177942697 1250 177941447 177941471
    0x60807031b0e03120c0c19030503040b070c120302030304060e122709040c090c0201020403030e06070501060b0f040f0e04020a230303040b04090b04060e0a0b010309052e020c0309040b0112 82
    0x2e071b10701d02209000710101060b100011002c00c1d2088141c3e0b801c40300030352819181c9a103860255204100a031a007442819001c1807824001081e404a14000d44c0211384a0400b810881e00f181d0344040c84405540c4410440d0035034846050542c2c1049416410042210300d0320202400139041c20f5407415808005075041008000140e4941c80c180e88501904100707400003800140c0c203c0c0310b2800054003040817032900800d203241c00c030700918203070344a000041210b0366503120720f141c280c000060f80e80e015000030a05209005408604500411840000011908280d00495150080c9005096003071000060310518017184800c51158840c026080303940c0c072990380e00c02c2c1d48a0341080c003c5004a6040141081c4c4a00e010300401084c0c1c0c2844450b02229100d01000000614010f01c42605042c0c5900105010913002d014100c40d484010301203462503031081d40c1c04400b9280f50b0141c2c41d5414418001413050000c008140c41c000c05042e10001600c00c400001610f4140005011900e041c1c1880e82408035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 177943947 1250 177942697 177942703
    0x603091506241409060a0c170306031b0603130203150405010f0507020a0c090513061505180907091503080a110721060504080f030907060807031b0e03120c 68
    0x2603002401201c2c00c036000903812540c1c402e0310003c1e41081c42040c0040262840d100d0300a0918015604120460050541d2130010b090806000061350380c00100421400e414140400f06d66060315043c41c1ca6459182000240c0e640009000c0f1807403107916082440440d1000c1168880d4a100940543c10910b054909240a0445041c030480309600741004600324138000240b1400f1644d00c0038070144850706000c14503004010040c0302241010f101c011510100e074140c40f030702110304424135262800c1e074200028400002c0308100005440340802c1c1c00c2010320000890b0500948034400c03000704420215054514504009403c0640440000100e003060160008206110f035484601680c0c15a0340d64036011841341100440010600c11444420001030007a03880164418440d800007400c040b0711000c8484d035030f08116101c86241d880b0000a0040b10b420210701607010440740750a2100450b040710141550205402074000e024107800d400d5040e9400340064070607042d10f05400c9465444115205903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 177945197 1250 177943947 177943979
    0x6040f050c1806030d0c020f01030f0204051903020a0b040605030a020c0703120f090b1e1308120a0314130303052e0e1617190f0603020f0f09010603091506 68
    0x81301c1c1c403418010801150181d141d02d11051f400410038980c0c140c0311030040d0081c105032048050360030380c20000030525030b0300d0092407807a2900c000441021181035106000080d80315801c42a58468240001c02159074440201c03030f40070310383c4a4056203929104014610300050f540006280c80c0c1403091004138640c0c48022001d0302c1d4402d607292420a07039203441c04005445054030644000e0501149880e02001e2a4021310081045103c40b0784030b203030f4500240d424207040c10302340300000c1c100013904941160b040c01404090381161036003100d00c0c100030713081c14100c1c00318401c02001c0c1a00e4100040340c0300081c0308508002e058803180c100c440301d2a00d90640d1010f20340d000310b94180420202040a0520050650034681030329240c010f0384190001c1e43d0b1410106c0201000003802010350380072101a554010602005885680898428250f1041200d054414103c00c0d020340e82030880c0c000190713a814042c5044400c9420000f40d44c41c064140301d5520220201e5401195051400000340c044401514203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 177946447 1250 177945197 177945199
    0x309010f0605030c100905060412031713020d03030b0409080301091a091f0306022a0d020d0e0103271208040b040809040e06100303020106061106040f050c1806 70
    0x503001810400c601190214010142c050b0301070080030403030b4208015441c4800c500c80c14911a155a200300240c07040e403154100d03114100c5640341c00000c054014062890028441c4502c3d8601c0c0f81480b0300703d00000d0b542c0c0380a4401c603600d5003c9403d041c00b95004c10001100500f0a010f0a446803e016038641c2c0203200d10b0307100b2480c01d44400b900c501c003407281d20b0031030700700620a85803601d82040c41c009806213140d06c41c200011200c00040002c005100030401240c400e11802900c1420510b2007030143e640e02e02c100b540d50401600850310540c0842c03100142c40450070210740c11203c45004038014040c20104041c01030344900c2460700b90035010030040c522803041e1064418190642022030b2080d5040d1001030101e80800c01050000e80410003521081a0180000810b500380352101c92405609542000c0700c00070112051090690a01455014000d981402001ea07802e1a01c02e580c3c45500400140c9003440b54010201000001e0100c2107440c64010101d08002a0030362800e800b4140a032002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 177947697 1250 177946447 177946451
    0x60304031b03020f10090c0504020f091003140105010804080730020102090420030403080405030f030f090705030718050c0d02030c1201050a03020607030302070302161706010e130f17040902030901 86
    0x8080210300d800341c1b141c4143d1080c142c01540d0f00d8842440041d402242e113000c20000305105d041d04036211600454041c10b040ea402043310420000e80000c55071041c2c000a040043c550200070201d24031a04070783c8000d80c4442198040e6480c014124540c80d03a6110a0303603010480c1520224450341500a4881c000c0d04603010040302580344c84042c400c07040390f07071140c08840042c000500424024400c031f42c2d0280c0034005691411840e6040c2903026030040741d000340d541401c00240204501708001440c003504003038004041c1e05003482d80d00083c0701c810400813808130b900c58000815031941402a15042911a1025512030402c0c1144002e1a0000852244642007100000400b480c20294003c11a50041d10031841c1c11125202107002c1d6001c01000e60035407051820b0704021140840405004018a03040031101020145402c1d05202069100401c1c459810080c44505119043c82c0c0080903440036a02160200900d0300c003540e140000c2c681400c000303010a00250503406600110f114001100003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 177948947 1250 177947697 177947713
    0x5070b0a110a0c170304030204091a06120606150405090412081f03030804080702031005061008040209010b1e1204060c02032d12180106050109030b06060304031b03020f 74
    0x15059071414110b41c0981107880703111081245520141c2d00e040501c142e88150381c074190705c03a0080340030388050a01c11558040c00d5490041c842c4070140481750000d4045a10351744584608071602c0d0380d03642c0a402107220764128a9090b60462a203803c4800600d0050402d0f2400c0c0390500388021104035034800b80001c5540c1c803000800c40c040c284d0010402c288101c104101c00c034219141241d0121009001f29500c400411229015175020403202c09410080103001c20b0615010342031003084502d00f04040117102100c0706001c0140d6480b890355042d0786085410781d0729014420390032280b82407500b410143c9000300240c4030000354809c9000c43d00c0781e8065034081c081f601d40c03404100c4e40c80c400c50a15103e0000901c0f98070f581d400c4510b0324100d15815004400d404d01d145c2c60600303400e000007528200c9a030b440e02c10702c254400b00203005e40030042a0900b410300352146117403100c801440d0004c184910500c0004000307000c250042011141f45442030302c03054001029442d0180d505c51a01030001950b2140ba02 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 177950197 1250 177948947 177948977
    0x5060406050709080303040318080124061d0904060b09071116060203090f0f03101e060e010911040306050408030f160203090d020301180b01170d140a020a05070b0a 72
    0x30f04040340c036004011031070340d0340301d4030100c40c0d024809185070072400100500181c0c0034800d024213404003081c100c04000c40fa217101c0c201e801c1c0184c0b540c005400e01084004004000c0d03140421803004110944503801e0598880c5041001030510078089239100e1090810300540c96809841d14042c4207070003088610014501c01c0c0300c041121188a1000181c0c030030041008141810460305d08401000b40080803110103240000c0d052807114030780201030503174602000d0300f1451200122954480395400400826007030501140c0d0019050180c80f4804c1d8641402074040e4046600320750046070801c10400030b50409140c00b015030390094034040031040700d50300030694000400001c000d05800f0307034000310316102110060210300005000e050f81d05568961949141d0551507003032401d12841003024910790341c1002012401405050440700d8954010f1032a0040c0d00c0d04110000100014511820b0b1035101d072100480c509034030028000c02c203005180c000070768107584001a000300e10350f6440312404090400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 177951447 1250 177950197 177950207
    0x120703030e01170402300309010801090b06041e0b040b070201020f01050906130212060126150a0509100c050a030609151a040b07051c0e15031e04050604060507 70
    0x20242400d101c00c1c2c1c0f003c14014900b8480e0742c89078180c00d00554040086081e14000030064a540840704c541001a8460403503a00c83c61142c05008600410043c0000e040040741440c001d50241858100e4480d004003003014100c038441c030040c4403020107142c0d41e0b500d409507900c594000c0c0c84201e002d44a0300c9401103402c0c2040c0203d500c65610b0000a214a030b1f280c881540d41c040e440f82d03051303130400c441646183d4142d4042c400315000e031881817413501d043c005500e03116080103c1c20000d029550003140ca141168401511400e801012140003c20551034210f46c1c076051503030000099080e14503102070310320419000005021146000c0c0c80c1088156626010482a144921440c050404401070309001c007403d040030120160502080305d0b41000c2d103404001388282d100c064140e076a0f50102c070341d12802d9110344002040c1d0b850540b0300034044d025031001098081b001c84d4609110781c00701100086803100003643c011500c00e2926207411366800c0900703210f5101d182c16181500c583d03083c200000c8081d80a5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 177952697 1250 177951447 177951467
    0x30503132112121103010f08060c03070e010f0905041503140102070f060f090c0f03050d05191d0d03170c03190207061b05130f060203070201050c0309120703030e01 72
    0xc02200c203081884044129915030811030003204483c0d0341e94404c0030f050300d988080e41c060aa20300b0410b200900b000d000740d28000000f000000034640420030403480c1d66000b00c08249414082c07c24000c1c1c1a02000700b0b5403803e4068010907005883c01080e0401802c0c0000080200c1b4040c00c1415000504041201c0c20b0b8490b0b102c028001d606031001d441c00059860f03020540d100814080064020895601c400c0d00041590006040c1c0000700c000303100340701041c0940441c020440c01d0061800c2112001d60000c140740da1852024004007840d2141103894040601c0281400181030000301c0d0841e10740982002d03800360203080a002844000380d808050a4200c07401034a100c4480d0b005113b408501b400a9400b034242203c1954848508040010207450700006154494403103d0f11050741404284003521142d00c0702d2030342502c0c0c1c241040703a82d802200326a812502880c0203035460138220300b420315501c120110b40303400c844442c5101c03072007020215104060b41d02c84d40d11000d0360704044004546662078 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 177953947 1250 177952697 177952703
    0x30c0c080d0c081623070b0108030c010f0b0108040201050901090312020d0201110a17190203010e18010b060319061a0c0f03040302090105040c020f0109080a0e0312070b070203040305031321 83
    0x1041c5030005d204510310146203204004d460b45898401d8544e9001e0485200b83c1c4525aa90300c041103a800c40002070082400001400808100420342840005c2100c42c0c00303000070f8140080064039180507449080140040e41e007000120074080c80c01c0000954a01551344104015440c00040f4040c2c102c60204807002c240065030751810b2420694074403100c11501910011060bd01d01c2c0c44560a500746002940c002c1c501c01a104e20980341c0380c04440c400d405900c1c6c0c840210f901d4038048103507560314a03082d20382116406101c0c10020461030504002401540c110300411914441c0e00c0305203074218002000481c4d22801521090740503100d5582c0c1e680120700009500c0028600140311600f00303907101e040110864411030300d8078240c01c460ad41c2180e01110040d1211200021003040c900c1c0c004807190310481c0c041d03008100804442d0302021080c010580000c101e44c9009004c502c242d807081081da070145800c1020303642d0310642c1c2d203807000016580d403040c0019440b00e00d1010546516130214100340d00c0d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 177955197 1250 177953947 177953957
    0x501090503071d0c040f09092a03030305060607020306130c0e010e0c0d0b060a030603120c03020a1e02030f030c060c04051003050a0f022a010b060703030c0c080d0c0816 74
    0x650400444407400d0700422a600442e801d1100003044071000e046a00245444540010414447d00b0203249800305041440d00c4104000c0610b0355502706c0c20804005c9030b801d40780024841e210300000416610420324040d5141c400e40c4103200107100101c54190300c0a22800c01c20380816034560020181010074070481c040600c501e00081c0f01a64064002c01d0411341840303000a0b100750030b60026040e034014090410000380e40314024010841810648441c81c4580d06183c40502020f603802543c13101a00300060a164440301454010f074002c64005010540c0201524405241801036030744d6900f09407410040c138492080811171215000c0210b0341030350b8018000d521440c00404058002d80303c06454514026034400303207503042c56141d01c041c00c402d840c024605104040103200506c0130501c00381c28030f41c29901d000d40703040b09591140119250581e05083c0840c03542ca9480091781d480d5003400e00039050100000b500c0c0d05850039039200d000501015280d0003040c2d240c01c01001e05d40641c004e540c1c00455 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 177956447 1250 177955197 177955229
    0x903020d08070c060e0c130e0d1b02030102031608010f0308091002070905131104270501090203011506021608120c03040302060a032009031b030322050109050307 71
    0x14070811815501200a0038404070045a60b03444108440344503041d902250422800c00102d40b5140c0300c164954084550240948610200d0094989603030340003030700c2407018200e10300b07401c22003c001c22004140c0080086403079280202c13800c2c01642c00e030808040055034803c0081036460b1940d010354203490300050014108003d050074071101a1102d0502c41c150300c03c0c060000b6006256003d07042c442d4a0007030015025000600d41064000088560306115505111000b4038032108003007800c500034086201e030f4040302c2c444c0c14202c1c0144404803020f509542003043e0891285040581c107001c94a42e035003220010082042451440d089034040c1e1000354010b0610280c0c11040c40c0702900310091036105a901e4696240d0004109034071950841d4007180d120808095803203a01610103041d40c001ba0101c500d055885000242c4031064081d08105040c02280c6600842c0c4080003502c0c41100b02d101c90303c0840310030303526442c80300c10b051086d02d00007600d540c0080317047d05012902d081210200c3e20b000c8854 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 177957697 1250 177956447 177956473
    0x80703021002100e0d090906081018060504030e0907030b180709080f1e0f0a030f2606030d020f03192615060702060d0f0b0a0314010f090302 62
    0x8011048003207411481007107003007000040140f01d4007450b41521001084200500c140140c0703000050f510122900d840c04100b0084d071200403c490001e03901400c40090044582011495008070140004d0000c51810040004140d0003040d101400103084030300c010310766607509040b0107032581108065049007002181c4080c500904d040560000400d042015495458100203450102904d14008159001c0c54010700344c9181020901e426046180152450b1402c103100c42c1e55800007044010100850000e041c401144200c0001d0703981d002c091040344a042e0642035040803020103a4000e4402c0c050042c1a450007070000540b40000c5050b04080e50070040d900004111000b010317400741c41807041100d604103200c0c40b580704010614409008101c82418403100c0800c5c403080c151300280c0100c2c0e080040902681e1800280c0d48000400b90340807560a0302d40c000c110240c914115800d0300070b42d00d44004010071502d000e41482c0608401c000b04100d5410032141000c3d984140005005600000e000c070302c2e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 177958947 1250 177957697 177957709
    0x1203090b180405090705031002070c0f081c0302040f080d092306090f0d050a0611040f0312020109050313030506060a0e040803090c03100e06060d05070b0c1f050106120608070302 78
    0x4030403449016115003e560f0346c0420300380045800610802540020319000b0807448540070806030000d4840c4510fa80d00301201a0b40c2c0e0503032400440281458960b103500050f10940444010340402010040f00036503c40780700b0365801c0010340840c0880c00d07001c80412a052006040307960328100c112a24910480241400407907880000c006411224850036140c26440b50980544c51911410041c82001c0441c1002011074419840e80c1c11034a4081008100e040d8802071158107407a081003088160940150080c0d0042c400381c070b001400c1d80000314103c1600b45016540341e0450f4000c2042d50303c9035075640100244013036140109100100000d0104002c207c04038003540e030140c0703203900301c603120b56015000a10b0100e02c881540b810940720141044c2c070381c800f4014503404c00001e5440343e42119165441e591191424001c0000d00c010114207042c05600410540e00300c070302c1c1796102140c115621091a000f510702401610080703103281c1880c1001840c94410030040b51000e1000c2c0003200e086508001c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 177960197 1250 177958947 177958951
    0x7020c040e070317070512070b0a020d0b090c0a170c04060c0302030d06080102070309050f0a050f0a0302060309010b01030e2806020d1a040b0406050306040f060212011203090b180405 80
    0x1c151103014004000907580020b107020202016400c29254a22841d0003480c1c44111405084051018406a40015807104400e904a40505000358a8049180320310380205510703642c40740d20406400074042c007210124010141002c2c00d40d80c180e0641201740b902c160b440003e46c1c080e41da0603006c200c02c12407144a000a4081544a441501d1400108a4842054904030b0f0418071a5940c0008c50320201600609190001c20040d03498000c205003820004452003002d20039a40a80413214403418995115a030000140d5401032a640c1c40f4200054482c1c0202000d02c01c0038013091400d4002540f41134000303509206810107254058072203d00c540400407028200b038040359070503000d000040044107036018a85e03803140b40005184600b4501d00400c42540c2c07034655441d024600c0c0460034001d030b80300403404c56031082d00090950f20501991030180024030942c0c9100040c00b80c000000300f0b01d00001fa0303044030254003e6549150f46a150700b41b03043d5038881e10601c02c1307200e060f10a00c580241040c0d006a5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 177961447 1250 177960197 177960221
    0x30c15030105042a050a02061006080a0b0a0b0f030906151509010903080a031406010816080c16050d08100b03270d0c021206040b060613080a0305040302010f030507020c04 75
    0x21344000d603100041c200c60300410400c040865000300c1c0e00824650704000706036100c6104a030309a003061401c840505501c1010b00215041526007080c0381203600e483c501d5000800c003d0440968400200d040e01d000d58005650741001801044045410100c490b11007685001c4003c0c83d940c008048902c40c840103500008c40941407104c1164000041003d4201400748801c954902069203c196031903014140c81c000c0546040c85000d03810300988805200722a1001589820844103503290001c3c0d01040303010751101d070814030035543c010b282005808540420750b02c2c000d85a070021603d60000b524003c4807140915612180300380005941c8681d0341d81402041565512820300405901c5035450610200a9003030002c16005002d12007141400e01140241704410409000d150516503259100c0c900003070041c501c284030210312603545100c01c1c0140c000804551045928600a6140c00b4203103411038401a80030944400b0000f08144c024001c2610481e607560142c855680988100030050a0400441c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 177962697 1250 177961447 177961481
    0x307020c0901030303051e0408040b0705011404060b09070203090d021012060e010614070b04060b0111010603060f051302180c0d060902090301060b040609030206070f06090b06030c1503010504 84
    0x20040ca600c070346510601a500964000c40c080c60700000f45000c1200301440014050040ea08100105030a403055405981d00000c42c07550703c00c1c903030404601420028041c003072500301c880240010480340d54040c04801400b030707501c129541e90310b40c8241c2e100e010720411035402070801200100145070000010016124a0411901c203094090000080302d4090300407440440d2114018002560072500e4142c64009000d8420325014081ea51003024400161008240da0386402d10000e07036a0240e000900707204074801c020810b03035a882c10810050300b9002c003a01d009a140030003059040500034240c0c48525000f0385084c0600d02c607000e43c2c81c04080c0c0280303114039004c014808000c200c04a0300a00b401041d078124050f848501e03840c101400c560456010b5104800100401c20103160000941802c41c0e80441c6d0264482d1601d080c58280c4201609009041c6803034000c048082000541020780596405d40454406c80b65203010f000c5200d0200d0040d401900b000e01c01049240f42c40c0c2c01403541c0107111804 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 177963947 1250 177962697 177962713
    0x6150816050c060a27020105040b030c0705030f0403020f0402070b0415020d0f0b0f1206390706060803030903120a0b10020f0105071b0818100507050705040c02060c030702 75
    0x20b042e08000d81501d004503401d890b421981007103015040b4400280122907481c00c141030440d40060860311441c82444440c0a000c000a0201c2e1701c500c007a240c0300c60700203064070b54480c880c2c40c0c0700d8059401130000324450402921822401d09007403082c0d81382903600c0003800840740c440c0c0e180c404411241d10388403882d107a002c0041e400404058040c0300701405103448003081c6075590104006103104100d8003680500345802c4907003d440030000c4d030241c20410f661a041a01054144101014a0f281c10303072402c40059203010000100c50070f401400b0044c0502d0080003600d4445118544034130090761000340c2640140204a61210f40010841c0c020341c051000084030015800407850100400c4a81c50260300003040c0741880850a00403150300070340714509240242c0728801040c0785510b061070041c2c070f409004100781c084022a201c070344640741d0b001080100580100a4003c0040d44203100841d001d016400300020942445c0c018101c1007190340d0050f010707966803480d0b6104c141e0070050420b070452041c000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 177965197 1250 177963947 177963967
    0x50c040e10050a23030105040b010501180b0315031b030706030b0105041505030f0901090b1305100e0633010c020a090501031b060e01020a030f02010b030106080c03010615081605 78
    0x40d40b14000c00c030600c10090f0354000310764214034003200c0e0032045000c2e9047c03408120004181040c09815188242040f05107209800e0b8031041221041d009001c42032000000d0103401c40e10080317a910450801c40488803458084a030f145400c203c1c01c4002c980560294600b80b002e41d001c4e8218210403003040c58035909143d56911400704a00100c89110041f45c0f0004c184039010b030000c8000e50b4804001c000a110601e041d03660b14800710001404d042e0340c9142074000305c040042c01d008442c202d200d14a4103000308000c1141254440c0400d80c0c04045c404180304581541ea41d42c1181e0b01c1a03031000c0103036034040310a02c7d001500c0b80d030030108003242c0c4130090751000f04880c01540704040c00307180600410440400790380c400f0700d0740c00d2142d0040010f00914400030800c0d613038001604102c4541c1032038100c1c120440a6401e0380540460186030b030341035003008800300301000c0008544e030140358210b0003800042c0c1e4940c080242421810741540024400c3c030002050302800c81e4001e4501049032130724610b0205070107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 177966447 1250 177965197 177965209
    0x3010f0609060305010507051e1b06040605070e010c0c150c020604030c0914220309050312130f05090a231f090203070c02120109080708030a050901050c040e1005 71
    0x5080140401d0b40c403041441070140034890941c0c4145941001480d20000351a804440c3d2a900252101c3e000d0000fa042103030308906600e00c00245001d01294868240b40c6000700150004803980c000095140c07401c281250300c5500c1c0a20324903000000b51050078180402c900305603101d00f55102c14070080844200060712088001d00082d40039000740119241400740c1081030302c020300a10030502c0b00180902ca61441c0251090040d19010fa00080c0032800f14541030311404901e501141e414024210040c00030030070040182046500c0c0c1515060080d100c8034100200c88807030050580003d2140c0000d02400c030160b0082004680403d0700c014194501d261800720500c00700c403680510000da030b00250b45540c062034204042c1c0b030a00030a60071031802200c018a0a43e201001920078046000c41844154003907018100381c40d04a98801d40d141c810781401c1c03d403503106803500c0307000629000028420305418800d003030041403081c108904d00303880d01945035200a009414125004041903000a1a82c3c2d15 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 177967697 1250 177966447 177966449
    0x906150108061206040b0f06010306030201080109090c0e01080703020102012406081305010204060518010206011a0f0906041410090f030f2a090c03060b070605040c1503050402040c1112030603010f06 87
    0x40e1b110f81c1c1c024501242c18000c8000003800060515040400c03d00050381c210b20b0700e80c1920101003002942070b48038201a50f620f0281c0c1c3c081350795000c480c070011440110104241054034001c1c1c000f48030300510044513a42c0d21900c604040c03005400031109001c0248100d010541024030700e908003020351965220203007264800d41c06030000c1803000070390800480500c002141c1400c002d0028055941c980030010191207100d801085103500002101d109900b019001e58100c83da0203400c1d16122929807000c6000829920246449285460071145c440707407082070502c06448016503685a06850f50b0747e680c403485034120003210780070f801030300d0280842c02001005080012030b802e01b9120714070b080020411110034030280c1041504180c41408070100c400c0031103040540c0000b0000e06660303541814402c68419400103031403002e1920003a00d1003a0326420890280c0d008607403c002d002908102900c1e05d441110031500c09030029200c56040750a403601035640071102800110301164100e0300e4408030f45031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 177968947 1250 177967697 177967703
    0x21509010309060c0f171005090613021602150a0210020a02030c1507140403030903110402160f0605070201020f0f1b060a060f060f0c060e0708070306051603020903120f0403140d08090615010806120604 88
    0x1034078dc800c80030743ca0100429005400c102001c24a00041240029202d02e541e40c0d80c12103403500000c4485c18603100b0011903200300e410740191050300980062290710b81c002902c08400151841e2000070510f00740204aa04990b4141c4403050118030315500d000010510406055005038240000c41c82e06040c1d9450600c580e126201c0c02c189200d2510700741e070482c0c00281c48a0f0840e841032140d00d00890805040f541540080a0276039100c01c40102c450300160110302401c47c45005003814002a28016003165003511101d4074003903103003a01d07080201e03072110b20058040e0004d600168808040382180d03005061100c404800d5546a503218140c10303140000d564011104140c0c0c0f102000305c40c0d800102c410400c0790503481d042d403910740020b00080d924440d00d900341c24000000214515480d09900464000350383c001d4540c3d070305411311003901c0d44030001c01d60000007150340100014220440850b146200b40103403c5001403000603000112511207000b8102034000c585840441242e01081105c00c3c41a48 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 177970197 1250 177968947 177968977
    0x23090123070b28180209040212030c07150503070504032901060c020406090b0303030f1503010c05070203010c0306051302071416051903021509010309060c0f17100509061302 76
    0xf88000504000214083d4a6000610780041c03900700c8400c1c84107921050342c044a13607070103035213980c0001514008500d101400034400021038004d101c0020941070704444a001c8071030f02d104031280041e03500e440100c4107070001038001c01c02840021404440c1e40c403218401d06c010300502da0304c2811140020001e80209000c60250b840c0c030400c600d4103021354030281136429001d1065160040229075a40400b520343c0010790300450000d400494101c1c000c0f1489030b0000e009110825100c10081c007994001030f000c2e8020750070000c078082400c0c084d000d600f04581c400741c01080c02c0408460703401d000b5002403000315000a071500c0e4816140404114030b10b8656010f85080014a19040c02c01c006201d101c030525a4421100000b040940e81c1c03400039004032800600340c43e03030740c0ca080c100480003014081d5000b41500c0c0f80c4001001300c5648420840e41e074191544807888000078880e1452030282080310340c2c01c50100130040a100c103061615113140c1207440a481c0040b0003100080b810180d810030085800844 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 177971447 1250 177970197 177970231
    0xf0f050309120c0303160f050a0305090a1d0604020a0512041506060c1a040c0b0c060103030905040e0c0f01031e05040303050106110303041b080d23090123070b 70
    0x102d01010840b0064001200600d884421840880e490740201d800884a031482c4008040501c446071000701d01195015081d500c189103546406007030b07900130301c0304540100548400420407030b1440c2d840520100404448407040d50b07514003004041e602081031401004410b0101c1c40e09908034051041c0120b11862064600c503c041201c58110341c96540842d04012070811241c3c0400c68001000d5602403403505041015601d5092045455445070700420858a0000d103401c903248001c10943c0c107076886683d800d42c01e0f69440040100386c13010303070b907100c01c56401c072180c0c00e1510320b045801610300c820181000300350302100000034040311940889500c0c0303040e1140c1c1000300b0580d040c49400d01420290910861180c11003482594a00000308018503001d00c0502c0420000a0760940d5001041103404403094540280c5004141d1041c001000c051603c0c2210000a224410010b64a440e2810303521408000c042031044040d03030f01107a4040d0111a4100a6a400714140303006081c4500402002d03402d20b2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 177972697 1250 177971447 177971449
    0x1f060c1103010603080d0b1507030809060604050702030a051b0d0c1407030b040b09010b0910091a01020d120f06060c051605150a03110c0a120f0206070305040f0f050309 74
    0x850321500c08203100e649000c5040c00000c24031400d4414074420140c0002d41c1c1c44903e00480c9410000d000c101712400d50129044003015404094039200e40c41040584109844140500060b0b0704107560b1200980c0061064003035852061024042142c03605900b282c10280407038407582019100100301c0700107040e55134441c052069090170b00040c81106402030007420301c0c603110b403041458050402031000000c1404104854400d42101c4201000208a000c05083c60411100d40300d40c00d10410480c10b05201c81a0f141d13045005000c00c1d00d00041c6c02404281030005400c035401502c1504c4120100d41c0d802018081650611600028003000c4d26100c5070b641c050b0030f00305e240090210603144030340d00e100c0085c04146c8500400d4088602d0340107449031592042801030700030303243c000d8a61005070400306600b000281c0000c2c4101449008810481e0074410f070100860b5234000000000340540d00c803030042501d00748a6445198814002c6113005191002569400c0710f0700c0d01040107507015400441c1000207 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 177973947 1250 177972697 177972713
    0xa031d030304030207083c060c03090d030608060c030601171924030305130e150108060303031302100c021305070206010602011505040203100e0a020a14041d1f060c 72
    0x1d0010040244101100081c00d1a4000240b0300b29122010300d00103c1030201c405001f0004645240c0c0d4250740e0546440d80400c082900300b00c0b02c01c000c43c4561420300d001c1c54001c0c4500780644520502600c135654446048070800d91000d000c50b07042145208600c0282030206d400640100c02e80010144584256404130064031001c0e5000550b20f407104030020071803210540302404681e0326080c210b4940da40d01303007155984200c03035204541505400b030400c0038158542c800c0c880030220980340d090040c0c8408060503601d01080f81c1d0411209412040c3c1400340c64111034020f280401ca141510b003d10760795010513414907034054016170098a8409001d200764041c441103004d05140e01c020800342e14803550000e581c0b1760502c14103004d281d000001c507040385da40c05000c6001c2c095005020030a0308106198070000e50100000ca00060b0340c0d80c144407290400b541c00c480c100c602000d0500c2e09880e1001d019590803034040e241d1307580c243e41c18100c5035002c0c011050038001408107880740a8112102d04004803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 177975197 1250 177973947 177973949
    0x10f0b010801060e040e030405060a0e0301110301030209040807020f04140a1d120310030c030b09010c0302070804170f0706021b09090d110c18061201150501050a031d030304030207 79
    0x2040c4101d410060001691100a0745500042100d0115030050302c952410b04500c5981c10031500000c0c00144280041d80000c41c061407030700306500800041414046031300150100b03010080d84200032802090105a40201402209000900207090a5154000501207903100361a001d040d00c0380364100b10000c005031140424014008001113140390701c52b0700700358031303640100c4c088410b0003404404078907a200c92402d00809144e022084441c201c0d1139017410082000100c03402200c66081204204d881442402a9000607034032584190500b400d21019684001c2182c15003041d03842101c0c90602804400c10100300100310a4000e007e00d07400601c580300e40c50080c00080d60040d040103060251648001a150340c080c0340c00d18180025512000c0c4035410040e0a02c4016400701d0000c481c88048200500020300844013241c07100000036010448a098400001303180309260700c0d03900100181d50042c0d0003007107141c01c00d1070300048200b60f059000b00f401c0342c43c203030b500f0342c9a001000701b00c201501000010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 177976447 1250 177975197 177975199
    0x140906010c03080705070f050f160f0f030b060402130905010801110705030a11030d1a040b010e010c0201120603020406080c1504030c032306091f06050102060109180803010602010f0b 80
    0x1204080642d10003074103c0c00041e200c0c10400c040043c0304014800c0300b007210840907510806030f60b41004000709441e0780310081000d64240c4003c43d600019108140410b440850795500c0c800c0441d0391039912407208441d8002c1c40f186d005502000080607800701200c41e4009040c00c40030008055051114242c00c450aa50f40b4007400c490401090021a20000036100041028540a1100262102c666080d8003030448032000302c1d41054580601d9064080d00114840e1041c0c404000018196004491507900030040c5d80c08102047c104c1e0001d0b500c5140740c0030b100ca501e030202180c01981c950105080f165a54400440c5401c079802d91040c0346096164540740100030040d050405003141c40e03c0c03484646d9484006c03d52240c0c40064021802d8a0307840c0c411341c410300f070141d803074524043c1007040d100e14900300700150700a02c004406e581044135204401c10340d130f0103074000d10980c1e0900000d0300c010030160b00304c52442071a5880f044c00094481c17000318040d100c0e40e8004070b80301041d03c0d54038082d540845046 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 177977697 1250 177976447 177976457
    0x50f0309100e0721020103110a0201020406020d05030c1b070b0f13050402030c0f031302120d020f010507090e04080c06040318050324040c081e07090c020d180801020414090601 77
    0x204403080c14404d03281505605282d01e8070128684d03100581c000c1c05100510007041307002081d0a1072803601903019000f12071040e000d0300c0781c0c408170880440c0c65120840e00020456418440e071000b528102020903505401201155034454031246020b0719604840c90340004500005000f402d10784904d1a60001800181d0b41903085003041c18000c00030b0700445482c000d0300840440001c4124011460b01220503802601d80c0f0511800012b415480700c00030420803001d0b2042c181c031240650014854207106148a9031901903940c00c029100c0da0b8100007800541304100180241e1540c15014080d0714000c62094507a0340b203107140030051490704040c03644610300c01d4000b100c000d20041c440180400440102132089041543c883c80c150308a07680f581c011105038400c4004a02080035404071241c240030203041213902c61580c60712410199421000c034040103030064148001c05500916114082c0382001c01c080310b21a0b00c8851031402c90300030390310032111941101c0124915041110b08180c000e4002e181c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 177978947 1250 177977697 177977699
    0x30711032a010501050d0b0405010b04050a020705011b05090f0604030204060e070207080d020303010b0d09060c03050a0b0a08071509091a0f040506100503130209040506090105010e090a12050f0309100e07 89
    0x10385607860406020300707c1d965420001c0c08109080d0301510034148028000c10840c245012520020740041c48104c0700c3d90b20b807415140508d1127205405411701c0352503907000e25029401003807294104c5075036404c9801000512001c030042e40c07580030b880d01900138600c0540c424580083c0081c07402e059036200f1103150b0000401404c146501000300c0c0c0c103603085490071540d41e5004120200040030301070700103402103160040f0a003503603a06800560050c60840401d20964a85008005140c1c002d880350028035804242c04000480303408009490081e4642021081c2e2665030940728251155600d01c150908070040400301186031102607108285019038042000d442c021002c070390311078190480c2d01c06001d8040001601c83e0661442c24041ca40e01401c0d1201d10b091a10b405a9105030a0303513950f50755400d1400106254901c0a01c3d40d219a1060b80180070348606c0e85c032081032310b202c107034507800410504100040000c03011100540c0100d5071100101200008450018100c40000001c0303030864014101c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 177980197 1250 177978947 177978949
    0x11070318080d030b13020d1401300515130515150d1704121104020c0d08041505010b1b0d020304140d0b040b16091505030711032a01050105 61
    0x211048070110300d082c00604801e84c000021003c02d424003074009020700000384103c1684843c0c20002c075040750107900c00003903600c0f2071030b44030142c1d0034078449032407a0942c9034861030100e0042e07940d000300740c0681c09440d00120310420910544900700d41060043d00c0e56a840c1007002410895481d16100b002c1c2c04081d10304081c00311080ea80100c0480b035210f0401c4004000600002c45030075403c0100c0780806954035980c400d04100b032009400c8040e9125030a6054018950034a8001c94540148110240c0240c8030034500c140e40d0540c0281040d9060300b101d00302008814041d04c50203001e44400c101060f01c6010080060485032001c03018103040c4d400400103860307419000070558080e00d0f100b11100002217111404603180103100407000e440d40a0030014041800210011140185020188a040144032840c190703000c10340ea204007402607008446004445118a020b10780103240b500c0d01c5241d0007221440c1c549150000c00c0100710a4a02d003101e000b107002c030000743d08100c500400080c080c540c98070b8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 177981447 1250 177980197 177980203
    0xa020a0507030e0112150e0a09021c030302070203010f06140a06082d1005120313030b090c0d031d04140403030903270f0608040209060f0607061107031808 68
    0x3907002818048450300072001c603806800c843c1c8a14411880401006861003c258528040c3d8401c0d01394854681d0b010800031042c902032901070a0700989455108250b5a0410311030f07688007a0b055003003540c24848a0010780e0207002d0386186840e60307000422000c3c00c00f00080904924480000d101d0b9407140400c01200750400c02c203660021388400420007100e0b0039401704010345c038903199031010009401d0810403107103000c54040040e1070055500400c240704c41c81c8240d43c3c03885803501c0844410b0400d0400c10024011580c540c7d80001410103841d940252540454900c2100641c114081b96110580514845448ae52554006d504881c00d2101c0103980f07211208406c0003400c0503080540702d000340400d05014083c022070003803040030a049a0b4045410a4181484038018050007180290000480604c070306001d500035500240800b0243d01c45004105034076180c00001d076042501407018201107100380c8500384442104041295540040d803030010603803e0400031031035100c100c0e4501808601000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 177982697 1250 177981447 177981457
    0x9050a02010e031509070609170c0d0f080705010b040f0204060c0b0a06170c0102010518060628060c0b07020303070c1104140a0f0e06070f0c060605270a020a05 70
    0x28280008001400008203040440001c1440c113483c141c502072255881e0300140c5201141c4c0c0b0780d591901003940b100040c80401c41010000b00341c0c0e40c41007106030024504100c5076030404d8461302c4c03203a1035200307140d0319040d05802c4200c058845942d2504103500c24107041c0138201d084101110118507082c14101c000e00002c2c0c0b01e101c00740200c908040011460320856000202074001a6041103500403030a030400d40d10f1440007500740c019402c1c0741c04580c09110302401ca40c0040b00b0382019081950f1802d05100c0f030a00c000b4119090700c140c800a5004c08030102071203001030710569560624401c524240031040b030f10040e192a007103500800030003c80d5544511b80302d0740703035074042c8400500e20151b8000030040d002510b120030200c0c500e28244003141255603c108075241000c0c0007440010f008000194581808a41010210708504619440d16209081c0020520b2252000003070450702c46000c102190074100381c00541015096414008203050840c0070383c881940881986400c240130002003050140b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 177983947 1250 177982697 177982699
    0x40c120b040b03060103141506010c080a120606050a1b030f110a05060717090c21120708120109020715020705150c030a0b09010e2206060605040501090909050a02 71
    0x6642600440340e0341d01d03080b0b10b611000c01000c589965071039061240c8041030b0007031021068810815081c13400201805034620a200c16102d41101d03650a403100f008690003206a0340401083c1134100380c4150551080901034030503651030940314507607254007500b015600c0c0e003112203032902020350f18002584a6002c241d802820f14104004036003042e251880c084007060002c00038003c9404002c005944111b600f40c050448040d101c14648540d0701b800d482e411049a07041e081022040700c102c444412041111403010580203e840c003054a0321f103100250803c250848a0250000e00c6100e040110f9543d1400f40c40d0340c420031450405180d4488500b0350140d52040c004030b0300428801c0601c0424001041e0450410000c00c1c7d03d40342c0106a0500c5030301c00c03504215a1450085a503246013008100c240c16111300c5107045515444415200c000c3c03001c6003045045940c0315200070b05c00102d090045200800b5640c6517603440303600b40700c0007400540864004401c1103190916038808200300250030800950 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 177985197 1250 177983947 177983951
    0xc080306100528080f0708040b060f03160306050c04080601120c0b0a031515020307110a1206021222060f0f02130e0a050606070308070203090a03051b040c12 69
    0x800315020b94441c05511001c55503800b000081c03014400300450040101049551100b04581d40c01000c0504200e0945200c00001c0c03a690029002a000e81c0945411100c004c0864000300e501c04002481c125480d80303110081e40e4100c20401c1048281c1c05453740007503591965070304241c00e210000c0da80b48014441c40c50000720064102c0d05020041d04144040c3c1054104143c4d140d003e40006000b60100244528400c0c4180400107218004030814003580c0c0301e0395002d94a040c0c07494480180c1c0040050b0b0307440e444070102d80002102e0500040d8031a00c117101d2440503032942e080a40000708208010204981c0682c50002010384200a54005244990100c0c002494030b0288074400020180a000e14400702d100058030440d80b00d19100c10710031168040404c0085555143c0000d040c2c5a0a0300d030282c000d8002d009210000340034529050380107260b131040b81e08001d4030400003901c0b110390394070594060304640d800e094610f482e1101240d42c0001030380c042c481e02101d22001080e480456a01129141d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 177986447 1250 177985197 177985219
    0x8070806130501090213051e0f0a0801060321030c05030f090705030d12050c0f040b0a020114040b07020d02070609060e030c03120a120e100f150305060601020d0c080306 74
    0x80d07540e00c01040d90707000340401000340d0360310b40440c000254001c4103903603404419140005500c6c946071001001880c01c6464800540410f14240500c000f856041e5a500c0341f00302c0070110303081d002446410300440c0078070b1640d0300d00e844c078640c40c0c1d40b921580aa807000301800d01f44444033558010782165007020340e2081d904440c1d07480e10380040c20410300f50411540740c0940502c1b020110b6001c0c2121b0701c0c1803100c0600304550313124920400ba5601c260744090b0f210800c14401040040701c01d001070418005c1900004c0390498a044008105940440d0110b90119240d4103210445074104a40809252580018110b00741080d0004e40440c01500c80c013020018038596110480c1c6082c4200c0d60859005001c95000b507511400d4281030350030400c110303400111594400c02d2806070034024103c03058001d001a14501902d00d07030070340103030901100c4031204030340307940301702000040d141d503d00d00841c09031005d4455401c205000a05210104030360204001580485001140d052812250444421101e0396015 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 177987697 1250 177986447 177986449
    0x9050c16061401080606030f01051006030b06041e090b0319060c020c0d060204140316060309030e06030405060f0109140609040201090506040803040906050114120408220e0702030301030308070806 86
    0x342030840407002d40702c20400b0002800c10720000c1e28502603c3c0460903980d002d125a41182e003218002c0307852400068040408108660283d80058034041003d455a0b1401b901d40003500d00015104900303088205c0414030401c42400350384039124188900310050044020070036070404094000400242c5129656a85889440c0c0200000d0010040c0a40020842c00342418100000c0d04a4030420580c52202030000041e403401141ca00604001e0501b100c0002d820418120020500c0000480a000c48501568180c1d540c1da405103118600c100010011032904007010301c50380ca81a440001c541e030034642c04005d01d02220502030303404181a600c411a40e42d41b40012240602c1503801160043c2000a010480039030100080041e505202021300c10995a0b400454141c01c00011241100c00e0074064440030720503811403203801a000e07840940c1807120710b01c00960b0503000d203020112701c24072951041140c0280086925441a0b950021f1400d540c5181c0f806803041400a20000c10030403085d0001d825 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 177988947 1250 177987697 177987701
    0x318040c0807230d0f02250c0e070221212205010609093519030905030a0c0c0f0807060c030c06150608061905010507060914010b010909050c1606 64
    0x8510707130b003040030300408414201c07520082d800301800c014507001c5070141034000e900b40010742140580c0301c040403102ca45420b201d0710900c02c014000600b103000d404901c22a80980b0900100105560115aa03494030181040c0c0122200c000304001003c071490100414111400d20f20a190a40255901c0498001d403801c0d80c014181500103009091420404400b88102c0340411040d0720504900c08e80072603c81d084042c9050140320811620540c20002d0012081104200c1c0c40c2d120080d040c0800c1c501070a41c0c0d86802c50300107440c6140015118004041030000440300c2000a1040300c191000d22800c02d0b40454644000d4000c03003051213081c00104081510442d04208210342002d02000071840d46496640c500d4040e10034017002450342404600981741503082e000041141ca100c0d00c0c0c000b46488015503060300a0740c8103a410903520000100402c20201110300410078400c00020360745198000942440da01d0b420440401c1e00d0441048a80601c00084410300c0300701e0b115801c50142649482c0d00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 177990197 1250 177988947 177988957
    0x151005070b0a1b0903050c04180f03050a033815040e04030905040506010c0201031509020309010204050916080606090d0f0c0501020f0f0601030b0601110318040c080723 74
    0x200000301c01e400c2001d00d40283d48181c80c038510744010101100285801111030f07a4482c0006409a0022034900215207019801208041e0181c40b424008001343c1d21031120040c010070041d804944005249204140c0c94800c40858040200814095020400030f22100c5800c8190603000301e00100c0c0d00ca0300350350792901c460703c101d00d161070300558881d01c44421072415a400d460441c00f09103403817004aa189810b02645206d98410394810b2070003a2942c0044000d491808454642000c1004000c0390309003480c00154800c1c54503400150340c0f2840c00d414080e62010042c40340c60240d6182041e82ca4070766000604a422840407103802d600c80009000003603945505a100802c19040c012021003040704424400303045400907000c0d10300b00741891380b44c0c176129411564450702c260020300041c00040c140b145101c0d048203061400c0c40302403034203417913051840e0700c01f82000d4000d0060502015042c50030f800f4001c0c074594545401d0b0f04170300304010054081e45001c0f12032800c0e0906c6a42007030f407010030003050311 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 177991447 1250 177990197 177990203
    0x60209030d030204050f040b0105031306270b0912040b03100b040612050a0608070611030f130f061706010309020112050c0703110106031113060302030115090c0815100507 75
    0x1d401c8401c5448090000d40c09445094041c0c03008003510350b0903203024458003108140c180c6071075155a807228440c10044415141c1252071a54801ea0f20300c540b040014809003290349117104110801031400c09200480c00140750b50f1036540251158840c005040b4140d03022110802070f40c075181e40300c0d4620b10046031102c0d008282800004680021010f6200f03806030802c4251180401894680001e010103a03501c50041106603480240100b203120b00c5031664007452000c5005503070038180c4100d03010005500440c0601c640d4080c42c5018030002542c28100001002642059000035281070b04a08500d000101501d050590710400c00b001d40e4060f802500a01d460038504028600d0401441e101030b03003004501b40e0000c2d90540300076280d802d05100e64020b89401160070600110503104101e000c03454404c40c4c0000079112040000146c03070034010040340f80040541014010300380000b800032581000c1031070042290f4101880503070001c032100210844003c3c0d81212100c0140c040a6071070340b10f0b80300c0c01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 177992697 1250 177991447 177991453
    0xb071214030c030403030506030c031c0e040608060709060309020108010e1e0405070906060302070b150a0902030f1915051903140a111f0806040902060a030507020c031f02030406020903 81
    0xc00c0101e8006501c07030f905c6510304205039180c0303209065955401e2510150158080080c0101510258042c1a0303034100e82c4c584481c034401e10802290a84101c0e910651b01c42e8044070a101485401248440c00b43c0b41c1d51808004000081e00020040203040c4515500413107041c0101d100100600d120300151030010f240500c00e800d1a161085d81c810062045040c0a40713003030710200b0030301e2284c021500c0c00758000c101c1c2c103460303260029060300c2c2c0f070f1158800035800200700d14001405080c2340040c61044980d81454800d900e0880c0c4400c05004000e6031070b9a60300d01e40560303000352400d0110302c8003e46105469251101180c61102c0101c0d5209400140180544609066a070702c0005141c0c3e400a1051101403c80200c81040c0101d5000709810340900480b03981c0064005480303070038a194480300040021600c85902d0700490200c3d030001017810300090300c0f5010400701130340420240038074100a400500c00382c40c809410b48406d500ea00f4002000c26000800b2509024054060b00c0380c0c01402415 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 177993947 1250 177992697 177992701
    0x50603070e27070c03021005100815010602010b0612070806041805061006030c23071707032a060e070510170f06010801031218090b03060c03010b07121403 68
    0x4116011440008401e03120704008000f89199100f0920203094036416002000c45019408040c009800001c0c0140c0c515140c40000041d200d40c104141e450216290815500c6075041820082c252460740b04000d00403c0300b0084100b144040d00b00f0303a940100307585030048840d1030f51400100586520425280d02d035244003004c4042c0007021541074001c1d405103214951003a5035071025020340d1061046000800d80015691030040f4440150444201c1c98810080c41c0604c00c0d41d914502c00c0418407503110000c1e01160b03071070806030046041101108000d21001001e801001901102608400d0013091141c484002c107007100ca0800a20002d00710042414844440c0410001d1041251849001c4080c4000300810000203141c941d9a01550041c0c1d00e00c82c0c280e095455203243c050380068020104404000b5000d469001d80090201501e8807120202d005440d0070100741c500140506021207009081004100c210840000c40e44e0246c0e0101c1e000700d101180c0c01c0140e841e4044080070300da20703c1c40081 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 177995197 1250 177993947 177993979
    0x6011205090c040e011505120703050706050a0e0f060307030902010c12020a030f0c02030d0e01180b030a1127060f040e0618090703060e10020705010b1c030801050603070e 75
    0x1405544200305076820000000700142142c03e84910b041b501c10003210441707051000b8246410750b100c412001c24110741b80d050752651614600241e0754080310015001003400c2003411381c0180d444407144001c8690b0182808514001015484068040d00605513034842a038116401080c1c06180950001600b01c0300151981000c0e4a612940c2c2045000503d00300715400340601480b1460503540c0c000c3e00030941140d8007075059a2000d00c40310807a0500007482210514003c2d00300700701000d0540c0c0e00d0700d00d8803030402c60600d00581d516880c940c610618280f2404800d6010780c0d102004a100c626020035245c8140350100d49a449200d84940c9103030030010b004240b0b6106c14580c140125819101011701240702a08030701c008005688682039504075402c00c10100d001c1d03801c541d96141c610000d80e0151107401c41d1034000c0764032410f011112651108490801d902d801681d15121405505407040c01c0c049035a002081400305011b018032880010000c104843d00c100258400710201030403c4032808070710302e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 177996447 1250 177995197 177995203
    0x712020c070902191b110603150603090d02070f060503060910030b01030605100902040602062e03050a1a0c0d0c090506180a05060901050f1b070f1508010506070201080601120509 78
    0x2060440403c95005e40c4801e0780c1480380c840e04407190400c019a044030034000800000e580090f202d005900c889000709a200c0c1e0311080114011694070340202540004032401030305000700781d0300441402c00403000030072400d500441100c1e407004044a18050b2550341030741080c1210350b0f0f500080c1c4102c0c2d00d80300100c00c001b900e40c40380340241e1038601e02c0001150f950b00040140d00c5607004020050300310f000410b0304101e00b4109000490800210308100c41e08031032842e108050564070580e281ea11045d4100305100c60700c82400300ca200710250844c21803501d40e4450310310348a0501605604e44d0f543c3d0b082c801441c8201e100401030300c0c00602c1b50340d94000c1405840c24000414450034414060440d002a06280c8201141c07106001a1540c504000b59084c0c01c4580382c01510040342c03800d03180080e8200c03a00d810700c481c402030100f500c03545180340d0618440001400800c0e2030b68051204010044c00329a841d4010344d5903a41d42442e041c041e650350355004881c15040080d070144070500301414070030055004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 177997697 1250 177996447 177996487
    0xc0f0a0807110316020913020301150504051e0612030c0d0801090c2307110d080a090f030b0c0f0c0a030302040810050f0112050307080d0906060e0712020c070902 71
    0x796980090801e203442c0c865103030302c0b907490a940b40040700c0803c031005084c001c64040d48064692508158400310b03801083c00c1d25034101d41060f511200135010b05c030a01d8031740700d03e17a04020310070307100014103c0c54502e182c4c0c8450060820340c401d9045089034000c10404004460b04103602d0300541d00303031110410010701064828040c0d9400b01e400e20005124181c840d40d1191100601915000b440d5004410080800d071b00c003800a0305d81001402d21803a960b100c070000d0301003442c4640001503079040b81c010014618455174020007501c123505007041000c50311040040c2d0304141c0d00e4094a50702c0000da0301507543c901c280400c5040c5c50040494000601d070301580a00304883c00d4100341c0d914805064a41c1044841c01c0f207110f044d4060010042c000044070071889001580b140f400c480c5020b25507120f1007070315000340001500b150380311a581010002076000b0040180790141d8541c400d402c5c071510141001081121030080d4039804281e020480004002d040004c2c02c80590442d66120200c680985018403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 177998947 1250 177997697 177997711
    0xa0f05120d14090a0b010905070e03060c030a05091209010305070912030f020105181902030703020307090504060b0409050a020111120a092603070b04020103020f030c0a0801080c010e090c0f0a08 85
    0xba03540012010307000820200c681136800024894180e00700804000104000303803240702001a45c2c8020411038504000c0d41d405100d441076410b4881c64200341440940e50000c3c00300040390481c3c140d50310a8030034181503883d680001d0a0105080d950181c0480e540c80c015803041030040703810244141855002624400440b8855000b8016550b900049403440c0b841822041001c1d070000d15018041c2d0301104090214902c02015540c00540c0e03500045d1a040c1c298000d5080c1d20f80d154240030070840140b090504c8000281c0c0c052006008a403138803611825540b0b4082d0611010b011b240c14403034800c1c4040d035500d05407500034903159606882d00611140242c00b400344009820301c9600710458810a0301003815922400451a00031b150713813002d1041c040a08120f041c103030280000210341881102841c8560b600210058903012030080c000c00b40070060380030b04850742181407110f1a42e6848818070401c03040135924582503481d2112891100d110b040c41c0e82c01c024801050b509103050740100c100b40101c407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 178000197 1250 177998947 177998981
    0xa1104182a061b02030a1416060306030c0b09040609050a09030206011a190905040606050a020d09030c0506070503040305011107170909070807030902031c09090207050a0f05120d 78
    0x310324485240d00303406030041d000420005040045584000f01540f40041e2024095890307401c01035950040050440c020080d644e08404140d15064181419500050103030780b50034403800e8610f0b160031840145174010303010326000018606080c0d40303d64205000600000004108070300d040c120700001460381c240c0c1100140101c500000d119201035409003a00075440c00c0ca6807400d07096503a00c0c0c4840f40c1310309103001840388181c0000b64554030303803168000401003034880d15030342d40c144040242850104c0303205e6001d00c001c40d8003e1010400c0001500103940c0240c2d051a0b607421a030a00f5443c50060341d10041c019030070002d007020007400c1940a044d155124255403205010035030400015400703910b030071035002100800001c1190340b103204e080d5009072103414001042005500400d041421000b600c00100341200034000c85580e100c007441000f071900c0b010031820000555521500d504e00040064000b244400c0d44c5014410240414545080c2c924509a5a804603101070009031040c054100c100071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 178001447 1250 178000197 178000253
    0xf0f07051801030c0e070215040b01030c0b031b090307180605040e0304030302060c07020a121218030503040905041a01080f01200306010f050c070807080601060309050a110418 77
    0x11410410382e050b80c0e44140c016030002c0c1004001e4515040040c2000c00318441c5101c0c980e402c100c04418940610b01403151164598103604042c5080e50b800c0e44040c40c0045c0070404c121500e15070155005503100106003642d40c82000c01300007072411780640c0000b0104002c010315020400b079141e01070411144191340c18000800c2d001c6c2c0e081c0d164042c1d4032001e00035800400c002089140307402c0090000301d00c000d001c3c0d14a140c55141c00702d202e081d06141180d03c8600351210740301243d003080c0310115402d01490a0002c081c115518140c072801244a504501502c40e40410100659000418075042c2d400d100020b456a48202c3e0301c0d0345110000045840c3d5292102d10801592007403030078031a40181410251030764441e030740112000c810341d03900941041030038001d0706200b0a0500c80d02c0d009100d150010030400b41440341040c100041a480907082c180340181010018002058140b482c50708101c2100041c04030f140401c0103003c080e910852080710003002c0c5010800c84101c901c5105e108000880110 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 178002697 1250 178001447 178001479
    0x60c0f0a110f1509150307120609060803121b0f041401020714090603070302090901060501030509030c28050703031e0806030606040b061204060506030d0201050705040902070201020f0f0705 83
    0x2c0107415510fa041070b2410201100400c05500400440c5009071441076911062410a401d40d08159011800a0560380049000000c1801142d01070400c503201041705a1901035181e07500e00c51690740040c146040400994040209100e84600724048102d41342c0d5030308224000b40480d0302a00544040c420b07800b0404406510008a0005850103c243d00c91909092410803140c844000c111382d500d0711480c103000c8016281c204149000301605070001c1059802c180014041d01c0b80180079180c03690040c8103c0b020000f00151481e59159003c281c058403181001d800140300c0f050b004050040e20031040d0000805510400c5444500350b00203803807603a102211001c4592840030340e0203d50590000001c1000c1f89002c0d4042107110400520042c90b0440386c40841c3d00ec50000c407816903c0d07650741e804119a034201805081410301c5103100030005440c0c880d00241140c021400f4a21401e5408600d60003164001c01880c0310303a0481800316806082070f01302311a940c85441c0142030095510071019951 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 178003947 1250 178002697 178002709
    0x21906091e080a08090118050310020c0f010f02190503150909150421030c020a0206090415030501090309120b0112080702091006030e03040e0a02070f12020d020c09060f0d02060c0f0a11 81
    0x352340004020304004140204540b019401140b03104050703000702d20031394071440d5092081419080302c2d50310260b121a400a207030301106000b500040c0901108000304068540401c04c07000c0941c904032540410350300c8042c007161401c001d440f1105502c0e0860740c248402e0103219010020340d40f0400020365002650b03604c048054a4002400070050b03840307540c5407401071404002603c1262030240c00058003d406915646c40b4122590040c0d5199644059850505502082a4014003112900d0040c4103080d590b4018940905100703095a43c0d0100e404c010812101800b243e203d0360300104140400d0070460760130859981c0602c03502012a180113550003622401200703aa00326071009420f8651545c4800050007e58050340d0100c4400031011080000203c0c080a00c51a200c020381c0103100c2040d80580203846c4c90720000c4a030307116600301c50402415581d0208480c1c1c40003402d490848074182c4510100707205014031000325241d40903800e0311001c40140082c0d6041011300a00e860f0030290041414060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 178005197 1250 178003947 178003949
    0x501030605010c0b041704090f060602070e04060509011b0f0908061905090f01090503070b0a061809020111010e0a0302060a02070503031f0f0e04021906091e080a08090118 75
    0x800f00b00500410004118644001944540078a9a0303d00d89a460075001c450f5600c150000350301603a46018055840c54540720709005483c40d8001019000e00f002c0606a0074030f00184010001a2502c0001e4100003080d084520b034401d01d07002d00502000d81001c0034000d07041c590350042c00626200030000e070340e110005d6404c1c094140040720005058403040c0c1c10020b8040140341340e0180c80703407040c0e4001c0c0940921440c03038440e00810180d901c0d1310051510441e066030140001c2c03001800c1600900155045003400582082009400104a42d2510044c2c41344510260580b11a502e00929400982d2000ca10030155600ca0b90030740301941c0c2c41c103881204030302940b0b00c0506940d01c18000140042e45901c4040c1c02e0410301406200761540c4ea061007080c00c45941c00c00018110000180701c214205030042040030225030805044040c1000e00042542d10345d40b16210754205944080c3c000c01030b00349070f05c401505504050303c1d40f44400c1e080660041d40000b6041c6c0c00190403140070030410100030329200c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 178006447 1250 178005197 178005199
    0x21204062d1e0c15140903071101030b031617010e0313060f171e18060403050906040b03041101020d09150804170d060311060715050405160e040b010501030605 70
    0x40c4002c146842c01503120080400c0d81070034406031118000c0850013101c81030604480c1844041440d52050b0740c0701c008614040c009031910b50051000d10002140b803240c942d1039000030b20340041d0600da4500001d00e0008200c0d070394070741d1080c00540410f21100c2c0d9040e0f514180018002842404140940640d480c030072424664010350101c2030511040e0b100744080c00000e030359850b1500c40700242c40d4064030304074004d0701d903070304c0120341280204c15040201e0b40c01d540c03041c240c54810041c001d0908d401034503154000c01c010100140040c8001c880d0b596070041d5405015440c040507181c0ca031030724040c5000e002c820b0b28a80980b08076030341c450b115417056404609030b039002162107925500100d41a034003004040e108589400d500c0c1011218020f90802034011018038050106400740b5504003400d4054001c400540191810001500444d20500c034415582400380341c0000c55507a02e00709076080400581c0002c60304640002c000403403601d85a0300b036015600070041c00c030380381e44d84100650444c0d07414442e42d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 178007697 1250 178006447 178006457
    0x60905090f100315051e0112110a09090c05030606150a0c0326060a080f0309060310030b040b04030e031b040504060e01060b0d06080708030316021204062d 68
    0x80100258808142e04442c038450410701c0c80d40c9035030321403000a540020846030329984100300702070b8050441c3c0354121509400a40361103941001e01818800145810150400000714650552034651405403c020049000f00b0071034402c0311301d00103c8520452140c035119108540c04103405160030940300d403111145041076480c181409200f5295041054819002c1c011809a08199030054070a501c440002c03511075002d01e0f02c0c0920800c0741d0f0582c9a000302c54035510544d0080c40020000040b00c184143c01c07110141c07641d80300760358040c070182a600000e00503030b00c030340501080101601c20756006a02c42d0303c4074a041000403080c940c4d1032003074184441080d1031100a008240c02c03e80d103e69001030007100c000c07130302e151410304a60075116240d0194040200005003407044131214403aa9000d0100c580141c003046244c2103038203039280005042e000602d41c400f80c188000c03c0c020000030741517069a14400d921a0f55504c4090320108005d20204181c861040000740c07074422200032800c140f0450340310 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 178008947 1250 178007697 178007701
    0xe06010c0318031709011209031d03100204030305030f0c07030c030e0f0907050408010e03030f0408130305070b040303110d080c0f09030109080d150305060f04061b03090c06090509 79
    0x104031512815a11000020b504440000c008181550034200c0800b0300c0c905015925000e00c0300041c0001c881d074140020607481c200080c0002588100c0700c00e10784407480444030f62244450300090034040300f040238106052000900100f0503070420003a41c8100404164020305a40340b51140b4020f03c540e03e0000c0c000b0300051000c01c0044d024008035456040007500c920014181035002c10804801911008080b1707001081c100300c07200090040d95825041003000c2e5055052102985c1c2c540342000c1c100030100000407030381c40c0b035480208010400a50300b00d011100c03115950311400e01c459010307000036000164505a0000049000506c9418000c0c0b16910b803420390303841c0c806450094020303035001000c540007000407178481d40d0300340100941c46001c0d4000941d95584201440200d030310072504007100b034803011030404c04190040780c1c8584c000d40310241c40ca103d950318070b00f200041600c803802c544a00d128240c1c452407158143c0c0030441880c800d00000c8680c40d19600c00313841c42d4502d4480c441d032010040300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 178010197 1250 178008947 178008953
    0x6091406010303050d201b1e0a1514010f061e020c13020904320105031e19030507020a09020c03161406010605070c090b0913030c0c08010f060e06010c 66
    0xc1b00880d040001c800f00c1d1715088490500300c1081d4000d581c1c0c64090f60140c54000904001841074980100c6a00041200c515540c48921303180c2e4081d81002c0e01d0358440e8a13a418003e141c54010001c40044c2842e400c075690784403441b003230382c81a886c06800c0009940c1500341d0b090030084c4030300c0c5040c0e44180e0010003030f41c0100d03002c20a022842202e8014066000e005402207030f15507000d080080192085d04c3c4c040a6485554558800741400310303081d80c2e1040100412041d1001b16641403410002e9544002801c07850341c2c0d26240c501068000755100c1d44066482d0309065100001d4261584219600b070041c940d50200d05007a8018040c1c1c1194541003000314000131122602c003004250b1107000045000d0910003007450901909070300200c04940005429070800c084128110060a40d01404104d120200c8010455000c0020b245000c14080004000c1c103140c014218841050743c400c00c2c188452341c55480d01c40c0a00303c2e1031002d031001c6081c0300b004181c0d600141c0889201d00c406035940e410115080d2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 178011447 1250 178010197 178010201
    0x20409051e0a0807140c0907030f18080a080a18030e0909011a2107080106031703010e0114060d1d07080c0d020d0314030406020714030a2c030a06091406010303050d 72
    0x2100400d01c03848030606c03000c0d2107401501c1d206400c0358a00142400e042640e610a480880b80c1100b2060a07110154000078000410b94043d403045141140d21342c1e48982019006084e08001c000142002803122400c05a2190142d00d1a120030780300480192906c242040c282e4417014240d2070088020031840005040c00d1403a491045000400755159401a040303240c01d00c950b5400012441e51a44410b0080c0304511028015114050a40525542c5061040b401c813500600031001000014a115001d41c1c2c0c0d49810780b01c040000d29020060030b00d01c0c0d20070340c0c90410f030b0003100d04250103501760000d007405d00400d40e0100d540003d404807904442603401c1101d1800c000504509010f50503614000100040010750710842c402c8034010307940d070100d091084030407540c80300411099000f08803001c09a54801c8174020000143c4009000304c2d9002e070010981e07401903601841c0c040c819042442d00780320a03a00010b1525025910041d008140c20302603945440e02400080c010803000c01800000302666 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 178012697 1250 178011447 178011473
    0x140a02030c09090a09020306010b18040b011205071206090c1d01030e07031515060f1409041103060f180c0705191b050108010f09090c03020409051e0a0807 68
    0x84000c1d01e01e00301200300003d11140d0160f6004ca4043e5455040000310b003800c0182a026014824215060010100da80c14820000400306170203143c40701040101a40504600703184288401001d00140c9000b10005090034051401d0b10003041c10000e001440808034802c0c1d01c2010310554a104109500040409201c004144102e04050381d45544e0052000240440e401940c410311400070700e03000c1060001c05507400307000340d0603180d00d019908001807034004504800103001e5082c0403900c040460f1114046001d002c42c62074000c0d0030030440200b2000480e00661146000709c660801d034500510038401003001784001780505914210202d1841d0580802611401c0c0c0b1400c1250161040d6a405482d0014100c1d011101da0440b00c0c08902001482140400504000c0c44c0403443d0b0740c0342140368105240c00d44111600c181d43c1e0030300362060080300c130400c80145801602c2403060700c020307141040d658402710040303a04120240c11490050300002c98046c40490308009028107054250b11034240721604 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 178013947 1250 178012697 178012711
    0x304051c120203041706010501090509040f0605011215110f031b16020f010e01080117030c01020f07210804111c050105010f050306040b0a020a050c0102040b0d0c03140a0203 76
    0x128126000558910341c107501454140e0b02658443e1715100d6030b48858490012001c005801c0040184034590740f1406078001c80d0001c5840f001c994481e820708085808900101074681801c08001007040004800c1034111148075441c034610720205041c801085480d44900c1780a0f903c0d04000070303101c4950001c06550480c905a4040026440d490000d4070b0992003000002c0ca9500c007400350000b9803801215014a1003002e00f0442040c0c902c0da40028400d0030140540b4000709022600d10f0000b83c8108207681c5a0002c04000b10350340c2e81502404246074008507012200200c40e00f041d800326200b1811506480d040e02d417190103d41d12165102200c40084e1280345411808000301c40c0e1014120003184018980658000195541411011805240160030440c003e0344105c081c040013603c2c10007107540c801700200c0300507103941c40480112864410340f8141c00c02076001040200ea0300d2807940013400306005ca00c500300407200300c0c0c55059040c0d4a00c44105610115664002000b80b0700a40086600c048 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 178015197 1250 178013947 178013989
    0x3060405041a010609060305150307050112150e0109290f0427150c020606040b0319080d05010929040605040e0105010e130221070f060e0310020408030405 68
    0x8941121203100010991180d40020100e0801304141b81c1c151040e40d07000710040e01e90340403210341d90000c0307a65035603e44102030422010b000d41d5101031030181d006c4580701c820804510900340c1d858405000442d021f00403e4041440c01481821a5460791503500c0020341900080d04c4142e180401c01180041e298000d0750001d40321400c01e210502003d8030080812207003403401d4410002ca0809103010808444900101440d004015035080d40010f02941c4c8014102c1d00422080301c8003000c00e00b0b20341c0c05240650000d13010768610701040000b00142a50b60302c00d00303082006030ba850b0184000d460a03074011002d05002e1081c4448101008880711313451140c00380020903501d40d01e04c0031800b00d0744012284502659100d0040c402c203078034610b00c180c10803410380340c41190030301c2c40d00021246100d40b0702000c440d12800701c581a04900511002d0700820341001080140c60b5240c0300134000e0058400614800c1c0640600d001c0310ba541e501c291020340701c20b8401581070904010a1007541d01d003039450050090 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 178016447 1250 178015197 178015223
    0x513090c03150e0919060204171c02060c0304060504030201150f050102060c070c051e040c030c0e0a03031e050c030408071d060f0103330609050402030103080306040504 74
    0x9409401030000031002940c1c00618014115004030700a40a5000034503520700304001d000c071280c0001a1110440c0c150811500840300d04e14141000303100c0e6501140ea120090000c884c601e21001c100c50b200c0e80400030026201805d03241080fa01c584080b500a581d80314107001090208805078445a031080c400d0000048080903043c0312a11808a81e0116481c4210703408248461359042c800030b60804043e841031418609142c0e5911411012400307070500496140402c214000d8240004240d07642000d4410002d2036480040103016201c6c821004011031307d503052204240c14800c40001c21250503540e200342000300e481821a1b4249840007000400c4424040c04200320818002403008003140c60041001d14902010b18080420079050940b4000d00c10042007696200c2c0e42e0030402030407003444d001800b00303907401011403040090301040c24250321030074200340410701000028080c1e802c40d0b19141381045d9a00c0811003684001d0200410700b5105202281e0399042c16008039802c1881442056054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 178017697 1250 178016447 178016459
    0x1302010e04110903100e030403021009150c290612010603140d08060102061b1608070c0603050c181528140f0a14040b0a02010509150112030513 63
    0x254601030002c61040d500066941e0031407400704000c00100e44a403034140140103402130403685034003e038400a40034442141c68511841d01c030300381c000c0181003505602100004002001480803405100440f5040d81d204010304007025410524041c2180c11300b406904c036030782e10007400000c0e03081e44c0c1c54416540d2600804800201001c1204036503640004c0144280480b0803002011b0300400b800c07160540d0001c00901242200395168842c0344d01601c0400b96491115641400da22000d500000d4400c0c2404600d003001c010780c42c120001100d469940a010644452526134154410f4a00b4000d84480e6906440e9507030408a0144800403003038604e190402c20310080c0c107520a182420281d0080004040c0f00c0d1340c040d0001c006880c985840b110b09030415039030880101040c441c0c021010240244448180c8068012078111409081c591006580781d10301140c01034060f00d01500c1079082409201d0104401a0540c10418101d034800d800010018040e80c9060354a039005560b8101c18840c0307600c0202e11 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 178018947 1250 178017697 178017701
    0xe030405030a2a0e0703020a090e01060c0201020c031b0d11190e09070e0f10030c0605120a0b06040b03070c050601030308040b0a051902090f0301050903130b0906031302010e04 77
    0x1030103403150703c8001c50189810500e4803689500071400c400420b0303050000c1c44581424690210f03003420016900c401202e02a20b10340c5c0240c0c40440b50085010000c1542540100c044030068401c0e002c4424501054041507160404a0b480303841a01d110210311900c0c1c070700050110785a034000e01e5004c0c01070500c0c0c0040b48081c03070240320112a102004070200302c56003180c60314070351202e6800c0c003600700b040c00d284caa07810b415070241000408500d81030115025a50404403000155400540361402ca0341c4c641c00580507411204400c80120035440c00074801c81118003401c2204040100080d282038100325a007400c40c0c002801c09020818580e9441c0d0000d030003000418040c1d40a503c41c080e6501e024078042001d180000c0030310000340d0901e803e000310103601e44a50711443e555031001584411074040480e43c000042c40d0b44079890741c00d000c00d0201c03c420220044c401c08461018000b81151603a10700c03d5948901c42c41c042d00b00e101040020110031071441070b1130266205141c030754854a0491b0000d02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 178020197 1250 178018947 178018963
    0x60c0d091a0a060e07050301080a0f0303140a0e0709200309071d0609010602033903071b0b07080414060c010912180e040f03021609020919050f01030e03040503 70
    0x415583d01d42c010b004460140441a900880c6440e00c6440c640c18074003940c1d1260703500c070f0004103e001c0c2c41420004040c020f401817401e4010b424910b004600c4d000012401814206002080500603a40040340c0b01c02a03010300c01c489000000703400441800031750340e140700364002041e402141c00346100108815244540e5000055400c00d044500350805104103c0a46010b0b44418107551003000b900301905000318803c0403001c0004103e2600b65007034240894054014000b440181c0000185802000038601d40c1001d10001c400840501d030b9180c1c0404603003403003585405441040144401c1040c8821000d130300c030041300d0103001103051940761310100b829500c00400484048081818210009038000707855005550307219102c40c903040c0b80200800c00040c0140c07001e0954008954440d060600801c0054100c030a01c11025404541d03540d540e41c004d4000091140c441c03030000b48620400c4403070001c2c00042d20002040100183c0d0766200550041c4403203041c4240c18041072000007003031755051000030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 178021447 1250 178020197 178020211
    0x2502010605030105010603051e061c14071a0304060f180302060a0f02041505030a0b0d030f090501030501030b0a02090f060409021b010c05091002010b03070f06080702060c0d091a 78
    0x4100e45041208150039250142c120004040c6003000b0132030b0001002d40340203d1028818034900c043e171108808582ca000394000226501d400042d19203080006003103080900c0301206059909807038640c03802600211101c104c1c1c40b404c82c014008680861015800b008400f40301c10000503003103216200c000344442c0c2c0c10b03000f900560420010070500501502500c0181500c2d040e00b14a414246202d070406003545078444402c0040c0400060b14030b9038180d0292040d10070081202c0030040c6245001060000c0307030640c080003e80f507800300284950180c05514180c80c3d00019103020b90761404154002500302ca054a544200c28000c00c8059480356401407001d441c0143c07025907910b0500e0100d403104140b45500340f039160b03d01024800b4440c1d2200a507140510112014828145120800c034091712005081d0b0790f00d030103503900005008901c50400c004844090329082119901c0c200242e854244c11102c2c007800b0b1800f0080c206211a140d40b0410070a840b030196112118000080c0c5280718000b03c83e40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 178022697 1250 178021447 178021451
    0xf0c0c06030e01200f0c03130b07030f0c0503181804060b040c09050303040306151e090b01020a0c060503070302040b0c06090f1204091a030d030504200a0e250201 71
    0xc078402c2c001c1c0103841051044e14040041c0d141d0310071301e00c2100e1003102c1450141c1080402e0150080009100316450265580c883c003155503207650248020703510901c4211301040401110038140c50041680018840d003040c00382d410100a400801c24030310b800403010341e010304c0824807005072000070020a40507601031040020b03218400350a2008503024480d0b28014402440d00420403039900000b1102920b41c0580007140050045174030000e100c07502d802c0011416280b102e00070b0303444c11034103810044400a100c01c1c4010003015005980340d03019540c020f098045480001d00146000d4001140c0200292800616081da60400440660084001c0018a8100000780050720b00200405065180c4480c06001c040348000c00350f861340d1049102d4242042d4840c81e122103131070303000c0c2501d84031a40007400f0b0300e41001a21000030009e000441d011160808413600f11401032030f51042d43c10708a50043e001e070b2035090401d010300400c01c00040941c0e500000c1d102c5244610b90725480600c034036683d55000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 178023947 1250 178022697 178022711
    0xf020c1b0f060301170118120f030b0607020f0f0d030c0b09010501230307030b07210e420a05070206070e010c1109010605090301060b040e070f0c0c0603 67
    0x21155000d611a181103114a1160080c00308582e40d0760103c03030440710390207034036a0708004c2034054034058150310306072854050820b020001031002c0740f80c40034481130180ea101d411107002031340c050341107640418019410900c14010b02d0010b0425040403660141c0051402e0207245c41d0900103140303501d0784101100007421a480010803c60381d06066500100544000d000310340c1001c0d102e0304896401440180c181440307a00202254501b0310108000c1d5801403407c0020345041c0c2e4014002d2481503080403088810000c07480c01e041c0c40c6108440d030421580003d4086265580c400309103400c40703010081480344109143e004404440300390350705046000c140440d418070304200f0b070000f00c40e4010719003025034000d5003c008903150300050300c4001e47d200b424041c010040c142010b07002c2030782c1e01d0001c0386c10506501c00400c000e42c022001e0300c0c980108600902195460740403e000c7d50160b4420300640c490201c0120b52064010240d01e40c03035040a2034040307541c1c4d445854a500529543c0e00c010080b07030780c4a403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 178025197 1250 178023947 178023973
    0x90306020c0a0c0e1e0c040b121f0e070507030e030d0819090209040b132a0503070f05010c15050705071103010b01020a080a03060b0c031b0d050d0903030f020c 70
    0x40c42c0c0001d0107460b460038030902c0c5c80070b000f03841070103160450441e0060324000182c1e602003010554014186901d112500c40c000c18400000d000020369503826804008003500d058402d41891900a42d08a111080116155000155140d8208034001c400b0321120b0914414039031002c200c16800b6101c0d030b9982090324249080b04030071381c0c10a00d03c000e5079181005951030150301c501000c075400a500018000440c2e40d88180d984580a00d108028401401c4410290310b542c0e80900310101240501d10035032403a9030b5042055038900940c81030304950140c040082000f98043d0a0048000d40603c803140d1240070b10380192400c540d4102e0380000803640100300a0103114000c0205c40c00640d041e4001c014041d008e1001035991010b500004184081c00a4801c101078480d03044040244150031003c2e868001500c401ca0b01c036000650002092031154184004000c00000c00d8a030711041502ca241c944845014003501420b40c042c030070b50601d40c80782081c003000d610070b10050101d1808100a032584802441d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 178026447 1250 178025197 178025213
    0x90607060c090b0705060609060f060705150c0a09091a060d0c080c21070513034b0614010303030b030f120d180f030203040602060109060308040e0601090306020c0a 72
    0x900443e1941900713010040015000140e040c2d044007003225030f051079a403114001080c59030502c1d00c03541c00101c041040001c002d40010400c14071000c00614503400d036030f02c1801121900038080e00200240d44104200f20001642c0c2c40700e0000d05020030051084800100420030960000e000c11180c10b50350022298000c0d881541c9907003004404416903d40010724158003d010003c81c418103100c800341000c52401e5000700d00b151068503100c1c0800c260941c2c0da0400c2e5903101c19244181902d03030a00c0801e01072012002003007540849001107614860f00d1034107020707481c514900703204580030343d51038411b5408180140c0340c00e8001c5109580c085418203190b02410301703081045401040c01d510014488054041c548280d078080c1d043c09400040f080c000b51002c40411501c0480981054055a50403003030590200c0144107a80158084902c01d0b640c40b50790a00b00c8030f5501c4054903541c824007052042985034030381240c000c401458900402d40c0c0b00d4540c00c089a00c031452a40c295484800c0c5001089504 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 178027697 1250 178026447 178026449
    0x1e070f050313080a020901260105070302042c130507030b16020c031204170a0804080a02181009020a1e09090c03090206030a020c1f05010311030c0d030311090607060c09 74
    0x1040030f80103202451707001c140016018094161211800c843c5884010604640c0c1004401914028061030406c003102030025800741c0504629442d05210b0054584528260345405400310822403299a807085161150740300500740c101c604ac0119040000460071540c007150054802d5030200d2240c0000140203850f0000d0502d240d40241c128610582050910405950071551020b20b082d0b0a1034034110820700301040013400130105100443c0c0840d06003c0090403180c514420380e03003601c007c20b90007401c19540c1c1085a05801c005044c0500344a0944590003030701040482d82046150121500310441180c0c1c0c00c0080c004c001140008100f2042d10b0714080d01c2c1c101406070408000304003840d000705800b2b00c00146103034030040c2c00080c4904e00a100f08190200800d00041214001e0b045804c07040242c0004e00c01607940455a10280d0b0340c0b4500404c41c220b0740300c00100603501d141c00a07a001da029000d504507001452405005143c40c42c0c884e40018031203107100b03090008014800c041c018242c8101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 178028947 1250 178027697 178027709
    0x302150601020f060c0318010204030c05270103030c081204033603081e03130203010f0c1b03030e03040305010207050d050406210b0d110102010506030d051e070f050313 74
    0x88800d080303c81c10320214440350032807100c110b04c0e9900c1e84c1d1501050f4401007210324020440d1302c0058000144500108208142d50b0100c0b48008140e030344087d03030407a102d01504482d22140c0000010400a8000c1d00c0c0e983c54584900030041c10321001443d140c0074424100d4007031300840c03200049900700a881094044249180100800c407600b03c0c10090f0203203d0050000074490700d00059182c100a0f031001a070382a00c521501c40640da441c0c40008034000c1055644101d0003513090500c0b40c19400000d029038070303040040b540c6541340001d1600514600454000e410341c1030507a00c0c0549203101a05100503c041c500078000980e071042d4510b4640d1601ca603030343e1614100a014413040c001b03075901155071455000c111540c0b0080342549401d10000717201044040f58000301080856040140c1ca800300040998242c008100030340d214014592512258a11107002581c1002003e0100c82c003500d42c0c1d0290035403180400e091810f25510b8020f1920a26000d842a61000c142543c401504d00e0016003c0d2075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 178030197 1250 178028947 178028953
    0x20d0902031c27090213060e030a020d1104090203030307020d111212040309080d0c02010f0827070306090f05161203080c16030905010207050402040e011511010207030215060102 78
    0x1c450b5400a0010340542000c2a4209100707401d2101c035883d11104102500b64290110f68606c04184040d80d2180d043c4154408180805200c40c0b4a00d40821300e50045a0040c044207000c03000360f40c0355211800d02c183c074660702650340c5030010003607102040a14440c41c00b5030000c11440c000c00e000030704490b80421294071158044150030342c00114074000d44407a0305015800c1e44450310b0704d180075070f1034110340d42200d2181d05c203c1520380301d410b521600121004d4000e0b25401c00b0035200c600300f103c003140304680c560301241c85101c400c454020303d003006980c1c0640d548207840da101c1c2c03a5602c3c3d0040da8400c41d004c2e81d8101c3c0c601c0900d424481d0034050081036886000c402403a00340f910703141c40101d10304454042d051094030800540107032020421919900c1c803240c2e21200b480e2440c075007d060f6400710300545006100e0702c507010500d8181071003100c00303a45a41c540c800b1580e1810044030240306120702940100801804d0b080021b83c03003400501201c9200e9009400c4d5aa001300b8421140c480040031141154 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 178031447 1250 178030197 178030243
    0x60403050a0605270a170a0903110102030702090a0203100e15041808030a0617070302150c010b19080c01030c0f030b030c0d150608030a1b030e04020d090203 69
    0x92000112440711690015010403a9500c1410140c40101d020045081c005544581d0391307050a0085002044648a08094100040510b0b1040c0150103005107a4000c151494414004a4001c1c617202010010520407249406035542c082a030b290005e80381c00c29180e40204c140144116000311840141841e036450548034a0425000c00c000303484000054007c0307540395030040e900e0104030003500300142c00c0902a41d682c14001040402400c036445626004401c2d0f40c03108440040c0420b142084a4009200525450f80d03a01404515805001180d00c107640c0d030300c10304d002500e85040d00920b03601024484641c1d82d15240c18181061450007441e4101f51511074003551030340e007080b18090500d00a20380003500d800b000012070b207440270720381d0703500e60102c0000c04020400c40080c4032401c0c00e9941d2201440b01e0369645407901c0c0d40780900d0710104081201e00096802104071a420f103003109002c0d1801850361602c040204040381d00901440c619103494122aa0071742c101040407128001d50107801807112 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 178032697 1250 178031447 178031453
    0xa080a06090c080424020f0703020c030718021803010501061e0305060d062d0c02150105010c03181d04120c05071202010e10030e0d02010203160c05031b0309010e060403 74
    0xc140f00820043c483c92010b50b40d88a5035002e80c0c189074100005501c1156079007011000400d0542089000710014803d100084105003000f18015045512104094040030020030300c50303021750000b2803400d038901034103c0320303010a82d424001c0720300074139a6465528041c1c0d000706002034a1405085d00780241410101030200d1a201c000c03988801c2c6401c560b002802c0c01164000c0810305695040e10120081e4240d0140b66960341540001946809030302118048100300d0310074600c0401c244985d03404a14003007038600101e800392806c3c4842000071400700b8046929241b125050300220351181546140301320411003006900e2050035410342c805e040c85d403030400c8a5600c4c00da543c0c4140c09800010160070390360f0002c6901400400c001000c0042080a40d81400c1000400030300d040c01040c0303400d2107840301034000280180b017124011403020402040da42e8400700195103140005108581c14070040081080d94500310102e0381181d400d00024550300d0102500040070710201b5507141e07110341804c01c420000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 178033947 1250 178032697 178032707
    0x907050d06090209040b10081c0810080703080406110303160302090301180b0601031415040c0908031306020106090216020906011b110301050a05070c0b0606040b0a080a06090c 77
    0x444208032020030000c40d6a00d0410060a034070380e8000d4110711400c0500041080b05102d451050b00c80100100460f0758070708026541d120703003c45406c43e03900745404001149200307803091944840c110160880e036540d1840780ca03140160a50094503a04400b00f42031044c6a408190b50100c103100800560441c1041940821034a0f00700340f086050650000b0030481c20749003904203034484010703c3d0f03d07650f0a008a00705030280c0e0900325412800a407404003801501182446810b0080c032785081080c500f00000c5007840001e0020f0244082030094102c4c2c00500d01e40c080000704000c00e4642c04a04155181c2080a400e40350340381c000b20540c9005000112046d51400c03401c500c2142c045484001c15110b80e40140c2d0743c01c050025010b00d48194051550500c201c10740141c1c0101c40c158000c01041c1e0b590400601201c4058407110005140007402030086180d1403203054000c0401420b0b10314040d6680f140402951194401d0004102c0306410440c40c0410f40c4920b130000c2076070040c140221100480d001701 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 178035197 1250 178033947 178033949
    0x10602031204031206081006050a0e0a050c040302090915010b0c2107020a061706010905130e120d06170304080705150405030102030103030509040510240e030601030b01030201170907 80
    0x701c000c0c00000381890b106299001e141203c04c2d20401c40191100841c42c1c07540f6902504241c0103040510016050510320001000c0b101c0280c28140d0b180c584141030400f81c80d0280c0200c5070140140300100141e07417580812805003862000420441e035003c21010500f0344141c1c050110200113101c12300840d80c01081b4003450000200c016000344007242c10300c0b525405014006900580044800320b0308a8004402000c01d0018600000041d42d8500044802d00c0d0b842c01801d07040500d001c000c103003151040c1c015180d00b00580050790b4503a03508100503803694002c00310808100d03444803000c1080003400c0850821501552000c2c40c41c19040100e546d40d202d0407449614060304e0b040d86181024600c48095a001d404002e009640c2d80d42d50781001451900300c401c41c41e11861400d00801e900710340e10b00c165001c440d480381c5202c109c049200303401c18451310440005c000f03020314007d0306444ca603001d02c41240614410b100c080e20035410b50000500c0851109240300041030903c062180445001510350 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 178036447 1250 178035197 178035217
    0x10b090103020d180302061008010c14031909050106050112090c030f0f05060f011a181c060f05070201050c04061b0201090b1602010f030207020d0215070203070308070210030501060203 81
    0x250fa40e05140c290040207040900d9891250041015040704240d4042009401a0103a00065042c16100c0510324220381d00106448003061a003240e1442c101505006154803071420400b20b2901e2813804000420f0b96000700045a0700e07559070506200030340e000703100c2c1546504001c40c20040142c10390b0300e851544055010280150700d646025500b0800038401e00100c0c282c2c008195072040c01c0600b101a6004000c0c0900e1039881c1a41c0b1264482403481000d58941001841642c00000c03603450502070010011480d400304084d1044220002c26001d01400d1080300b0222400180c40c0307007800000f03084a102401241a2030381c2080f04104042e40038088209121585940a009100c6840140c40c2c0584d243e100c944894000714142502240c030300500c6071607a000780c84681c5080c09081e411000c0b403181c0307036000354030040359080c0c0e4000d82480014405c02d0017015060529000303881c1c0000f0b18044c41940f04480050700050301104500b41040d1016090b221802c0034881d0b94106035005e0b40b2402006524 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 178037697 1250 178036447 178036451
    0x80f150408031510020f01060510050a0e01030b031e15010312121b0206090d02031321020a080607030b09010608061e100e0306090706020303010b071407120501050609010b090103 78
    0x10515210f001a11220080c0c00100b45140e184050100039441d80c181440c07800d0594038000001071281451440008181d41c0399850902e40600aa010346407000c06103041da040580e98440d8840c1d6031410080c5c126001c1c1e5082046c100f00e10312640b81803811a280e020711810302003000042001070710b4031f0141c0c0420680340c00d00909c00c4901f1020030004218408100d40103140752500c40c982d041c7c01103145406201c9220a50b0b501040d1071000340d95a1042e030075011482c14100f8400c1044002d504d0a4802c5001c01c00d0142c3d00d456401e03000600c0d4114503400040554002c101070000240e014403815040f03e405a034200115890110f014208041c014078443c0102c2010201080751590240b030031000540040161281481201004069101d0304031501d020b4070886000c500d201c0303030000e10001203c143d503004601e1350b820490014550b805c00001143c109440d90181c1d8140c000a00204010f030001030109290600035080c400d00355000a0a000d01400001005108120340a000c44003c04028280 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 178038947 1250 178037697 178037701
    0x102030412080913090510050405061609091109100c0209070318020d050601050f041b0c1b0602031921050c040b0d090b091f0c050409020a09080f15040803 68
    0x1004616200c1c22003c40e0788013020b52504500c0560760390280b20b0941c050750456082d9001d514580c0d040300d8007034030003406541c01440045c00841c10300720156100001d600e0407540e0141e54a000c80156949060903443c00074008c01c0303006c81030600e4421030281c8016442c0c070302e403c0525600400d0300383c0000340c503d804064450004402e02c00b00e00b0300101000342d0180c14410300d00c100e400c285407191000c3c02081e20509c1e4070204c03544035103460700500c40e0a0000c10901c0e921510103004c10703192500304d1002100c80f844014406010b90326100a04402401c86402442e0341d107a003640b0417130300011013940901c144030f009126042d07c656950700d4050203541518000500fa2a010207039192340c025030744000041799002030010780d600c13681e401840e2040d114420800440c0c842140080c2c40b04040c140f280d1900000c806080012030403038010365094070480c10020724203038a40d02c3d05000e03680030b5040c1001144c1ca0031410800c68200700700e61102150414003508000102c0080080b800c08040c00140401e0f0300400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 178040197 1250 178038947 178038953
    0x3070f0509010e120a03020610050a0b160c081513121206090614090a09150b06040518040506010e06030d0c0204020904020319060605070f030c030c0209090a200102030412 75
    0x18961000b2940107109613009034980c0202e036070311010041d00314014060074003c02c0c1c2107038504040d801a10001085021403d0420030064030580007041031098039030f0342514070408a1081d0460398041e014400207000643c4640d2250380c9507120142003903407503000c0c15081d0004244411039054045090385440f03407204450445030070280840d9048050002c0c40c000c000100720b4071150384003c41c8041920b81000e540d03505a0024100d4000d2035001d45503403242010a00b070341d00b5a85c064500b4071001041e9504103604c42d400319120011040801c0000c02445040c40248041001140e00402c6107041c020300600c3c006020945444000c440b0320300f4020090101c004640d201c1d0141c8a008501610442d1603150000d0510f6400c402c0440d100404c0786040d0001c52203a20a4003115055134100e4201c1c6501c0c5120760b012120700d441c1c40419002c01a4500c054401a0388841714039000b11050401803580d0012402c110342c4440031034042c60b02e618100e43e80740c40d00da60040162021640000e808003404407040c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 178041447 1250 178040197 178040207
    0xe06090115090302030f03120604020f0703080c120f06030f0c0109180905030f031e13081b01060303030b040606020c131e0203070c11180a0b060417012003070f050901 73
    0x1400c000e41c94000c40051600703861000000e42000908d0401842d40b40d114002072108074400c9080c908a400340400c00c0d00080382c0540480c0d60080d42103121180f070701c5a410660408a14180c8200b600380440b0301c00c1c4a450b180c1007004000b40d07003441028091a0f20307200006004030b0358602c03e0340c20104200d401e510241090b0742c0301c1c40c46a60004203030380d5503019100c18154207500441d0100d14241000309101a1020300300c031641d205c0c03800d00e0451000c094803602c4c1c0c1056a003107100c482001450746031740c0c006002800c0c0070759401140310303403400f2404288110400c029210310350000c004540c07181d0b000000da55101d90311441c0745401428001a00c05a4585883c84070702403100c9055000d00000902c0001a4041c1d0070540d19800303510846401ba10000030004451381c8098200c02603041840071034203070384c03041e0b00004c8411070080c64140340c140e860040030000310404880203140c5c4d5554107203652464803040541c885042620302d00d442c61134103c801a004124000b050f00410601107005031581e400b42c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 178042697 1250 178041447 178041449
    0x110903070312021501150801080f0c0f0a0909030807031b050f0c0109050706020c090c0405031f0204181b03050601080408160c0e0907050a0807050f0d0b090303100e0609011509 77
    0x4101c218225a1590f941071b06030704004031294000360f50b800000440d0000810718004420002c0064104018150100309041c0b5003101e009a0207610f8944c002031100c5c0070302c180300110f803080d184c281061400c0e42c0c0150886409941100b062092502c1c500001e5034000c0454191804860082e038480e10210241c60041040c040c005095104151002ca080c50300050b119076000011504644141d4481d44090182d008030320410750941d10000588031043c034142002002c40e42000001420250b544562690180494030360401c2c647e5100c031341040d1188800250400a905401c080c0030b1402e0180000701804401400504000340c0410142c0f40781081c0c000f00407031190040104031500b511000c0e00d601c0b03483c00382ca856080d0700c00e1480024150600a10000840d8003450182c1490381c03409042c01440c106007121035910502c9225150005001c0542c05805801620001c5480b407504110480a481c003d07000400303024007100420085980c1c8501c5181074400460221440320050003080d182407101e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 178043947 1250 178042697 178042723
    0x100f26030c0a060e1c110a052a0307050108190b0d0b06190602030a1103130902070b010603090c031202010b18100f0509010303200a0507050411090307031202 69
    0x1241c21030a50700090300e2888038040d250400503401254202e81e81e440c20701c1030710040c01c442c1901d11002d9500038410290f0f400e10080680d034403070450355941b9040644524184103100d0800f050282004003002001c0e041c40d00c00d40040c00132605010003e000c080e002002064a4149400b03c60480302e0250010b0480c250060710b45042c0112074588030540d00000c84446019118100300140d105c407080c0030000407294590050351424001c407030304507103180c56088294403c0c4020418403015032544641c810003011010001a02c881d02840c0c00000108107070312010030503007040e02220228502c00584811280c1c007015a2a490005403020b0b4003400c24003081ca640003440c10454048086101c02151044210280300300310f01d5103d040d41130103800b031070140c5270b006041000140000390203050701500802000214115525200705000d18080e00100100c90540007a401001a070810f8001c048a1f011110826030600781418042a40c0f49018070005d0428041344a0070b0700c00900901c610114942 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 178045197 1250 178043947 178043953
    0xb03190308040b151302090109030c170114010e010b090409021c050d260601021c0302070b0c040b0711060409090c030b060105190e060f0304110405100f26 68
    0x1205040c040c0903054229403d03a030b40010100080c0001c01615440d5489610040442c1036034484d10000d90001c2d0041d1030621b05101c004180440804c208003803101c018018900e031080b0320a031002003903080d114135000803440100440014000030407905c02080c1501e003644840380c0c03600f180f1400100030342a100006500726811900f0000003281c1090100c0c5024090313000ca8050607580d4000716085100000c1215070288800070b520542844485c010350882d405104480001465049400c00784a02144100c0070a03400039404040041c035020a951041101c1809404c140c0b40025000c3c841c4a0410010310321168089046016a5040c040e40c0203420b803ca410049221710345001c2032011003600007928810f03190b20011305151710841c200c43e00c8078902690001150b81c6038000b5100e07203c4141185500c10802c0c030040d00e0599246020b03602c10b03802800144a00c802c0c0c002440100d500151400420b0304074143c092100003c0658440704a80e50201c203440d84500c480b10520000261000d60fa00b640 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 178046447 1250 178045197 178045243
    0x120f0203011b030209040e0d02070b0d15080a060b01020a0807060c0306080f07090b030a02012a0b07090321050316030b060d0603020a170c01030903020a2f19090b03 72
    0x142e8194045d00903480c066604000a040c11001d81e40d0342c410700c0ca801001a0300c00601131041290100140c10f22034000900411000d50a401e11140031645400c980c4035039000100075001c2c06a03c1c01145500482070000c0c1619082c0d03900c0f03c104e54412568081c14880d181c038920342e10b60f8842c1d03201400800540d400c1d00c41e2241d08504e056214201362240c0c122003800c0183c08512883c001c02c2d20a0040c0d416110700d80c84e4282a00303000340c11141074010042001d03000300b100340890001d071142e51082000d1750701e5054040c210320340701654a103180d10b80c0203d580909161035a49801070110307504001a50f0f000075031142d100744224060500f48003126003040d800b003604100d460041d04141c00b5684200e4143c1d40d0141c0340c54517036081d050145402c000e00d0f8401000d21550394040d80c0004291402031041d50520401a2211380c2c200d080203d01d50f0300801c0c0c14000000d080803004440c0d6803081c0490f410910708412008150145c000b500548001e80c3c0d0301e800941181e0f07001c0122003c2d40c1c00884ca1380c5000c17 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 178047697 1250 178046447 178046501
    0x319080c0f0102040b04060f0210180b01090c020a061805100c1b0c03061a0d0c03060609020702010507170c06070e03072c10090f060312030501120f020301 68
    0x54000c10300c44840e0748549109500040018000c2c0e8094999541085007018501281200c0281c51165042d041d4010401d40c00340c0d216070b40c003450714000c3c640c0921290801c0245068500705005a01500e002031900c2a0144050303030100b440c10140345c0246c0302240c4520381410302182c002c05454002e06610407010b481c0600b50301031b08440040c002686030300c25050500d6201c1d00c5184501500280540383c050000c0c00000c107594460411040c18450721032405411102142202c4c0488500351074001d003a80b070400030000319008860140414001c190308221065002a08900a42c9401841c00c1031140000d01c40da084031055034040004d01c8115040b50621020103040d40e0080c0440340d00900668002051680061900744c1d2456002c4000c0290103d990030b1300c203040f8401070040ca03410351a206000940308128002c0f104100304c40b000000301a032945ca4807111803100e840003c1c0505060030300400000c1003003440c5040d42504450400c0d061245440000c0c018180c080405074006402c00c0e0040c41 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 178048947 1250 178047697 178047713
    0x30d0606110d0c020333130203010509030918130816030201060e07080c090301060b0d0b090f0903040e13060929041203090311010204140a0b0703020c0d020319 70
    0x1d00d500007015102c241103000c00031650078140c110003a400d03600410708031201d0799000d005090410210501142141c500c0c02c1100302c4a08103960700c2d20312164245441056240038801c40da045500700c0c4c003c625144901c07002c1400b0400710759402c440101e035580002c04200b101c2c1d91143c41f1a03400822144d444007202459100600541b0090300150301c1c00742c020403240070805100b409191300c2d45031800aaa1003103480c819a502142e00c1982654a5a2000904441010151104114046011500c900a1014400042c0009000d00c161030901024001d81c504e022080f60252000c4030000c000e66643d4403041e04045080002c018581e92800030b5030b10500664501d490f040d56460200e544c0e0503811302c1050560a40e0544000d0040515681c14130441802603008549451017414017102e03076045007003000d089030050761002ca4080f8840c08014044d181c00e03400d82c030180c5000e00c95107042848a85000359a00da0100b035290040c0c242085040644d9400c0140720701e401c00c4400d061088500900e0210700d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 178050197 1250 178048947 178048967
    0x120603060204030b2a0c010b10020105091504110d0302070b07080a0801060206040317060a080304090509070501050a080703091401020304031d0d03020c0904020621040c05060a05030414030d0606 85
    0x40303a404c1040070401021942060301903150070f012103002006030719040024503a12031030750030500d5980c80c0b41500741519111040d400e0b4203896000003500b8500103204c1030074421101a21608060140300700000900240071002c101d96041c4c502c042c0c030240b07a00c3e00713170300d483d07410340005100c14000b0412500700045200100081070640e9035041559a036000d040ea51800241c4000b0040b80101c040441004a10b640c080d5102070014450008155204441c9007594015000040c01517110f030104685a10100000701c0104800c1c0391541c0b40c030360a07074001041000041c8c0300310201902c0306e0b030003024800c00c480c80d60820080d42d0b000b1556802c0c07514003c0d15801c2041901815991032003030000540c44c0494445c9219905a0060695840007004014061000030812a4400c8050005448400e048a400071007c0b416030180b01090520342859061038865900c49441402c2c10424404800d0380300c0306603034020398030055070507903480807030801170550240c0488603201c645062400a0004d600c452010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 178051447 1250 178050197 178050203
    0xa05011a06071e060f020a0509030606060403120e030c15030403080a05190e0a050d170c030c090d020d0611220803030609130f0803072c060a12060306020403 69
    0x2505592034601800400d016680707025211000c0c4041c0845000c40181c41d0752802d40c0305460026604081003034880480e0045180740c000200c0100307010290f07040421103282c11900448203182003900e195648820142d042c0501e40c208070b26400000c0c5952810851041000030040001d0000c140006803102550000c450950004c0c4000307000c681e14501038800c16001d000d005d018164500c0c0d041040c00060400c1940c104001d216601180000c1141400f07010b0003401103648141c104840f5001651408001a00300140e2060800030300004072014800c8407032182e0241c8140140000798000254864034200e000382102e818030b80342c05042c0000c04001c1c10a0f240e856813448040c5400c50399403207200181e00807540c5503842040440c02502c9d0159040340d02400402e0008510105541c4228800b611640100c40c5407c0c040240700300c468000e01c1481ca88680301d500d420040f121070040c3d031010740b01c0b0b80c212030003042c00060f401c440718490240d0400315003000d4000d002959981c50104001d6010348015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 178052697 1250 178051447 178051481
    0x160b0109051501320912010204062a0201030b120f010203240307030204021308030703020a020405070809060c0d143105070e060604051804020406120c120606080a0501 73
    0x1202d0b298000c0b11442074110a40030034407240701c800420814003130114902069550400d00850310300359030b136489649500ba9610009600c0341e28000c4090095040c180724000900062081441441d0361243c03045901038091a0100e0002c901d00081401c50702d03825000240b50017803a0300480c00000540056000e44400310420340303000d000f800ca18411040722040d07240c0c1a08010344c100b02514064010b80340c155403202c58200700325a280d1500345168000e020890140c3c0010f0840c2080d07140c18424990320201906005915240544c0b400740c840c10010090082240041520704c0d2804003076000d44079401000e5403801060803e00748421680c0001411305102c0480010300350b441c0024000610025540078008005907070614442d18040440101042d40005041c8400503480e56407440204041d00001200c1c0d48605140c014030054403080e420a070324541c2d400c0c1001d400103000c80e0300300040f62100035000d685000c891a2800180540e58400909880b50852582c00d003c03041d8041c0c0c6c284030500b00c03d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 178053947 1250 178052697 178052731
    0x309140a020f010207230301021b011401060503090316060213260312070c170703180b090f130e01060602070612060501120c0e060f0c010e060603060c160b010905 71
    0x1245d03641d2280c003030f55505101c980c000c04540c01009041c4c4d051054024009800c0012034011055843c0c0303d4504605140e44983c90441040c2c1d00c544403d024200500d00107140d464010a041d5a1740310308207682c41c0b4508904210360074480c40d40e041d5101c4010f00480c0400003641d41d1080800440d034101445054500703130590414800001049503202804000d006100f5a5044000d803000302103c18190382c0ea50505140d00100d86500300240040341c401d403110580b1401904803010240c282d60030241c4854810400f00e80c0588d105a040d80c1c804904690004120006444241c064210314000410f13a60801c640890b0707ea402144120540e0388a907120f10651398521031040588510703110350307400300e260300801d40300d100f51981008100101504112a500030302e1408523040d81d1000016509a81d0007244c5401e80e11400e003c0c02e103c00040301c004004508140c00083c3c2c555401a052039018440002d81e1030300400c1c90400b0700c441c141c002c150402d0a40e95130364050f0103404111080c1800d503282543d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 178055197 1250 178053947 178053949
    0xf0b0a0c112209060b0616031d03010203100e06030a0506061c1a040506090303040c03080a0c050708030c0106090509030d0504020d06050405060613050702070e19020f040f05061c0c0309140a020f 85
    0x1d80c1e030802200c480452142c166602c050380c44031100994270040688048219050761400d000a40c01801c0d041c8440c400186080344401d14008050011403090308103200340c002056000801c1034120300115454403440c40c2c2d546000c010040070503401081d0480000c11102c0c01d03002d8841f0244518040c0302541e506617500700c5256240d200c200c1c0d00400d00d0102c83c406201003111440a441031001c9810702c00c5020032180c07125442e068040d40110600d1340000303481840783c4801e015140c01055066814800c030300f007220480391030b400780d81e120220241c0d43e4000a8159650021800f0750150002010841800d10741089038452004582080c001d0503100550820410940700d10b40c810305450380600040c03406d000c590b10700701c5000381084e14000c11158105201070f8191000384021842070010540e21807425207202e82c5c0c00120344c07102e8420101801500c1800c8443c0d00e9003152003000040020f15542072610a4009000380000600f20144041044c03003001c5001032200c10f07080c000c0f2070190110302200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 178056447 1250 178055197 178055209
    0x9170c0301090c0f0e0129090d060603150c02030919050604090501030b011406070f0302030405040e071811040603091a010902071b0b071b030f0302070f0b0a0c112209060b 75
    0xb101d595942492200108200031684250070141f1050009251a1403a084001184451079400c2500e10780e950351020010000081c0c04c0b90f50309141508184540203000802030346038000e40101c1c074000e4407190880c40c004001d8a04140290800800050b140e80c0c031252004001e080c00d0004843e5900d00000202e10310141041e03011314440020141450190640d84003031440040308011420b5100c284004220755803a4003402072180c2015004048440c50510010301e1080c0c1a010414514038020701d03171509041c1c0c081102c041d900c040c00e010460451500d810640380e1848940c0c13000d8003602c1c40000c10710b680030b40c0080861500401c401005801c1841d00c0c1040e19200d40304205450804100e084001001110703403401e0000d81a80c2c0c50004e42c1e0b651110b01410031070800c03c90050300800e03410708c103460ba51807031300c4082c0c016a0001810b0614010010349448000e01c000b0b060341403046000b035050780d610340c0c00c140040030100d8000a440d02c448100d002805520504840c0f03c9d0811000d000e00c2e04202c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 178057553 1106 178056447 178056449
    0xd0b01060c02130506010c0803040c03081605160e07030e070801050412080708010501020c091909030f03180f081c0507090603060e060109170c0301090c0f0e01 70
    0x703481003084110742c1c02e5420468500d040c0900c003850360300c180c00e00d2200e41d202201e03950702d0f1540e080555401c24079038001442c1d070700e00081c0d140d40444e11121442d2200e2240084851041640079101d2000c0c14038000c1001c0884028000303504540309810500ca1040c0c14010365800603201c2c040c0798203413007044606890304103041080c401c0c1d40760302c1041c16901c403106140c014695410a00000e40710814592113071f100c0c8600e200030480043d4600f8408040b407281250030080c011091034058241006450707450003003890a0b0b024120385115502d58910f40f58401c0c1204210403495441280940054000541c00d030780480c4038007801b40c1030344a4140a0b8895840d81e0501e28580701c03004041e1002908040842c1440006104840c0d1b00804a0303002d81b140d854410150868059040d460711001c556255413546c01c1070881018400400d5600d401c0d0341c41c041c0441102512910f82c0040007600b = true := by decide +kernel

theorem cover : BRFrame.Cov 177877697 178057553 := by
  have h0 := BRFrame.cov_init 177877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 177877697 ≤ n) (h2 : n < 178057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
