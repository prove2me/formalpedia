-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5551
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:14:35.381818+00:00
-- url     : https://prove2.me/submissions/93e6f826-8939-47d3-a9de-49e4f637bcd7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 998201438 ≤ n < 998381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 998202688 1250 998201438 998201453
    0xf08040c0b03041a0108010b0f1e0d1211010203072001060b0a031d0a0503030705070303110f04140f0a1403210c07060c030f111608032203020a0e0c0c030403 69
    0x1e84d0740d081900013030303400040c060700d040c440e0086048002d4540543c105e2070720b00b004441041e44000c181c11340e0f4414020061342d210307100d011402c02e2042d4003901c5000d0203402c01401c25402d6007180d00803a03004004010145074000691655407141e4080441400000d000590250945400c01c050a034004511480c0080d41038000500046501d8502034080c9070300d405241c0c0b00c0c1500640a04a41d0041010030680791140d001880c41300d02031b250014041072451000307041d962050495100030701c4017050500c02a0700c000010114a4030496682809003000380106411510707a1050441400c590030b201c4110b91001d200d0000745201c0210150900301c004d00303840c1819000402001141d00c00c1e000045030080c0100020010543c00d0f03210040d0661803214201c40c000c0d01281c2c4084580945005091840220408031014040c00c902541e1209258003946000d08409423890540d40342992041000d80c80d01c01d41c3d001501d004510f00a403035550425404007911500620740380340d1000080000034820711 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 998203938 1250 998202688 998202713
    0xd0c052101030c03030513030602210a0525031509060f06211a091302010809030f07140c03030f070c060c0203030315150409060e0106020a030f08040c0b0304 69
    0x1048040300142591440d814030100007400020a4040029820720110340148054555040d508004a20441c0c40b9540d010036a0040b01c1c0b503001800c403806000608811119159510002074002040300d86440030000a041d84d0003181c102400d01100135221000b40300780c1142c8058007401074a01c080c40c0e43d07558414001c14a80c0b003201305410a0310004108613104092410705107001d0350b196130412141c49500e800034500d081c1131124403509460407600c1c1d0344600c1080d500c513404080340100e40f110140005080c01070000c1c001400d60f0410461288040b0807502664030487d000f46034440300c000841403092a10410b80082d55052001188005c02c1c80c450000500c00c40d40f050824095a9980700010b441001341c1c1c8100030b506070000c1c0005120070302c4541c6012900c101c02000d648040814041ca94002d61013034100d414960f8403100309021007807042ca69180141aa803004000482617034030300a14003880326101c6001c00c100000070805100c4905020307002340480c03070f1003036640b8109031030094561282e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 998205188 1250 998203938 998203957
    0x9060607050615030f012d020406140a05040f03081803010204120609020307050d050307120c0804050d0c051f080c18011803210206160e04110715052e0506090102030d0c05 75
    0x101b00182031507c1c065030080d641104c0e487d0f1100000700d071505180d40c4260304a44108010040c1c2484001071501240100b400210f000351b0889640750449040b42141200c81035206000f60700400040041030610f09034040c1c4075410030400540903400c0d10000381007810690081da889071480f502d0505001e40840102411071180c008403600d0f241410040d203501070720754006800307290306010810003800d0100b50300a4071031007400c0c20180503455a0028103500300080342c000041d04283c48c0d0102d0b158004410b1900302c990284068107143c84615500e400a0b90403801130f0401801d840c1d0628012a00102d80c0059948004451004400107182956081d01e1480c070000520880e00494003103030043d42020b071580314640e202c40d10700c000c01c02440054904071500d2000c1600c01c020150100e880008110380c000d5080101040b0b5080c14020602088403880011210000e60002104080d04626400080301c6041d1440c03a1a001d450340144d007180102d5a40348440f50826400c00f50031740e8050002c0c521200b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 998206438 1250 998205188 998205251
    0x70503010e1e07081c0519020106090c05040b1905040810090c14030d200a0b06091e0601140f03040b010501020d031104090203040c120c0509060607050615030f01 71
    0x404071075410fa552416100c0c440c6150480c540090b403982006034011344480e46820003a140c601c030907442810714030101e0580c00060b59241000d105000d0240074561440a0b42d1600908040c180860550346220345240c0d54811255234020040d0240a00c05a4005010040c2a110071011305040c00c00034041c07405040301c400110000100c1c2e5101c000766001c8182c0005401001d41522507441500c1040c1404a015502003500080005607030041000e586000d10601d966011410300c90140004944041c2c40c403403101d4003002045002d10210703140d0562001d001d10709284c00015094500c58035210b40a040310b400e8400004020a022440406504a82c0d0a0703085070400c3d80780307032001c50441c3d810b240345801c41c2c801000100038091143d00a190064040e5140003550340d0350b1114400c00440004080b1014642514100f00031b01d80242084e60190050341c0f05464541140d40380c544510b4020001d444071045c00755041c00c192400c024144051150000070003280c00030b01008501c1c2001e07148241c1148 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 998207688 1250 998206438 998206483
    0x2100c0b01060c050d0809010b06040f0e1312081012200f06090910050a0e1009140a0207030c06020c031210080a0b040501090b19180c05040e070503010e 67
    0xa9100f5a060780290780c0003800307011030401e241c0049a5503100500b51609a41d01e50070041c14a6403140000c04c0100741c1c4100048100c0c5c41c201090b489420002c142c41086034042200b0710124581041280320038645181c00c540e103594246c032801100203e40c01c5942071042200845041000c44003131780e03240c2c800720707081d03507041c03020080420003003940b45140d403138019200b404059694240b045d80726070080e10041c446d80e801c0380c5a10100c1c0385412a50f201c4c1c00c01100700700c14024500314810925010745800b0340d041c85841c1d07070361811541d03542014241c2d1034601c2d0700091441c1031500c030f80c03005594a684a4019076440c02e0800216a07280c10040c20a001c10800401050500070309003003500c100e80251026203012040340d250702c0203402c0700400944455480d40c039074400040c43d88010030702c100c030030900b5490703100300f0444200111a404000340d000810382000a0006c0780180e02e680e01141d800b01c40105966805801550500d80307203031312054041d070030150100e0442e400400d60089100c207102281010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 998208938 1250 998207688 998207699
    0x1a0d1a030c1014070302030d0e070501141201150e03160f06030203040c06080711070f1401020a03210b0d06051815072604050f06011a04050402090d02100c0b01 70
    0x4061810b00c5400c003060b080e10300c000c2c0180052004e04080303400790040e01d052a201d041240103641740c40c18014419000f4600030b1100e5030f003003403403414a84d070185003c1e4101210340e0045903d0201c103006042160303a14082100c0c40d540b00e0b41a52002c0030b00682a18a0381503e5038042c01c01c020306000d000f0804150f0040895140c0c424408c2d01c6c459500021021203640c82e100003a11821009804003040014031411110a80d1040080ca0300800f034014004170a02d00d44034020006207100300071141190003e00c1c074480420740c4807800d501c0305d5100122860050041c82c40110050804820a540205c0e06088541c00d00c606640a54490240b445000002201139403030341d6101d03881d40703030420f85403801440414080e5108503001e0030a030142da80c05919203070355001c411001c12000c03901120194003801c103c4901c420188500c50040804131001520321151414041c0640118001c0c68000c1d0350105032040d150355201304451200d038020700421140540312900918140d42d98009690b10340891000054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 998210188 1250 998208938 998208949
    0x7140a03020306210604170f04120305040b030c07050705040203061806120a03022805030a030b3016230d080a1214070e0405130501020a11190203071a0d1a030c 70
    0x10313232140304c2103c41d00e0541481d040071404044644142c04020082c4008601d9100c0c450013036026000c80300843c1c1c1c5400e4589440748c44c24040ba0170560007640107009010044c0c0320700c890015002100045000a940e42034003090022030700f0640a04a44503030107030001410340124171814041d407580c08441c12106500e104522440040300000c105901c1000303550003d61280e846082c0ca240010300c103046070715140d0f40208810340070b03080503070341e414200c541c80d00390203020403031000144240b4141d051000d24002c0c109800d030202c43c2c00c442810002004007e001d079100107424004c2c0c0d5004170403d454014042000b0800c1c100c0403841082140b421881c20680c06904192074821f00b016650405421116000c1c4005880c01805449401c03840e2204540000c0c82070002e00480d042c01c1c0c0c0c80d0b40d8100c0b00c0091141c5043d0004c4011088170061072a20b0000d83c50209840c001d0b0748000050481000c600803813a038152007006e804c0203540349001e44058008070b00f0716400900c800110122086580e40c42c04005c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 998211438 1250 998210188 998210197
    0x90901050d240e0a030302041d25020a02090108070e0906090c1315061d040504050c1005120408030613053903010314010507140a0302030621060417 65
    0x1030091a1080b24541c1003089202031001e031080808011030400d0700e01826074a09003003894110042034001c1000c6c494100005003140200900721000030f400c0c208a01444050786182d03090034840d1010148598105000308280050b85502905240d000c7da91260003d0302c0710024001c2d036130a04484000700310400c0780010518012007010000e040b10440820812003004d243c900081145521011010540103880403100010540f070784039890050820034500c800303403074100d082d0780c447ca00e81018480030900004101700811025034010340440300048048d6114000c466070980c042201c0001c00081100070000396014407001d0f81c0d50384a1080c64000c0798187c49007200c0e8800750b84450411000e030005e03030500c542c0c00300c3c1c003e00ea0548914540100c00d19250b00c260829110507071080e00c14200548241303e4554490010f10b0400c07030305d41c00700381d080d41148036a004031420590040042183c580d21b40006454210000c140c140138220090403050f1511812981a10006c1c85440f014545400900885 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 998212688 1250 998211438 998211443
    0x9050105031501081e07020c1216140409080d06080115030209070c060f0606030911010c03090b0315120606100f0207030303020c0705060f04080d170a0c1112090901050d 74
    0x1280c8528142d00110f039001c90050000354401c0144a80b190005150310000d405540194050403000013580305200000340b0703404140120354048603080304880c19040c507000c1540e4201e0a0a505050707080005001b8180c0f400001e802c5800018212400c0031483c0c0c0410304a80549009008440d440c581c0740c490401b240c80041c0d00b00824900040400303104100e8400110f20072030000848002c804084006c640301340e0000c10103e580c0f070511a00340f001043c40b98080e20400d10340100c440040346d400500515140c480d000302d048011010900e021644002c1115504e40944600d18804100001541c0c440c029101e0f039000e040045c07009100c103881410080c0c161050340d0011f1268514507501180254001a04c5116900541c0004030381f541d102c20003030220003042c0707070300c1d689a03030900c8221030400040b8020102030050000c00e820f03030b204139440480c1d840340050b00f00158a100c645020b03a465030440a00026038020340300444080741702800600100c003029108002030380c0c1c0b16424402074a0500802 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 998213938 1250 998212688 998212711
    0x403120912020105160b09010b150301060e1003201c05090c12010914030406020d0813061107050706050c0708060c070f020d0f0606170604030c110103061d070905010503 74
    0x100099405013000302480e02020305500d212440c20344a0000f004429910414265103030011102140790142d10806c107220311044040c03540d40740800290030700070506a21801621102d1400343c025006c0c0e8008180d40303081020001e580803017152042ca072584055a501c807142c8024074507a000c2070091203518415101403000302160010386c410041c40b0014009580c921750b482e090b000e0001040c0c03007010a0340136034000045846030706100001c0e090405185140042100c02e030100100140444185440c10340c0000d00040c60701d190401e80c010920400310040e15911514900040442d0b00000030032103001400160790000340c49850043c1c4503075040e600000210002e12640c00850000030900c51003d10080c90040a41d0b12551030301011310281406403950b69480500f04030f0040101400202c03264208003034281d5142c5950094001810808041e03c410308060085003071340d00075070203000500a610030600c5152110801c411a802c022180c8000140d8400710001c1c031540664241e03070040740301091 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 998215188 1250 998213938 998213969
    0x5010b211009180b060d0b041b0b030f06030106060302070b0105060309030c0a052803210b1e0f0306010f150e040507030905010c02070f170c031204031209 68
    0x280c4004504007810010966030032101c0000e4542c8203200b102400118042191490304080c02e0540d000031000b010540900194480b003400590010b10845e403155001c200b08008075402d07440c01080d20b40365001104a850700105000c03981c111880c005100e0f000440c000e0002645940e41201a0700954030f000740341804a500502c060302d080720207141c0c0043c0c1783c802c5030b080400404040d440d001700d0309400e88254000b12450170314001071550804481d000c0040045941c5415a0000c002c010b520400c6150941d1640c10006940c0c041d4005821440008102c001c6228180840300001d680106202d449401020308600041c02c0100e01141200c011240e510f401a242102c0e0b441c150100c212600e0802011804440217076403244a443c0c050b454503500050346e02e940745800390843d45800c400e10155802442d042021680007070014090760000c2d60250b0f0880c036040181e0f403030550003070842c0d90b16009118401c18200010805001224000c84400c004808c18001c1a58220154000d00400c1040000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 998216438 1250 998215188 998215237
    0xe0705010c02180115030509031305060c0705030f03090a0e0105091801020d060b2709070e031f1b031509051909080a1202032a040f06090905010b 64
    0x4001d50603440c0040c104501407441e400342c2102c0d15009801881808900c1000b14102542c50b210706948081017000642c9400c1445640c011350000760305c2054814000042c40450078038041c00803000500003e402c480d80340d44940e158030348a400c03603a11940280e0411800241010350341c952281203c501a0850503592500b6004a402c8411510b41d49481e640030040301c4c1015656104610003400800156034981c15032b0f400d4140403d288940d00701c07501031750022080342541d075000800d40003002e0341408002200c032440885c0c2031a0304c0c2d420a02c0d443c00803000c000c3c9900304640061805081c4c000403410204041003094044400c42d9080b1941034200c0d80b024804210241e00140c0c200c2d1211016040c481520100e80d02514180b10046900c440041a01500690800f130701002411400340107600f14a00140e00241c000c5909000503d404d0b03c007e46504188024022500078002c0c3c54000b6a00c10b460707500142040c3d40c54400e0400061800c00000344040310f200a94080f11192001511100d5902 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 998217688 1250 998216438 998216447
    0xa08270a060c0503070c0b0304060605010507031d0a092a17010603020711041b020c040b060d15031a0f1b2710090e07050903030307080c070b091f0e070501 68
    0x40070115a588420171045021408601b00b0000501031104215640d140c5803501c10306481c0c00d41c0c81241070040500441d000241c100d03000c0401c2d4200f9200c0c0f010f14002000020303011100c80d40c404070b0f4592401c003060400f25488100d44c4685048002040a80307080341100706d07450300c0c200d000110105145401800528466001000e6a5000d12820700410440400107022500d109502000407440c4904450340f09806001c0d080e02104103e4041140601c4d80c00810401c1c402c4400c06844203554481101d8002085d401b80d50145030042010400317201d840a1a1171603110694402c03451031b0800c000a0b2119060241c030320f40c0c0d09501410503047c5040c0004100300100450700820140303029007500c0d8466120340724040316800c19030340c403000000d20380b65010305a040c0180c1244200582000320500b81d440000803280c002c0000d141c490380560b510342c1020344c0c034003403000010940358038001031225104c0e00182c140400240422111890800c02c0c0b4000102c46a90000300c0349600800700070820766004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 998218938 1250 998217688 998217707
    0x3040b0603011d0c0a1707061107030803010608011d1302010e040902120a060506040b030a03260a02030f070206040b01051002100203010305030c0f0106080c040207020d050a08270a06 80
    0x1500228034003c0aa0b440d070360403901c22021000e558081d00c1c00320141d00c1d00c1e041c03142c001c082030000d410070001102c0c3c0007500d542c2e02e4002c000a00081c0c0212000503007003000300318001c5401200607616940c403080000c1c01040203200d0340581840c074000a000305800501d030b060188001a03400441c8140c01d43c010340310000c400034029846552985440301688034045003601405003034014040ca411a482c20301c00701c80025007007900545c0341c840ca07010281c4002540c5030f089501030916040341490343d01603828841c0f2400706101400c90040510440030f4032a00518000c19140601550a64403440100c3e626442101d024000400100c0100114109001c0c051100c440500c10f803140c4414494504d8240c5e482030f84216032a6000090903481600180f01001c80d441c80c0c140244105450400c056658281c044801441a0f074000740c400110b50314500c40c1540300340d00000f558003207241410324440c0b0750804600503840c02521801c404001c4140c01d24000b840d48000c110b44245803c181d8111a00d008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 998220188 1250 998218938 998218951
    0x8011d0f15180a03020c0a0e0c0d020708040902040b07020108070507020a0b0903010b04020316020d0503073c0906030b040603021302071b0305060105150f1207230405040b0306090303040b 82
    0xd800509020b4904180b103a224024001d0b0001c10f410b41c1c0320020310454070a40c2d4000c0f10310004c0001445041c800420880d845a40c0c000c07005601c41226040c00c118622560744101d41e81c0344002400903c140086014144e124000d8071446103070703521444161703103d01c12003100030b612a90001c000e00c01d440600d80500101e02000d000003c00c040c40c0c4022408a9001750b403003d91502d24802c991010590400102044040b90314107603045d810700300c1000d000c81020001da00f6180e9040941c01c00c108400c502540c1e001001c0d00405007400740c40410140404200b80140340000c0d080002c0080a400d190252804503603010b0500c03007800e205440c60314004c0d0402c14040f9004a82104820212140e070908500070718040d030b0181669500d080e0400c04105000d650032842c426040c481d281211422109840e91410845161100c0396101402103c004070a07242e40903521440c20380040ea010302c1c290250003030384c809507810000c40040c06e0415560307070f41c00c030b951302c8003a8820800580003030a2600002c2c0c0101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 998221438 1250 998220188 998220211
    0xc02010e040239033117100c1e23030105040b01030e2808031f050609060703030504050c0406030b0708090114060409021503010602030d0e12031b0403170307180f06050703020a060608011d0f15 84
    0x8108034541c160501e1194600304ad080c8001c401400940b40511800070301c0e0809090420940034007050341500d4002840d901c612840b101e8110030340a04030251805c807519400f5104039581d02c1c1c00030200354200740e10000d8091801c104180443d071070414008172044070308010161070810480c2d0b07500f20302401008004848d2401042d101d4a1183c071140900d2001e1889100010002c1c54866401040d04000602c002c90582c10048a1a02d00280c0d401c3c0d0394203c08241d5000ca55141d9500104011080c8030010f80400c400004c0001080d550100c050101e10641d41801d000340c07101240d8803540d503c0d165210a403514820000309544138500288600540485100e0600305950380c3c5074110b0711074009802d141c07071600000400c034589a101003010b05203003000d00190303004d82c1405101e105034400c41c0180000c2c00f50000e1380c001494000c00c02003100c1c5074003100501c0616141d40e6020b0280440000d800001c4481d805041003000001c20040712020303055000740a50400c0031445a100b0001030071111404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 998222688 1250 998221438 998221457
    0x10b130909050102070b13020114090303090d0c091d060c130306020705070f06083106320f070c02010e040239033117100c1e 55
    0x50298011000d001d03000c0c00c00180c0340c921030300b070044200320010b000c6092200d1540d0081c00507030b001a042842c11620b15503094a40300c1d4240401d245110762400300f944140042c3d401400c004149007a070b0140ea40380c0e40144908100702042c1507200f21441d01170465504140c0c00181ca000c210005048656050800d12060700d6036500c4840c02caa000c40c0d41551180c0050100340400c8500a4125005040c145030200c11441c0c0860100b1444900c21b21280015088101c0d1707402607840140307603618040c0c001c01c08000203009020a050700c10030b02b1540200154403130030490141090020080d102d20701a410704c1100d40da44071390031100c1c1204443d0481c10b00000382040d0341b65844a1001e4100112001035070100007031203981d5004440e9080380c907681045580d80c62981030711008026100103c14100600184a02450202c190060790003a41c8280c807801000005254400e060245c80d0b03411088103880040782e040c070f141410f66090414078070100b01d52802a181494107007402c85802d80540c42d1a01c0030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 998223938 1250 998222688 998222699
    0x9060f091804080c060705030c07030806060906130905090105070c1106131d01050411070b0a0e030a020a030e0108150f030f01050108010b010e092a13090203160206010e010b13 77
    0x141d18041c1c60a640c100360124004444040c1000402e802c41d119044c0030742103150911103100a442000001002c0100d9000401c0842d21030744161070040f40c3c014501921208100c45042d610b18042c4039a490482c2010041400c2003018401d80e401058a5500d2141d082c080d6210040d03488c04101500d0b4100310200103003c5565202640740c0058144610030f6141d520f554051801c00346c0c81030b003149210b036280880c40b84c0e5241100c0100e60307410394801002c04055469282e041d004040032800c0b05828000020b000344007540c00305924440070704c40c2c5c4075202400291401183c00c2101200e000400e852800700c800d11703510b000c1d0141250a00010220744600b4220102c44d402d483c0e0a90040601b0380d1180346c402e0041d030b0410003603402a10240d5602d8170500e4401040042030b107403400500052202c44080b034624268001c02c5030000c001001d0b0402c7c0095507410024025481141c1c864500360f0031074040000e85101007074103030495106001038022070b4201252290306500482d101c01c0740308004180042d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 998225188 1250 998223938 998223979
    0x13060609030b0912210907050105042102030307081c09020303030112060b041a01090602010218370302150712030e070e0c0301080d110d0c020d05060411120309060f09 73
    0x1620001a0480381781d145900351000c020b2406071581c1c196802910f810700c8107980c010262001c645600001c83d4030030009400f08501c440315004003039014000003961a05020044004050f6a00100c0000045480c0c002101c1e080301e0440200a5240d00100300400101040718803044046024080000d0011503146c00074080740d403114010042200c845003d58819a0043d14410080031307140000d610f01010114800300c5c607a0802542881070707128013011481d401840c0c25028400c8606d40308a500d1204031031003206825200c1c442240704494418000d14120414025120300d00ea010001d0401014811400e601500800090b45214400c00740002540b402e003081d900d000c0d260740502c4550303d50600050b80e00b40308074600783d14140543e510020015100008143c2c040c90301500e080070b6120100e20000b000c075800744a01030194858070061200384094082124445d800496400380000329020945899001d0420000c0e40002d051160524004c4807a0050107686002420000d403132008190408 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 998226438 1250 998225188 998225197
    0x507120f0201120621021c0b0a0e1606050c010b011b02010e0f0a090204090e0c0117280e0d0f0e06070204061a0d05010603140109020a0e060408030913060609030b0912 73
    0x200464061005c010640c10000d000c0c003100500c0300006458100c8684a101c440100581400201a92401490010385042c054114820003c071501c503a080d0340ca81000b806904201e0b44864030b5481c0100220301036010f00c0d4549220101c0b50000d0391071510741d40042d5807244645040b50707040075407060020385c142c1d586184003003c0e000300d01c0c0042c1c40d94105045001251070100c82e8100e0fa5120902e03d452aa0308080c00a404041404000c2266030340c0120580c82191000311941e080c00078021300810002c03203a00802061041c2d03008840c1961060007017128034440e04190000440c1319405e0440c4035041080003072203240d0029001103051550f904201c0c1c1c403c0040c048540760a07901190901603914603026060062040d482d042c00a0888505070006c0442c06114140003107600266481c411401180501414400200780548495451091170b441e40d000141903446a00800c0c8510540300740b600c00c10041d1030507940c42095960840ea1181080b85001d001640036108072144000b401002c1001030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 998227688 1250 998226438 998226479
    0x806040e0118060506040b2b080d0c08060a060f03090c05100c0311010207020604060e0409020301060b031e130f02032a0a08030a0e0616020604030f0507120f02011206 73
    0x9102c2040c1a0804070708035000902458807603424042c0f850b10556407101d0141c002915031181a066410303035100303002c0b629248240100340c0da4010a0a0300350004503448a05200c074036031a400e24a59418013000361034a002d0084030301196074041e15000c030512a51011041e28841c01100003142e884000150b41c82d0f0084103030000040003102c09408065100d02ca042603040c40307100a50601c5030660000741c42e8016030240c4010010806100042c5584a03001060314940140007000190b464a40481c038070b50040701d58181c0c4150865000b65010104c001d040d01c103d1110011400c01d2103039644130800e51580c880180e07450f210381e03009182d0b0408145c41d141c061440e914807005200c80f00805000c1c54145c26449a00c090300b003480500d1100380c200e0b91490148208030341050b03880c420202186009915004042d400c841c0c041004030400c8200303c40166900e005030f044130700c1035685c0d981075800f0b05501c0c103000f49508140e401080055005e039403d070300707582041c02011550039101c0100905200501a0742d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 998228938 1250 998227688 998227721
    0x15081b0408060c1b0307350c15480406211b11010f090822180203070210050411040b0a050d15020c12280804030806040e01 54
    0x400b01078034400c0090a035204c040d0020714200710554956400021003082c2892060f1b0403e0700b45600307410100000010b4034440502c03a038680d82c03610174090b1741d04902040300b0005440007021400301075020b4102e075590640d510201c054000312724014400c025004101000300c064200010b0710400f11040a40702030f0000759104646100e00014002c0c8040400644a041c21700d00300a1014a030710345042403000b5145402c21242c58110301200034010010220510881c503c1c0c40410030401c8420b00c0103110822903151902e4901801c204413213420100c51007010a04010043c0241b1101c90300d80255a0082031401030b1404801040c0d074540a030345088404450100101c4605000c61510b07120300784042c5030035502040564102004034144c0c0045140190049496004003418606c040e0103d4080140460603521a101c1d5040c1001658001e407500340820005052800c1c0402250188081d1584040d0b0382c0b0303007590300c07141c03010744450001410841d002922940c0f001044c0c82d00340140302e11144d86550 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 998230188 1250 998228938 998228947
    0x60d1403160f0b1e060108060d150204090b191e0806151e2416141b031b03010914030a020d0c05120309030d141015081b0408060c 57
    0x80640c0d0700c910080a160550310016446800d0704c203c9003110303034444d01c01c0c00c1c0203ca944891000400b00c28a40034000c0103c0208104d844000c015074015004945404400b480807004031010400000210448001003000c81c0104101c034030b03000348100500a9540a28007401d64450794404e0812201f19003001c981d4148060a4085017440c208140b140508440030524a18089000814600c00b0a4481c03080d400364005a600a8181d1340498007400c40c1180404214200d82c13400b8000441072422048141c0104220711060b550641c5864051002c01809007807008440f4010700c0004030a42c8240d601503507140b070180e0000d1540d0a8200201c07841d10000c0d6221080c0301b000a2802612104c55000c02101080200005000282d04050240039824441c0c40f940e85010300340c558042c48030300300046070603c1e03402580c2c03c0504180f81e0007400815111140395880c3c459503080d14007014040360000d40d50304006452180d811441100c1045d241c12000c0c50700759603001035031038024180c842c41d84114000a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 998231438 1250 998230188 998230193
    0x219110a0b0415110c0c03070f0e01030201140409020c01090606080d1704050c060307030c03050705270f1003020301090b090c070314040b0a0323060d1403160f 70
    0x91560412140000200340e09038541d40ea0307401c0e40c9400b80000305040c5580c8030150011240380c21482a5440c038a40f56501e81e4060911286c0d00c0600641d214043e021b402e00c0419041c0f200f50b0380105032444840c2c0807519902e50b600440715030072161031941160400740408141404640010f011200b540c9002085281003400e194040703030401d42c03005c5801c3c1e1003500841d100e290098512821603035110020070003650360303080c19418600003c8205a01400020400c00c0c1c1c03d8255101c410200e07540d42d010403030395807609004e64042c0310b600c19117855900311804a5801e80c0340d0758030801e00c20b4800380100f01020000c0c800329100b45c090348141400302c0d03008030045c002d1180901c511840d41000f250210b04a04110003114814415010003404101d80700c014091540060003c03078009090802005d50340c1c1842c0e0400800900001c00c242469900710340051507210f40407001d407800f0314001842d0241d2001c0381da40390390031100315410802c42c0c1d01081c020a106400200010702060b8001c110700c40310343c0e0091 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 998232688 1250 998231438 998231447
    0x90b0f0d060617010e060a0509060a0906060f02010501080706050301032405012304020711090a0e191a010b090409030309020918070b12240d061505032b11010219 71
    0x5170800702c98000c420003005110758524a1180c11039109950300302458a5030404a1810710301c5801151031581080d1000840d954499a04141d030b0106600811050340c036100d0031615004944210000608142300500c082007070b0324044800308000c0f2003041030f6809103e0a00003550300981c08608448844100346070784102c1804564100f403003c840840c034083c0341d640d03480c401b81e000121160040d8800380001d0344814695020301e044044c65400c41d07504400003214036203941801c0f0422208081104107604046103506181c605803600111041d00b4840c100e41404024042c0050540030580c0316920315015850f041907481c00b81041c11988000803501c000401e10f008001c0d03204900391001000201d401d1500055a150010030001d600d80b0282401c000160a0000003030186a000c20003002c2d0108200e441c0c0d20071590b010448180f0301003e544c503410075460b0140c03200300107d0140c108400f815015101c1f5100b0360800f9050806548400c4016915800c981094a0040d440461740f405405410f800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 998233938 1250 998232688 998232691
    0xd0806190623040f0605031810050709050f091801180c03020108010806250c140f06160c060f021303060e011508030a0807140a0306170d090b0f0d060617 67
    0x402082c925162400d42d1068010034944204004c1050110110362800c0d008140302d0401c510035812603a440c08a04c050318020700082d40c0510101da000d8000290600303121b0000c4207105001007840d241641c511420070714000c1040030b0044c0c25582c0b205440d401d94030031032040c0b00c0780740500c1002d540360781148005001d101301a00103500c668815420400403113480c485003604040b4a40700016a850f11100c03d480d0106c110300014445c0002a0049000710800640094415124011124151640c10300d480a02c28100242d000045090060802080c0c20350410380f150004c8003001403030700f414040c40007600d001e5500120344d03940d06c4d00c040d1060300009014400500d540d4400310140280780c841c0b000d07034038410f142412090041d090000b954031406940b480c221090350f10489584c4000c103070701c010001c0003a8043c0f621514400e102d0310185c00c03400950204000f100b0b031035a0f003600781060071498091b04180c030006140f0300100250401100a401080010449a1a0020410842071980c0d040500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 998235188 1250 998233938 998233997
    0x405121c0809060a1503170d05070f120b0a03020904030801090f0203150d03030b120a2102071a07150c030e0c0a151101050103120815030d08061906 65
    0x41d410a100c1500808501c0700e4114603c250300007900c400c0480c0341d01ca0589650b00260402c40c14030f0b00d2000795480c1c04018609580c0c2900b0402440e9500c01041d00e0002030a060080010481e4a01002d80f60607035100e000395810081400d0b07146a52507001402c400c03400c8034110005080d000c01005040c1641c060a046082a2238055055240c80b84480508001d84820f040c89882495040414503020740c3c00382500c104045c045500384420414503d540324106c010458003001100542c140c404da0b103802d001103140640c2c4c09001020b1410740f0443c03036030783c58801a1101200802c0b007400000c4003480294081c061086022404040c2034102408880c0450032604181e0000c00300c401869a8540704581500c1d02004080100072850340c04883c86250310910411940c601340c004400d1182c0100302c0d4104404503900c958040c0c0d10440c007005503007a9190f01c1c1d90107034042e140d1040003a00541c09107a00c900050207001250015031125132510341d03164441000700f190891000c41c4140b030b080c90341510700d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 998236438 1250 998235188 998235197
    0x702100804031b03030b121605010311030a0c021005090c120d090312020c040204032d11091323120406050313030e1207060e0405130204110405121c 65
    0x240988001e84003c2254a601030280b1506406208060095200062513040989940601071044004039510301e0a201914900f905103000080c081d8441d005041a0010303100c0c401e401d50311400c1e1410081c0007034104035810360081c880c1c0c15202400c1741c0b190b03a114281001c01030400c408640284411800d00c0513081546800040ea0a0103042c0c002c2c05040840c0c3c0d00000d40300e440a2601012818036440c00c0f840f96110380001000000d0142d070240d40d001852700c0711548091000c44410001250560843c010200c070010310000d4143d1410030394180c0e10012905058840b1416541e40c90f41a203003070a6841401108100002d0a03400300f04906002d0b00c031010030b4146841d06083c00607200380070007030a00c11405400c3d47d9203010180f00e1f44c0c4003003c4800103403d01c803003002041d180580740c01160240310300040d402c00c0903030b2a528150007218007401030756104c210700a0841c0c0034400948005030556071504801c000008035500e5041800601140e014058038445001080c40c41200844006180812 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 998237688 1250 998236438 998236441
    0x7090f15031103340b0a1d010306210507050907090324090b0703060506130519080a0c061206031a06220b011b0302071e0f0e010503010b120d051308030d0207021008 72
    0x158001c0b00b1f00d8510802c08450213100d0340c0c04030040300581410b81100e400840a122003000c1d5000c55080d40c0b402c64480c100b9222411348400500000750012101c410005001000c01c001191829900341e680c0796541141442240e4520745643c00d5a41e503c0c400c42c1d100031000104440a03500d48a624080c08080b07a68520704054402e003d41000124002d03a07219020404003165141a860007a000800c00f46003900d40c07210490130100b07000182c910440c00800c1580b25041c10f008107034450881a243d0008a001d07080c25a0245030356400d0780188105d801c51280d00070700e081040d0160040d002c0c51850768010400ba82e10000050403005000d11105155141c01440c0380002e4010410600b61040c070045038080c031304401c0604010900c81c0c1e10000c9900104040402e50310340f81e9807128103942003a00203110001001c814040940c0c000a80b14485401c102400303809548a40000c1000300952048002030740c3c6c842c0a001d0440e030007041340141c0035500140e01d008500300329044400300e41050510100e81e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 998238938 1250 998237688 998237707
    0xd020a09051003062301020106050d0506010f0b2a25080c0108100927030c0b0f0907051207180c0e060408190212060907090f15031103340b 61
    0x3c10179943e044a140c0c0c209145454050b403003540107000034030b0000d1140521a03010308203039032600401c1c040d1007201a0401c001040000310b03034003110409200031845041340c56107850460748541c04003210300e001e401900e0020161120003c21060258010101c4960040c035010f110740c90048000d50807414421050f040101e2055105224030480700e00030b10104800c1101a00012800704011745010503010100c409000d240d44040c06800e801e20440d088402526148150800c144007260b0309a039036408142e0901c014103181c2030315404075490a08589803161201c9002e414100866400594596590144040240d200717009064030002543e00c0e902c0c09003171403200c0d42c44010090202071030f0038007481f03440110348a09592807590080101a01d2107410203041d5507458007410f10983c0107490408085800000141c071401c0d5070300c000e150095848520390b0752504000c03406034400c140c0c9402004803034080688143c001c14403a000001081d041414040d00420103c1d1185d003040000307010034021141c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 998240188 1250 998238938 998238959
    0x10605010e1f05120a02070b012103030c02030c1e070f030b0403210501031a070206060a032303042907022206180c0912020616080d020a0905100306 65
    0x4840b0754018a07600c0d040740c0b01501c56220315194918401c3e4120704100007031603181c1c06021050f106100c242e000381d03030351281103103050100f1031103c140b204660405030003c2c0c0694060b03952400c4900549007002104007a0600b440341a0060401141090070204201581480381a0250101d50241300c01c0d241182c8807410200d00c0244001e06002071040030440049190320f56100000309079000b440950f0312440d00d0f505160703a00c41140c02220820000c14851800454564460300c8050100c031250341c5103443c0e54200c402000d8400c02d1001c124441b0f0b0440c540700744010409031110a010030b40507510325010030f851a0480081008126050201e80016550060002c8003811444030f0075a640d410720f0712940040000c0d5110300c15400c80c40c8151a90880141c005622000440d100c40a80c1c594640034125150107503400254482410004200d06100d0140310720422030207442d1881c14142c10042003c100e91007207030000041082a403040005103421804600c04c0b5083d80340c00e0101a2400034000c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 998241438 1250 998240188 998240209
    0xc0102150717190609020418091707060b09040b1b070c260a05010c0306081f110d0c0216090c0206152403061903050606130626010605010e 61
    0x82640c14501d01188088540070480070fa0009208020040c0c03540c0c5041d280000e600c1031040583c08140d001100c00e013500a0b02c13444c2e10190300003004500c105a01442440258040f40d8211295a80e43e0305c250000d840d10080700e48100d10803e06240300b810100401b0702c080242c4906c0c0c0c07240722410051200010840c00110003119480c901d40494501c103802c0d0255003a8131030804000794480c41c43d140081c00b405401c801e0144001b500c0c10854540c684002c20b803a401d02842550024a5181c02c0d040020718a9011503142600c1d082c86506000320740030300320b09507082041c039880186d00001180c8060110017000710000d2030050410014215404000703500c0b610000c0c590070ba21414154180025181c4202440129425400020028003210181c030030b41d800558045020300b62511801682041030000c480690350400d004041555802040264401c03030310940c2040241c035850700180c0b00d20f041e5110301c4033400111301d4181c0d813240d100240d42191010303407100b41000f08111030882d007501c0304003103003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 998242688 1250 998241438 998241467
    0x9060e0103030332040f02061804060609030206070b060409020d0b0a1109030c0f0301021306050304140c0303030f0408040905240901120224070f03021519050709170c01021507 77
    0x84d400c5a4450600c0300400c44210704c065000078002400c2c0e60b60145d00d001d132510b07141045400700009603e800040343d00c00da89000c0250003410400c802d0001c101c4141301160710500003400070514036a03903400704030b02c5010054126920000d550611403401c4aa000783c08c4400e01c13000300207090048a0000903a91420419240d01a83d502d2030556403c1d01c0c06e4040350028403280d0011450b080e41d440e0001c1c020f1340300b2281500c05441001e05440349007400b194442104070014004c508541f140c0800280640003d0f00031600d20300c04000000d0f1031201401100c1c41801052610801e10360800c4211003802c000a14040c2704095541c014000c02038024121607001d501901c104200800b0f1061812030301214851b41c1c503071001c2c0440c41c10200800b80e20380880d2140303e0fa003611800e0341b070740800d0780d04d4182c241c0d0444425007000707607115080444c0b644102d40c00351031880c0c82d5002e1940d841c40700f0040c041c2e4200b50400ea4110414120080d41c0401c0703881700c4aa001c0204120502d00410000c0ca529003642d40c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 998243938 1250 998242688 998242781
    0xa0314040b280608070f1205070e130609080703080a060b0415020a0609050705151206063915010302060702060a11030c011e05130809010909060e01030303 68
    0x101441d1900c900c0c600d403440d40741642c20444981c6807049140c0d5176070b40380300b4113404140300400030403442c0308201018801540b200c000c3c075010707081161042c0b04e135000400f900b10101007194040c001c00c031107020f1060080c0c050500140d846800d41801010004010002550182408410403026080d4400c030703400c03a417008018015100da03001080703040160101d40544000d050801c0e0b0783c14050042040d60854600307d455014420000a03001d0490160f00c0d04640400c60f0000010b42c00d08200000307118031010040080802589468001c00c0441c041c0c2c0680c48442a65180800380c00082040c800310702d182115928a0303624580c00241a4411000004c0c000c000c0404d50355402e034055040000c680303c18070180d03034407120505041c03402050402c2200c0c1406004c80c2e40700040900c80d07c03401b40075000c2e0084004800e04603860f040100d91011142d81e04201c0644e02c00140e00489100354809054445900b00315540b440c01d0040c00c2da0720004451041502c620440a040d88003941000c2007400c41820 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 998245188 1250 998243938 998243971
    0xc0602090604050303030f010501030e0d170c0c1006030212071202060d0612030e01020c090601082403010e030714010c05030112060f110702040c0906120e0c03070b0a0314040b 77
    0x416014001c0d50f20281e058800442032001c1e10396003840c901d0585200b83c2e0100140c0342c55003421950f82412812400c040b034601001200c103201c40c016002d6010094507913980ca01040f895070b03145080e07001c5a0528000d642c0d1a024421440c029071199030f40250310006000741400c0480031720071400606030081c41410001905048070320141c205900500c20a8500b00541c00607050103803000d100c04074403d0044c0038440340c42105280c4880c41c2c500440c810794072440956034012802101e00980700c5025141100c0310f0188600395402d01500000505041c05540c4034407951521806450040f001c03520203905040101041980c07004c107603811158650081c541c50140742c00e090008080980d081074825081a00d19060140c000000b030890610a41c2c0400c000901920112180302042c040c202c0025401c0b20810010440e5420070300b0003054a034151914240d81600003454450103034007529100c100800d1051406406210b03070b241014090103803540d6071070140d4584850200c02052440d02814454 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 998246438 1250 998245188 998245207
    0x50a09050601060801031713060302030717010611070e0c030c0d1410031110050f130b0a09030b0106051804091509050615010201091e0f0c092a0c0602 66
    0x4010140240c0c210003690714a50310f0300b01c010b11a00007400182c0b544000607030319090f144d03000d00403110400081c3d84d0710800c07917041c148110003961014211608000e2480b003203a40554900380c10a000340b10039294841c01602101569042191660045d991400d00e00e0420003201e4080c802c0703a51080c182c100c403c1d55580d14180c000d0080407004507082c0c42c0003002c802c10000d80e60000000c4203036400703640d0a0564001260800121081980e07090380041e60a02120a000040f040504100f0301d024280000e40c58540a085d80c06070441806400040c410510810520440e00e032401c0c05813800d032078030524001c192551507102c002401c6543c0e02995031603210034240301841581100c44504030106010548490030010b980d40c800781c0f20306001308804021104c180d8014840c1003421944801d400c02d099490f84500d0f060780c0008007041d544058240c81c42000075100030140006011030950004030960703070701d5040080b07140c0d000030550031060100282400c0c2d908144040c040c0b40d071084016a0310071504 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 998247688 1250 998246438 998246441
    0xe0103140703060e030418020304050a110d0f06020d06120c03030807030e0f01090308071b0602030903120a050109052d0a0209210d03110304110f270601020601060e04050a 75
    0x30741c40600b40c9460000041d80d100c402000800c01c540000d54a590030f0307d1410384c0b6400b240300580c0c0043c01a0720085070749000a2090040c5022228020890340a00750940c840c0e000d143c55015080b180b1039400a60b8040d0f8002511450f0040c0c9844503180c1c669003141d603039113480300b500c5000140034401c00c0000980454030907001114690928020380e040d1200c07092266005c3c210303071041100860b04201c00210754520910400341e81c00010440d0032007500386500c4070402984082c200f00b4141c0010040e5080d5014004411401011102c0e0000382c0c5602d481d0140045800240c00c81a28208000c1a55100014007407000702001511702e0085035900c0b0108081c0081c86420401a00000c45c0d602101d01003c45401010302c528050041d910207002c600c4044040340d80c04c1d440c058010400380f01007808107003d00d8505103c260050185a4414003407400110720300c2c0383c480b401880401402c1100036200750f804003150443c0e0280002c0c091035040410140041603103001315401150358500196079188107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 998248938 1250 998247688 998247703
    0x30d0804020d1e0501062411071d040c0608060d0615241202040503120309070509010f05010e030c030d0c081c0b09150f0607060207120203041e0e010314 67
    0x41003003551918406540c80150041030f20003038810b5443c0000001e5070000c016200d2400c0051513910440091038200d090710030b811000007040d40c0e8490101e003c20308810143c01e0603002c40403a00803010616007031404072182c1c000d03a009841000810818884691121010300c6900c40d4061401300d411100034500b0350800c03040c0d0784500d00c2c0c2900080030800c0280d00303001c121250f4040e9032303c0c0c0700c0c0401182031171800d0b0720461088641544c80070b644801824865000386810110101c00d0784c45c8240d83e8000280748481c20307006400521880c190801103983c11600022050138194081c201d1080c03050000fa858407010001c00b01804140e100c00c1d42008503030710440301c4c504406e5442c00349000c0c260400c98000c1628500309802030021030041440c0382104801c1682584009025030782060b4503805000303146d00003000c102c1e5516000c0c0842c0c000034004442158065102d540296120303480d1400c50103040b980c0c907038502d0140c1c40d5060b0520010030701d4800c4c20b0550f50071443c1c0074010490f04403c10310740341c0b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 998250188 1250 998248938 998248943
    0x507031d04090303020c0c09060d06110c0d020c01030c020d0e04020307090314060403021513060c050403061e0b0d0203100c1133160f26040614010302030d0804020d 72
    0x2502420000f0990558064681d03610307014100e03003001490109001c041030b0181d60440d4070060b070540c4a000913085403c84075021480400b0241401e10000303600e450a60b20031281d50140c0c126810402c41b950b41031007040c1c07401e015031005107201303010a00c002d8072080300100920b00030b80d0000f000480f85800380b44024011036202c0800d080581c1c0703010680780c58800940d411801405805c0007040400c6030b00d07101e94001d103148006c641d017001c00b555450000707210a0303100740107006040c000000412209c0c807074400d060f80e014105807150901d0f10000c1c000c0340c4002600741e2003008540303503042c05038900042d400003203405000001a04100002d05072040d2000800031440c51151489000c00901d030040481403810201c40420190b10f00145842418030007141d0005e10358000c140e5801e8030030f101e4031009407010070a00f02010b113803401c1c14240b180f04032a80700d0101d206811209020402c03800e0b02c1241c03507201d00c1c2da0740d0215650440e800a51500790b80000754080010001c003180035940c070108010011a0f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 998251438 1250 998250188 998250191
    0x151608070e031216170406020d03020c1f0203070210110a080a061e0e0702150412091806050901080f03191b0f06140106090501180305060a06180c0507031d04 69
    0x1e0821021390034160a0420844000c464040c00e218140450001c0e50207507409a00034190100700003000320001d4010410301c21940c403680000e0101c10b009402c4841e40c41d5400c460240e03407441c1400d0702900d810041c50705c6050319898404103500d6500395005071401c1411b649003100e010344075590480060910398014500348804000e20310302441149d0b1122044800d210f842600d650703034008041e41c031030210081000009201d000042d000070308a05270580c003c0e0850400e0141c4d55215041010b0040085554000140d5560b20a000c540f818000007030044c1f0b10f642c01003600900b000629070300e90040040e001d00080044554851880c000d028603404241e403480e50000d12449414642d22001810200f940d40c81d00d090407511494a0300303c07199042c0d0b140d0351241401c05280200443d0048801c1003120144d10304403001000091092019a020303041c80740300400d110781401c41c103010070242c140055110514100c3c03090095a0080103403000c240e0581001410300c51100d20034400003c2c4540c8066100307 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 998252688 1250 998251438 998251447
    0xc040e030903120703020f01090b01090203130501050712060e01050622082a0f0a2601140717070e01030506041404060617150f060d0b010602151608070e0312 69
    0x10383d00c12000d8010035000c0d41c212204d00c49844085401c0380c1000c040601502c50100c014081008990000c581119915200c400a04503588405003140c0c421345183e4006400e82131202c6010a0502070031002d0280005d0a04455140500090462081e08203d48500c1c100703070800c101c44844024500020f0130a80207680ba0072044075000c1c018004080994425210309002965250501d1400c00c140c183d009010159001d0409a0454030030800030404103c0700024132010120080a000c0e6044000b03104503201c5660500045c0541080c4008074601c21030710b020700401c4400b40c0d001c600c00c4082002803c1c001102e4441c1c1001c213001e45405611800401c0b0304100380010003129a100d0021200019041303442c4000c416002034480304103000c038031426030549003c6000340c15542c01007170b00008010000d501a83e503583c0d85000c55002603000b280903810882c0c024803540c503d1032502d43e01c0803001d090b15508000002c405010303044058030300e00420000c01e0820070f1715242001850000c0003c502c050b51107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 998253938 1250 998252688 998252713
    0x3030e030a0305091e0a020f0a120609061b1d060706020c030c010c030b0307051c0c29160318081002070606080c100c080405040c030903020f060601020c040e030903 72
    0x9418251104055441056400040101c80d000e850117070003081009090700c0f40036a000c2000c02140d4007001e5600c612003510000310454040d03126549544203040214410000e401c0c10400c843c850b0704a07241c10310120382c602d11030a900c02480c40b401102c24010720b0400c05850041a140e00805000070704042c40040c10b00c0f07170444000058010300210400074003141c41c80107412421303030300d01011050f0168454441070005152400c0405103044c0e04841400540300b1584590150740301562141208814100400c5c0020a0b081011a80b0103072405100d8a403001c184c404c9100754548180240c20410102115401d0707903061100d0300028800c21088a20b080f81001d580343c025445074004641c054a8080000b1348490085034140c0030400042020142c248500342c20754807541030b00d1042710000740401020440b9038440c070030f010382200c1c1a5030004482c0420702e4044c0c80c0c07016030715078000a584102d00f08409a81d00044540f0640300070b0b500405d80c4c1418202442c0f0307501a52011507814050008140381 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 998255188 1250 998253938 998253941
    0x90a0e0a0303060801180206041419090204060f1e1d0a091d06040512071e030e0405242106011d1e011a2104060c0e061603030e030a03 59
    0x5607413008000700100307030301c50b0074000d100700c0c5443c1e000750484e01c01c0c4070404c07442c02424140300651402904910b582a10034070000b188003e942c001c49185a40843d00b07000a41d4400604407a404003800c00003407044240601c1070103410a0165030040100011074070048a814040e4003902c000302411482000c0d0300c51024a01900d4200525410707040c156019410140b8005500c0380260380200182400184900703000440303a000d09020344035180c850b5500744243c4050701243c003005002c0d54030008445480803c010945101a026041848100384520109c042400c01640bc2000c115007940d041510242401c00d0381ca04842e200d0401d020f0b850000951304100704035190708121000100071941e07991480c0c1c54800d1450380c4111503d021a60040c0400c5c2007400303e905014240b10343c842d0400702c0100c0315440c2c03416600c00c46140b100d2940c0500c820032003917028050180d18503003011a0340780c00358804240c0c18029060224020920915008145802580201889855681038aa80303d809000c00780 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 998256438 1250 998255188 998255201
    0xc080d090506070f0e0915030f010209010e0f062a0a11040b0a24030213060c050c060f0703210c050c161d09010e100605011404030f02090a0e0a0303 65
    0x32070700d008001c006180e252040884144110341c544504200c525154140100305030000c1003a07080c81c042041184145c0e0b02000b50000030b0700d56000140e45e40030300000040c4100c40e80ea10f01d0340513101c40c444c424410b58071f00040d9554107000403118a10301031083d4035011100901d400810450181209800901116004110843c50140c43c103000c2d1000200034080d003401c45100b880d0000c80710080d40080b8074801040300071511060b140c0135080903032458031a00c20440c141d000c0380201c3d48140941c8100300044c0303c0b181300740600b1a022030034000800c4c880ba506100b4200000d0030804d0718154101c00005c14002e05903000c208100401c030350400e91001070480d40c00350341022042d214803040c0410100c1105012020364174034494080c0e455042d20300000c081c2d40e026100c101d00c1d541b201c0000c4101001006409500d075000c0c0c201042e110b00d00400034004c01b0742d0861089603c1802c100603c0484c11100d180d131080c541c1074482881580d1045000e2008001c0b1038080500c1c0d008640d190820b0651607040f09 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 998257688 1250 998256438 998256443
    0x112020d151d070f02010e2b020a050606060901201f0b0a0e04030e0d0b01051017070c050f15060a140d0201050c01140405010203010e07020f0714010c080d09 69
    0x200340d50301c038041e0054840c60101c140c410b00180200050201e03105035040c0604512034000428245024001d585c00d00b612582c002410001035034040c50320840903807482a0041c8140040c1210414030749403180c885100030b2103180280c00000b01c00070103911401c803001c0304050154403001d240d00c1d2929110340310030070704106001c040e1a150700764140500b54407568030380e000024003080b0070600d80206215114030040064050044505040500e600e6100c261011140314036120f041c250b0508040000e007207200c4911f031041280c00b0303005001c0504454503a9810002c1820a03100c48540303485d1540c502181342c0014403040c003e001d03189204c9040d1600c0c0034000d0408413644011680c56800c0c0700c583e482c0c2c514107203501150000154000d54014801819101c0514001080c800c1030314007511a1b019040e1000ca40580d40080104216102d440d60242c2101b00b52002c0d140e18940100659075864143c000c4082c0521440c2d0030130216030244003200023055120b004c072a20f400007281500001c10754403909 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 998258938 1250 998257688 998257721
    0x20c0604152033040b01030203010e030a080606070206040f06020705040c03110d051906060206090f01090b04200d120806060a05071113050c04032105180112020d 71
    0x3010b091015102155111560800c010601a044080c00d49501c400089051407400345405001151001c140d4055224038025000541c079035155105140c21103141080880075900b05000340c0c0d680c141c0c40300202c0e81041c811030300b50341c0302c03069800002c0c1c4510441d8440b40e5125a07400340050344580101d9170700b0840f0b0f000c844c20401044907403020740540d0340621203c20042400c1040c400c10443c5944129007000240c080d080808002c220080700f101d016401840150380210300300004010304000b030b015030740c0c03581000f886040241c0e500c284a0b0540944000c0c0b8a6101021107104e01c00201c0031070340e01040040c0083c000303100070705050300c001804825540016120314001400c0341403000403110307000459030f60549400070613101c0d01a403402103200d06600c0701c21042042400c0d091405024062400e08040f9903170b0390b07d0b51a040d65000d0046110b25400b04514000340f0415802000b955400390f08440103a140c00080740048a98180312100c1c0d071032440c40411006001003140d400300c072442229101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 998260188 1250 998258938 998258957
    0x40218101419050d03120501080313080c1008040f120801150e060906070f08030705090a06020606031504031803030201051009021903150f0312030b0607110f01020c060415 75
    0x1d001040a9180108880184508041083c0c0c1800c103040340466000303250060000d1415402a01903030020b90042c0b91a900100d203200f045030201c01c00c03a00a000030b900801c0f4020701c0380041402561305000e140305001000000405018180718903034101c030f61092114180c01d15024010f41811028090300c07040300c0400100e84800e178050003031201000301c001c2c9114100a0200100151540300c104120344080c8140800800a20050040c41c0207400c7c035241d0b5520340700e044080c452004059400101154010703002e0100365180840c1e454010b208106540d90103651f141001c0d0f442c07a00d520460341e03014801c61030010030301d0b0781980300394046e03074178007503a4110707550b0b501c03010016400f410000d00c86411914034080345180c040da2040f00014010303100e2011042c0ea03404135080880003a401030301d5588217071603050300c4030b030741031280f2100306ca8202d4690713003000560744801d0101007040082c180500fa521409010681c0208006c103e0400020714040d5501d40712611801902c0002010b00b011030248503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 998261438 1250 998260188 998260229
    0x9063a0504020d11040204091a03010c05041203080a02090d031e02070e010b03090c03030a0f02010b06040e1303030209120a06110f0316050405120a0c060503160804021810 75
    0x5041c0c007903500244a8900003401e6191084079881840308145d000703030f0800c00003800c01d0b83c0307000d402c145100b02e00d210203a00010070141400e44680007000c0b800c106042001b07000100329003243c14215509440e10440a41d2041d403664004c1c441c0202e05a40240311030100003c16511411180d0242d0b00d8059102071400c80d4201680e85242c2401172286200ea58030042c425216024040d584c48010b9100300d500034864440840c0c00c65020402200c0022801c1c00418605034090180a50340c2e0415124140390524100304401da40c100038190881c5104800b100c81c0a01d031080c2c040e506030101c02400c21322045015801c0c190f459406880441d00c25041001c9071008001010540d040090f81d95000380c5035941d0244149010300400302e1140502c54140808240354459854110b10f07a015480140f01081041c1819260503010750310030400c021040041203c66215140e048403005040c0c03c04000035162880018042d4103094914100e24000d04c08001960402c1403947d001c4448018950b0602541003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 998262688 1250 998261438 998261441
    0x22b060506131205031908010f081903030f14070c0212060103020f130e15010303021e070b070807060f05010303120b0603010608060f12010506010f090e040809063a 72
    0x40c0c400001d09010250400803907441c8205851003504c5441528038010708a0402c1c0702c007000441c20032000950350700040c0180c0351111682c0e00504032080040c20380d103984040400a0300b07480b2030001d00b00b41c0c84d40d5181031030850540108929011880d00c2a18a1034400b000034080303150100c0c1030b80f00300c0010b94000341071003000c03400905030f0f500a0b005041d0702400e1014805021488074080e850790359244264004440d0078408100318406202070800154034505000b86000345440341c3c54440f80030040c248808404c0001c051040300c00c030f281c0d01e88e00d0320781500300016240640400984403d0a150322600c4400340350303020b0b9041c0c034400d48401c01900b08000c0c2c900308a41400c4129a0824801c1006000a40c00703030030703070a0303100d5001804200c44003000000f0070b40034216118403c180d80e4492082c05800e60300014040058240352078196172003440d0000003051007030050405030058500144160050b20b8203c120b8100610158034605800c1c151050100387d00b1002d9503101c0c000c4001100344d201500341d0b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 998263938 1250 998262688 998262697
    0x21b010c05011401061107051c14030f0f0a0801090c0f180801020c1006080a0305030112110315041e080f0c070b07030507020301050105061c0c0e0a170f060c0307080a022b060506 78
    0x2000e603116071000d171651352b0304d1402d8003513501e0800b5100130700ca40140200d8141c01007007217440080c5c150b600c441008502500d411010b03004981e58505048408203015130200e24062400443d207440d1810a48400480c40b5207122a08842c01c503500010700314494600004000740d40c0c86001004100c41582c070b8074103503161520450003c00180e400c01c010801c000894000a280c03900407191403261444190000e403070243c45400c156190700c1200e0401c800c0c4140310280701c07900d841c07a4102006010040da20301d845072143c000718625540000c0790b0420051340410150b80a000315508060b65001c0c50706000d0203d420542c0124440c3d82001c00114481c2409410b9440c0d8014120107260800750a0b50084050310302e1844038001c02505205c005900d0392080000c000428a2840c00014210400c200d43d04101c1071a02ea2030707040d40200180480c00414608803507100080d0300d0b005180d80c44030784014001c5d2140c0e5011281c041a445100ca401000305240040115061001080103568540600100740039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 998265188 1250 998263938 998263969
    0xb040f090605150f040b1b0609010513060e0a0503030103050f120421030e21070b3a09030302032a0301150306030c090605030d021b010c0501140106110705 68
    0x1484140040f0300000403000c1d02060f50308001c5242000d8862800c2c41e904e401000950255402d0724403480007592040c000585c20990142c028001c034500a400300858024445004092569590790001031500034482034413541d900c1000d495032542e5034200160303141ea101e008107407e4010511007a140c100080101d50481d26800c0340061000d503a5107019880c0300202001340d081c0182980348040f0b5aa80740c030368004e08070158208140c64042114402c0c03804005070003000260504100031090500010158009032141100303a1480764030304403402c50f0252031240c8440c1401d06000009041640540141d4415001400d0001070645c86603034031008580c0040182d420520204010700c0344005032070761600e104185040c0822103d0381e942d9103200903149a4022030310b05036180d01c24000f030f1030b06100c1011104810320080440758110100c4502050f400411103043c000c00e03158080400c082034110460000303a181d00e80c01c076586d440f400642490314004071600a8090340304042828070f0070003101c0c05083c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 998266438 1250 998265188 998265199
    0x403050601030f02030706080421051303140d050301181d030a0302030f0906060a090b03190b072c10030b0315070e012f071502030d0f060308160206040f0b040f090605 73
    0x48009943c00b20ae82400c0301c00040110800201d115028250f180c0c1c0c008510489904268082c0c2081d600c2c2070440c50306c1040d040240c208010440c00c0413028403104800003003400012412140440d030001011404000c0c5000d0102080300740d40740390564040e500c2860348078803103806666018180d42c0c89040403075003103501c02500d160a00c05e01440d036028035440040a000c82d0070748104500281010103074200b044402c2442442045002030341700c42040400c1030340702c00400b80840b0350412400042c950040203401040c0385110211014460b0300840b044410260540d42c0300308441500c5074010000f21004008214900f4817601d05511a034001c0840c456048808100884e500322040300750f000d4903905800c54442d0b00d40c04200502940c02602100703540c0d40007541c0d0350b144001c503601901c0241c503021688c01e113821030400c042152101111801042620b1040c50250903100040007800b49410017080d034814000003069441400f4000c2c42034481c11103502d8032196565542c1403c2d500d09015040c2c000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 998267688 1250 998266438 998266463
    0x203010302130905120c03040314010207080d0c02550230030c100b0d0f03091502070305060a09050a02060a1e210c021f020403050601030f020307060804 67
    0xa2099078000c03c1ca142c41131090f2402c140005200c0d651030703000070442e0103841d00000f800700200507400400c00100c20741e04009606241107505c80d09100c1c051b81c031325603010301c0d12010085112071081c48130112a80c4010901e210342e1034884100d44076410644c54102141c180841402d940d00c88921038850214030450705990750a000d9800c0c00358029541e606503030308001c2c0403110060101120030011003c10f035040107540750440c01c0d05a504e092070780c00516498518090300760740651141d204181d0007513081035010b100b501161800722111981076019007250317200032100b080220384c0403d5100889004404a4180d51200340035031b0216100e1820061981d030115a0403001402e004019000000c55410511144a84000200c10001800342c051000403100ca590340d215100c04402c1c100c05c1610000200407003052041c000c0c0d5035160103009080c0344407940c0641d804140386601210003640d8410165046542e4030b14080c8140040380a08a1082c00380200100b2103034452a0348620590304844039580c503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 998268938 1250 998267688 998267719
    0xc01150f1a0d02030702280b0412180e06010f0305061f1101020a23032403070f0801020d05010b0f04140d1e0605010f05090408090406030c091e0203010302 68
    0x10540c0300c8100740300c1a001070048005000c00d51019600c11605a0083c0143c0c07082d2400e000c03103490508a180000700c410552038404a90004030700e6910542c4404828000d0080e288291806104800005000d036000310300490500c0821100318000d84082c0c854147c00d2641540a40548104441e81d41c0c01502200000b0500107406000c2c81e0103440d02d0504000ba50002d00386982640c1c40440c80401003085400742010040180304c20846000117100754500314100021212109250043d61914101c004412198655410b00104000b01441c40008403407540d84c0c0703d603a010350041403100304e40c185840b00000c2c00095040446500311081d43c005440d103070401e01030740310312003000c0c5040d60818211045840090488401000400a05403e40300c4000003490a00700ba654143c0000800c5c04003d5070410498550b035211903081a80901d8254940c1d624802203402066154005800c140082c1310005550110703030300064811003110408007a05100220f800143c1c8400c2c40020f40010384015001407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 998270188 1250 998268938 998268959
    0x1103040606080c150f0d18050106060e0105070f030c020a05040f1a0402041d1509090102090306100f0612271403090d0b040c03080408030d0501090e06010312090801090303020c01150f 80
    0xa400006c140000e40310412510f066000036141c603045940e43c2d580c82d000d01030f0036000556140c1c40e023424138119182210b01d988003503d1390300c00c55000b024040d01e01601e208664982d184140035100107002041700b06d448000c00c0001e0580c508203000c18031010003581033b05042c28000c640580d0541004990702c44402423800600d580c0041203440c8040710541040e205944c2c002e01c140c0110b07100c20015840d01084010941000c0000d07000480c20080c00e44100280781c0320456a10841d0b00720b04001b61005550200080030b082c9040d007056620b14031039000080c6071003035011004c440b4010031050315145c00700030959a892288041240d40111220118800034141c1e07482103a00c10310a400c0d80c4503080c6e89a464030070940050700508a15000032982080481840c0f144500400003007400b80319036003480d640c40b61903020601010f4030883c01d8460343e13032400340030702c5100c0e00174032544000300100209810028002d421100d07020301c06500f040c60440341c13031701d02e800c030344060b507504502240e80d6602d085030003074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 998271438 1250 998270188 998270197
    0x4030801032402070609020112051b070f02030d0206090607020f120912100f0b0a0509070507020102070e0108150a0c1e0201110d060e0105031c050d1103040606080c150f 74
    0x65001d920104503082c5111240042c0442611840300850074600321320002d8840c1a8801c0d544060340d1504c02004882c8078a20781c3d4051800e0035140c10390ba18445d42c01d060303a0806c1003090103501b40c45083e1010380705e40da0002d91184a400200140c03059a05c8502c0700f2038440100b41d00200c03540e889494418841103003000208001840100444115205c0d628501d0410f80d9481948a000d90780b800e4841c540038007402560388410040700d095030101e00f03210010715403040c081c0c8104200200401d81c0e1003164000c10581d03020700698034012110790303503c0807a540e46074842c1d80c800002d840458042454041a40648a2900c00b603131a1920500860a044102d07040e090300748000319074840960b03800c880303c900700030300717200004040118400b81418208180940e041e1304c1207000e940304205039030010189840343c0210310000d141496807442110034800c041c10591902e003c0b41c5900109100800c451580508101c3d900c0d0415281150721100802010020f2078040d0078002c1803c121807402c0003221030042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 998272688 1250 998271438 998271473
    0x190b0706180b06101b110f01020c010c0b061810150903050a020f150c060421021b0307031401020903100510090e120f1201080d050f1b0318010905090403080103 70
    0x1724048a00240844501c2104070058a03c42c260300c0b250a41c504188000d80e181d07107003e0008180100414000078081c0307030700341c1c0080c3c0700038100307008500c980e80e400c500e802410b120f44400c483345003800c0d030341055000200d214604e0b02d1a50403d83c0c2c1941350041d01104126030304400540012030194092080c12401e9002070703a0300c090001c05e656601d80c240000f80c030b40744040c20010500c1d0b1a00e450544148001c040c00c680413580c000d41c01d5040319500196006448034202c040c0d029081e040c42c0820326100300e641000b0401d2422000b0b04100110560207003060120880071143c038200062200422039000b81c42041200708480014800404160422400241341d40c3c12108540c804003003144c03494200c2c280480c01c1c044001860705a010300c1869081c090a102d1029051002d828517010301144521414004040d01c0030407110911034110540d0500e4100f90400c0da5914942203a2a108103052101d4040c042080d02c8000b05403030401072110341c461541516481e0042c0d0850725081c0843d240b03150007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 998273938 1250 998272688 998272697
    0x2a0306010c080301062102120117010e03070b1e160e011107140109090204050109033e121f021b0307060207030318150209190b0706180b0610 62
    0x420005810b100258000c0c04281c0d0380501c00303a1141d000c0d40c58036141069016209005111044890000c003001c1070440303804548450a40341c802c40142d0250804140600407400082082801d00003131582c1036100c0e044074140f014200002002c5140030340c1d0140c5034604401500c2c40d070201070034000c0d400f12462300ba050504461103d4400b03481d03482d1080703580225241103004003644030319507044204140984483c5000794101818500024110201381c44003421508807000500034103085a6102100d0800c1c18407980c200001c41c40c0c0b114018060f04003107500402e420010700280c020701003102e01680744041c4d0404d200095400002c80a50170940220070703003802c0900f5000c3c180300204010000903201d400c0141e01c941d80350130050100c5003001c88241282c44040d10310000910220582c80d105075040d80300584481d8a00b0215408000c00890b66407810900003010809070342500107000002e21407d0f0038844800035800c080d41c02d0b08801c400400c2280c80c40007054042c0340c000b0804c800d0b141075240 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 998275188 1250 998273938 998273957
    0x718061206050307080c0f0109140904031418130e0c3c030d030e0c24040b12010b07080d0c020102070204050f0a0b0303131a071a07082a030601 63
    0x80e00740b541a17800803010743d0007561000303418104154602c046040034240001054580740e020204803005210700c88c4034a0480740001c0809d40101001400c5042d00380e2400d4850641551107116511650b808034450009030801010036003180c050b41d00300c402c00b040a48891503010007442070070100074290120fa1024026004000034600f0360a110300c16018515842c40488003080c581450308584c1ca0750101402d0090b009400d0500007050145002c003940c1c00c045507000711030302d41d50782107000e0707005050703002e00140025020710914068942c400c034250904c000369070788803419500c0d80726038607001701002c030f0070f00ca03000100f003a90380074450503c0310740009450900107038001011558111110820310300c003030040c820114110310601700300c40c070190021450003042601204914a843c411325188084000c111b468a40251094a00440d41720300c45803e2000020309505001000300c0380c203c000b500150020b5a01609400c42d6216550002c0210182040c0407a84840704d620060040d03060091400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 998276438 1250 998275188 998275199
    0xc0e07320705070e0f070c030c02030f07080703060536070329160e0f03190501051905040206090f190f08010c080903090409031803030807080718061206 67
    0x10080403220310a02c007921900d41481c0c20300c030380510080c0120503a00d000d10700300031031590081081c043d050b815040441030b00025200003441c1c985800350014460003440400524440c0004908059a200b001c051002c0c0d0b42e0001c00c103414416401402c40145505103098100314296018103180320059020f980040340c80c2e40760b0203028400503050f4250328182c0c4c00c0b5100c0441804035406e41000c0031071035201d242115880c00910800d24540601c0c030030440e8141852495070200010320b94803607080000004d01c41c803070404500070304080f9009491401c0804412150040c5442028400c0d40c1c01002c030340c2005959400c1c0044219083d48091300300100c3d0200e80000110003400c18010502c5807002181c80b414001c200703007074646954100003403005500c14401114804420f8a2003032070140e4002400080d941002caa1545245850b00c0d411a0300030300110a1545c800c0046108088545820900352503406c400c03181c0c074a03e055a440301c041e0601c02401541e2243d1010039a6092034030020400540b04e5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 998277688 1250 998276438 998276537
    0x40326070c060b0603060a0627030f021807020303010b070309180b030c0102010209011e020c0d03031b2c030c060c06040204060b070203071202041104030b040c0e07 72
    0x5490100118007081421010000b880c02002e10401060340c48500f9828103001107a040c54490080702d0512410b0030040342031180c02d1003044509a44908100115a540e04203121128000903007a0f00666101c0c130050441b44000a90500400441e03008502c0c50b0b1034801c3c0c101080e00104411001c001540701c0008111150821005c1800f4001400280000c04d0f0800c1519000e00c0aa0003415a4010311a20000ea030304021050200f404004034130304000c2d0719100c100d00300115109926441080d000c101414568582d101d0003a41030460846e00c101510500f060300c0040c000b00c142c030301000e0000c85250708000101c0c48800c241c1009802c46644440d10b50010394039400003030468a09034069820041545410b000d114000c0c4100700100d4903040c0750350003027038455019001d40402078111004810840d00c8075800030284040f00745006407259182e2420701824041a60306840501d0396001c0807070380103413080718580542155128082c00722401d9041000e00d040385084542d0b9505060010780b2410140e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 998278938 1250 998277688 998277691
    0xb040c030c0e180f0a2402030f0415051b090a181a100917120412020414190c0c0b0c1228110d0606020d030b18040326 52
    0x40302009180c501d84025402010310800181d40f195510980351022030207804643c6161260304000e407018100b085a40741c001e109507000c1440101440081041a2460301c44c2c0141d001e244121180403040f0510101c21055900655414455100514400030b40380d00201c014402c0311030141c03440c03030b4103559a61340e07007080c0340061800e014281d210040c40612609807110b0740c820840490300c18004082c0c0310340040010102c0e0080d41c80c0c0720702c08014200b00b07100402466810841001d41550707180d4491003055960ba141200880c06a41040e100c045001000b00c901e034032405070713440e42901c9009407006080c0a0880343e00250240b04404c0050008202c2ca07000840c03180c90b1f0f101c5a590355040705100d203500c0c2c102c0141120244142c05080116209509003120881201084c0c04918200d00c40c2402419104100f1a440100e14091000504a0b0081a904210340e016141040322001007018011220112001e50141120000c000750021f030203000300036804000d050926071364241110b60440781440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 998280188 1250 998278938 998278949
    0x10203060102010b031617160b1c0221061c050106080d050c03120a0618150603020903062d090a0b13150c11030d1410030f0b040c030c 59
    0x40010801440d96024001c20b0701000040e4002c1000c0440141030f801307180b905004a50030203095807a2038403246800c10141d140a0315500c100d20040e82d54044410440e03020014401800142c01510300300008540700351005c00c0b4a1407080e0b550010b82e42150314840c0b4000745025030042c00030450040c10346011102e4903c0e14421030000580740c1c02c18909914040c02c41c201c04003040410001c0b070b46071304404000c3c4c540c08448070700c00108079100c451100b8082c1029801c40004000f49044080d42c2410b90741003000e070a204a0380c1720000c66100e510071001d80c8202007149403d41c0c4903d0215189034010314203031900b89020003d5004e0310034102482040e80c2000d64128080794030080c00d200c2804400c0b000343d078000c0c0d5600f201c40d0010f50300341e840811500c0c6143c400100d45a039103001800542c02011108072a00c01074058a545040c18800c071402401c40c0002107a482545100081d511946115550240c3e40c11024415001d50160f881c108180c000500440f4000b0712500d00000180610554001400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 998281438 1250 998280188 998280191
    0x3090309040b19121e0f06051005060d02031807050a03080d0f022206020321070c0503040609080c0f0d02060d15060e040e0d0906050703090e07020c180f0622090501 72
    0x104d07810851030103408136000d0182d0100c0c0e80614000162200c01070400c013a8085804900341da0340e540c000ba00848668001070b003000b4001240300c1402d035035600643c420608401507410721a01425119603481081c01400c0c0c00028040007480481d205101410b00c0d01902c12010485100d29401d0710180e801c5401c01000d808104020b512002005006260240160784011410240c80c100781c400800300800550401e22898008030359040c0c411144000425040307000c9076500d41d5990350042041c4128800c40e1464054040f0020203441c043d4915440c0c200e0040040401405540800000e540b0080014441c80da544c206c501e4080a0000040c00801c402d4071001c000b40d070345400340000c0e5600d0085a06e0140c109042110795660000c0c068001d03038086140c5903465840c0717450f00343d0f8010b40c15001100398048030010000c0b043da00003680700410000b5550000c03403000c141d640904001003980c041c01811030080c001412800c01903201d401c0c40d4072107228030184d0403003160124100c3c0c050350025105039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 998282688 1250 998281438 998281469
    0x80f0402012102160305130e04031d0607171905070812060307080d2624120601030b010807060f090603090f0204051611070b030a0504062004060305010b03090309040b19 74
    0x10307e003240b11100904a0360640a031a00d02560010a03000c1d001c411480d4820395007040d61217503101c110a8034429507001d00465803024603003804130720541214040550040c074023502101210711540a44010a40c0600c6845c1414140100c640c06560300800f01038151060b6840000c804004119403002540942c0703540381001000d00c082000c0e010010440f1002039851000d210349009000020f49583c04c030880c0c18110300d0300450001d01c1c134214030301e05640c0070f20640d0004014070242c204468125803043c01242c0c0c09554480082c1c520302003a0700080302050450504024036406504a099218891102c0c2481080f040e40007900701d40098440315888544840304207007960300a0016403491201c60000c01e089440c0c00040c001b180b100038481111191110701003030402c100750b005000280d1426425001c03103845001504043d0704980300f00e0307002a04001c00040c9414200c3c00b101c2c0501040405186848000c0052001401d0004550764128150148000009281d9000000504007440e0501000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 998283938 1250 998282688 998282707
    0x9110d080c011a10030e031606050609060f010504030b04110607050d03060902270607060e1b01170414120a030f0605030102040f030b090f12030601080f0402012102160305 75
    0x84500070651800c003000d42210300800c0340e5861051000020742c500d804941d140d4001b0b92541580202d4a95004d9104118600c404101060304124450031041c1c540c0f00c090740d1610300b041610520301c001e007030208408001c1030020541d1000070903440340c05861103018a02c030f084041590359008620569194010382c20500b4440e5250040307000600342200f056090100400d409050310202e2090600500307803c1840000c05c1d00c4442c16101155082001040101aa41d04494940000c3c0f104c00d8441960f950401c8510760007420004070742c05030401603242c107a0340d50351070000c82c3c02c072061a14050b2081414040c1544109801015010f0046c0e03000300d00350300e22218400035200107810441c0b00ea4010701060007050a4510140102c07a080a02c4601540301c4800f41414811b101100301e105015000501048c901014003c5010701d00c00e81e2601c0d21503540c910100c110032800c1d00c0007400a900704000002b032000011019140e019024001440c0003521000c410443e04503e8040700460808204004e2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 998285188 1250 998283938 998283941
    0x22200d06020306120a23011506081012080712020319020c030c150a0c0212010606090501120b09010e0a0e0a0506070207081207080a0302070206070b06030111091309110d080c01 77
    0x810040c0b01c4d005110040c0150350f0300b0700070000d80302c0c002d100c1c415165440b1030840094006204c243c80d130143c068000c1e40c40f0540100035240860343c041c06241c4039400020611100200703204c61580000b10700d030074952207607144881c0100200384001144002d020f850f00340c03520205003451000c001d40013001c900000340145404e00c081c00d15807522642c1d02200c80703103042d00380c40110788010340d851400108402041c80015a400801c1400d07490a618010003c100660031111560581d00241c840c540003a820644000a80745507001c02c580001d003000c010003181d500c3d80700180e0031081a0801047e920a082001860700b00303148400d031000e611400500450f207806112174009000000c01a0844107010545400c140c0724012004010310400140495603e04c207034151429964000d01c00340e5104514100f605048109072400e074801d5107090350b0720b00040d015000319040c80c40054404070103440b11900c3e00700103100e140000c0d10300442c0c180152056a4400003000d2001c2e00c01c05042d0389440c0c410086a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 998286438 1250 998285188 998285209
    0x2070506030703140f0103120f170c1902010e06060a2d050301021201170307031704020a0b0d05040302010e0309130b0a030f1b1d0c2206020f010522200d06020306 71
    0x18004000e45034480b1640c08800d51104207684076074ac0c401c03030b2110408400c05101e00541412900c4125140700807480c1c0c1134120000061a00c001c45880ba21050108006800d55202c0e42c14400000709141346031108440d60103000d10808203070607070232030b42d50300219007680d000103003c4141d144140010f01c907400704030702a001c140b80e1004c0114202003250f58040c000f615a846204400104c40300040c007103640f0a00660003030581d5004540e1590303800011080a03000a031000c03009035080c8407180030700150000654420b18002005180b059143c076030701c5001170081d00c5449420860007030011000c290b000b00030001c0944202c11130414024426040a00203004d50410420982c4518008082d41d405200d01d90b08000300c100c10644d21040c0d11f45c1c990000d07100310070820141c400c10070b001520079000301e2440c0200407000024003069880c0201c0c600a80750b00854100840034020400300440c4072088500130040c440c40c52010703044841e50002e103041030800c1c400c88203e500002001034500b401300446 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 998287688 1250 998286438 998286473
    0x12030606270402040b070506130206070b0a020c01060303030b010f1805010c020d06141803030610030507030902030a0b0105040c030e0a080a0c0b0a020d0b040513031119050304080706020a0302070506030703140f0103 94
    0x2855100d80590001e524ce00c206403001c3e10a103600700206000d4000e9504480d00d04042c20000c20620341e40b8500079002d0142032280234003140e0880f00100c46035026464503211880c10000ca00101030404c0c0064409205c1c146003607070803019218018000910074030440a0f543e0280c03954101a04e00081c0c22564400c0d4a601ca045580041c003c0c4106600c03901000c01c0f0110050402044a03503411104030011b104081d4040e62511a4102c01c03400c1c001d81d200240c4c165075068405000340d5002034800c1e800d46600c0d501190303003540081d185001041168020b041800c0c201d1514600c242d00607101e05140c4201500c0c81046580d00068207003a22074603120b0f0b620190016038003804545045250480c440c1040c06000d414400b0401c245000440d00384802e4003180005800090040800d044c010fa0b40e81250150f030120b84070f10140440c45600000304000c107554036034024090a03040c40180216500041e0200c81415110000d4580c07050903000107621408440e110341d01d6644c5941000701078000040b811 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 998288938 1250 998287688 998287711
    0x1806100f0510350a0903030f02130515040b040b340213060b12090601080609032205060403080705160518041109160212030606270402040b070506 64
    0x14281e08a4110345404510803441c04000c440d060454a0802c0d401c20107803c1c03840b4140580c0030400303801010751003400824020f0346d08000091000030188101d00c25205180c1344101e040400700402c0ca0101418030184402c00605400c0554604483e0340ca9005504a84424440440c500c118101002d03c448001c0162031110b8800100750312010035100d51307007070303019000c6e2842e1800c0703a1562495400c00c1e4010001c02141d030340d40301101100e014521070166130000060280000010b440f08000a499010301c1406018616003245034110b06118000e040300c45140700001100004c4982c0c0709400b40c00258010075500b40d682c245403030081c2c201b031401b2007004040c86800c0400d116a8903451a1388190050700e0012032000e85540c10138650000118028541c0300b00010304001150740513035616003030a20680c0840c0c900f51700007041c8191900088407015086030041c42800292100141000701e000c0e1198600ca050b40e40050114060b039200c7d8104980180b4002000000c102d070070002142e0110031030703c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 998290188 1250 998288938 998288959
    0x6021201032105090f0307180903090512030f07050a0b07050702100815040e010b0d0c050306070305150603273414130f05010f121a1806100f05 63
    0x30050300314000d00d08454000d10080005c40802d0714208450009890b41285032002108070f442c564016141065040b400a108040d00299500741000c0b4142042045d0028505040400c0490702d000e42041c04141d49600c92405000046164885071030701541d0380b40d44140d81c0d40b0543c0184948200420380c840108290718041110302010840d140c01b04900840e400f003004460f9140c00c5003d4182ca80820f0350220200c6490340402c01c82207100350403100143c040d5000c40c0da80b240180c003100c0c0c040b0b80880da01c4611422a03607152034020020b503404480c07005504044040f803060140601c10444070840039500098801c40c66810400301c001c4078a0703907808841c80d4001481e202081400c000d00c61000b1900b071701d48880640e0380d43e0b24654240141412810440502c00301c609401800007072160000905e803405010420703000c55183c0303a0506810045119050940c450040c00c02c2e0030080900945d20010b011502031594240080da01581c10503d088800d01d042c44513108e184900c9a1029214a45104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 998291438 1250 998290188 998290253
    0x140d080a03091a06240705060c04150203070309030f0c0e04051501170709050405031903020a0e0904020105070b07210e1c02070324060e0f0c03011404180602120103 72
    0x2207417400603142c1794101c0250090b04103645a00f50148410007045402104208840716941c0000382003220004411800c1e00c00303c0140c00d82c2c03648155480540026942c00060000c1048150700c18503803840340864040c0303242c0d21403028052000545d0201c9440e00401011040204402125805086485002440d400b0051759036540c0c5c4c015841514030041d1650700140510600340196008080740c154845000552440300500a42c88107000030b0108525514005075801e142c541a8442c9a040e11181d1501784192680382001070010702000800100481202030711610702010045d01001120201300a5014818181080d03003c008483c841000211555040759000501e07c0441c3e80007880004841000c0b4003d80c603003500b80c0d48003c0158145030340091540340403c90030f40304405500c4080c40d66258a040c8480c248401c0c4207041016010301c1162846182581c010005045c83c442c003001c0c460070640d20201039030010504c40c90102818001001404031849107103542c00038003890340c0e4030944540d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 998292688 1250 998291438 998291449
    0x110f0408013306140d0c0906020625051308120d0f09081b070b040e070e1002100c050702090a020702031203040f0f03020f0a050c100302040f140d080a03091a06 70
    0x40c0314030010084203418a4084c039401c80202c1c5c080e030452080511024085100280401e0410700c100c034018480c0b5000648502d485907a075208204c07803000550700065200c0021940b035041049040d41d1040d00040000780d00f0b104100c1401101c500b4451700c3e413601c600403900c00445040c01400768446003406800400210200120768001100b480307041d000c1880c0070b4104e07103020401d400001c0568000900412150380301c001082c0b0a450b41e03912007480380000018080100c050800e0341000d617001b2103954110811540161084021514000d4140036170341d00012403608050b25156000340e4001034040c2541000c0c0154841d095881c0c410784e15604069440300300324401024050900c4101b004400d00b01407091080d40e818007c184220b4250012b981045510ba138143c1c0100340c45550707580f40d500c0700d050190003618100d07140c000700209120b1400012401510100d9040b582c086880c2d200d080014540038040c103a003541c103581c00100d142079403401202c1034480f84032107105410300c20200310156440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 998293938 1250 998292688 998292791
    0xf011e0c110a0b101518080c09040605091f0c1b0c05210307032a02061c02040506210c03130f030201271104060315110f040801 56
    0x30fa10029541e890342c004034500f401d1130b0403007940350301031803080901c030380c0c4c85034000005112201d54801d04550300e11506568001c010300703840e000006400080c021a0455001a9104840400391480320b001810140b03540418942c100c0b2901e03540d038a224900c03951010f02002501c0e400505c21004ca00907407225036217840c107441118811885021140c1600d00c41c03014400140880000f1261900448c2c030f0003400f10301c0174946120b001c1c8001203a07106111800c0d01030b00d00dc0c03074000c2c3c04540ba15001e003041e01c10060102206581681d001c001c00240c68803000c005000111a02401080c480e2082e0b1910760180409130800c440c018061040c00780d031000705080a0f10083d030116800324035481d24030341079001d01a2004805624004e51852002290420009819652140c0c2210780c101035071a040104440160002615840c0840304810f00c080c0281e010800405052402e60308140c41c0b1040d00c042d03a4420b8202e4140d40c0d4480b401d00c41c0c6001c00007468140c0381074684030780c03594402898594420400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 998295188 1250 998293938 998293943
    0x90a030f060204030c06080a05070822021807050301080606030a110f01210911120d110a0203011a03010e010902010f030c050d020d06150503040c0b0304050f011e0c110a 74
    0x11003264440410000c1c2c0d0440340115803004026001d84c0d9103a0303001c0c05110044440c00840c81c1080e00050340140300d007203a280b0038989039a12440500040b101035424019a50781260001d40c400251980210446103441c4181d55a23594541d99604000107203090607005081c1d03600945c002403504001580020191541010607511401c02241050040700c284240306010215050741091000e1044001d030064000540182851001c07180400107111140c0040e80307218811f600011344039040640318480b0711126041010854500d20456000642150080647c2c00c242000b40c082a4455040038014442c1d08a4050020070540c01180c0020704001321a501c0002016a40d61a075044203004105a541524102c0011929940c0c8002500010b1905010700350607110310340c0102d4862131040e41180e00c581d40c040e140a0245203031256800c25500050300c2114a1300698901e00e030f218209104581c2d0045100542000192022108800311420200154100258120000155240020030061443c2d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 998296438 1250 998295188 998295203
    0x50603030d091a0907051002070308040b030c041a03041112060a270f02043c0e0d02010c0f320903030703030c030506060309060a0f0e070816080102090a03 68
    0x2481ca03021542498008043c00b111440c0300c10320a0380d0400003441d5095440548114000344581031050743d03100450700c4014a0b09108000600c00105c00074040e58001643d0756105041035113811406209440c3e036608241d4019000c0100400e0140b1586801c5031038100b910030010081101c8002c03911104020141c401c2d0b1a00c4502108190032140c80c124190207490001000d244464500034004000c400350685c8620f003000e18000081c90140c1400305078006004041c005804080c000f4020891000071540d102580c860001c1c00c1160700340000031000300d031a40001101da005c0301024140b40004a5104104641740440b10440e12409100e024104a80e024111035280c007201c006540d0b1081c8640d46805000101b0741404058254004261048090310148210340da01d10901005000c00c8507401d0043c3e1001d40441d2000ca0175502500036604402408101001010140c515054607648030200075800b180105400c0340001b00303140090a6010000d51508080b1000201e2210382404080c3c41ca8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 998297688 1250 998296438 998296451
    0xa0c150b0301200316090510050d05060111100e1005040b0402032109040513080a110606031603060203060d05030307091809120f091e05011d210726070603050603030d 73
    0x1030b001b40324540c0103000007030010341119004280101203412140701c0550140c1030401040e203643c000d55102ca40301014000174400c19043d02d00303040103001e9003e4543e6880c06400a21402c45901e4003409205502910040c030160600f80305141c5061041d5a0004107245004821700341118910226112190100c60218882c0c0b91011400002c064000000b000d40c40c00003045d0241c07039008403580207501e4882c02924581d54800c024180c41c0d0708007440c082c0170440141d0301400003c45540c043c0d50000c00c06410f80c42d924420382d8401d85541e00507609800130880884c800c101d900d40580045d2201c08003001c0500000441e9503611542c661885140c40510000c1e144c98000c440c86150054002e000740010700069102e0080d012541440c103001d03480c0000d01c0c0100415145800c6114032280b0718010340700690301d450020f445502c3c07021840780707201140111400000c00350082a80d003281c0005000003030b007200d0304012009140c441541d00c04e4040c1400c100401c08141c0d00442601d81c0d0050300304000c20071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 998298938 1250 998297688 998297731
    0x9050f04050408041211031c020d080f040602162301060b0c03030c071a0a0b090a05090d032304060b0f031515180f0a11120c0a0c150b03012003 63
    0x2844d40c006c00303841d090322070400e10718811103084403a01c0448050b81c0035140320303441300142156002d0382282c5808144060602013000515260b0007007205021084912a400310350341e0350500303407404d81741039054008031580210121010a201341801440d580018919041010003842d0b1240002007040c0f012141c045040d6050048107100344451501da8081a06945020302401c1e0052081c0d90300a4014400c0400040043c00b182c810343c3e0280c5180e03001000c0b45050b94030104e0262080c210368166040d40e11007030100c003491108180b40554402c007404038944516100348000341c2c0010018503c80e5002c4010000710401140c8520b4001915a10740ba641d800b0f0100812498004143c420494135001c400708101d03400c054104a008000200091110b01d0484015611030b000b040e43e5548086890400306c1c0c131508005000b01400c41035400c0c904001301d90b944400101140d442c0241500b80d449041940461800b803003010720f04802142940c401d03034a09500116a80001002d21a1651142119200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 998300188 1250 998298938 998298953
    0x80c03131121250509071404120b0705070503090d080c010603081905041d10350319050702040617030a090609140d020f030706030f06050301060b0a0f050c060709050f040504080412 79
    0x100190742140640c8d00d07a51441c6050f011003d401c01070340e4400303289d404102424815021510002d401030001c600740004041008a0700c0340d14202126005020001034803007040071f00910004500a18215231038a004030603017982090a1005101009400c00c401d2284448800c203100d41c42418451030449039842d0050a4040300c015082031201c8400c4100c2101000720ba0f652980080b0540d02070b85017154104036910b035580c0207000701710340450703004820411403510130009004041e00003040840c0040d81c2d48904002075030310802d031258503007001801102c615000020a401072071289014140036181000b140c00e10810500c400d480b503455004002c0544d580d41c40d944104000050a680c3c4090b900c00000e030080c41c14501c2c2440340c504110002406150602c641011910511407447c40d2594030803003290002c90403940320090100900c0804c07a241003c101d85882000c1c075442e49c4039007130304100c10406205035240c540c502c22130400080000040c008000e9a08803401e000c0307007512040f680e151220 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 998301438 1250 998300188 998300207
    0xd0201230f070803010501030c0c050615060d0e0d0f081605090d0209010608010f0b0408071715010605070201080a05060f040c030e03130f06080c0313112125050907 72
    0x201c0c0d01012408034140014500203604a074070988007040440b00ca00c105950603604c890025015800c0380c000100a103180840c080e007140b00c02043c0078035040080c02600202c42d00c4046045407640480300d0b1100307843d0003945100d404072480c20480c070246001d02c400802255503403018820403002140d107410fa03844441c40024940d50007406030b0600c0d03031100401000e91000340b0039400c08007000c03c1e0010724500750904480c1036030040e5000c5c240c2c850800141001600344070800300c90398030030000000200780035010858060b200603950141d484c1103a000041551130044c00560000c0c0c40c01042c0b20655031040001842d0400996011800f007551a105070010103648448104a000018a0110882c4038041c0c00082e07a202c02418101c0b9a01e581c01243c0d200d004462099056000300007040b600310a005841c4051481034007900064008200032501c000841500400c08180007425541c420b401804200054903081680c82ca9819100180b2000c4c40a035206044c001c40509020490041c841c11425 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 998302688 1250 998301438 998301457
    0x809060406201b07090e030313021507060207060c0f02151807170d030902090a0513080a1707020d0f0809010b0d1b0605030709180e100608010b0d020123 67
    0x5036141c800206070f50b106410300301ea110060b0301a01601188a202d40d01c50910003400b404000c2d8150f640d06041d001c0ca138002c031141070741e0201c140d08910301544803100050400a205600268480b6610b20b040800d0744c070001a6081440f401c0c100703181040740e0004081d00c42003c6203050000c80e843c0d4241c1c810844050100c0040070f07000700580491200c000c1200784448040c2401120b0051400050860440d0480d040096100c3e904c00c0220f440354143c2e8100c26005401d1012241d022011940c5941041c1d012600703038008100d90209181c1e0440b0910301941c1e101690b03002a00881c507280d42c00070441c0c00d40ca00060148550400802c109210960201c4601c48029185214000c0a4108013145070300030418849a030303140501c00301e0110b225a081c0c90260609445050f5081d0901403050052440011384101e10f9681d03010f0440362040c100103018039a08407003000100d460504043c1e0342035550440f0198000c1f61903440709001030740c0c0712020080303142d10807480910000880000380018070030400d01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 998303938 1250 998302688 998302751
    0x6050f100c02090711100903050909040c090203040b1801060b030c0d021b0705130e07060f020312070810060311030f13080309011e05060307090b030a150207120809060406 75
    0x404c40529086414400c40256800c201c0b0b0714007001c41d0a14050320160500140001c030300f0b0100320701d982030026009401074451410b00e45080c0d110707035541d41241c2040b40c3c00d0300d824603040d080c0300300228002109ca2082d6001d200a00070141008202402488040c1c4881c0c082603002404012100d07a650503213440380e02c440908a860034144da0701d0356486906019180c418440b200c140095140140309400004030740303001811120b86801c0c02a208000013190440550000700094018800e886d9802d41c840e600b11f45880b0400d0900d404c00c2d00c00214680c0011091501d050714101c5840d80c2c000075268000300803126001290703100b4030304554000d0300d0391008211500202c00d01c09000c0e0190000c203020074690007259804141454094156402130745d0180c0c06400202041c40b01105135000081000c07030142c201c1d413180009075996501d4680f004d40224801d0f81c0415002d08001800c1c81403200600340d460301d48524182400c440380c486401410040505558030712104030300204480c12481070884815 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 998305188 1250 998303938 998303941
    0xa05070501021b060903030f0c0904020733090507090203090a0c080c190302010c0312150803040503010f090b0a020d14040b06030f0d0504170703020607051f06050f100c0209 76
    0x400380c543d1080003088684c01000000b070b8446000100fa170b0b100b9118040918103a4450003c885d0faa0740c002c40e01143c01c283c007081084081002c000003c0d1514000301032111030744c6005140386010900c0f5081c00c00342241051100400f203200001c10100761240000300503500e440384a01b141c5008403501c40142628001100055212004036407494030940070707221840e03507030403020b01400e88501c0c5000090100b6181042000440d208440001210b201c003030000812001c1c001c1a1110000994410f04699000040c14019404e0a001c0d20104045d81b440510092880e9500e44034a030341d0040500858075408502c00c082c07044a40c020140003d25030350401c07000e00b400e0405540b000b40494496010384120f2407002c1006e640094075903074000031680c0e683d003010304009040714036140c0b40140303004500c1100d5000c005a0344400080c14598801c100a01ca41d003840c0003181c041d01c0c1d5005910b0b1460346440010001a2a6a900e41c50103503402c40b0010383c000c20700d200a4a8100c0000400380d0020007480 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 998306438 1250 998305188 998305207
    0x6060b03010f050405010b27031c180807060c080f0703110d08160c0302070302060c0601060f02010c02030d0e0a1a0a0605091005040c02100507180506070506010b0a0507050102 77
    0x2507058961031003003203480503121401d02c02074440c2071007268410300e010460041d11407075500401203050903582008800d40d1a40740040c1c6000c50f0129001c43c4401d00c21201d1180d42d4001c031100a1141112425020f810b00d0650000d403100b80c54410340c810f02082c00c080c0b4041205030400c4407448000e0f0b4584980710710036800d00074000040a11f02281d280b003400c240070b03019400340c4942c6200c0c800b0551540c40c00b01600760704841c2c4842e084000c4055204103e800700040e0b4814001e410400c20080051113907624103940105144080b628010940e4502a81080203560102c1180d520f40c804490106450801c491182d18200301b0a04c041c2c10381d2050a01840580440049607018048510341486090344800070130011607005e451580140810520811507414140c001038a07201850040c0d6907502010342e44041a1402101c1c0e2000080007009041c0c10b000000301d040c005071600b41d81c100e0400c102a81c40c5c5036034000602440741044008a04000018842c00460b19180c0d84400290f490b010184d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 998307688 1250 998306438 998306459
    0x60d0602030a0522050d03020d0b120c01090e07024603231606110d05011a0316080a020d0c090503060a0b1005070302010b18070e03030c03090112090606 67
    0x98855043d0708481069010b0b55810f0303200c2d6180b0b13860b005009802d01d0454010180c009521060b008080103441c3c0346400d902d9510703658400b0750305910a0182c01e2440c1280300042c0402055000024462001014030a5080c3c0c0001d00c0c1c80c0003403c49201c0030869114500d41001000307015081c40584541c5055800848a040c0d0800c44c1a803103a12212010381c21101c1d16840380c000340c1e041f88001001404089841004c4280e009032040c026000050728605420f0703036055541c410101c81e0700954a0350010007101049100e0800906c60220030700b1709506209090784d41104603c901d0030b040100701c40200b13400018130b0b0304a0310045071054003041606c410b228003400085440c45514800d00502001410318003031030054220100e8010006500f03040145816900c2d60130508040c3c0456582d0030240030552030341c5040c0608899010300b429014902640c1c020801032a82c0c01c0f4030b002e07420911001d080103000005894402c44242403840d10041d080c400b1100500000002500040c03d0000004245017403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 998308938 1250 998307688 998307691
    0xb03160308070501050c030112080f1e03010f05040605060a0f09050310090506090a03090b030c07020a030c090e1204060c05150c2203080f0904090506151e0f09060d0602030a05 77
    0x20f180248110360312284141105c2c0002d21500c0c045000201d824400161030308000d22000c4c140c0c8000304c3c00d121901c40722054035468460344038021600000184101da051003040c0009000440c0e0604c40f0508010226180d4080c5030091000c1c0414000b51444148c020324206003c2c141c090201c40b40c4c03c07081c9244001034000f602c07099032940100004030b82d4808020400a40040c1c058a840e4032081c50000d0b8148076520092503082c04180500510b8016a50544071100540c0140c10359100c450421042004455002d07420409581c041401580003001e4074054400311501810810006010703810900c0c100351800d8030031010b82c41070380704008520707404101500007400f030700100040d62030181e4140c100141e82c1c2d000141c50100d080c0841400d507400c42c00100fa1580000e000860002d016a8800749083c01c26600071141c0008208420074609201081542d640790400c0703041850782d00704012403d0030285013a030b01c0c010b560b0b090010b022030700c4009070044881d60100007103517640341109440c80100300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 998310188 1250 998308938 998308943
    0x206180708031e07410c220c020109060501050303130e06030a06020f130b040e04151b020d080604060f14120a11010807050a1b050c0604031a0a02030907090b0316030807 74
    0x944681201d404e1702c2c0790000051084000000304040340c0d5040401030103140391000200c64001e030980c010f03900c000c68041d882d12188583c0010072584018500300d0143c50050b0480e9000383d1060220702c40e420000e1003c9000c0303e440005040f03007511038801090070700070340e008050026400021001080f0501c2c0d07004100300e8564080254110351103441801641c4160712400c90004144404600401c3e0300080400700200084070001d038082805c00d010000e443c43c2241c0c100580c000c5242000311139001040782c0c1d44108200e400b008034506121007401314100a00442500030300318800d122003901c40355902c0c0d281e4010301040b952a81c0b410f240005241e40140820fa0001d101c6401284500e80a1004e13a907444c482520b8100703041c0f403201d44030b200300702503000c0640e05407160b4007000c25151203034030003807015500404084a05202d00b441c6102688005889480024410010821201004142c0c40b080e035500040214840000c100000d00e0310800c194800855190306900204022603000105140c3e803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 998311438 1250 998310188 998310263
    0x140f22080712050c030a030f032a02060f0601050301060f0503040812010b2502101b060f020c0c030c06072406180f05071e120203070206180708031e07 66
    0x4c0390b00c280f580310007400400502083c0c4122008840c10700075000720082003c5180d50031694804014909213012201c054400980c0040050000b20588a222154440002e00b80346165515046008008030b01e0769079072804102c00032010500b000151021145040100c8000344541d50f190300010005500c10f44a4110031102c16000f890107501208030840b415070018445110230280b880e05644100107404080c82d8507419860000005041d03210f03180600c140d981c0c1c010307100d5026803495840d065005800c06d1003640004000e10385946d9682c2100d5580d603001070040e0160005c0c05803030558454412204000c103050200108201040323000001c548040c0c00350600500d010329000030219a070540c0c095000844403c0010030705141400725624030611807421707440008042c1c00c541d00720f03041030320603a0058200b28103200c280c241803025140c1401c20740b00900000c529000403a5903a216581204007a0a03100e10103280c00016003003940d140b90f410030040510b0741c007113444410486d1800d02c0300b41003d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 998312688 1250 998311438 998311453
    0x70803030c13080606010c12110f030310050d0b040303240806102124020c010e06160203090103050403120c0804060f110f0c01150f030201140f2208071205 68
    0x43c2c1d00180d414080c07041a1030354079444007180c45103c07040940029400520a2040304184811070800038110462690390180d922418405e480114103000d9502641c82030f90400342c10004100901c0c9010341041e4541070004800f0850004150300e4102c4220007d40d844413840300061510000c5109442014592250b50000d43c0710034416078a403014500c41c01c05242c0d18072520000803850701070200c020208000640718000350910300c40c1681d0007610031181d00c1e51107402c406104e040801005801c03031074415601402c1902050025500d0140400d824105510707400481c1c181030050004d110017500c0b4840600c8ac45000c2a4040c0601b001560229130301032910080040110880c032420325141901d0750318500c1c100851403001440d410420b82007105560380d04004a13148801e0601000070003034241d0540200749140005021a6004612540700036420032a8407448041c0307004542950950458064405000303500e42c03034546003030742c002e44218416040086051a61044898080c51040e0304503540c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 998313938 1250 998312688 998312699
    0xa0e0a0b07140a05340804030210020102090303031303120f1407030c0c0f020a09150801050604022b06090e030c0123040308130c0608090c10120e070803030c13 70
    0xd07206100d014000188241710080740a12039a941103030f04041c0d94060000c440404025071603601c40910112444900024200308500b41142e15404420740703400214104140d05010036201e1100810f0788100d8109104404101405840740040c1075404020421001c02c3c1c03200507000a080024415041d84041070024080d83e11038002d022450740d83d40c1da41004440c240c1d0384d00e42081903524040b030303002442c0701000c21450201c0c03040144020340000c1c82e05510340703071299841c21944041c10260149004224035201007880311421098030250252501400441c4000800142905c0c0c2207a590341d030600c0000d821818000014280441c00c000080004e8880b01b444a81122071240d112699000000e00080110303000c4c4103032990001e40102120314041a580d102d010660060b048030010410710000e1040440b020030112011078015254130400c176a440c83e01604804100541003000ca031190416001540305004442c024541c40b81100d4881c01c02e141344203880c1d0050b2810070350241c3c801400255 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 998315188 1250 998313938 998313977
    0xd0609170306042406050c071503061d04020609060702031e162304021c02030c1e03102c0c0309010c080c070615030f0f11030706050d050a0e0a0b07 65
    0x4500991284e07824845203040410789003500031030440305c001d00038910f001800c00f10915030a120080d16a90010b4824180b1801e552529241d009002d08144040c0800c80140c50b103d0440d02030204c00caa10580f1095240b0000b450200f0030709051074a454000c1440c84c09040c0000c02c140c01e40701c0e1041d00e07040e042d11502c12100800160f24281c07006404054015582e042590080103420a00742c4001c080a280105906c207981c0141d03001101002d0000f00400e1203025006a41c480c40d40085087d8075505040c2d40342003c10a42d4001c0499002c40c2044007031030a82010f81100c10030445884c0d0112500d044600300c6440c0e00304403000c1426500b052919041c4602c00c0d0100c42c0709180002143e800c0c4109030700d07601c00800d8001d18100342d040c1109000700200b003500c600c001c0201d1040c3c0c0661140c0640e032402e05901d0f454158040d000703901c00c4005110854000064540c401c051281c0003c2c00e41d1664512805001d0744500340d03402d4064003800300c0174084001c254500c9600540c48a1400b4200b80c0511310 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 998316438 1250 998315188 998315231
    0x3c0303090a050d0201230421110910090f050103050105071e050a030906050901020705160b09040f0b0d08070b0105010f1407050c0301061206050606070b04020d060917030604 76
    0xd9226030340c0c01c1c080c0079078903010482071030b00703401854040d894406045502c11a24080070040351208000b29003000101620500082c80d00b5029100300152311180d07540c151280c01c00b4284520901900f80051854085441e5000c020000018240300042880e00c0e0030000b060280019521035081100207000d05c3d0094404505000c95905410304036643c50100b1509134000f0b8440c2010503850711101800315180d401074502440c441030005070784998a140452034801d006600d1900c40030644000c0003480c201809551101000b60340100c4e5881c19000e030f0400610f040498140d000003c200c66000780f15002000c0c0c502c0c00d102d200e19a0050741c0301d000654030140d1079281a8001403902040c0122442c2c2030f8007901205101e0011907100070b102c0e100190a403115a003000e000790341014020701c00e000c0c0c140241d81d0003d01c140e0711307075140c0300f034035180c3d017111580c000d002a01030070203050784504001c0540c0c0241c407d19001540e942e05071294560464050b801520414855030174034082c0641c07140d2441d01c0c1e1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 998317688 1250 998316438 998316457
    0x3011409030f1b0d080906060a0e150102010213080601061205010e01050d081e220e01091d0105040303021b010209090411010e090a02220f090b3c0303 66
    0xc5090040d140840140c80e80f00b0000002034041003110180c408008000c000a0910251189412443d002c16076924081004001c20304c5061307a94420000d02e1040d0030b01903008004201d01c00d00148400f401030740644540754845881003c01d00c0c2c001444500407a940e81038441e41d948200c0200419010441a0f0301c0c20b015080342c5c0d02c19540104403070301d05031010003c0a485280c9081c10b01d01c081540c202e02805002c0c1e40d5141c1807002600c8243c04420b4801441505d00b44083c003244981048006110f00340140900d409c1580e403441c48078600e03410180b4401076911607a00030301c00c03131030b1a01d40140a90820710340c001000c0460300040300c506d90107000340c0e400d820015209400030780c3c81c2e40f140d0310b40e40080302549041c171008994120540e01c0300c480785d600c00c01c10940b000da41c0d00004103000c080810750740707014513100000741000c1c880c2d10600341212044402e4400041150100000020700d0081482040020480c41d07507001c0c80d808014411018a071540a42c0c401010702d841002d0507140c0c0705a4052 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 998318938 1250 998317688 998317693
    0x2191703041409041703070e0906010c1a100b040602030918160806061c020705060711070312120501141005130b07060f090803150a06080c03060111030d090203011409 73
    0x2c8030a08000041070340c85402120316060031985000c0c8610300764401d0310400002a6008090079081c2006924150803200a00e4000b003040602d0301c0f049802e80d100c0c4903040d40350b003008010031001c10803120700002a00103461603550b1603075100d501941d0f1f40c4c001d40f8042e000d8890044020105120b4034580342c850b10190104110313110300043e00b1601000002c00841d070050042c01404950059555a415101c890072001a0b480180b41011403070040c000f1301440400803900070340480d0000102d01c0030102c9034840d150354a82100b03290150f6010b086004650b07029481c11000290300c1c0111205400c0e0349000f41d070494004000d189044070148104001c0d030004003080a810040702d60010014220385001d520009010306402c803c000c2681c41280e03042d18040404401d021031071200817031140701e080040b01c0c8020b41c00c0c60180080c15403130008200401c4010044001803082c0d000c0c1c241c1000101c1c0e4201540d6460f14040c3c0380400400744044140e02030b40c44c1a03109100b001203103800314054542c2c07100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 998320188 1250 998318938 998318969
    0x31205012304150f060e0607020102070513020c0a0312140c041a090a03030327030206040201031d0706021006050904110409051e0109110405040c09180219170304 71
    0x1550102100800079080e0003a980ba18032850f41c10810107071102614104406980076450680010003040f01c01e2102e600c0f40b2000c100b10401030f03070005188401c8030301c142c030a0030007841d41c507250b20002c2c0900451009140690500c420416030310081d034541c1414010f0b001c01c081440c01e48088103185c2c0c2258142d02c00b400c100814070a07280e01e080034920078952140e42c5468110300d4400714080c800c56501c2140800e40751102e50251620440104004100528501c00d1000031618003e54850010300080d0606a8a520341c00e40d450420409404494446044030030080e541c0d1002580d0340703d05942002003526110003c5420b01d00795005501491300100a80010303440f0b9030406c0000d25031110100c4040c821030101e2000c1c1020540000f04c0d007450b0317030000a01068a810281500c2c0c400054072440303240341008000c000740e118190310064402d500c000040140000000380440c00001d44081e6000110b4502a8404034821036000c0648500c02124294004a010b040f83c0d01d014030b000d0f0061014480d0b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 998321438 1250 998320188 998320229
    0xb09130209390403050d05031938091806041b0e1003020a0e0f1b0903033603071520010507030501050f131a09090a03120501 55
    0x10a29402c01449100740c218000b0400a540d148144101d004140e10201060400900005004d0f1a0480b80c2c4c905002e451031500c214000c4030034800202c0f154209a603844244004000c1600c03100e400d40042a00c4240c0c03018092031078003440084080b00d8403684186000071052080021104218001d80b0010481501c0e155600d2107050070415100030706143c5443e00140d00300442051500071054070b424940303514158018007012000d80d4204d41190f11703044090108001c0700e40ca0281c0d01072499030714040410814082080a48200411b45034035210100d4404103007940c040d00900010003140b169511011450b4400c000c111f2464401a8182c01040042040d4980e1a140c24081d1105140034810740c1344190b00311801048502401d0740d00e80d519410040c500b9094412980036002c1241c1c410f0307021000b500040c240d104c5015809040e80d840d5094031007468104025030440a0340102143c020b40303484ac55865032000030b900242c00007280d04c0b0500f071043c4214856241a28200b072443c403100d85911 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 998322688 1250 998321438 998321461
    0xb0109060b0a0503091c080106020d021203011710021b010b040c052a1603110a030c2705010326030c04051e0301060b0a022406310b09130209 62
    0x5181c42106e0080409800e0580c10058030a2008a459101c40001e5414180d00a00c1c000d5800301c1c1e0002c2d0740c050002c0c1d0303102e0031421003500c1c1111010f88030f40b5002c00710b81803000d09003444c11441c00f920b5400071807840014441e51100119142515001b0808490316070f04120903140e40d41b91040120300d040050114246030240301c5a000c0700004541c540c10480d403a041e901d4141d50210403584050594000d000b0003004240c0b4070b00300b01049070003901c0c0f141103442d04204c403826442000e0b5584082c40a00810002c019071203034209110803400c00440d85e484c181103504441281c0b0071900d0512080c110315140742c0d04400c1c0d9003c1c80b040c0034814103142c00c2c10144600c001d9881007840340441506c40600859a09000e00000b4215034202d1a40b80c5150b9500646841000c0e105001c91040105020401440102480d076200000312401027440700c0c142c441240354481c1054000301500c96040100e40d031003c5400541d440300007070312601c4081c0d41e80040141e03101420f00c4020350005c0404003161042010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 998323938 1250 998322688 998322691
    0x9210315031a091c020102071443030f020f100504050603040f060f0c03060b1c0f021b010b0906121f0b0a06021f020717030705040f120b0109060b0a0503 67
    0x160085400c0301055400d60015041864001c4c00180e400003a035504200030200080344103151840100300c1c804c0000f810f2211056645a098080d1004929050009004c00815a8440c400d400350024842c1c6900f032800814000b85005c1e8000c0c2c600701844525400c0c465003200358841150307a02c0341001e040ca401c00019510180c0300742d908410002407030000c0307034040c0310710307840504501e80014000f018504041c1c02e5410650000c802c1c000244100220420303061495074450300710349000581044094025030090103014200704004400032184048182d0550118107254070485d02c050a40c1c1d103440402c080b0440f450500d0116030042c00c3d40c00015042e1f40e284882c814400b02c8003143d0b104203c0041440d00705030750b200340010307440010382641ca14040d646800440c58114811b41c5000c00984582d8016240410000301080d4008000b803002407184094a000e0146a000c00240747d40d2009a50540110b0384401c0d42d45008000001609894a20681d0708640740a03160b2403c01d07a0140081d41c0c140c20 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 998325188 1250 998323938 998323951
    0xe0c09010909060612060e0105030c06130b040609170a120c052b08090309010e22061401030c020a0c09111207170702070303021504030309210315031a 66
    0x100c5075001c00c01118500514020b40a95900e500d00782c101020040c0c25514664400c0d03510401c200010b0040b500c0c0403030340d07000e0401e040d9242507581000400e000840c00f0603a00514045401240219082c1d62000f03000080728410401c2da2440c0156001480e01c41c002a0401049030f003d21100e184020b00031500c000d00d4038040c0060740e440c040c00e042400da1a0801154079106000040d1402e14503981100328140c0080164000310704000c1500c0010303051001e030059681c81005000b095441c641d80c220226800400c8070002880010340c1c42d0040310500da5a0b0016901084c20b1580849135503100081d03032800300e901300900c140c0742d45c036104204004103c1043c41011901c8100715100540c034a1200c014001c0d00c003031390740039180c07440025501d050100180c460408c540020314104042640012101c84444000d140b4050700e44540c90180c00401080030010542140d01c0a44088480076109881480c255900d040c030010140d81700d940d5504c00940030040c03014084841ca0f542000801d00207690111 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 998326438 1250 998325188 998325197
    0x41b060c030f031d07051005030c0915041e03060c110d05030a0609060315052410030e100b0a050a08100c0207080604051f0209130507020316140d090e0c0901 69
    0x490510641c064080c0001340d0b44411800c0126040042006400840720319015045090102c1c007440e40348203402c041c40c030819140c01c0a215101002c1c04071401800304400c000640d60980300040a85091880141c0c2ca29182651011009000d240050f00b408621805401e04c00d45400c41601c8640015004800042c0d403481c01240d03c01c410702c0f032580a98000e5800c01a9801c0e0101d5100a031030000b000200b0020810345440c44440458070512050784042b20006112031008404400400c2014001314951041c0c589140090f031035980700d0005844107591161641e5244c6050058441c0750340f0801120381e10115071082c580780140e0004880c081c2d42d1040c2c0c0e01c1d40b9a9500c210b454400c0503501921190401404111140041c030a258041d56540c0b800798101505000001e076481040079001a05070f8a460000d44d0840c4244116841d04000040d005030000088c201001084540880042248680c403c03454019005588050840e208180f045035943e880b20600b80040d04101255412300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 998327688 1250 998326438 998326451
    0x912161b08030a110706022815051f0602010b03030403060e0a0b010e100510050702060304141002040305010e16030201051b031c1407120911060304030305041b060c030f03 75
    0x1c03101400204502c0f09550358001112071101aa030b41410701c190300070302c195031000e808081d200d40d561410341e81c0301c581c006e4412402140d500f8040c10a40201184a010720700c1d04040195003074040342c211801c2c1940c20741302a01d40c1d883d44c00503400c82c3c3c03114010b9507240d4000c1c0410400220250411040304600c1802c2e1110b81165170f44011100c0408e802c4030320107050901c01c01c00c41c03100c02c0442c8801858110b840398480300390782201419031b12858034081d006400001c00607007032001410b11345411415080440b10000c001c00c000400072342107400103c0780340d420301c04c012642520010380c450f400d403116002c0600c1d241c40c550054480d94840c2910b10304003449a140625014424005060380201c0e1001c520100c1c1120311650701200c86000924001310300c0901444007142e4804c14a01c81c91492000000703450301c80e0b003029441ca0205111261f4030402c00410001050703032640299000b644a0000200001200b80440010000d14080c1d040020300e0482c01c00d000c00e200d90360004609080d8140050752 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 998328938 1250 998327688 998327699
    0xa120c03050d090503120f0307050322030206060a0b0c030d1d0a0b0712151e03050303090a0c0f06080403080a0212130b0705120a090602130e0912161b 66
    0x4152014000b000812041e201c10030a40c00c09200c0e10304900004508246050000003044040e40030140030741e0b00f04400071000034411f1180410122500040c3c0504c40814003651600a54500d070891352107025011415000070607540305019141c080d2840d801443c2800c1d5000e89030801881400030003903c54101041c0f800941d1414490b0080c054018180354140d4988004050718000501e00f04401940c81c124500036011054884034080d59490014014078440a0300c0c100f001c0c058903000603041d40800011302002c05000a241a034283c41507101980c520b54584921410702110b108a41c08a0254400180060310031010b4075480110810014141180350440b00c0d442e00048034864487c02c18032491505000d098a00e466020044d80380003880c0250280c40342c040070034041d08031031095441d81c0441040280540680b0344c400d40003e0243d0219070b40d040c01e4601980d00382d1b099016030103007121100300c110300802107584240ca1680e46220140705652110680404149a160ba20320355090101c0c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 998330188 1250 998328938 998328943
    0x6140609150309032a24070e030f01020c03130602150705130906030609020f190501050304021519032304080d110307170a05070c0807050c0d03030f0507030b0a120c0305 74
    0x201d8411052a501c00482c03455080e468801702c03001007018849000c103c3d00001c02d590b46c4a5074005403504d03051240516040200e0318244081c00380c010294008199a980c016001000d4410141c4800361009404e90b15101a40c0b903018008103801c1d41e145031130000d03040602800041c003071103062009d0100074540d5411030108450441c2c004962103515014407106500c0c00d40414400541c08940d90368903078040e06480310420300184109814002e0200004055580b40714600ca012605030003056980d103000450540c0103d547c3d40c00c0c9010074a01482c4e54220740143c0d450200000d10000782b00544c0d00d03142c40b031218940280c2902000c480c4c40f4040b41c040c842c1d04d80003460050040391652244103802105107049d03050007e140151051900d030404c1801a0f00030040c10100750040c00c05561380f01e5600348a42041c030000440c2d40c0004401201c0d008141d41540064803403540d140c0300308500c1c2c0b40c8290480c16640c1e03409515a00440b40442440310619203400350b880d25104481c14455160350307a95290 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 998331438 1250 998330188 998330227
    0x6110f0d0903030305150604150e041406010917030a0813020d2004020c0607080601020304210b09010c0f11030405040609020403021c0f0b06180405010614060915030903 74
    0x19040302820803c00da014060303d0307000380d0004400e41e000c1c0700790b90106001d400340d07124510303001404d1404696801d014451a0b65400d502510600c4802d0120042100c80002030b03a040b40019012b03c0c001801c0030b058119454095841030117980342800c041001c9666180203041040100341104100d0010307610101120407683c483c60440740c5041846c01410034050141364014007442c010030042002c00f0010400307543c00781c413504041c18240c5501d00101d00d140078580100c1c0e6181420b0001401021969403050081c901c0b40510189554a942101d03081c1c03118070320100007140c201c0260000090103404415404010803049a06059850380040c0603104e85a10861b01c60307074005028010340c2400d2014000c180e124003142c825610881c1c1e03c40aaa0345019005049200c3d00310100b803159403010f00680c00001c1301e034100c204505007400c10318000c107000d10038035403140018000c4580504200d4242e0358003c900601c50003607881c440110000b16030004000002c9404100031003454000a0071040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 998332688 1250 998331438 998331463
    0xe0402030616020706201509010524131b0e1e030a030804060f0f09020a0e09101526010606022d01021b030a02010b031b0607030909050921040b0406110f 67
    0x35107800c100743c48c2402c464003e0094200c2e40102c030424849444d400c038001a4420090314100f140c18880508000109002083c1001d428500003407201c2d000c1c0c0c010b03105504541c0c1100c519911001003068030341d0303081515240d260190040400e440210b800b0b06a015841030241001040c0301c8042c0d0542c10440307070b610000725108d84d510a080300c00d40c141401408041c2c250300d1450f103080e0401420150b0344040f240a4003000790f80b100d824005941c2c101c0401c5c4001c0ca107180c2e5440c8100c52030840c0402d00001d4100c60345c010b602e000310002c1c0462000601c1c1d44654003021201d5075a0071902aa201c035550030260070b03a200d6408019400c00c0c82850300040011020031409540c45651010000b400c3d43c2c0148982886079001c0d400d015007440c1c454051440b502d00880c0d2035960780e00c807031909072080d00d0542e111440803172034102000075444d00400d03110003400d06000b4040b060801c11100303d05901507801040d060380703000c1c0424050346020b500d0005260b41000c045644141d04020a41c1c6041c2400460 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 998333938 1250 998332688 998332723
    0x1a0114270709060e0d05150a23070e0a180c0c020d0809090a020c060105120a06050c04090c02070305190f0f03020706031a1f0512010e040203061602070620 68
    0x100300ca664484c50004030441d040300c00d03002d0300d1101c1d01c503255924050302103031051002050200b0b20303003115544034424010002c221100d41048010030074000c140700b201c03018041080e0190701c0714640340c038011311425034040c41012007a040c0900c04a4008002c1120740d402071041101290700076954001100c602d452141401e80d58401c03100c01030043c204006841d4084c038500603c8964400003000c221541962425105416000014079040d0b103000c900c001c02030100c602d014240301405d00100020425201004824030150031044001c0360355007128031010380280c00004000700d01c0b11804030081030050145416003011221900c5e065400100300c3c4d01240580e000c80300821100d905030080780030000035404e40c451020b0208021420300d1040300c80c5c1c02d181020302c3d5a545019405402992054417003e40d82c2015583c413503003501c00480091b04d0980c8684650000501201039440310030929410a41c0a4441d4918281003130300e002c60200314102d490403402420b511081010415170740d81c0c580380c801 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 998335188 1250 998333938 998333957
    0xa0f080601051201030f110d0506041704030b0f0108011a1e060c1005061915141c09020a08060c120601020c0d03081806090a08030c1909031a01142707 66
    0xc0807c801440704c0e40d51402403803403c100201191005c904140e01603003204400c07074888944084006140b0681e00b00130270303401a02d824001001741c441c42450603030304620002c1142c1182c07000700c1000c080200d0319241e4000813055680890030400081b694000300080e020b54105640c0c00b54444c281039410400034000c3e9520070420040d445c0103010840c20b800d040300300c2c3e4074450800703240c085560503d43c0080c0074031945045260a807a0f00c0700485403401034203004010b110704c601a0303030800740401840a070700c24140100c0c00f0415000c0842e03003d00412503444498a402e5202e1040305059000808031415406502c09a81d0143c444541881049200c1d90b211001c528140144040f45090141902420b5210008000711120001800052a50012001c1c1c0d181e0b9120b82c490000e07071082d0100b81c3c4a00444500300505580c0020000c0d003901c0c442c0d03429000c000c61100c40d404180c03801344540002c0e00000d01c851401d905204103800c4200c01800d0400081289000c1110300021056504000003411100b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 998336438 1250 998335188 998335193
    0x20f0f0a021f0b010806010c02010e030d0c1b0602070501180b040f081b031f061503051909080706230903031005040b210f1b1003020a0f080601051201030f 68
    0x6a511071808040d1042129000703002c00217051160050040d030600004001e01019a8000c0804040403040103049440000d650000148407078003041040728040d1400c05030381780703040070300303511a050740d4556001b031811f9440d20700116005070070842c12030a04582d116012986000740e5008102820217441c15001d06403800c0c5140703180c91041f0000c107a00d10058420241d181c0d0303012030381240b8022402e140743c20b16884801d1100c02030450303030b102c940050441e40c98131184a40607040184038005101c0580e03001e1354250190303030654072110320050071410300f08800e02c0085c9403640110398181c050b40c1d5040c2075100d0411420071031901540c604906900c08010400c02032584401070018004c20b8a0601c00c000042000c9102101c015520900c5041407181e408910101000481d0000c5c40701c40468901c030070295121282808132041075030103542e280da08080c030b0500034021650017a8050351a1600ba09070341c00221008000600f8003030400800b0040401c04405801c0450f002e1030259192481180c12031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 998337688 1250 998336438 998336473
    0x3050f0f1e0a0e0103020c0c03190c0f0e191814060a020405090a090206071b0608060d03020a03030b190303050910090e010902070206250b0912040504020f0f0a02 71
    0x200820307040c0c0810400400c4540d07010600c0f07580d41d003080c280580c4034040c0c01c009174180403000c6203c58252248000b8500300c0440d85802e60300c014000d40c0407604258840c041706640140d01e0045c954480c501d40045001d01004117694069030307040210015003030300103084402d00e4604400090700c2c0c80c0114039407a10180014441d1642101138000118502841e01c0046200e01c41e00421005800323640d440b404065449050032185090340c030901e1215100098030107004440842c1c0180c50000e4560000160325003000390508c18801c2e090b0700100000641540d0490140c0f040450746500b08480b0101040c140c165500810051480380e118191500300780700074408211110b04015041003200c803070800c544880e0b5000e46040d500080e40160355002d5900215036544a004c00780f0102e040303901c001030541b01c281404445454823403683d40003039465100f206176568010703260040c0c11400800c820420f52a15034010040907030020b448600309070380c04210408070b410500000740584c10012801c40904c40c0b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 998338938 1250 998337688 998337727
    0x40f0b0307030f0b1518030105100e36010915060e0a020301031208090309060d0204080105072f0708030408150903281e030c020c0607110d03050f0f 65
    0xc443c010000c0061070000105545d030b8a20f15414015030016909000440c240c143d0040102c01a000f800707170341800900410b461180e481a00c503505001004217245100c4800103071200b01281088103800c0d03200743c075442d05011061488030355665990700c409000560118901c41c03081c07042100010954a00002c0000b84180102801d1007540304000510004110701e0f00c0c1e1280312114901001039540385583d152039440b0703004070517a000501142c044260a210b40050040d5941328009000075103820320242e4946844900540b4038080c2281d03502c51408808000c4900d000c2c4080440b26540e50b6802c2060455000c0d80058009030081c04100000c030500780c090316000a0010021403a026580340b00c41407404050445611403c24605148120352207840c1c00e103580b0706258140740384844010409001050f0070101000980620311820000740352103015164425000040c0d011402c01020421800c41c4031140210184481488582060601c034030252080c014a03103000c40d078542d2950b08420803000e1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 998340188 1250 998338938 998338961
    0x1120216110301180804093317150606030603150906090d09030f081b0f010605092d13081908131e0204021902010506040f06060504060c08040f0b030703 67
    0x882c00c0a00010045d070100c80c101e0303461038000140003500b0340400c241030851007000300303e004994070300303544e001e2284590600319900240b40724080518031100d6034490003c002d45c58081600403000640c42e091200080d07030307c45002004e48405080c81c4c01101d04030b000a54211146503c10810419006002c0081c0c803ca4042e40c203240e000e29246666010404d19a804003c058010101e4014800750074084030008140c540c0094607404003c5030326040c001c040300d00c074880c8900c0440000c02c0d5801c448445048420030010f8500400e0b810710107000c03000c0c0704068802c0f100d1082032955000458059809048000006005c1422601040c0c6009041540142800e4034412000643c000000c54540c0c8a118a808020b10303040400300303c4c000240240202025190950002c02815201d543c0c10f5004604c1020211410003566403588503407403c40d40d4030300030b001c04200c04000a02c0341c0c5001c2c04c1c81540d51446600000d01d055180c55402e00030312004e5005101c52080401404021070300750040c000d4115 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 998341438 1250 998340188 998340221
    0x39030b060111030a050a03140f251704021302040803040e0603031204030c02130c0e0415060f0503040c03241410050d031206060f0f0f0504030201120216110301 70
    0x2030300c40b980c0b0383c9134403070b4071000c109100d4000740c8650101d0107a00b2000e1a2640d41e959503000c0d1412402c00002100100c0781c620030403203600e1080ca4001c20a00c030043c00400266160541c0f1800c0d42c60100d1031010140051360702002c0d04085203051002130004002030078807540507603152031816a290880040c0685454400c2d00184046440e42248808540d40190146088100c8400c98004106a11145a04503000604004460030b0050b0401d400d8032035410f00351410000e9180e54101e08a12020f54090b101c0091400c680040640b44214050364106009030307002a1820b0796540c1380080381c3c41c1c200c0c440d40001c02841903052220a070b0310588891180901c120b980d0b40c684136182100000050191522820880070740d081414820070132501c2000c107804040040544484010b89000400110000000d044200c03d45140d80b10b650f42440c0c0c524a621001d08160a43e401511841c840c1d421942e8615400d0050803c0000c1203070003c0c9555020300000042050f8140606095035015a500f20050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 998342688 1250 998341438 998341457
    0x80609161401140703170f07090f2303030d0e2802030c1e030105101a0a0219030302090319260301052806090602010c080c0739030b0601 60
    0x59030041900761480c9002c2510595404e518901620400c4405e07007a581030310980420403c98031145030056000d02c0d125200e030f84860b507440090120454040c000c04008407600e4618403c040b60740310040f25040002407c1c2c034240804144003900300d0342c824540c2c174a280d200102c0d4034014458440c1c10005002c0c200c042e500b81c00070781d402080d50342a00e44082c070300800d00d4080c9440003605891b650407941c00020000c3c001d501300034100d41c010050600580182c07902d035140039400891214215042420785401034050704100c08640f50711824100000d41c1495020041545a83c2e4240700010070000b01010541116010b4240285415004940c408800c9084405034201c1c494070750540c0e0469904031124070920300840891a41c00c0103007407180d00f640c42680790100c1c0300ca4005614005854040d0b000300040030f603462048440c01001c0c1e91040c41800e04101080101d4182074601d0441140c4800d905e00c01b10102140000504e00550440341100702e0034418020000312040e901d401800928110200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 998343938 1250 998342688 998342729
    0x5100506010e420d0b010309030c030f020304181a0301060b0f130e0403050c1506090610180b0a030f0e0607110109051c111b1908060916 60
    0x4054841c5002c408460143c0ba051003801c03071000c0a040500039102082c0e60560032568422115003024804802c0c282c14201500301a5109100302c03c081c542698030307880f0f45803450301d082c0c4134801c0c038209920450104001c00300e60340c412810b03808803402840c6070000c3d101c0e58040806d0460010683d1061099042407000c000818006007503800755001c01d02c90654038006c403240151103400c1303a8010a507590120040100b4540c10001501c241d4912209513403115092400c04945c20b2012a03c0540c01101240401c1c0e0a0401c0c59601c0382c5641c860804c08003000c220520b0710441642c607070082d00711220025296808961500031182090a2040c051100403806004a9105c4600800b24401c100c0300c0f004080c2e50500c03d403c40000d5607000004c0c0c9540442c0d02031440c4510000e0301000010402e000b02503005d50074001150740e00d2034010765840c044103443c9070400401410118007544446c0d2a00c0011500240c00d100180c000c0f800300b00100200d0488031251000c44c8aa17500c45510a082c20444480 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 998345188 1250 998343938 998343949
    0x403050615090717190914010b011704050703060c0201090b1609050a08070b03100e10060e060306030c1e0411041d15060702130f0501091808090f010c0f05100506010e 73
    0x7009070300340404c551745901803000c660080110711805419084c0030002000494019404214264000e9a9030880c6000346501ca60b800101582d00900c01c4e403100300d0408c04140c2590060401308030520010900c4400d40c1c41d0031030303d4503080c2c0e4171006694031a903075075107880c0d081030f10a2700810094034100032081c44d005046444285510030320f041d001c0700100007403940d1010b61405014012030415403881d420140d1014464450b10700540e00400e504080d05443da29240083d2841058010000d11426079250140300c000b0009444e01c0788503240d06003400346940d0b00ca0113401d045a2107118402e464070320746040264045040b41318604640601c405000004100003862007038030300d05940700c40d40d03100c80e4400700c0c00c0503a1640c0006031042c03800c03e5000c0c0e030003000d4100e28100c0d03060700c4060012040e0b01d50018105880402c1c0100100c0c010003110005060a100c01d07103c0300014104940b8002079601c800c86511041c00045842d0340001d8440b12103003210b48203c0707810a40070710f803050305d006131240444c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 998346438 1250 998345188 998345191
    0x140103020910030b040804090f020c0c3c040b01080402011b0f0c1e05100504030f020a17100c0215060136050915091306020403050615090717 62
    0x9018221a0780080d40150951010100850380009494078510781810440400d40007801006a513500b8200340002005443c02510611410240506807042400040001940e4404450705240c1801c1700708034803d40c00340d000019003034211400202061300407010007013200c9681c0c50003810702c030741d02c0180320160b40c0c840d07071a420305010001c16a04011190800c00550b007004003005140c4900881c001c104c000050f004031000b40041d0303801074201a00d4038200b1900900c060301040006030f007031008101007a2400c841040d4a80050841c05880340c0783c180d00d48108100340784082c9990710580da2a80702c0c1000f03216000c481682031002d0311290001e0459103078100341c0a0203090400c1000365404012030004418180c8010242d13161b583c1c603200300d0f070002020240d41e100b11807145410000103000d807000000b00540e0340b20024007844182c1d82e907100311241101803200649000398284400702c006901003100394026050381200d132001d0486da1007040040c00d4000c04080412a007846c0d8000325090340c0b040603 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 998347688 1250 998346438 998346443
    0xe0103020603070e0d0609030e011110020f04030609050d09090b03101d1b1207081903141201090f090b06010809010b151308070b070b13060504060c090504140103 71
    0x81d40d8a031550380c03044075820900f064050b80031000c22840b80070080c8039480410b045200742c4a13140544810702c0151054220f0705c11f035500c2c94020b02c9034056501d4071540186140c468010364039041a880b030320f6410480c1c0c0c0343c01003102c2960141d550303400b0342e6400c181210018070709080c09000308048500402e84840140081071070860302c0b4a15400c054145e400521400c4401c18102c0d80500303880b5955440c908844080d880c01041040107a600c55900820441d05480d60315005107084102031000c240e10710240c010580c00c00c1640034104180c00c5c1244004d04421001d90001ea01e0303035041100d1041100d0305000c00e04455440c00e0524000280600c40555200d542420310204e0360340d400b20004e0242c10102000c41e4007212080c080300e00c3c030810348007a00101c0c40b199400d00c25180c0315a030042c0c1e0b98002d4042d01040c4131082c000b00e070009083e822500d41c040c00d0300f01100035804555a400054a50a0f501200c0541e1a2119150340941c055107030f90003000c0c116803e1148000c45004000e0600e01030001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 998348938 1250 998347688 998347699
    0x180821062b1104020304060623150a090b0301080a150c0206040609050f0a150b03160b030403090513090b07050a1b02040b1c0c0b0a08010b09040902030111070302070b03010e010302 79
    0x1030050060362035500c0c0509030b0250041d552440d0528240000384118003540303d401381c040e01c0c4c42008008024143c103400001600d030622001240b4040400c540040402c4400c10107138000c0030a44041340d07800345008086200c000e0882010328508692841100500f46604500d0681d00f4000c3d50b900240f9590011381007070001032080c2260504034209801e4040d601017511460b04080b080003065070350121214140e400030000c010000d01015128400758400245a600c0c00f202401542d40280c000c5130010b1003810500412a5290045006119602c2c02c4101c02035944201e6418808400c00c0306505c200d041c030706185441642c00340500070800713170584080840741040e29038045450f107a01003e82401d000f44480c001080c44580c140701c01280306030490b414220724000165140230142030381c1602c8200d03180c0e000c407a824a00c002d641074100c0708101e41d0058503400d4000150310300b0701c2158800e001502055540c3e601034140640b91407001d030310001c8183c2d01000100b100b2031903180d041e411759504a40303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 998350188 1250 998348938 998349019
    0x111091309020a12111c12051207050703180509130f06022a0715030e0c1210110f0703030207020a030c080610050907021018082106 58
    0x30001065480c1c0e009420814201c0041945140d950104030424030500304140b07541c00744024010707107840b0b0688044580702d403a19840009286e44c0001c0005041a10b41242000d00d4260341d1050064240d0300000840c0d400580c050070705a101e541c04c081c3d001d80c48003440c0384a1816002c80c44d00c080041400d1507040f0f20982080401801642600206030000b60035515809840d810705800807503c595410210a00c0491110300000860400300711403808460611003002000c05038090038440750284124000e004105100c1e40e51064011885440304004103c1420401e111000300c03151001d50000840302804018444a0a00200c2d60f00c2a4940f501684840c401c1c8013081c104403660b08000d0401d90002ca01003650600014107600c100640d800803100c16555005109600c4070a44500d00140c00812205000e401203070801e8002041c0d204802070386100c3c0351640d08881e080408844a034050b040040381d18042e10b0020305400c00c000300c4401a07070085403900b0703009000320081d080007150740402 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 998351438 1250 998350188 998350219
    0xc090c0c01060f0906090b01090b0d050402061605010506100908030405120c0d031e090b1207020f030a0306170708030d0506031f0207020306010e10060509120f061008011109 76
    0x100001c00400e404403a10f80384580b12440030016040d14001c880a181c0380c00d0982a00798814001c18007110240510140ba20314580045006800000c100384d0300181d08000c001704500c0824480380c0b50502400c000034950500740104059801d15070400340401c08061400d01a0b500301004540480d28201d90805000b01105091401c1600701c618481e40b06115064100c281900701403080260801d00301e561050110401c415190311384a130040d1181c40d00305104204600740802540781d0001190b00480d15204540086185154003984030700c00040c1d107641042080701c080300324501c801542003010300300c0c8a00782000c4a60701e014140f0002c203030b6521507000c50519141800116841c05da5814100c43c0c04aa2241c0c80001e540009012402480f078503000081c8501000b0b440c60080d801860890040c1d4070300318080301e250308010302088c1d00c42184034260922000812500b4900081e440140c001c602d00829100751204041c2e0086030141d06080050704c4007416141241d2503150211216400c01b100071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 998352688 1250 998351438 998351441
    0x604091d0604030c03121812021501090b0312280c0f0605010e130c0603020a020c21070902070507090903170a0b0a05270606070804030c170c090c0c01 66
    0x55a404150240c60180b000b410351003a0700240180c029207620101100c0488500102c07070b19000c41c05a9081100010030000310b804c000c02100345014070403136441c841106800c541c4080207910a071486d9582313401503002c0d810b003440114000b03108511142d052003210000c02c5404180080c1526035820000c600724101da0065562032442600320418040e65081458984010402800b4045110280c03100140303121241070101d4402e154081c0282081529000d0250065000080c6c0c0310150300909907a40c4103500c5030010180d501400c4415511183c09011040b82800c1c5140c0200c0c1c403d5004108020220700002411400c903007031403070001440324190400300c0754142c044002d00e903240660403e100204001e81c101100d5030303208403001c2c5903065035a4108406119400314900a80f0184a903c641040f18649255400200a000f5070f00e4480c040c2c0e20711455601c00d410880b282e0341c400c101800004481c007400360784140e13030318000c10420600000150082c8002001c0d00041500040c9400c04800207 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 998353938 1250 998352688 998352731
    0x90b180118050703082a06100e060a030b180307051b01050406050702091005030f0607021c120f0e0304150210020f120910020c010506090a0c0f0f02070e0a2009060409 73
    0x101118101b00d07400f1420f10944500c0706517101060410b0038003020840d540c2d04a030710344c000c4074010002d44c0c1445c519038039011080e200078540b03500304203003408902000100744028900305d48903501901c0550f01010400260307194191a06040210502043c000d242d005800c542c0360716012945c0c0131070b40d5a00c804c1251040300c2e5800041d003600039140403280408001400f0303402204680c00744d2341c1c0e0360701d040320358250f0304410034207000040c041280418007900c2c02d9000c112039041e0010082400c02840d20954510340c02a40280385403181c1100004150361305000c01c1410003400c000030361500c180349400640500512000004141c0b446010a4514000700070302200e80aaa400554880c032040304c4050003042d04807000350154a20900003805103960b4841c48480c1e1242d5143c008a0401182c1d0032900d17011704240030b00039442074020200b9811194580c881c412908008017040c005d010101451041003074002d41d80c0490700c00c1c00700060555800b01900c003070301c506440c0080c1c11141e1540d0100e81811 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 998355188 1250 998353938 998353987
    0x60207030303091509060213050906010e241303060507020627210a020c04090822090f0605010e0109080c0105090a0b030106050705151b090301090b18011805070308 72
    0x2e401503170b00800c4102d17005448c064681d03da0035130311595070f03006001f0450701c101c9001e030015003500c44d41c0f0f10610f4280c0035000c40d80320020020700051030b20b42c3d03814501d52083c0c0c2058450381485604100700b28a40c060744c1d5002001d803000e03114500f40750118542904c42c5045901b900240c81300300c83c2c0c00000800c917100140300c48031031070700300c03044440100301281e885400322500502030306000b401e0381d007440d0082080c0d0581c4621745900d014002618482040011105e0400c030440c5980005035030f61140c020380084151104002501d145803c0003d00100d028006107410301c10006030030406100c000c103040403041400c1c2031013a50f5961200001c0c407400259085003c641038044004501198004080d01040748030f04111100d0f0109000d640496400858440440700c021441d04c0b40350380c0410001e4400c001018001041141050761a0400a01c2c201c3d040514010a00344003a4000c03800d00407810030101319004403110240e035441f516140c0d103d0f0b0001a2000d030000590560901e03001d9007003030040302c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 998356438 1250 998355188 998355191
    0x4060f02032a01060519051005070b04080301150c051002030c04030c0f08010b060f0a050a030e0a1a0109021c05060312130303090b030c1c020409062402070602070303030915 76
    0x5100c0c802c60760182007008250950310b41000410281000e81b4507841001501e4001b086031031400c410416080b04601407501000014803000300040d0303048413698050741c80f9241a076140c1d0304041540c9460b1405032000c90400070180e125001090000ca00c42c03115010001025070703259038090309007180380300303980c802084446141400a0700116260048094841c040002d002003084041040614040c48250700d00c00e410800002e41114010b000030802c560045c00c010a412075060b08607418400074080c190750211080c24480e80a003220340340d580c094003a0712411400d2882c1141d181413400c030351520291500b50b40f4408074015a034104000410908141c50155441c0c0341e101100c0207021a40c03000303d000c51118400410041c409200740ca110b807031205001070500882e02031410745412070036030191079a5800c01c004101d200260282502030314503c040380019032251862203a8410040c440b200454110709014003000d50302144050403650980380105280215080040414080c60b02911a00c0d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 998357688 1250 998356438 998356477
    0x100905060708031611100b0d0614100b0c0d0c0c030b240a03020609061305040608030a0e03010e0d12020f1206040c02010e060703180b1302090a0c020304060f0203 71
    0x1400500451142c0703048000801c104c0b901e20b07000c0da0500c68401c4130344a030b50001400342a003101217911880e00d002008021580c02000754660204903a0681040656220380004000704030408103100360040c41951884c91800c03054000b001d40b104001d034540c10030451074610709404c0c0030b5046c16241c0515000ba2000780581002c04544040c100e628510500e401034403046807089140000d03030300084a03000f414440c03411100204220300790f801582e2084516a6088000c105900c8500c510405084440025a0350350349203c4098003465203601424070a070304006003501212000320b841e41200c034250501440c0010a03d40c0b00c0044e008440c100c13104210081104015080c840402a00415060b41d04216401d1403000c00c82c2a60100300c022021a0300c0000030072801d038840c1e0f00c40c80e07645071501e64080041c100c50f500c82060780d105590500d00b81c540398410034103601d050310486803c44400d980801110b070803010040d4403400b0b507116541c1031203a010b540c442028001d0044800e00000c840180800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 998358938 1250 998357688 998357693
    0x304080d03050103030f09050a031509050d0f02190812060112020d0b0906030f0601051011060a020d0e07031a0606040323120405010c080904090803180613111009050607 74
    0x4120922050f000540100901b400c442d0269103880d054071406000d4405207410740d26441010012001e051400c3c0740e50725011400f2680500940602001070f540720b920402d69144001c0c80d280c4540c0641c11001c581072030740c00014080c0c204980010155023803500c07041c0d80d454010780d00a0341744a05100c403180002346002a4400715441111040001c0740d03140b660351501c2c000c0c503595912a0352980311603480f40f00144894600f51a8006002101745090520445052492818002c00f0390b2000260f0340c02094404501641e0300541140864000042000c686503403141c140031401c0f40310109100e6489004038005403141d00484014681100c210035518034104460034ec0040024004111805500103031300004502804840c00c44505170748040040c05251182e00315540f050700303e5070b8803541c5c500308800029144001341d80b2940a078034140b80110f00c1ca900050030080002e040501d03070544200c0a00018000d0041004441400c2da4103840c64000640c0035598078142d034002c80c0d484a80451034408 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 998360188 1250 998358938 998358941
    0x20606100c11041806140f09030306010e0f04150e13020108221202150601020c0d0b06131d0c010203030106270506030108010b120a02030712051203070f110a02060d0e0304080d03 78
    0x11440d402c280700860503594440354a1f1052410380382e00034250030420110b51258854000c0103100140100003075148012980085d0440d0010012807250714800380f4104206403010305c6540d842029084055824051540003d0150310300808000c4840d510213008a18143d400e0180d004856003d03080c201e040424000c040d50f500c101403070f403140c0400d1000020305154408a1082071080000e49248214801e40d50f8012684074014069074014109070701445c0250001d0140b1225104240c0c04d4050300c1220410306800d100441113010b05652042004101030f03640070b800c12100c0700c3c1c1c81901d004840e094040d90550001e056225690102e000b00c00491840010b43c080e07007401c2001c459044256013000343c402c2d25501000d602a505801041c400c0010b0001403507004119031140041d00c4445052031361143c41a00706560100001c0c0c52424426030701e07a04000360401141202000707025010036540011400e11900049061a03521009240c451a0313003041030701c020b442080140c03507011840c0c8800a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 998361438 1250 998360188 998360201
    0x50a09081603120c0221010f02030708041b03030e06160204331212021501060507020103050c120c13180e01060b0309251d010303020606100c11041806 66
    0x242d40c030a0745418584603a004c0c0403180340c0b1a41c00b0704070040c01c3d2a1040c0c9590f1000f82c640992405540f140a103400100f01407004511448a40c0c903080020304080c20701481d24140c8224403180000c400e0341c1400407a8004180c1613000000f22080c580c2d601c0c0c6c001813032003000e5980500a4000341441d848000c044854090010b51800070041c00710810403107003415090324107600c00c03d0540c4110101d210301040c0207094400c3c2d0a001401111644040756018180f00c0009078000d6000810201e514070440d1380c5170150a40003400c1300c15081c140800c010b07103000c02f10300c0941000300301a40054012003100907428003100800c81e5040000ba031400c6c16500c0b4000e48140010400e40e0351801002150b80f50b407203000d6901808084008200100380c40100c241c207004a0751401460400c1510b0004e0070366400c1c11401594400d45540c4a1254503600d806480c1207005055180b10703e8008046c0c0030100d9026101403500c80d0000c04804403041000f0201c0c0080c904160402c0f000d940c01c000c2c1d00c00707000c03450b000b03070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 998362688 1250 998361438 998361443
    0x506070e01020f0705150304231c051213050f01020a08150415091a2220070803270f0f03030f0105060904060504020c0a0302010b030c060a050a09081603 67
    0x10b0707980c0c03e04102d0b004e403241e1541c00713115800503a818900403010082d030041c540c0240f2a180340104001d1551984420700100e0308102d040b0f502907094168002c0d110341c1c075682d054500e401c00781d081c4024210100b040d00401420241c0402a05e03540105010301002540c03200d04d03280300215921020100028003030038080350034052404402822820750300f003e202e03280000a203019620350b01801c10035035901400c0340440b55202d01c440e12100c400c640d0307120003003c0102c4d82964454588006030119220607504403a12100c46000420740405c00c81c501c440840d9145940540d151396203541c0d8006aa240e0b80d040001010200188510329954110025880c1c4032210000e04841c1c004101403d5590b0b270744400c844088904040703000400150800b003003c0c0a45400050001c0340c283e403100081812038101c10421751a661140005405168080c8640308414405401800040b032115000c60710b00d00c5490380260400400099040c4110b1288418001404802043d1001026103601e10a00d6075002c0c00103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 998363938 1250 998362688 998362693
    0x90a090f061d190819020a1a0604151a07060608060106200f0a0f05011b030b040f0504051b0312040b1801082a04030206070c0e010803070b13020a030506070e0102 71
    0x951600f40d10307541194140e510501141c540009a03031205801d000300d01c00380342984110220540007941c41107000c06421512042820186410420801a98060500c845802000e81c00910200c030482c0c94201c1c144103c0242241d440410b49482002082203030300c019100d00425001040003680a103070789031210b8004422001040798a04140e45598460003c184158480c810440c0014141c03002d040c4030354020000042e401e000d1030200c822070030244800c040065030740d0300d1202e16883c251151440300c4105076010001c0d0f10f0300d56151561000020303203049944000b4041c1d100e055400b00054588004006881d0791900c0c0d50f507040d240030340c02140704c1401e82c00700c03a42d140445502c103940c01849290070707a40ca5501070360050537920600b0803d111803508404100400f001688450f00100031192260100c00125840c0c018660602881030b0400101e5030410403c48011603201c014054110302c2003401120810614800600500040e500080840c021071041104103074104402540044080c0c09 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 998365188 1250 998363938 998363953
    0xf1303080301050108090f1f061502060702160602061b130e100603051614090d030509280312030b12030c0105010b0c0a0809040e03120709060c02090a090f061d 70
    0x22186d19200c00418500301f90348140100c262510b50044d0740100000d206000043c0aa00e4200302440001c460240c81c01603480b180a04c100140c0c10021030901c11f0f182445a4a102e0908000a48840f0050701c07440350800b102c0072030201100c449089640c102c520701482c02e0100d960303100880c0309800c01c0b6500c102d546188000040c605000303024084c41040c04201c004011410044103413005c217916650303410121020320000529881c1e9183d2129040d0103502d032161262800e0b01080340d0b08041c072140004030421809040030540181c8010340623280d01c0500d50354440c1e480d41d4210000c11660268982c030140342e0340c0c031b20740c00c0c0d102100500d0150905002448183c0e200c81c0a80007510661480f0003240d4440d018210119a805020b004407400082c40444d10048400c809403864000305209004555038405107c2305d6508100140014203060034018540c0b07046400003005144010085c6c51820784030080041042043c0c2040086551702c201c00300203040000340410384400c80b58030b01690900c21110b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 998366438 1250 998365188 998365201
    0x2070219032d03050412030309020a0f030b090115230a06090302040e060105010f050c0f0a1b080601050d06050405010b0a03060605040606021605010c030936020a0206010306020f1303080301050108 86
    0x42c04001d10a8268440d549080d10f411070000d84000108001d500305551443c10710016559805000300030100070321001105419800c2110648401a0401895a00d0f0410201130101e2007410001141c0c1d01c0c1040d0103505515424100d010724a1116299000822003400304945401c00342075070a0724001c4c3c1e020000b000b003c01001d981c851702070007001e0201d803980d004903040520607401046415000300640300140307c00085640b81c00f2181c04200d6890210900c00b5244c202c613074012100401e0b0303400003010035514100c0031403818020f1210180059480e000041e051290175085555680c0018204a0f25266607041c07480c020000d50003550321480c104403000404901c006500c00e080601c0140741451945071800640b40301c008068110280446500e000070204038110419444252113040c0d80b80e40e0846101a001c0560840d64100c416807041c004240d603150b0015400381580d80c030800041e5200350b0801ea40c4100c0c011044292002c243c0c16801000308041a005035040320070a03200c90b00706490b02c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 998367688 1250 998366438 998366513
    0xf05041103061e09010609051302090f010b0307140f0706060f050f06090d0f0209090102040914090d0f05040503030a022104081504210c0c05040c02100207021903 71
    0x645507440540509242820041103ea00c45900020074800010703016075181001d4007624805c80350003462174a421001d0055081800d56503070b010440c2226419990304082d1003a03124000504a82e0420164130080c00b1741004900884540000e00c80e0030513200c2c042d91402d4005409540180d00c803815502d00b0010300c9050441e1400c217010001860310313041a511005108500c1d542c0803080d42d003000032801000261b21410000f9000304818800960f45606020745001591003800e03a291007400407004004400a0125049045440c10301e44058155100c1e10210750b04d0150b40c000300e5240c000090320b08038054002074001046020140310351a9161100c10750680c50045111b611917541043d4031001d210b0300b90303002c01e90b4040d100d80390254104040502c01c4a841103c509410040f50364804d0704010b001c0c3c40200c3c980101f03011030f010700c0780d0121520000d44403000000c1586034140c01082c940115a214404184600248005610b04035902e04004540c0842c000b00281c00445500c910b84414112 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 998368938 1250 998367688 998367691
    0xd170d0c020106060e0f0307050411070b0601020c1003020307110304080d080906060604270914150603101d01050708061507020f010c02010c0609050105071209050705150d0f0504110306 81
    0x543c4171003901003d540180b240004071100d8040e49030141c00c80c0894155140d125001640203814801602c0321f5407407800201e201c0b03000d8801c80c1554400e01d00e460b0260342c2d02c0034504c9092100c0c940940ca989440e41d055a404028103040c813141c0c000403d02045001d00003400704810a5181d64101c0c09031030300011075496080540b01250001020402032011000308084c010887c0d440042640340001000001300450701506400c0381e0702111041d101c0300740e1404000c2000c00c80420300100889007050b0f0006075413240b8000c0c24144a5440e004143c0703105180c0710740f03001100c000c20000c2c051442e0041e0001d20085048400c0392141082600e0003000c0d08181040d0354055501034407000b40041041d00540c2e00603401c1c0f0f000c07410040c002040c800040c291380113aa21051003030002040301d04208002400d407011020f0b20034601172800c40c841c03000c103800140f41000c845040c0d518042c213941ea80b42c82103061048a0409002c0e900745181c00b190b5480c207521103031242d4082c0c01c4004510b4540d900300340d1900d80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 998370188 1250 998368938 998368949
    0x1204060e0c0a051005030c1603090303111b09090a080706360b0a0e0f161e0e0406140403020c010216031101140c1906140c030a05060d170d0c020106 65
    0x490b0300714103601780900b005581050b41884601d0902c0d421006038900a9070b83d074000c4001480012007002056001640c5840e241c00f16000b400781503440f040d0441030104090a080c0c458000c0002240000406002d018840e9400c00901c9270794541c00d0914801408a14054800024240c0000c01292641c4924400e24650325404030b50184010f85612280079000707001c5101550362038242601c462801c000142510401001910041c040a29460464000d580c403000ca004501e00210102200e580f4191098841c40748680515440d18100030009140440074640380c54015410310050640000d006010302e04240d00b1100d420110300111040c0d400e00d844003c1600c003918203d1440d03980118018050340c0818121a4100501e82c010246030030071040150210585640014003808014020000c081c582400d60124500744800001e005100041406a040d9998400f050345551810000d44c10140c225846e521880604a0b0302983d90b8414403040100914016209410307034010f006080c11601e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 998371438 1250 998370188 998370199
    0xc060108070503030d05040c0b030a0c090905090c0409050111130317160204050718150806030304050904021e0405010e1608012d090509010c09060206040b0415021204060e0c0a05 78
    0x980d45c2407418017822003e0412103074040b90340b0700802c024484c100a14841c4160320001f14200000f2800508205041e8100b00c0343c00d82000100f003d082c0700000e00c940c13002d0301524002400d1809003062801000803111000c0b480000045881300c2e2100e101c01e42095134082c50416a000040108040062040060a03000360010003440e0001d1b240503440503030310078001d013002000d4480c640d042c0b54001c40320343c0200f19028501d852501d11030303611030a801d03071048050b4015454103003400c00050b0483c1005000074411240741e984d811109111007a81007020001420a0055503195046401840011501a5030450a0b01403a02c0381c141300d04c00782070403200c030740c4040d50070b01405268410f20b1210b06001e84d007104417810000550b60009200e442e1048001600002e40f00580c03002c000c0540f60594041c2c0d085602400078000402c00701c0b5643c81e00550300082c14403107000003890a00180c040c0001074201d91600204001c280295500201a1510040c09032140d0000f14410401c000d11179000316900107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 998372688 1250 998371438 998371447
    0x606091303050f0d0e070803390111180a030512130f0b030609070c0b0c0d09080d14010618090b13091104180302030306100c050a14100c0c02130f09080c06010807050303 74
    0x6850749c1c2d19603011900c21454501400382d0280550a4440f0741c16241140400061200c0b4016010389078940040c00071112281070a1468450903030380d4000720102e07590a100000e0000c110b038078100091008085080018448555400c0711406a400494038140601c62100001d2078052040c00a04038095001c8042c4007581c50322285100f19421030b141440c1c00d030f81c0d030311000703400b1410340400782402c80c00000001c071b8481c65100f0600d000c000c0690080080c48105403000d5442134560035003c040d40c8450000141d051001c00c002500c4004101e4043d0290740740001c0101800104c040c000c03206d01d81034078240070b40d440c04410400104100c407400b4005800c2480411070314034040940030143d144501e41781003d001035440b594100b0390b441d0b84c2120103100c0d040038131080b01c0b000d1086c20b8800c040080c040064001500025201c03824100f00248640c000c0100c3c8502c007401c607808200000c0558800700100c0f12036191404881c1d2000301c000c0301d10700c103a0340001480180010b00d201900c0300503010350b082 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 998373938 1250 998372688 998372737
    0x15150618010201020d0e010204080708120717040e0916080c060d1d240a0603170d140108030403140304030c030b250e0906030606091303050f0d0e070803 67
    0x51400c4004614110f5400300200e01c0c403500c0034001c05c060521180001a510383c074202c89103103081100c2d40003812541000b40d000d123414100c0001c2d2281581c01c465050146807000020701903e21950300000321503001641030182c00000050310082402d83c80120b219a2a118080541d458105209155200c88200010481041550004000c0b04000f00003928402003024484d07083c50b21022500f80e58a000101000b410403403082d20f160028402801001064207640b2106000c1201c2c29149045110000e40c0215080e0303241e0003000c0ea40c0b007040006103135584038281e0503181e0b801444255240f120200d003940380c00402004950850ba400102d6614451648d03480d8010b040d4000d004c01107847e00c000308a0880c400048804d10440c825541c2c441d0176055110810540c0c260141000740694890001c001c1561110928a5000b907100365461700c40010750f18046505205030b2411075802c41001c2660211000c450300902d4081c011031054441d02500d900c078003503513030145001c0d030030101250308506c442 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 998375188 1250 998373938 998373967
    0x206010e070e010c0c030f0314040f030605250305100602060f07030e120f030601031803020c120106051807030606050a090506090f0603100915180e01060e0405151506 73
    0x42c0c0c0c0410305001d40d9814944d161503d054400707620035201400040c40e140101075100b49400708450000c10031900705070030306082500c1e00307200380001400159100c000c02c000d00c5030000384000094541c010029004042070000300030b440d06551600c40c108400c01c01182d20340c004034100384180c503a0001d008295451b20002c80c041c15043d400101d0318000c080c411120130f076412000742040440410290f07600d04203c400142150070245031f8014002c0c0c002c5c9944000303580821058403849086403d100044c0380e02000500600041c0c0c000c0b41c2c8241f518401449611940c12000d100c2d2007643c50030070105646080503030786841407000707000015003c5407003403000345030950107403801e42006045c1541c000b0002020481e990310549005c8000440d03904100000d4040b4082c2e0400c92800c80c2030b088203140703450842000343c180d0441c0d0b65012a10b40b0720202e0030b01130951005000308900484100c040c242401d22a4450a0484e1418503424003040041c55001c000042c803584201d001c1c004a00c1c04110030710496 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 998376438 1250 998375188 998375207
    0xd091109150d17130e06030601050d03053f0f0f060306070507150204090203060f0105090f04020f12040f050c0907050307050304030e03070f140a0b120901060915080105070206010e07 80
    0x106a041c060002c04401204e0354112400b41c0042c00b003d5003141405420180303003400590203944100c10b00340350f0345e001940c8182076881c401c00003220080d90081c45040710900003010008068800390001e4462164a94400c03914080e00004100c2c0140b5121803c50054148003226580e805511050203c1c2030301d407003800100342c8107010f020408400381018a10700160303030296101382c140d1500842400020710b0864104040da40d02400c0c85440c142050000c14110742501060798819a80854202c100081034411500c10000b0300828000f903181a103030041032404080015a16881990071740210fa040101c822802500c4d80c0d200c013402d55072003542c1100d1030f80c0b00401c118100b086090040728551410010f41740502808040c035030500b03081080c59a00ca40800c510144140e004103000c001141e0b07800c0440391608491042c0031120350f03a0054007400b400c03041c0e00c040f00701c0745071244000b071850b9600119002e480d20300009014988610700200e0b07071100e0a01600302507520510203d00c00720701500400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 998377688 1250 998376438 998376473
    0x80c01140c03121801050f150a0302030a081201092f1b1c020c091602070b130f06020a0210050c150f010f080303090a12050d091109150d 60
    0x40d4a0020000501420358116180b0164003145007404d110020b014140780c407000c400c1c468000c1280d450302c0c2d110f0519108020b05210f80d00703120f0b42d40a01c119120000000055a005003c0742c440c00c0081c0f52000440d404910444c44c15900b0b04004655600b4a0080c01c2c0e100110b030f805401c9103008140d41c3c05241c00c2d00d03810095203038010001c060311007a40003840380300d1a000380050844000005001006640008032100c11504141000b00c0955580030150b908100440e941c2070fa40300b0594020b07850082290442600c22602041003003622514072460070540c0d024040703000180e40d40f8582a0b0b40c40700041c40080d400452200c078481e805202c1e802400d400c03202e07003044a203240301c3e151542d031800a05403102c42d604800500140301900e19148048010001580203514616100385456143c91072220024810030400112002d01e40c030440540e003158012000070404040d4507c0c2241000d041d88141074020a80c02000030041000049100003c0001516003001c0340c070b2640d5141010014050032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 998378938 1250 998377688 998377727
    0x24050d02031302120d0f0207030b1305150109020a09060912020f06090406060c0218040305120408190c02040b0f0d0b091203090709110a0504170703020312070318080c01 74
    0xb9a00507a031450002603c5182030b00c050300350001e404000070800c01e8039100201c2994461001040000c82d00c00e00780703510005103051400100240d1804500b0024160005080c1440c1c43c2e001040091051340140355940311611111842d50381d5520a556024051182440070641c1058080c007505017000d490701c810200504080c5003090010025007101d000b6005140000e4454003410110305001038800a01005420040d0341454030f550700030100e03c134116500c0d1203011214082020040000280d840825150720f0110500701b12500060021400600580c0b049060643c00c3c0d41d01c4c01c0a0300f041c42003144c094001030000e1600d40300c0b120805005403001c42544a00d503449502e000161010714024210400035040c5285861404800e440000f800421754480c200401902141c11004481c100e8100c0304804c400005003c00850130110035500c017030b405014000740071840c0400040100315191003a20f0f40300080c1d0b1140540d0301d1803046405114115481008851980d6012351151030300111546803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 998380188 1250 998378938 998378971
    0x105070212011e060902030c09120102160807060f06060203030604090c0906062102040b03040b060f0a0803031605040f0522090804030b180c01030e0c090408030124050d0203 76
    0x403842c211000c03040f0490000c4160f031607104000700c0502441c0c0007000c400109500b10b04084209440ba4820170500d68404c450001851403001029011b0300c00c1c0b1803d0407205034485c4c59904092086a2003150100d60f518641401201504868480c41c02560116801142950380c3c4005110092070090710642d60f00c0d481d0503002905004500424001e081a079466144842c440c040f41d5000d800c415503c500003600500042c0b1101c2c00d42002d581c0c2c0320b0f800403002c591a0304c0b45000301b0950131400c03403010340040719100c01040d030b544000015800380b0308000003454150440407040f2541e0195004a4042c03004000080016151480c1c0c1c40e500e240ba030401d200c0c00f44404001c1102100c800c11000c840e0b56101050801c28007804803a12075024050340c1d92080342e52925002140c4420020307142c103050550703810b880b00e8240410482402802000b402c4484541418203060038290800d1180213400c4560800100c0f030301540381c1201c4524429030711130508094403149110082e410007400005110b02251 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 998381294 1106 998380188 998380219
    0x21030708130b04050a020f04110d0e01020903030c010c02060a062409122d0302070303110a170903010f050105100509030c042a08040b010501050702 65
    0x203024030865454107540e11602188400203004405800304003c108040010070a02e414000c07540e0019444c403035401c010503a2400903001c1d528000c2030007000202909600405000c07000c1c50009800c042c4a031000c60702c0d64000104a414076915468110f903156010301080780c126039452010b00c15241450a2201200c22917903410445040310409519402c0c03103841980c01514111810206c9080e0500700102c514500001050b60f041c7c5054411010350f0400161400e013551507006481c882d842d54400f500c0c09006a1b030280880d004002402c8009038000340c03812006045258603949a1006200b41421a042001d20824031407a10005005541d02e0140e1214140c2080c9080d990b102c04a00119090048410300b894000742809080e040d054400c01d4405c1254103440e4081002070101001190703001015103002e4014030b501030040c08154820f1005154040c005040e0a60101046 = true := by decide +kernel

theorem cover : BRFrame.Cov 998201438 998381294 := by
  have h0 := BRFrame.cov_init 998201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 998201438 ≤ n) (h2 : n < 998381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
