-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1264
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:03:43.944983+00:00
-- url     : https://prove2.me/submissions/cc8c1ea0-7a04-4743-ad60-bb7742665dfc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 227158273 ≤ n < 227338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 227159523 1250 227158273 227158277
    0x3050a06090605060703030b0a1203080402030c19060c020a0306021606060605030c09210102042d080601030818040609021b0c060301091e0c0207030c08030307170a0905011a01 77
    0xd0155540c0310041501d8440c002c01d540300308200300c0400004d01039802003800020241c841c01c0d03416919411034000b4001d000080d00490540c1c000c0200b14a001c0c46024041441203e4106501803a0300a801518283e40501420320581d005100150341e0340e1020400150b903c98070656a80c180b8501c02940c49a081d80b0490780340381800e001241c0d00c1d01800940344a110840702003800c0101d540300b040645807a051075048601070041d18250b0050007800180040c116001c500d10b50340d42d86a80c24035042c0c1501d545140300c12191101800044800b10380941182d81105800f0386600e4007420300010924141040b6500510305400012204a40d4000e0108046880c113003824010348050890344031100110226403005c4204018803150106904c840700000c560f07a140343c2082c0761022690201c0b000b41c80044090703800401c08008221002d0600d2000d0000c00002e9411814100c0c00607102c40003844001400c0014140080c22540180c1d01c03050328990041b00030700c441031a001c103000912b05d803c0c000380c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 227160773 1250 227159523 227159531
    0xd090507080312070f03020c010c0f090503011a010c05071d1605090a06111f1a030d0503060904030311130608091b040510361407080910020a03050a 65
    0x40c4240000c07065480c0000b803c0d07010682c07555020811507401108014481c245035003841407104ea99000d1103612695440c07900c5d10072600c086484050a2044664846407090303050050882004068060001e0805428207283e4065180c9140450030050039800407004a07040c480710030203a11002041034000e040304050400100140141203510348201d100581d0440418841007010520a01501c40380d84d00340c400781c6003079070140c810807500748043e581c000d8620b544441c0000d0181c00085440071110008038010f0640d0507450001501341d0000034041440340d04004002400d05001e90050074402d20030300c240b00e91b030b6030f00c8001074654404035000d9080007c08803400140203070300000e002441004071123041c0011014402c00c100182400508611840002901c001900a04001c180e03139042c5054190808080300c603007031512003060300c0d4560005c0e20308000e1240c0410800c3d07000607402444510303040c1010f42d2509203141c6001a10340000c045070b071000600ea5441c95259000a0240001c120184 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 227162023 1250 227160773 227160779
    0xa0c0b131a250212120a0e0105010302031f060b04030f060e0127110319060509060403050301030f02240c0f060f0118090501060605070201030f0519020c010905030d090507 75
    0xa00307442411102d0818031600034481c105851500c2034441c595150a104880c2441004000c1c0c211076007101041120b064036410038004600c400c0e000303080d140345103940200007035895074001036612040441400404030310f422802100540c2c940006010b80744281b1440d40d0350741d8a103070800b40c0d090050403e07a65107103081016854400103000311034580540c22100340b983c0c0c4810340b4981015508200407100e1094036100903c20391020300416046060745400c11490140c80e04128003582d200600e01c080ca5041501040000798100040d6415640c00071200c0307803102e581c0c1c07000c184884401c1034240240c5480b001c440909101c450010540c40b80c0301d4040d640d03045d01c0402150f90b84c41040e14500420741801006029950b141518a800c2cbc6c10300c40408070310910a0f86034507084070300d15040075000440001d548000c0d960940280d02c04203034210010092480c0060112682d01444072003030310042d400040c0a5501a0b0942200d201741e604102070b40e5440d550003c0d203d00410315028100e03003074004c0480c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 227163273 1250 227162023 227162063
    0x2030415050a17011a090a091103101403070b09011106010e010512070b07020108060d0b0103060203040606050d03140c0106090203010b0301050a061b030804020a030b070e01030b0a0b07080a0c0b13 86
    0x1a03040b5504024181066240758103841d2040d00008141a00814038100005007410980603122782035880c03041075030f40c07820f0a0001c1440b00d9056040501c210b107040991000ca6207001480e201180c00c0c4c0b001582e210010030740121801452080380c000350340700e014008541000c03080e101038100c070b000305d0b110303001d008008244940741d5229205400315a681846140c0155006a8525905c10310080021002e40c0059852056110702078000340c0340b6590200070441040043e10809020300f004880000724441e032a07a00400c80003403e8008d142036900450180c20b00d08007504407402812400c0740039900c84da154140700c44a50402d214140c07040c4442400050380e035014115802900120250f1000250501d45007510100f01c040d00480e0001092500080400e0351842d081340200041d60780c1c6111749a0440004042d1100401240e1190080101c1000801c00303c1040300e45041e0710100702c41d290b00701c0d82e00c1501e030342c54000d002800303d4250804102c4015030a5548140c0b207445080e000500e490982c0301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 227164523 1250 227163273 227163317
    0x1b030c05070b04020d15050603061b07230703060b04060f1212050f030a02031506190305090c030a0311060c1201031509060e0d020c1e01080702030415050a 68
    0x10900411010400300300480d072900c030031550182c000340540c24001042d68600205180688100001c0c1d9590000c2c0241443c0c14850103400c8044600020320100b12407030481620310800c4e100912a400013900154100301281d00581780d00c2011060303851080e0340c0d040640c05001d021040622861400034041043c840c0601404141c0d0032034544408084016a07072680b85032940c1c1300c0a02880800d000300220012440c004600c0384d9100750000d84c0700d00b071004035464a0703071140410720b106040a00000c0b141e030341001401d0348002c100c2d24001c612526600320b00c0e810715040d1800c0e5a01406202d07000014107401c03241c0c0c010941c030f00f0003c654056443d2030640030b80340078512015512145540c010008075001d44540c8444c44205500003801e841c10756216011108000c0b10045d45810031107050741400e070144215100500c00f5288102c82201c910122500306d074419580c1070500181c4008200310718400c00680e00503041c070241c0110708041152010309660001425100002c01d94403504e1144111200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 227165773 1250 227164523 227164541
    0xa230102010609020a1e090308040f0305010b0108071b172a030307050703030b06160506011a0708031b040f0b030115110c1e19141906081003050d031b03 67
    0x940e5a50b10510120701c080c0b14080204404200083c1c02400b001240202d400ad00040110304140d4a520f40b444c075010f030075910200c0d001c074103100f081804c000c04282c004551a92511021002008418a0b0701d08950205051414103010440221300e03c0410651070200d00300d4596181107000300800d030103042690342c1c40116000380000f4030601a150020f4025003006008120081040781480100d0090001401c08246d00361a9a130102c00100401d050204a510400644001c0c03d4908031081c1c03a00600340c4406000c003403254210846204003080740b8001e07240a011808841d00303c2c1c507641e84a10210790002e0245900120400c4141e0884601459110034042011806170060380c1041d8204078078584450f00c15003003402c2c00306140007655101201c0300401020050038009041c148865022a5600c600c41c6038052520741400008402d14910058112a000d18104820740e070b03401c01205414030240e0004156102e020301054440703805070080303203030001d1650516550350211603040f029169068 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 227167023 1250 227165773 227165777
    0x15030503070506161413120c06030b01050702010503040803060616050a0b16020d18150201020418150e0411040c170a020414011211070c0e0c180904020a230102010609020a 75
    0x1100d00d0498041001d4082c0344042200007400d19950207487c0340070700251030110f4006958140030711035240c062050310b80001e03003823801c90b040942c02d40c0080c049220292016008d408040300207002c03551028211000704081009059031f1841500e070440d55040d910300300b11510507200c40050340303a070407580c101c20038003d45600401c50703400604026250000090b05c078100400c41d441c800f003550040700f615407081200580c001a0345a01c0c290a48450711280401402c02e00d051095500079000300b200303800c00f980c0c02d040008419480d94075100007006170100151b901703d03003050000f0603c00e40003403070380d40383c0303000c644989c5880d59514002c50224810303401981440c0c04510700d14121544500d080082d495860040094042c138003021108031604240e1044842111601090041e0819544425045299040164101072124400c100d581100d410302e140600b00c8540040c00f5540da428080006001502040350f2840e8003c113000ca045140c03c5405026600b400c50010310601c10303100b00d49802c0c041d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 227168273 1250 227167023 227167037
    0x50415081626090708060a050c040e09151303030b030604020a060c050703020a140111010218010c02011e050a1713080c030d02030903030a0e0307030903151503050307050616 76
    0x1881c41a03600d007400e200c4a24400030511100070105070141034581c040c60300c1e24000d00400d4640143c440c41e08000420001d4800c5c01c00040c05642403002013a201a10310303180b4002c00980d00d0364185450880d505400c521082e800006208980482c24088402e0b280244e070300380442072103182459600e9000380c41c003d4000300c42c09002c2040b14425101441c00520842c103413a20311f1b50301e800040440c00a42c010181940044242d82c1c815030b00008130401007007600000b5410132001400f101e1403021198a545c0c18414144400400c40e0310440810661003410203010086248001c2d001f4540c0d00042082400305244400c0d40199403102c13a500e5205114a020150038400c050342c3e030100582064402c580c0c42e100500c005142900d00b400074600c03c106100046489140201c50300b404e4400151f000c08183d0410040c200110b940001210141d80d0040e100740d1000c0d002d5400c400040400d60384030f0203c510000404810004040003e184090181048030155103c4c04d044081e82160008044040340306 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 227169523 1250 227168273 227168311
    0x50103050c03132d050609010506030703030804170c0d0e0a050111030412110603090a0c0b07051c0905180a0b03070b030a0c05040e250905060403110307031205041508 73
    0xd55406000c0310030a051103031030f10140300c241300c00600f03030304900c100c60940004007040b4604009200322580104220001c00c659840c68501078501080600058071401e524000014168600c6c0300310783c42804420100c801d01031000100400100c1000ca10500c5103044075030028140d8810030203002c4000c80d540145142903d002c401c01c5142d1920541201c03100c00000b243c42d115a501c0d80a51302c500c05032009064861054034008100c0040c1d41c1050b01c005405004071008500001400791054856103c010b145c02d5002601b80d410301199440241d000f0f1107112070b082e90074124205640039152801c018000d2a030140c04041e2104032500800c1c11880050002032000b060b20b8200f006884201c0c00c1c10303490140c80e02103500b41d21000302c86816036800350b02d02000c06950031280d2061811903d01d0700030240c0b0f0518000900500c101d100181c04442d500ba5042859a0140410001035512086004520364030402c0070b02183c109109654101340d076966070020701800f8102d020310035007040e40c0902040d05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 227170773 1250 227169523 227169533
    0xc03200f0c0703020d0b040605090607050405010c020a0e010f05040b040b010c15060902030703061e05090117030d2a080f130f0f032106030f2d0804050103050c0313 72
    0x120041c01640380c418603500101513241c12007251070f907130f025a07400c0c103103031415081c10000c1c0e620180600c40954442d40800481c41e45c0304c0142c80507030780c0c00d1805032109003081c0001481d103802c94019060484000c000051030aa442e4840710840b00c0c140c60500104510200b00301c110f0300b506014a011540003155040000c1c901840f50112420705038000a00d643c4840900b82240c0048404401081d502c21050190360014014250f01c5403090301030040307544c01c1c140820403103401803260400780a40e01e0031005907401d040c02583d01072030100380c082083c0640103041140300590751071504d219106241450340ca552040030440c4c454a00031b02e440315261642c03030548501e0300f0580400c1c1d42040748910600d000641400307481c1d9055000c2d9984e80700040041d5911518184c2c0e103d20b07290000c3c9400310804c0040d001041c0340c881140c000f25140303503072202511000c87e040c0841da020030400070360030301540c10070000001800c1501d40a0381d08110f60365414402c40d62622080c1c480543c0c1d05084030781c1d600000c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 227172023 1250 227170773 227170777
    0xf06121602190818130e0a150e0d120207080c0d080705040b040b1305060c15011403060606250309091b0219030306050a060903140319030b0f0901090c03200f 69
    0x30101400800400c14080c0070a801c03a164680c91006c0b50704010484010700a0681000401c0007550b041041a10040e120704c1d130740c80c403044401c035040c0010044500315400725a416900300ba60042081c680e0790503001030b2103850710198140b26020441d03200120385210302c6002600c040d40e0504207901c2c84d0606114090816030030501c0c40941c07280381c920000c107840d00d4120103049020756003401070501c2c1140c2c124107200f5820580001e000000c1d5541a0401d56400180c00c2e80c10070b40039602c19681d00d07240000d0800d0010321007070400710503403245404002c2641c4040c3c24411100305404c2007003121510809154181c6010890000507071141c0d80341518800600171001c8501d102c1c0c20300007011070365100410b29811056104c000070440c0b01c507041082c0099180700b40c2c51140c40202035403500840c002d02d844e20100f03214044041580d02c000380c800e117032101c079004014247c004258003003a40e51780040303001800c0d035402c0c1c0000190400700d00d08460309580d18008070003081103001c2400d06220981080140d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 227173273 1250 227172023 227172067
    0xb0706090605150a1e05120c03010c03021602010c060e060103080705010e01051e072c0310020403020105160501180b06040c0306030305031f0e0108030406090816050f061216021908 79
    0x70102a400091b040d0b50f00d445000b91181c41c039020b0410314814408040c21900090740700400e05004102d1001c91605042010814641c242054410000281405030060502a00c40c6145100e01070011091060042c0030300343d454401c900134440485151800340c26520141c5010840300c512904d040710049042e894541c0c050b04510b8603000f80003032014102e1002145040c1c1c5045034003490380000031414103001ca00c046888000055103030615540c0000d00a1081681c82c4c0c0a900c00c08004804004081d04005000303242c031000460b8500c0c0c5824010205141035030740900c1246080341050142e030103801084c0840e074040d15094110303aa01000d1041810704030040e105800451000440c400c1c01d41440b0750b010348a15802152079a0901d41c0c042d055807156004030140b503015141495401e40040444400c0e0b90f8240d40000800302040041007690107140400c0b58904000e03400c00000030f100f62403082c0300d4117090307080b00c030b00d500050005507814501c40e01c050512141007000c4112140d49420000700 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 227174523 1250 227173273 227173319
    0x1030807020f030d09081005160c02030a120203090a090e120c0708070803040303080c03010806010b0f09040906051005010f020c090702070f06030203091519090206040b0706090605150a 81
    0x503442e14000a0404030118007020104440d21801e1006410801086a11100001080005040020300e0390000c100088108080100782402c441c2151014403c0070360541d40320010b07400055203000046e407a80c010981690041c40f00c2c200000d1182070a0007103450000d0010301904d02d0003004150b440303603607204a5041a50b0b00c00c8040c0080d83c10002c200c0f0000400c203500c007641c4c69605501e4002e050f45070140283e08100403e100500201401051182c1150b0080021650760f040715050307101035000c0c1c1c034121039116140c00f507020203100042c0c12143c130400e2642d00c62101c0b0f640f90700054500d1300d0301d07946070001079101d55010000750900b84522030b0480e1450040f2107403107640b4144c0241480c1240c1185000036004028002c202d48200b04c07016505820704203864030782c6041100054441342c2c4031455880107488018040564030303440119805020358005095503041f80e410544054800b8800031030381c031468540017441040400340c9903150310400800d01b42010b0300d00740e0140c0907103800e1040980 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 227175773 1250 227174523 227174539
    0x6030b0114030613021306120507110616120f0906060e190b0301021306050d051e16110d02011d0a020d14030f030708010501021504150e1204080a1709090103080702 72
    0x205c8500054034001f008607030340d014080f49650006506660717020b00900c084c050025a001e0300f40d400482c4a42c0e0004c82c0d5401c19008102241c01220b0f8a01000000040c2a2410304221701d1040d2541181180d0341c082c10080c400b644c2e40c0c031207081c440203044584030406c18001483d20940b8140d9002003001d024014000f600b00b040510040c1c00381c5100340c0c00310011407000204420b0100c4035004041d4000c1055800d161541c080c0c4446a01c9003c00910048902d41e5416003c0c40e00c9002d800c290b4405e0020208a80c5503001104010b8000d1441c3c14086e2004480c1d411003201019002855010069000d0548800315405584207420100d80c08500c00c0107000902081d4201e4040348017035407043c00a55500e95841d4076000001e403c0603541009007080003c4c82c804c01c00071548083c41c1080301c0d0003826000034104083e941190601f4503102c1804004100041c001510f580c0020305049000c5c000e00b01c080d1800080d1075030200c1e502c1403060054014091380010004180c100028000b1b139800901514 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 227177023 1250 227175773 227175787
    0x3020c010c110a0b121303090303050a020a06051602071e141c0609021c03080f1003020603090615090405070915030b1303020d020c061207051b0706030b011403061302 73
    0x143c25003215401c400302442d00480d42601c07000c01040070030740011201c20100d12070089918010007a0016010107028407400154403240c0501c01c0180d13801721a0880010450b50401c03c01d4203c1a0240f50b4150006208205010915070012909a003200001c18001540396240400041c9003600c06074060b0fa05c042d0b500710003985400710601e400b4605115036000a400403041c41081801c3d003890b03521014854013000c2d05070020381c00014242e0004a845101d10f110355589038541d1500c499900f00a41001011041c48000e4200090b9240201802100300140c43c8100045c840c1050044401a0460348000c008000309211580500f0318404ca02c4040b081c000c1e05c07a210060030110550300c400345502100c101c1d034181a41030014a0719002d680c03029091000705040022083c1c024010000d08000141c4086003403680500100d81c80e4400c001c281c000c40b20f861004198440009200300404079052100c01100356109a1504100868640d502e5046489030024050266103030103031042c10329400c00c407032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 227178273 1250 227177023 227177029
    0xe1527010320041e05031b1302070803040204050112021503040302030d06080c01030b03071d06030f0a03050301080d08100605031b0c030c1e06012718050d02060403020c010c11 77
    0x7100407031410b51075442d9110720740b0350020030304031304c0d050001c880090709541030003651317000f060005a403a41d115031048961510300c00203c00030103810f8403039402440015500b04128582c0040c601c00d5008440410480e80e036128174100c0d01480810007036002c0c140141038101c0201c90000746401501a2044071705020510100d1000c03910355801c64020b55111b20072005156a0500a55591142c150081d20390140341200d441000901d8810342d6805108200005056807010008240f0241c2c450084680c11031007400c02401951013030007106120b0050000c00c20401c1e000b1503825000d11002100c5408d81441c111080b144d0740c0019140c07907050305805101c1581030b0003a501415000070003002442e503031200d001d032581c5010041d0130100b8403541050103001145001044d5141158004401c0020480300c1401860f1403200241540b50001e2914154058904000c1500580d40780305100701d8403000c0744603406982c3da035003c0702e000b0010707030040200c815039520802010601d00c0c820240c00880104035000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 227179523 1250 227178273 227178311
    0x7080705011104051e1003020a0507060507171008030304030c020d14010509010e01090c0306021c020412030822030e01050f04082b17070516030e15270103 68
    0x10301c4514a00100e002d01aa14084402c0740240c81c00c3d0440c1c205c5080040007003480181c01b4501c460a040e408226000e06130300a1044602c1d4544c01036040241d0b00c1d103500007606007041c0c400c40c08518074904e80026a8041d80440f43c400340c0f24401c00860940da502c1c2d80c11124801d00780e0040b42c00600445081000603036601030038182c5010348002040310720702000d003e821a6a50b44e10610143e04003044c201c046800c5400000540303420038401b40e5152020b050b812588080d440808102074070001d40010120490075510352418440d5991b41150385401224041c88a03002c18249800418011501e00182c00384100c0000304106062050400070004d02010301d035001a841240315400c1008014400020005001280408981400410902d07844010140d5a0100000e6500c005502c0400c2d0b0700f40c059001d40b001e010072441d12002d810030f02d20b4000c1c51401100c4846008401400000040840302e81c142c0f40842c00700c44d840c0c25420440300d002d8000b004548503040c141b65440c40d0f0854442c800000e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 227180773 1250 227179523 227179541
    0x40f090b040609021f05030109090516090b03100501062705040c08090d1103040b18060d09122a080d0203010f150f0503431202070807080708070501 65
    0x1c0c0000f507400e002c0c014080098450401d0203080c0501c403114003004c94000085d07a0648501c4140028030b82964505a481d10102e403007840c002000da4200040c8500e06608441e2442c0c005074252030761980c0606404068900a018000220340f10324022a50b102e01d2103661450070404c20f000708503880c1e49070085001c950401e042100014044010041210810030185580000b00c0c9016111995004041034480c0030741c1c02a20007149001610954103940d1030400034510100800309586e880e00c1c8540800242028001120032011050761743c04414003e000341e08190074440e80030001c0c50307203142e0340307070085007414030201c0300c1240a02c43d400c582242803000d18041c0030081400e889043c1031054032005903000c040c00e8010040d400e000e541c60700d5880019203170000c4010041d235500c044203135243c0041c1c0601d44165038402e1840b0401706042045020145840403658550030074903981240a1010380c401c2000280009104000001c0001e5842d4000e00e03026005e4000329052110f203a50307641c00e4954401c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 227182023 1250 227180773 227180783
    0x203070318030209090d02070605090d0303181b08010b0d02010c0803040516090203010806060a0f09201603080108011b0807120e0607031d0307080901091205030304030807030b01080106260a0203013002040f090b04 93
    0x190c280715000c82445200115102248c3c11140001154002440704c08200300040111a01102040400004019031030f0680c03200c0b40b541a12030b407119609030003504244640800c9218900101c1c0140c186001080305407070100d20a100c03c6400c014044002d0404070440c5100018a608804a0139040c035010740703290340d4101f0103c104003849080c000c051b04d0040e003002e9416454607401e51000003c000c2d04402d0580903040c80103055035010001d46032482c100c40045038850074146075540e96440451528032a9100d601d0070001e002c10682440114101c8440c090241c3c2c3c010405030012600401c0a451041c2d01407504041e01525240c0d00c031056007200c0c0c1c1c101c0e1640c2c07011042c030080641001d1140d03403022031072808121001109000801102301803041c071080c80001031344016060355001070303d80020b0707549440d00c002d814402c82d8034000398030034031030400c00c0072000350500001811b0b442d0115103030001c511038202a00058081000034000e030854039000564900c80c0500048120418910590080b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 227183273 1250 227182023 227182073
    0x41a0717011503061508060d080c0102220602030702150d062714040503090904110402070b010e01050d0b07030b04090210020c04060503030a0203070318030209090d02070605090d030318 81
    0x5250043d082c0d130565003003c186002880b51000c5515440f4299940c001c5084071017500403001c501708901e642c841c0c10b4800b01294000280c1c5403c0a030900240c101c42050401004c80c0c1c0e50b40c4000898882c000d5002c001e5100000e401d4000070841d071040580440e100380d41c00025402e03620070007200480e00c8001041e102601c4100e000c200400036110742008100344606c65181e901c0c01b59200d039100d101e6060800c0c403568480011901f8031030036002d00342124501030300456030390a0074102401110000d209408074075854000205150404483c1d20001a5010742843d0007511079030b00c01d6000c2e0024900142c1c100e6a105480d1025a9404061400a0300e00c1d40180c009000c0030414041030710040d4002c0c60190380304105007076450742d0004c11252900d8040c41d14441242404080249004295201035840b00650090111101d4041604560ba500c0d035000c58150319074500d0f040e00c1a001d404d59050b030014203000f100c000709020b0340100c00f40c40050302c800c03202d00c901030b80c540e05006445c0340c00081c5aa00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 227184523 1250 227183273 227183309
    0x23280510051c0c05040605010c08130306051e0109090305120c2704050a0b060901030b060d060312110d0207030f0615170c0306040503040b1e0a020c18041a071701 71
    0x1401d00c2c5000508401c5e103080c07010741c0c00c0c500041c0030165240c800400d45040020710620383e841d45035100d005503521800030311032070400401102c0140520000f450b5145090000055606064072401e080241d0544905041c80b4420114950b00c4200070004a0210810000ba04a8600d51a50501d9401414400000c6840300747c040c402101d8006000307003501d52801e1000509990b031038050720500007003440c0100d0840304206c04901240030f002c0c109244182020310203c100100a4248491036032140d8038240d40c2403c1d60001c8e603440b801900c440016807ca00e0040c40420681410f00000c079001c0c540100b03640b01c0701d076101a000c18030741d1b1204003010800e0a14061401c1d05010221280404900400060401c0c2c2c484548a00c00d030710801560040004010030743c1c00088208458441d240c00540b500d45120760406500c0c1c1c4d00140c021031290849031b085860342072840d00001d0103280c00c0640302012403100480d480084001400f40d03001d00408801941540344072440d02030191180010300003410803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 227185773 1250 227184523 227184533
    0x5030a0807030509060906150105040b040e0f0606040f090207030e10081506071e0201030e060a05040c05100f0305190603050f070602071212050d23280510051c 70
    0x1401801c40c490b01c5c1c000c007040c0300345200001086174014042d0040541c001d4030910043c0c2c0e05206591041815040201e030020340341c81d8034910b60b4481c0604585003c103564480081002d1881f0358010409120a80481807204000580c0a401c01c0c83c42800c140360f1440324400014801c51401c444e10307000948a40411a2260140b0034840e0014801d60f505428101e1a5844005000001d00030302008118484601c09582c801e4009100e025448001d0b6030090030240c01c104040c050440c1d043c0d13107001c00e4003070003d00c81c1001c0341802e00c928100d40d99501c200e4034418046010b020084c01c001c2242d00c40840d032041c022201c0c41031800441c800c100628440460321080ba0411a0036400030f0190740010004001d9458880c29499038103034000c00f1048c55035589078095a25024115000d20014139052099000001e00d841f03031140034281c050b52100507a01d0340c1c10b00520620700e46242344220805c510b0390b10941515041250440107050202400e540c445000c51008014108078031400c28041481c101481 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 227187023 1250 227185773 227185781
    0x9050106090b010504052214090c01020304060807050901033206120a0215130902041e08250308030a020306100311030c030405030c0601060513053a05030a080703 71
    0x1c40c40074400c0480c00800a44075001e280300c0e590254143e409550300c681049000340440c1300e200700f0200041201e051115084400803140e1940e180329040303c04100350300001c1940c040b41c06603603030780010b0f5407010030442d02c64101c12441b40c18552103450035841c9454582c440740c0d6440d94540300f01c1d0304884440000b0210400604124003815010740301e030b42d80f10804202c4100349a01600c5c4c0916100362100d880050344280c5000b40c40c1c0b01040310001c29000c542d40c000300112a048510601c08400311004031007400f8292042c1521740d44481c1c82148207404140c0d54904a1a54045420740a03940c1e403101e250031382c02100c0e22079035194000100700e6280341500008002500d2031030304120078040c0c119419042e02c000780c0941d4120002000040c10030104100301c480014041d425110696900c0a015240c0c3d040416041d0b8403007403040c0d0100709820446150003d10300368950381758684441600c10844014020808620b101d4500c40e0140410420001001c007400240d42e405203a1030090401801c071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 227188273 1250 227187023 227187029
    0x100b10050306090112021f09180e0c010e061c0207020a1a0304030c1e111315090902040209030706050913090b04140c0d08190503010b0f09010c0606030609050106 71
    0x200c1010700500416444205507507054a00f40742c1d444650001c0c9000161421040400d035103a000041e2600c43c20803a071280080e01161106400300c000d803170100d98254152104041c030000d0503441078000c40d08c0d6600c201d10300ca05000001d8105441d00c114080c1c0c142e280e0190050864000d03400250440440c20008102001801304440c3d070b0030448400d4014002030710000c1c03c00380402606200041c2070100340c851601152049035407958902103180780020505003102c0780c0c03c0c8103166000098907184518015040c000c92502d000c240c0e0941800030400c001d1400c250241e80095003407080764400d8804100c02c101400701504da0366140c5a01c10108440300a52055200699052503914800581c0c45400389800c40d03404060380f0a901d8030f0540f034030318010500c0c0529a01c4000707001d1510a010141c00248101d28650140402c111101d56080d1190320080c03107200b0b8840f034204100c0d030035001c0880141121100526000c00e0804140d241d142c03d403046c035002030f1354983e42d0b8000c100800100f44200001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 227189523 1250 227188273 227188277
    0xf050102030c03040608041a1e0c0c1905010e03041211030a030c02040203041b0b070c12030e130b060d0b010e040902150d020408010e011b08011212050c100b10 70
    0x18181404003016100d00480c4175010034025924007107800c2080d03c01526114005465400d000c601c0d00082a540c010f20a500880c07040a040c3e010611003a814012108580f145000410030b0307082c038a001e40c9101c14840010f854a550b030743c90030301124409100400081c401c10000d049078062504100d05910720102105220750300c0b190920000035040040741070b20540499005031250380e00d051040c07603034001030400d000d150490203020982600350400b411060b0301529041d004076407250210400c00e0b600c1c00014002c03680d05030042c17095103020580c030070200004c1400481d41ca8500780c0030582c036410007002182c0c41900d0f01495405541c1c001c20040000320f04403414400f0600903004210071500380705043c06901c9000910081c00880e540480380200002c1e070080002e8044551214020114040103024142c075101c0c5400d0340307622818100b81600d500c014002c01810f019580e40c840c0010b020f204201340300c02400388000564003403003112a40103000c040410b040d4901d00401052030054880402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 227190773 1250 227189523 227189527
    0x60902030d0c05060a050c090a03030206150901031e03050c07031101030c080609061e03030f191706060a030e0316050706030c0903120207050d0c0807051c0f080c07030c0f05010203 79
    0x403e000003542134000390011000140394640d04003e00f8140f1a11034400d804c801c0d009400010075070f0004540d4454010307492034080c010048420483e007118284006846a0000c2d40c1400d03400c0030104106000c0f0b031080c1441841d110040ca900350a2a159a0003950100d025040c0083c5558060180c0325110840b8544008d0701d10300140041c59042c4054019405050b0442181903115801c1144004640c0000e0440341ca65003203040f41c071003980c0300c040b15090305200c8440e40120207010300c00c404981407082e0700e520f1155a5a400740300d01d54100c502d0610406885840c5260061000d00080c15113140c0c1900c84410300015003001494007416502460402d4900105200e4403580915590182e035032110b409104c560150100300d2030321181ea00203e0f40b08009150340700810030f11034008030071a40da1105603071800703954400b0009102440c0c45e00c40c000320310b0b052810001501e03003040b1840c068818640301d1f040c07003640040a864803411390070450724500081c900b8004e81c1d4042ca4800c0c0140740901c0154 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 227192023 1250 227190773 227190797
    0x819020414010e1611010e060402040b1507060e071206090506060111070603020d0e190b070305070e0603060d120201150f06020a15110d020301090f0506060a200307060902030d 77
    0x81074801c0080140d6108500d0300903400c0424812104170b01e4100c001c000911440040308903c03603d40c1340aa500b2446a4030707200d107100302e50910f42640503550b082006010306051183d101d61001d42035201402071540600c900200b18017501c411421000c900500e4001174141061900c1c07031038600080d240605201003803c0034100348500040000c19a02d4625000d03803107012840700403000d0040c0540031141801550912009514248034140c810340c0175030b501070f00540305e1346c90a800b258810350745000010703800068100c840c140301d030083d6000b20020f014102c0c1d03110307d43c0341c81e9500c055405c0000c00603515100350328040240441601d01400e180c1e0000740006103410b1740a541d0b0500c41000604079000100182003500c80c0b503110401000280803c260f55036000d00b050b000030340c401d0080b038003828031f405c8010310712210f184946842164050401031409981420070788012150800001190100d010045003d400034000ba0807800d2080c18042400a0700784109418880003281d00030810041d9901741c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 227193273 1250 227192023 227192039
    0x90a0902100e12071205100c1b140703030e040609021204110102070e0c1c1a0108150a141002060708010905060d021009050910050108040602090604081902041401 71
    0x90740080141c10241e091914003000710b0090101c0c180b10503114020b03620000f40d00c60f040c40c0540c00007072044041e203118400c54008030040b60100c8542c80001131030240162049000741d503031440f801d0700440d041030005801c8146030b4500186a08103c00045c2c0c1181d101e60b01d400d10380102009812010019814660454455840c0308001071000d00200c62080220340140d000b0b0003c40050f2015915000952420790724004203540103d155120f40d002caa01913a004041d9485800710b42e905400d040c07460321210900444481c030019020702080410703086014410f5842143d810300805000c851024500014010400080c0c145014101550000810040030990012525065030080300000031181c40d8000400c0c0c0d583d4031384170000c0d040807a90b00f0301180190001c030303107008890702120840302699038003074513415002c1c2c1e5114141c00300c2c0ca80004600081c10f1a00500000d80003e0b0607907041c039a4500b02d06150420001405146803c4920a40198203150040c5d0884101d110f100a00b554540703806 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 227194523 1250 227193273 227193289
    0x609030314030a0b1203090f010f081918060b13230703060b07030e0a0803160b1911190804020a05060c010f020d0c0e150301170a06050703050402090a0902 68
    0x11003844101c008009406031a56511840c540c400142181003101002101c0a0b9039500c1801134910956680d40e4401296210300c9586483c01c06941d20300304661281c0035070394070820780400b000c0c00c45a1030b00903000d0a1b400c140c0c12185518003401d008103103c12030806008400000c20004008103003000e4000e02c64079680f2400c00b1350b1020f42e40c01c2481303680c0e03031034001c80040825401031220100e002503c281456804050344c03c486100b202c040c0300303260f51904403039564801c1c1120704110303c0328581400e0104000809081d803224180b0a042080341c2441e00c2c4200311181015070740e010100c0400c649844450400030903000b2071a9080046084c14581c00054806605200b1507209090002d1321080b03c020a40000b400200c00600075900d8a51442070701000d0700c0b14003c5580040c010b040040201e01e00300c800d06140b6001c05040030300e16424140c0402d48864007402858181c440c580d50f80c4005075243c4a800c0c8a81c5260f0b80000781402c00380b04000b003010028100c2c1d0701907420400054056958035030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 227195773 1250 227194523 227194547
    0xa0908120901120908070317060306010e390316020604150e0a060e01020c0f03180118030b1f060309030f180819020411030112030503040206040e1602010606090303 72
    0x2c012400900040fa51009061071100090589102003214003c040c0c10403184110614036a40701001075403800185552030100b4802ea00d071141007180413883c140c00740301c0c030703007045101274921082404182c6050b00c00c6000355654005032150000200107141e0108280750303281c0011703440a480c2500340f584400409018010310014441e5903901c2c41503803003a040202e00c0565900c94802d214002810200380d000f5008080c0308022030080700c02509039060301000300d0340e440c045021709250314034500d40111080d040b6440c604d80a81e0074450044040b801d1860380c18030502c1100241c2031050181501d0f0440320b1125800700061608000a61000a400681c40e491000c038502d40380d084095003c0b12110485071552004409010b41e6404060485582282044442c0252800d202401e00e1085c00c0b040c52009110f400c8200d07001d000f280c000248070710021500503000520050810341c88a02d145041c42c000d50f40343d0721500c040d11202004e2502030040f00c00030506801c0400350980386032030145c001c0c80c0d049 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 227197023 1250 227195773 227195777
    0x271305060601200f010e070801020702091801060819020a06210f0b0d0b06030124030f030e0406170c01030204080304051201020d0e030d0b030616080a0e060702030a0908120901 77
    0x30045608403c6071207603008100c031184007219510f44009510170700800e401c3d2a25850360041e01008a0100c0d0140210303604941c1c081c0a41c4115580c400f50750704a8002400404580e540311700e40055000310810038131662001811f07031301c042000244100b10501d00254003800500107010511440f2590000e100c051807025104042178110100103003100a040b4000321035406125010f07403030148001400940d00c20702e015070003000b400702d000007480000740741d0003803030311071000e00c16000d2001501c1d0300e40f2090a40d100b4242400400d00c0c070070004043d91400c0d0000340a024070200c5058003640204510034080301e0038202140780c2070800228544138803c6000d142c0c01100c41014810400c1400d60403500810500b210401450341e54004090301e0f68007a150f846010707401d1043c5405d141c0340105409000d0701d881141c0c2240c41c00403150640301c400c2c00902800442e669000e85801008090000500c905529400785070350300303006c00014110903800d80282c001035000ca4081030014403070408640e01c0150034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 227198273 1250 227197023 227197037
    0x1180b01031a01033306090b0f16030311040b030a1b080105100915030c0f030b0a090f02160b01051314130804091401031104050f0403030b030705271305060601 70
    0x12a07108a1751407040755103000001111101100312030741000185ca0301591141c0f522540c0348205983d074013611030a030341030200c204405400c03040c800000082c101d05c00e050100f5483c1401030000700c141c00552040401c100000104100c4e07441034071030140c0d5072090044030404201c00c83d20061020005000c0c0c507008801d21403900c2c1d142e034004c0f0759040046c0003c141020b40310700301d03d01c02006445034038168004908098110040f8038024042c04a980c08058103a95040349000420301c003401e40106420109a401c02c0740d0024036070440007800b820b5028003515071940d4900020720031002414050010101c1c41d040d144c9418240614100e5080401c0d8004800c00103054140418079102d1507001031462442c04045a5400e0a810502ca048038014003101420008101c1840255001102d0919004014400140009010354045403003a10007a0803206555106c502240d00071b0f02c0c1d1381a4060390b9042c8001e003412a121010400e52000c2d21035582d0102d0802642c403142d07641d0f4060600c606000d01c1c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 227199523 1250 227198273 227198291
    0xb070c05120312090106030204140c070305030c04180903090f0308090d031724060f0a120609090b01030b16050d0506010c0b0c0705060f1003060209060403080301180b01031a0103 78
    0x420000c0c1d034030b445000041c3c0196420b0100e00f080c02044248800c0b4010385c1004188002d0031442c200f43da11803103100c5400f9203071685a5a007200c00380d0004208210f00709050101007820466461710104801204900250707840035030501a003014a95880b80c502e0104c0307030000348001101030007903a10b031180994080c0c840d03154038641a50f40da91105164550494042c0c100421882c0d0110030f05003441512034407440c1880301400340440c0e881000c0754141100410091030481a104000285803828080c80c001559901c4505400030b549480301d00f0386684102000603c2400280360400341c01542000181100780c4141c24081d142d8014160840300c0c00740e503540083c10903401080001d0009620916080b064900f024201c0340c6a003001c041510f50344950b800185c8010358160043c0c0c00783e40301409031021186541c1c1e40d64041c2d4045070340207410880a01000002400f480081c5010f440a2290451900401c107841c20803142d0000752141094100100003022080d4049200306400c8203203000301e0f10b18a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 227200773 1250 227199523 227199559
    0x10501120b0d020405241503010e070c050607030c0e040212042a1715061e03010621050d0203070b06010c060209030a0318050108060a06050c120c0c04060b070c05 71
    0x181d11100a50080d00b40810404040c1c0c0c2400801b1a2a035a1803080d4181d42002042c04914004880d818020240400c010b01080d0740c05d0310388030790080003843e080303414075503030754456080003c1034900e400401d460700d01c19109503070040300301004054140c408600340301c842410b1103040e00c070140000e0440c0032142860100b103901c1c600c000507514021940001525914900e01404a40030700c804001340c000e60b140805888010303a01c19019100c01401680a8803d1403204040821080c540c541e06660718600001da1240300c03a1a46920041d82e02042029006414182d044c403440c803142c5000c5410800406d000503600f03e8160b50055000e19000003444180d103803680013446110000d9516100340d0035000100340d409260504030144508000200039a924015101e08a098030031f00d90208090000340000c500ca040a1f040c400c2080b401c95840010404000c2e074154440d11080d0159040500800c102d070030140107100003840d080c0a42407901d503449e240d503504e850842c02101d10904000b803c0c50a202 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 227202023 1250 227200773 227200789
    0x5010e0d050a11010c051615080603150903070c0e06090f01062c040f0b04060909150221010303050d1406010f030e0c0a12050105010801110304060902041808070606080105010501120b 80
    0x10740e1210487e464582c0b002c02e41e1001612501c54085244640d002e02c942862164400d5805458050000c1180d4036045004124070f410080885a0700c2c841801044003207803402d9410001000c01c89510038a5091407410321055050041c44074440208240041040c25400325050201c0104038004810071044008004024601214030301c1c1d00c90305280380c8054410003075100341541c03602110204039003035640300e02809545601030090001184841650341361545038009241d403c4c58070b0018240507240509407140c4003401e0b042900080ca010545501c415004c1c802d201006024001000003450180002065040c1d0341d000381040540318a413031884103008001498410100070300440d5000d407200817822105a81351410307106582402c00010780c206041c85078011100201261501d0340c2e8494969070040c104114040340c200f07a44411114400207406c0d07401c209140700307040e11660340610b818400c043d80e81c1ca42000041c1d07450700340100616070300083d8564181311100c03400705100c98480000b45080c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 227203273 1250 227202023 227202047
    0x1021c020c0901080c040b100212160203300403020f0f03120a030c0212041a03181c08090705010219051c020102071b23040e1002030105010e0d050a1101 67
    0x8400c1c0c560010444ca00040780c0b4071829442940c00b0802c40c441101082141055401c162001d1381000c400b1607c0c00c3c02ca100102900000d9985121400c4001da01103407038506011501d0030f1911403030766002e0080c2500281d92034012490f400050601d401c5800040e0260401a069485400071060b070300002e071024407c511641200300c0410b81c4426032840050007a2100808600040c003a00c4204041d4400000c1a1001e64680401c008140c041c0351042081d181e00140c290041c5038482c13480c0c40782005041220155041100c001455244065040070b4078100014004403141e41040206010991f030009008500c80c80b80141819401c110782003441c02c0c202e1403810032103103094881c2d00328502c940540040003101c2c0301c0c7d240710321a60610500141c500d00ca9000d24142c0005000240c0d594480c07400f0004040080200000b411903031900c51a4505000e2150018280d41c010004003c3d030368111001524000382074900040300141d594a507516084c102400a0007054860902c00050b4820303007a600340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 227204523 1250 227203273 227203279
    0xf030906100b12041e0b100e01030c0b0c0a080a02161401230904050411091e1308090306070c0c0501050c1509010b0a080615010e0f090703020904060e160e01021c020c 73
    0x40c45d02c060074021301c0b404013200c4031046110030550000c0d540319a140864122600185141d01190600f048222a9402800404140d02c0f40040301e01c00b0440c194020a0040e006800801c2602a104046181860640c0c480c029103070420185600d0ba1340c01150b490209074400c0b01c448022000c680d482c001a0003400c4280e9046490902000100004111240380b84001200d00300465a104c114550011144501b46121040c440e0086031000803844c200c07035102440380d01c04c1c500b4900b03040082407a0103021100a40001c54004100051041c4c411918000d0300e002e01e8020300d40301e490740c91207580350700b41565011404500000201d45d0b4500794055041140010000d005650b9510501650381a060f20022504581070b88401c0d070a40c061441803040300c130003070036000c280c9024030100034010900810007401e050f02048000701c141d0350740c46160b0182096020142040c00d20003003d0302c0c5401d500070380350180031240e203c1060740d07a00001d1141c96094203002c1032080c18483d41c0200e0401d9011080f40390 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 227205773 1250 227204523 227204573
    0x120612010905031210080a170409020f0d0c03020903030f13080303070f030501140a0512100203090f010e011103010b03070c05010c050d0e0d1e140f030906100b1204 72
    0x1040400310040c07945441151403034031304d80c59940c0e803016680c2003442594060380c401250304001409000e80b800e03210303582901e07440c245542d07054110180d80c40703d80c500d9407084000504040d121001c4c0710307405030007a2518003107042c03202c0480403941e40d114450031442c0183c0301141b0000074017101b51031080601402c2081ea81c82c1c0c04c0c91100a001500050181d030f011904040010501e04191601038075100300041204007264034280074086449110244a8200c0c00303442140c14040b01c403800154000c426a40041c1541107200d0300c0b103403c64040c121400b4699050109100c240c202c0d0409580c150750114151603aa511021410b4441d220a0b8000900d00d50821860b2800c0340e82040107495510346801040c1b141c08600c10505480e00503400154010880c891481e04040640342180d07003a00c005810081040080c1503041c6080350001051044400d40c00000c000039a8810702009420200380d04582da0242d007800140240c50094201c0c42090750107100024080c040c00e01592000d080407002103003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 227207023 1250 227205773 227205791
    0x70c0906030809090f0903072a0f1a04050d03050a020a0b040f0c141f0318050a050f03030919110405130519050303060d0503040b0c060709050a0b12061201 68
    0x107603243c10802140d0300c6418450f00103004a414055070038800c0c0ca000b000f561410380c49984031482110b041c0d40f642e1840c0c1503075990008904403a0003600140c91039105100305545000740560340c01100103400781b1100001e10081005031280c00840003403d07894100741e81c80304882e800407480e060b0b5550010f803550410006110074800000c80c0b03180398034010308483e0744503500d501100d81c603944050341854000e5403403244410000307201800109400f0301c514000c1030048000324104030a1528000c01d85040d0015020b000401100b007002801d5a000c0c080a541145010322280742c840c1c1001c400412400d59000052080140c401c084080c041030041080060b410040440c21540040310301c110f500788500e040c01404100c64060038482c0c254058000c1d40b86566038024403c03a8110041d0442c1d00344810b02010808001c55400f5220f05000700c0c000701000d2070140380080010705d00e40d1245005104a60041c0050520141190f030b0005101b416a03071181c0366240843c40921a0f02e01c0c00815520b4281c4030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 227208273 1250 227207023 227207033
    0x110d02180c1e07030212040e06010c02030106180b0907020d02100905120a170708150409080903031204030201051e01060807020a060e01060915211e0b0105010f080c0906070c090603 79
    0x107848064042c0d070859000f031451b519081d1562007140110319810040b580040c03d81d610030410452118405030022034440ea230340d6a02c2520500c1c1c652b070317001d0b06615001c010046003440602ca981c8003a42d41700410706401207283c0a904c03405100071034542c42d52502c00d44004e001d004c010483c000170900b4070081c0e448034041d400810070619044800384866010b00487c803405d1088111a00940308210854012490711003000010044464101d5000b00140f25110141d074003800588003d00c01d40c40e0185152404d454001e0854000400c41100f00000305507404c100c000d00d0884905541d401d0070300300240c0e01c131744906030300e030960f01c1000800d65400d10b0707088400404190801c0b0704891100406011081041c20268007100031401040241e0000c0140044092010490401310728050428144541458235594180c1c3d0035540095a0080c00800100501c1d40e10400500f6400c1d00380c54046650b007041c5c442c07016148201d6601d030f4070507000802c1240500499002080080032905801c0051507628640 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 227209523 1250 227208273 227208277
    0x216030507051b01020d0509030a0c0f03020a09060305030a1125090f05190b0a030c08010606080a23060112061e0b07030509060703050405040e0a110d02180c1e 70
    0x8507810f00070145140404020504032a508107016006040c5c0d80701c0c0050304443d2500100d55041d4144180182301000c500e04058140c041c21706034a0a051160560042c04810741003503100402d030306d11b030490800220b200071042e1760f1035504619003403000d0007805004a16101d501c092905c02641900d003160341d0424001f5042007124802d400a02101c44601540021600c003114005040090041354050900c20f40d030140d050600700525000d00103403a42c6440459524907001880140e640d00030900586810055441c1d02c00300507001882465003c2510000800004001a00c40c40120001c01c0b00c070380c050903203c44e6081081408110306941c50012000d41c2660007040340c1d800c112513601250006410088491168258139081c3c6070020260902202ea0701402081e41005014040400d0039900c41c0151484945800d0082c121301030b05081c00d0034070201e03d00c410362050300c4e60010240180c440c0703826058501400d44c90b40c1050740e202c040e11a114450024040301ea032043d0501080030904902c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 227210773 1250 227209523 227209537
    0x30a09200102011b0c0f0302120304030c1b061d031c0305040611120c030a0f140f0a02090f01030209040f0905160504020703080f42040504020108061302160305 70
    0x2000340130480c2008114611002d044140301e00240c0500346000100746680c0000960380d21a1040702d00c40701803001c4080150700700f614200c0004115010310030510aa060f40e40c46c5d848240c2c4010f00d0554034196016000301148224140800c201c1c0708600b8040d0b5003405507043c00c010183c050b51002c910010700030000c00d000c9404491041c0303407a1005541001405c00e0314000300500d1403a614030307190802906195003000f0900d15a254607000c03078655a0148e40201c05480d0300d200c030402058102144000f03401070004050b0050745105001207101662041001e405101e0b0a08006954241c0c10012601810300462500724140c1883e01803810800c0000e0003207842c000300b800f6a04110784440c200800c0c0e10034410081c00082c1041e010502d050882e136005034100c52041d0441300744490003d0800301c03e0100341c840c4d10802100c0c910310340c0c0718600c00441c402e0350b41c8112030420062034151300181c0002e10141026000d010990140c44003a040da034116000109400461103000c621850000e14590007a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 227212023 1250 227210773 227210777
    0xb04051c0f02030d03230405060613110f03070f0e011407030315080c1e060304060c0e090c0a02070f08061303050d051005010e04020c150901020d0e0703020f09010605070602030a092001 81
    0x41e0386103a08010940035501443d42311014091075180c1d0f41c100300300c82c0e0705444c0a00d0391903502d4003090342581001740140340c2607001507607940c1c0302d00e03180d2000362003410814404002d00c000344c141c8880d260303440709a09086041c0860100e07104c000d1814201d0082035520099036160681401c00702c0d910070300140c02c004c00001103407515001a61300352903054808030f280c04150848410b001150004541d50030595501304246800480c5000560010f450154240c0b41a04100c000080e031900c1c803941400802d01800c802c2840010b1f02c0d2800041640c2c400300245100c1c18401030350507074000c040c03041040720f040d980e60b19011f005600708001500300880251041c140420070111000f82c560800d8003c1d00e88241000700a000314610098512030f11642c01004060702d0356081010343e003051482d01c115070507600c0d040003c0c840c150030f40c410320003045000303100b152003102014010000ca5074080e0489d88001d905c401702507140d407240c03400c0030080c1c401001c000380705840d13068264100040c00103411180c0c000076 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 227213273 1250 227212023 227212061
    0xf17091518061303020420030403090314030c070902091c03090602100504080a0305090c0418051204030b01121a070e010909051b090f0a060206100b04051c0f02030d03 73
    0x404010040c07103041d0070f111400840140802c0035261940c0f120060340402c2500007600240c0e249007610940c8100d41c1100400c01402c410710902100420440380040880003d41c80c140030040d405944095074815100300756000100951180c446182c10810405e4400420110210902d07025148143c03074043c90b00140706610180050403010f008032030040350442041450000c05000840282600a110382214030480c001c81100703403154894803000b50401400c2622555443c5021414008440c120304103040060200744040340744902014112101c500c0d803108000454a820300d001d201c00d03040c0004c0655050100710007560030084e83c1d02014070036a2040046515280c09000300e4506071703150980c010380c4175050084203006500400e81000010316003003150305010000b0b84107a00c10780100b030068002c24280035207085800f1490340a4001c00a445090504003070108e44451601210000c0e107a08520034503050100b80b840f0402112380240c140d4003404000d06014003e0003200440100003111 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 227214523 1250 227213273 227213317
    0x412020609120d151d07051905090102011509060807080c06191707050a0e0d050d030b0a09020309031b0f12030403051902070f0e060906010302030631060e040f170915 73
    0x100c2d604480200b211440201c08c80a0340c00d00884d516005010441e056650b5580c1c030034091500e1100e074a00a140e54900412803d040151040c2802c0d25a403051000b90311540004a8a07901d001c152129a60500343c50100c03844800c60840700c0345a090b14408503903114106004416a00000030405240c85444c0c400e0302c900c400040c000c040030040e20141094005440140742c46201c1d4015905640004124101960b100c1803d04100c0e03006461600c0f0315440090104618078040c00c0700c6e0168030340791010b001401c4007145072a40300c0300b0381c0d511103185450000c001403c142c010001d8805039201603101014108081001030340d111450302070955180d0101030000f80c0c081c0c4005030107109000c003400c10350040e2078420056010390005812180d0140c1c501402000c41034810304210701b00c40d04540343c43d06050103000c0c0700040b01d1454002258641d09881000080b5140c800c1c9117805a90000031030105100c650f42030f64060044401e03d56000c4003045e503402d01e000411001d404d003400c0c0d00c2d01921240a03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 227215773 1250 227214523 227214527
    0x140d08180103061403100c05040302060c0d0e01050c0c01080c0f031806011a1603031103040c050405010b0a0815030f0d020307050607020106060915020109020d06050412020609120d151d07 82
    0x7100c034804c0c5e916601a801440c0440c040c1d41200410045505000382071a031240d0005070b40f0b41016003030507100e62103500d040046540c40441302d02c01560a003403803032600808103009915240c4807544641404031200100b1a00e1241e241207490305002d22800765183c3c03c11382d52144040600c4d00303102000b803142e000086540180c1c850000720000c8103104080c40c01c0004034040a010545e0b0009a042c507036160020204c0c407410070300441c49180f0a40450943c43d003820100801c41b003040e00b10303078010342051007032200080c0c020b143c054005448070b0740f03001d800f4078600000703103040d10490901c1002d0050319010340240783c00001901045104006035900340e51050401c0303003250220300ca18400a00749140411445541d0f036490400f49003a0310000c9800d2001d900400c440c0402c86608a402d02d5880d001c00040c48a112000894204248003510040c00c10b008130540d0344070340019403654200d000501901104850380042122108402c0c500001542d4003948030700703021002610700d1500c000782c0c00214058 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 227217023 1250 227215773 227215799
    0xf1806071101030c0f050406030b0a08070f080609070302090f132103110703090b0d090b070503070f02011e020d0e07030b060306070804020603040f0503090909010c02070b040f140d0818010306 84
    0x883c1c0c0c6e80c48509041ca03143c001c80c00750522482c0184c1141c90048007180c40d0609100e024007510032101d1503103006261629241c5801e1006050042c1c1c0d8005a07030900050307030b4580302d043c0c10030461031064420351100b40200c4840e040040006081502c0b8151403082984c103680d0f40315034014261000c000000e4512400010342c8502c078401000129008014441d646c880000741801100a090024405c000c5a8819200010699180300840e02c04420000f030658030800c9410080c9040c4020302c0b00c0c8031580480000000030400c01c4170150303000b29009085c082d65034401e01010391613100311045141e490426035844902621018000d00944000480302401881031030b019560180215145503220f4540c440460030644003111680020007440e00e00342d070b443e0000340c0103011200000803c4c40d1742c048044d00d0400564081809500701340001c2081c180c496407004101c802441c2008954002e1a0016055400d0000300030300004011030803c1c11070400044006018800303880c1040b80031b48408500e40b1607 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 227218273 1250 227217023 227217047
    0x1050a05040903020f0115031101051216111504030801080d020304031e050d0e010906090819050c090a020c01060b09210f19060f020f0f1806071101030c 67
    0x10054801049207040c035034400c0404038003a01c1070360142c0d41003103d0a4295003c180b41e086002c440e40381c0600c180145580e1381c0040c800d09091981c5060600031141b01c2d900c03c020100b100c41201c428110000c40d0084120800400540c003d48140c82e2040f04002c124003402c0d00c00b070300002d4140002240241c1c0002c0d0302050403899400840c20f00d4550f03a0b8400005284046403450005514008400110100540d0f0044a050745524600001c10f81c001040680d03594031203001c0200c9410b0400c141400418805152054000318034030300502400c28614007090310f012030380c02960070001c0005420441c1d01914410203090028012640d50b9002c015031130050703513401039104040d210200c0424180c403c003000320004d804140d4503070089608185040c030305111051111004550030003020020a4403901010b42d0700a1401c5082c800c4a101e003021a0282400c17000102c5400a0042500b4002c0ca00b01d62101000620881e03a542e213034903000c0d0304801600c2c4c10b94042800e0801c4482801e0103001281c00e2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 227219523 1250 227218273 227218279
    0x201031d0a06240f0b0a030f050903030703050a0513080304061103091b040c0f11010603080f12010e131212090606031109010302130207060207050f0d091401090311010203280210050105 81
    0x60603003090030105c0da0354441c0d0340d006c090694861000c11000014008c0c0e520684c41c90303001d50307101c1c6070095002d800c0c0c0f00e005005000091800c01080b100060030558856255001119151269a10714090000b0f01c416185031900080110030403525100c000381c81c00900341c85d1031061040003650030620050b540c81c280018042510a50361803641c62003920007494020241c000403070314a6070783e2240300a030760146a910b44400c1000a004010340341d4525505d004081a042030600c6240c0f45200044080e10020001c11602000c5954040c962050403c1200d00340b10810821100d2910301d0400c00520582c40f08031288540019000c105180400c01581202c4e00a498101c50040340603000000b0b601100086950690900010b00451810008040c0d2200a5001802400d0b00d80e40051300412050384034510322003104129001c2070741d01c10340d10b500700c0b82e1205050031440d5182c00103074110b00607001201d4803410882c0d01c0255643d0503605080c5210b01035000c3e01c60507580032070403d00f40c0d2024000c00750 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 227220773 1250 227219523 227219549
    0x50f01020418020f1605160815060f01020703051917090f01050c12030408070203070503030a050711041b09030c051207152601030b010501030b0108040201031d0a0624 73
    0x24500142e900144040c50014507010f00e00b0f265205040c0a04612640a848a601c00b03d0729008401d00340303041c203010b054401c0041c50040a00384294108000c000d040c00e018020301c800d1460503074003c00442001d180d200041c3c0700079100f50155290b4515107624159280100e684024900581080c11680d041030080c11914207590444019900d82c0d00c18242d80c000740c860303a03507071206407810280598010b40c070568160f036840084c5c1c0105403904404c2e0b04800c0c440d4004020401d180740c0c011084a0510744d200304c540c0408082d2070001801482440300c9240704000303000480c25016404039013241941e01c1040d040400c551140140911208034018403046940001018050490005800c442c0c1c00440c1c944a00f81940ca2460710002c1e91500304201d000c013440c10b0040c002c1050002c0514090030003813800f000300c1040040000c1c5440806072005e814155035450803502c802d0b600807110000300d21350b800c8901c8115945400c40092130520640a00005078410b640a1541440214000c50f00185d503001c1d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 227222023 1250 227220773 227220809
    0x11060a0c080601110c0d0203030408011104260a0b0a020f04090e0105010f05010212031026010c0302092d150c010605060306220b100816080613020702010c1509050f010204 75
    0x485509001c6d40141e0341840107100000702e145090042d80304104c030078802c0d40d4803189409590568590800c524805441e10125200d201030030010b90010b000b45c1103a00c1d22041d448022950000303201315001450300305000a000b18080c004c1e43c2044c0503045c2048000c000b1070303907031b034104138040d000d02d00801d40180c00110700306260b200c1ea10095a0441c0f102003e00210070b1340c1e606800b4524180e0b500b0410b105001070082014020300b0305c42c2e501a0740640c2400c2d441e00581f640000d41d103421100c0301112100500d41000001c0e0200c1000002c801d201800c0d6400014403501c40598681002280100a60070030b80c010a0504090064034080d51016028201050b00324031001c402c6810088040c103d603541c0d1091310300c15952801b40c86500e100c151108a1141042c146000500c401d001d5030000340000743d010301c40b1589400400c060220581c4200503110075035031004881c100c04460002d08201070030b4071000428085c2c5d80c0007148803449101151007114056103943e01341d004501c140100401d40e10080c2c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 227223273 1250 227222023 227222029
    0x3030c0702040f0914060c041202010516020301050c1c0603020f091f03060f0b01031a0103240b0307080906040302060a1518050115110a0f0311060a0c080601110c 71
    0x501003440c801000450428002c0909004898501406859280d009503240301091004c1c0403594001428664032858103003070006282041c000d01d10001c0c1003010014410802c00040304800b1100342d4020000c0c04a4208001f80d01c450341c0010380400b0b00d500000140b0696291540b00c1d40007103e6016104d00341c0c81a034a070801c140440001d01c0c00c0d42850081e241d94922600506007180170b140705240c00a003040b040303160b400c2100e103505032880c14945032030030700101081040d01c7c8464a000900c0d001c10f80c0360300f90751107810305074044900030800c1c0c800440c0070400d010707400007551060507955200c0809a9407004000d0b0341f00800d82e005000340c4c02820114100380015000b0080b00f09030f0107109003802d076640c202c01c207010b034088007581102a0f0707030300041c008c400030583c00302032024607460302003c1d100d544192030f600c0d1081881c3c001c1520038500c070180d0402d405010a4441c581d0341c0d2082d64168a81141108003900c0f0900ea0032001030086400034440390f0181e00800070700103500d40101741000d814001c4c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 227224523 1250 227223273 227223277
    0x10c020c0a0e060612010612050a050f0f040809040204060306030203120a050403080702061209030a0e060405010906110a0c0308032a2d0a030b0108130b061512011419060203030c 78
    0x51150031440c05c20407501c141604031250350007081c3d56502c0803e800b880e40c038034504558010309041c0b0828101018440e03800203042c01b00b130304240c007458403920701c1e2524030301409103110718a403540d0064000315001580913015030080c01100c0c003d0702502c4000c40070426082c0c061090407800c101081081c801800411034120150240c2d52020b00f80c1442c0151441c410706a0003402c6a601d20030b9070000402d2040c09500101d8170071110002d4501c40e041c00d0800c40041c0243d0780c42d00844040028824001c1e01c141c0c03040100c44285504500031040454aa040148107a40304070340c040030050003010105a5058111107040d1343c07a01d052001c9003090181c6c51040304294111610820070f80052440724114003141c03000702804259503d001420f4142000058240d40f0000d000402e0b50f100c844607500401c5041c1484c036400101103506140201c0c50a00d981d103d80502c0c88000400c81d03082c00003042e501d159031036260b901c5000b22680e10300c000ea801004e1441441d24001c200c01a042440420340703090f59080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 227225773 1250 227224523 227224531
    0xf010503120715022a0f06060d020f130c1403010518070e1306080106090209090a0e0319030605120c0d120e0303030f060103150303020703020906041d010905010c020c0a0e 75
    0x40c188a00103000440f100070307600200c9030902030b030414180f80000a203000740b0722000c1090100c090543c040300c00900703640300c810050540340216142031020007150f49062052000c40801441043d500c01d403188824024a01d9140c88404900c2104400c1d0101c41d0200940713049400080c58400b841d0f0b207003083c61007040000341074441030120078164481141c1e00d00d082c1d56280c0c861484009100c03860800c1c040c5c2034884940c0800e204a1040000e09010b884440e203995202c201d8100c08122244d45000301851446029100d62079084243e100d41003095143e00448112a011283c0640c4100404440c03500c40d6030750b5000c07030b90001000d0019400103c2e098a03500464016045c0400c0061640002c0b80c25948212400c2c607208100f0f008200c010b40e014030808655002100c4020f0001d4203543e4082d503a4121030102030310604003900080c0706075440350007804510046030700b903030042007a2000b400c0c0a400181c0048804d9400c1010a007181d500c0021001046d00b402001e80769a5481c190101c0310170100a8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 227227023 1250 227225773 227225783
    0x30206010e0c030622051f0b070201120b01050c030315030d08010b1801030609060e0a1d07140d061d15190905070306140406050604180201050c0a140a0204050f0105031207 75
    0x80c105881c010361741c414244182120342008401c032829912101040450f500301c000b504606200c0d04025036030100c2c0700c4054911000b000160150400c0041e01c2c20302400c0102c0c045840000b04000d4601c2a19640203900c403010b800f1205540c4a00300244e450710b000740903d40b902d01052001d0f100c4002090250100e021041c1030001c4c8050300c8800c1c2c4810f4800e51b8101700c001401410501c000d02c00c06101e4002c2e002410700c500d179811100118441d072075410754440c4003061002e60007041c503140d0303a43c484285078590001003040000000d512501042d40610b0101d00140164140c1c1c42100300d9080145100d6600702c440e001c0000540c403614001400c81950503a814452444003000244d824810288a105440711180755032400c2d240000c20350b0001000c05018a040245031850701200160011441f54242016600c2c2c8805420300b92501ca4801c2c8040c1850711050254030300c807880400c800c1c18840c020350f824062a980c00007003042044082c4941c9402d1f9020000900207030104030003400d03000d4410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 227228273 1250 227227023 227227069
    0xc0a030f0e0303010603060f05060301030f03080a020919030510140a0e0c030a06140c04030b0c0a0e030d03020d0b060313030e0a090204091d0a020d1707061404030206010e0c0306 78
    0x7100518682098201d80c1c04a65101c5051003040340c0300c203000001300800c1b00c0491456045950f03c144030711400400030140140103003c40c49550310740d0152009004003030025907001403c00b0050008114500c015103c40c040c0344a202038001d464080d8424295a042200e0034030744402014400a141c2030840d1505030103007000200b5141c0c3c0c107206c812a8103010301400b0501c492007a0120309244400f5004d00c400f40700800c800c00001300388184080d80700c440848500e03124050f52009031175404091a640b541801a0002c50306442c1e015805032010b81d2002e08104021503102c001c0c40542d1000742e03071030030740041140b0341400003034410700701d410302503c0140140c5040c69640c504c440aa03007180c0c00c803030a03031a180ca20032024001c5903c0b0105030040044001c00d50702d2400c0e0007003030380015440b5002d0082d2580741407400d02980c1100840d8250781d0b0103003003000305204014403c00c0025090310102e00500407840009400d0f00707004015401006100221891502c40c00200711410044c003182040440c0c007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 227229523 1250 227228273 227228291
    0x90703060305011b080106231b0f010504060f0b06190e060a0c0209130b0f042f04060b040605040b131214010e01020c100b04090b24010302030c0a030f 66
    0x83c01290100b895000c1c2c4c2c40c40000d2001000350188105030040030030802480c3c030480f04980941c80501c40b01001801c155910711500040c10324048004001710054410541c80c804032002c1580f1882c8034602801c01045810040880700c4251785020062941c422014040c6141c00801c82c01d1125840e10142800700d40c141401c004220700345c002e0302c001001b003a0040740e004c0641c1050041a44c1c041c224140340060107000360386110312aa8060110303583c81070718000060411030704240007d4140d060221500e44603603804010704240020b040c0e041d000e541440303400202d4032000302c191815946a51207050a0500f82140b069054115000078140b0707541402000449031902d090030f44034a805059101c40465000101d5801c0d6040c0c2c2c0d10f0040d01e0b80c410040400080f50200c0d6120b9045105600403a26a21200c0064050800c5030310281c103010022080c8a03546100310302444021076205400c0f011110b107040190200d00045906140d07680c0108244100c051107036004202d00f900003040054500a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 227230773 1250 227229523 227229533
    0x315060604030f0c080606040513030e01170a02130f2718080405030f0f0c10020708030c03090a060513050f0409050a1101030623060a050c0a0c05040b01020a0f020907030603 76
    0x400100035131390403200c000c06128103c0148030483d408001a00c00b07101c1da0610100b040800310f80c0c50405410456100300c0c0030010b81c031030102c04924007040c914054260400a04140c002d40c000c036050000322460315070001d01949034100d84d5049507411900b4407400e40b5030b40c3c0c002c8810420700765452400c99490f4034903c11208078503114540b050044540545440c2040c090500e004485010304505500203800a210904002221110188281d45403884d0004144060745015042e401940303281c00f0114141400802c000054200d4050458032403c01a0341c4580c10f5481d4855003900507029a465070090010341403a03920507540712000351000400900c10345030541030000c1d0300360441c6e02540d01e05803511690317854004c00014020b0300c060742ea100c03240241030321140c40c51044185d00414002c603510341510f000b00180c0307441e92540070640d00309141c1403030070142c110190300030940700710b10f040144121548001003803500303e64048500c0c0034802c025000c0003109080108041c0070141c54003c00700000e2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 227232023 1250 227230773 227230793
    0x23030409020403030f0c051b150d09030e01080910020708071509020103060518150103151509321c0809040c050c06040f0f170712020c031506060403 65
    0x12400010380395819413074000c11844040c0404420440d400c090400032400c0820314440c8441c0204410305002c50500c04503c1e401103c070620000f100340030038400100003940d002481c01d00d100c0d03600c4010b20b045080041d01c0c4420259110612980103080401080420380d009004e150700030110682499001da0718030b516241c0f04007070480f005172038151900440d600b40c000c00c40035060403218061090b03007000e4022001c1e200109001503024806400352016406a40100201c035040c0c103131790991503150f2178074440480350f4481800000744c0d00c0d0b0001030110448810f50088216029880101e05002104d1080d0b4002d040711013a0b10417441c809030800268180550a2254450100603845411aa041104882017800030100f130040030440c2d000c0710040440c01d10340c0550700911070a60f1079a5828142a01c0c80600c600504107011030341421070000c2079401401c00d591082c610428011b20045089854025100b00380d90903900180704080c82061364241c4c0fa521440207040c841c01c082c0d4a8039040b24407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 227233273 1250 227232023 227232029
    0x50d05040c121a06030d230c0102030c0a2606060703030f020a09030c08010204030816050708010f020d050a06083a0309211407023007120b0103230304 66
    0x5800c60400b00d03418000c01d0035110340c0702c4d10450140410030401c103005494107401500b0740140520003180101d00c240100300b984d0744400800001c5440f4030703080d2004042548240c241002040345618103d2082518a4100c02e4290350410208056100d40d014401c080c0c0082008506240d120b006010020060748050508001c0d10740d44c140606145d42454030241030160481001030340108018030206402c0c0b41140c0040e00c40c00740100c140c3c001030401500f441c056030411030386942000080113034500181c0103001100703130300c01d010030041d181c800c5610115821441404006d401100519034103190b81f001c584000d102054002c20350790007100280050303049105d03610012035a21200c0106010191000d80141421580081c07510f01215030040c12081101d00180012100010301d40c085480d030782c03104418507400003545403100c800c1601005040030000c440e8043c03032103400b41c001b074035001c1c002c45003c8054000010011316400c580b152951490720803004d60120300e4007507251020000c104018402 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 227234523 1250 227233273 227233283
    0x19050702040f09060c0f111b03100e0d110606090402010302030603100e0a0b0c0408030f091203340809060a020a021201050702010b0f1305060406091505030c0102060403050d05040c12 80
    0x91803451703200680300c1a506401038040020740c040e48103034940000b42e00c5c54025003052440200041e0700b000640703800d8400d40300c295000c1c244090174140b03410024000b18100d400713843d40d141c0c440c164940182d07030720b1701207410340e51001da00c2c0d02040255000e5802550408000340507a1030300d0111400a1040d681d020711000050b5019034441030a1000100c0346d160007040c4a00510300d010724100340582d0700c7c05250541014008001010156543d071400745484080d158000c1d2915945035086451450b1a803410040c0a28140ba080119040342004081602540200b070581091150381c1840340c0b90b005442408198424401014090707581c203241c0451141c1c0c0c03c0004601c5203001c502c000d0954a1410b00e0900030b40c0031884001c92646e9211035281ea2001085c5d00181c242d44103000540070740540c1e032046000030714045582159a02c6c01ca10001070302c03016801c07030b031801042c40012641c42c101107c0141c00280188040c2d4141c52aa8011607007044c003445141c0c40b00c0e61596a1001c2c0b0703903014803040318 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 227235773 1250 227234523 227234531
    0xf020a1b1118040210020d0c1e120507060c02160303050711031207120e0f0607110405010b0403020916090b0a05041d0103110109080304091d070314060c19050702040f0906 75
    0x1146040701441d002c84000e480503042001f032154000c4c051242074800100802c0b4000f440e461050b5101a8145902e070b00004988612a1200c2c0082c00130b500c090350640d4403504003480580018000142000e28945604001c00701c13601e1034900b2100c90b00005812690002078a05610640d60100300000350203407085400c0b559000103181c0800381c00e0183c00100140100c100c001c1e40c1307076981c08100b01242002950510350b10780d8280780c0030691b0302c06041078030b5200b40742a001186888000028000342e910903280a05582c0f24481039064003c14081000c0004591880c18864540d0100241400d1501e40c00c001d802d2503199244420310303810810800368002c4540e0010800d01481400074140441c1c00e00707020708031130304040d0b83c0c944078851400703092050381d22804c6854418400340a1284000c0c0d0700801d540d48140c880c5020444c0e8040340c01b050a8902c00d807404191500f01030805c0345c549400d4080c08024248180700c081c2c900741c00c0300c0e00681c2e0003642d9a201406005c29409481150703072040000003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 227237023 1250 227235773 227235781
    0xe0909010c17040206030109020d0b0409140706230705030f1206040c030b03060a0e0c09010905100605040f18020403080714060717040204110403020619030f020a1b1118 74
    0x180488100c040d4901c01041c02c000703000250312400110303415240c2c42100540e480407580c00b064091300e410904250420b1a008001c400d02003030030072541c50a6212026501074070764440e4110b8804568600740301c0c03400c41c558802c41c144003100008048542c0310303c0c141c9041c448012300074210b50300014010ba40c2c031802e40040051a18051041c1071011025007010000f07000c512010030303603c82d00240000300c003d940311000310340010100701320040b031200100088440c3d03171281c0c41000a01810380b0214041c1000c0c01010030454054429202912001c1c400c40c4580e503d8146424128094042c41600d859400c00c000f1020480440c01844c0c0f441c00b81c43e40c40c0c4171041984860380341c04401088841004807003025403078400c1d000440d99412507011a80412090581c1d88480703001d114961009600000003c0c80c0d44c10ba000c00381d40000c8891035502c3c20411040c140d007070303d4142c0c0310b01e0003200e00040c1c5040511017142100030305000054003a65007c2002d40444d808106081090444082d0060700c450401c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 227238273 1250 227237023 227237027
    0x606030402121902030c0603070503040201030509010b12030c0607031b0f030f02030106020307050705090106120905010e0109150b101403100306150905150603010303110a0209040b09060f0103030e0f010e0909010c 93
    0x81b000103c801e0743d10ba46503242c0340000030301901001c0c1000341059145d1000c01c0e010715094000310160f00e0010b02e0b00d001ca17000f680c8010386e40d034070400380e110a40c000d00c000181594021300c540c44032000c80480c80340d01145020401c4480c2c0a08400784001d16941d2801e00c0d0554034288003850107407102d5001195200400e0405515020440d44643d2140c851200103008046c0e21480e081d503244041c07580400c110889180c02c50140110011800e0650f00c0c005002080c03100c0e40804041d02800040c00300003540946041c4485a4a0014508003150540e20801500d008a00080d948001c8035426940d5507500ea0790b5650969a140403490b040503a095028802d100c2d10f485080e800c50001c402d4503000382d8021000c42c199010500c406414001d1022143c1c48100d020b11502c55021f03070040881b01e4502d06450306104911050310100014071544e00094a90680b00c41014141c980544401e659107205030100b09082d90b00340d48490401c200d049040000b80c541d1801e49028225031000804e0506001e400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 227239523 1250 227238273 227238283
    0x9030a080a090b070c140c0a090f02070206121603090f0f11090109060f080a050a0f0c090207050a060501080604212c0f030a030806040506041107030306080123060603040212190203 79
    0x21400c125040441c01d039020f0323500c5105800403100902e10214260741909011300c0240141c210194000c6400a00410b14580c84426580b040c80c803c8007a4a100380251011012034500600c000d041904040707101001c42c07a8001c6034a10703030344101041c5148000c1e1034041040f0000a80c02100e8698503104d050000e04030140040024190a000070401107105486440d6140040100a4042d148419403403090050680600c1302410b040300082d0f40c0c5d0201803070420f80c0c90841c4882540c195141c000085551800230540c00d0245400c044a00c00b02c22101d200907460418100b40034091108400000303013480903050030a44a50014030140d81c17480115800d0000003024116824401c0e00700010402c0003a0f04114000d420400a446c009042d03a1075401040040017130102d03440d1182404980c0b8400c060b03154112900780c401c5100244102013440c1710044d51040c0403171040040d02503890004202d03003022005140c2c80307400108000c5035002c5200d54103013000c00b28a45482c50304410040791003941800c00c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 227240773 1250 227239523 227239553
    0x70906030902090a021b0615010f031127030d020f01050105010804120f02281203060f14060702091006170c092205100315020309030a080a090b070c 65
    0x3014803080e030880e400076030b503500c00404c03d10b0301540c01b084e8010f9481000d01c0c0380c104200701c04200c0d0380500300040014201c034000b8903400e001031810f07420b00001c2031203070081020440001322a030f41825083d4600041e01002503540d41585081350000c6500da650400038a03605198540240c85640c092203911401e45005800590600c140c0009200010340f480c2108161410185401d186d805503004c4128100f182c0d070b0040251f100c2c104c2c444100840032040a2503d1140f043c240862a107103811310a80075941030380308041042c6c0c0864010003d0b0300c40d01103582202480103052a1405030300e07900041030340c44280c0314842010600f540c24004103800031010541640b40b10000c0a080c50189550190f92050242481c0142501c83c88000ba85181d141c081c407d009504070305005524080030004041e02e00c9200a442154007652403074010b04052084a0040300d00c0c40c090340c0b412407500403e480161014000d08201681c40c3d69010204100e100c50600413043c5640d4606244203e00f07200080d9107001c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 227242023 1250 227240773 227240777
    0x111303051c02061609030f030914041a0f06040b19080c09031c0507050109060509100b0d0f030504030c06090e0f070e120708060a0507170c1602040f02070b070906 71
    0x40041d140c0307a80004007154444184000c511014411035000c488035055544000d000082003482d110030947c00c00a940281c0d800814041e8202c0c10510421050340c082e81400344100c2c1c8400c0c400d01240c10000b29000c1e40304c0b40900500c3c54159100340c0200c180d40503844034888103030741e841010103240d84001012780106c080340c5d2403400c040e00b00d00001d803591190311405481003080381581d4091402001070380c1700150008000c006c0e01c00c0ba0705060000c0c100440b460382c114010340021008220043c4900f0200c0c00015100c0620700301c4039039645481100081064040c00710074040000000c00200e07000380640740d203580790184107181c0300d482540c12102030720b050095030100c1c01f0881120f0b03114201c51148007041f50a8203990150442090500c0d6240c0c1014501c2d02840c400c2040380c800d02d07084507005901694440e4642441c01d0500610124143c6190241e10710800038159401200d2886500d000e000600004810b203007114110200c0c3c0c881d035800ca070b80c03243e24410000c40c681c010003140e005080b54 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 227243273 1250 227242023 227242063
    0x2406031e0f0c121315090c080f03030c090d0203030c0106050301050a020c0c090a1506080f0606031e070e0904030201140c18010804060b04090b04050709021303021311130305 76
    0x201e04400300e409001d4803950714215450000343e51001c10103400d040503030000c02c00c41509104104141c064414010300307840001020b5800100501d0014188455170309600c02b441c115112a550140294051091075612400303011502001d6a001d2000340800c4101d4400011044e1802c818582507440c01091440780740e01c140200100203101080852151a0441c0e816001b40e85041c0709000800c40c0010b0b40c50090110343d404aa042e400c00c000c94008e02c0d0340030311a00d9a87e100b0381041038611080b030740c0d5030310100c1c074115030b00401d50355111076900a022820b211204190b0b01c000f0940501d0102c0d401e50040c0e45903400b50781d5041d2040074017a0054260080645003103a42c0c90003440103120515a5410011014000350511040d0b900200c40a00010400d0140389040d0400d590800300581d000c0d1428001d00c240055460071603c01c480d02c004205002e4001071349036408000c03140440c5003801040d00d460750110b599090403c0d004100150403141c941c50414154100b59181c180300d040c100c5540084 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 227244523 1250 227243273 227243281
    0x708070e07020a110108040317090a05010b191e0b0a0302190c080405012303011427040f030c0614150d05102d020307030e060f2406031e0f 61
    0x6100b0144c1902c0701c00b8213142c0d101e034640d450125a502401982c0304c400d60304002c140150307401c0108401041900400080c007581240004004000e003c182c4181403518010700700700812805001d0300c0c1d00b907511241c1507850161b0f03035400307050350b41d0b000508050000740c1c0003946c400041910021040c0303014203440c0490120a540c2e542103c1c1d0311981c010039040c03102071100341c000101c1c8580300d11300d0100c1400c0b49544a59480d5407a01c0d40c2502c0309002d511070000708180070006881001000c0c410580521500c01603141c0b13854100071a0b184e00d07400d908212541128102240550142103240c8014a80590781c07481c0c110010030341462041c81080c0304042d60300300c141c0030031000212140700420600001610b03805a4207408903028128080302800c0c802891322020552055024600c1007401c1d89003884500180c10301e0755101c40085070300162850400d00404d810042e0084800c1c0065070003140441411a603800003100342c2c1080b545d400f040c200210300070b03036809a250320107604a1100a8180fa203070134 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 227245773 1250 227244523 227244533
    0xa09120b0411040902060d050f0c03090604030e1f0c111005040b0c070512010204030b0c1911030c0109080c0d030b0d031202040306090f05070b030c0901050711030708070e07020a 78
    0x84040d1019001c99961180c94003107075a65400704404e15402810f4658815500c41700001508044601d035200b0541000000c5030401450110707031103050880d01819040c2c2d5a540d094640084107010306400c2001d1045c51080114143c0c80c00c0001c4485403550b06c109110f501d003802604884118803402031141c0f00031203000d250408192415a891541000d80720b03524001302c546030420940c00107900000c1c13000a00d91f00302c810340c002d005803070180710391301003643d02c00158604500c504052091000c00610500c021b4a11442080705026100010303640752212007642142964029942660791f84000200c46440803020402812008611300781132000102010010f010910441409014001010078142c80d883d8164100c801a643c00641000025900e00f4842d00c103d02c4130700212458814440d000c1080c0744002e00340e9120f0381001090500d050002c4004555a4011041c01c0b01c22000464049480d0750b0148104006000c0c0c9030000e000c1c19141c011a03449198000e4240307415500200004400301d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 227247023 1250 227245773 227245793
    0x411120a030809030f03190c0203070809041d010507090501020c0f0901150c08040603050915090c0402180409030c2006043503180f0d02121504080a0912 67
    0x150701070411440507907504048600358864921034116a0400200704a000d404000c0e812107024210b10b001c1140410280b8240da80748901c090140c400502407019401c1490980c0004091521908002c200b03161071421071400d40e60190ac003040802c40d8050284259641000501e0383d4400c01c548070360000f00d07010089021a6418000c80001443c003450500b20280104040780e0019840298940d44a42e18030b0020020b150030345401d0b015008175081e4400480d91841d40c90700030712580c0003a01c1000404410003009600500e0780706841c100d07010101030955600d20030806940c1c02620740c6056002140380c9642c0010550035070610f09000c5142c1c3c0c0240d074641d5002c0c0e8041e00c100650034902058041210b040701001c400851034241c64424030100c240001001810350900901c400c00505c501c1c3d04200500e207600411450342150103140c0503030140c6081d41d02c42050000714000e40e480010056145140c04034104c4080d910501c0000700e10750156841040b41c0300802e000540d10515120a5031140401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 227248273 1250 227247023 227247043
    0x90411070b010506070f0506070e0108070c0309051e04291912030c0519020103150e061c0b070903050d0504050616060e100f0b030c030d0f020123041112 67
    0x15800401e1541c10030450b450801d8546c1c2c1c12504031903291800d00402040e5202001449000410000200340407500403600540300c00c3d03254130b41005660500d0306210070302140c141c540c1d240d000300560180e40c9842d6441155452040c6c1182c4121030130204800ba81080d8003600d03e9401541c1d0625060440141d031012942a50381901211201d1401d60508440d5968020030180060050f101080060030226180214061007a2070078400400c0c00044084060210721800d10f02c8104080096070f0392410051881c04142c4134001c802d0b0484107501c070001c044404560b0702e0080360004106105200040200000400c01440e21a14090402001c102d00d4012164284607032282880000c0800429801c01e0241000420407641781481c0301c540b69000d04500d0000d40001443d1010100e810300340070482c22800c040150040130700c200c1071041250138500c181c2d00c4c00c0444d580d4410702c0340010020400700c5180307103c13402d0115040c142804c2c01882100c001c81c9042c8500a0058690750300d10b03012075648c1034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 227249523 1250 227248273 227248279
    0x108040816080a0f11010b011b0f06020c0d1107120f0c080d030b130e060c030a0f06030c170106030b180111030901020c0d0207050901090c0203070f030302090411070b0105 75
    0x4440c0075440381641400072010040c206000416001d0050f0f521100061201c0340d0790b40c0f0180d0380c1c489070300003a007281c402d007540d03500048501c080c91465003009054890300c1445070000c0e40300b0803802c2e1942400c90308100d240b00090b421440ba40d0080035809a0342d00d80c2360401401078200070f0310302281042400c040c10401000310b10000c8601c0140121019132000601c2c00300140e03501c2050041008000f0312599402c01e1141481148144044015108400b2840e1846009081715250661034030001e400c010701e5080010740301c100d5a4100b410a001d03460086101e0020700c858039041c054100360b80e0b00840c4081c2401ea161500400c0811700122203160800c1110100b0b01c1c3e007100d5055454054070034141406400c0200100340107030b01605600610001c400841a07943d4259609422612512184245039208440c00018003442c00550303c092456611801164603080c1d50380ea40d03200e00000c200d01500442c1e07020a140682d0b0410f402550b5001d52606000b91500c800f503038501b2482a410b000b0240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 227250773 1250 227249523 227249527
    0x60f080601140f014a06160c150c060608060f01031e1704091512060c0c050a0c061b02150903160b030403030f0b030c090403050d02131e0501080408 65
    0x4560740a0100d000303601d0315031665504d5017102e000c564801385818182014480c0380d50420000e440c460007007003618415006000d03500d003e40b00591151100b07502d410a5034a06403000002401c5103980c0740304c140d00d007610380700d00c40021401d04003681100c0c8903511002084e041941041032814080d83c485055a03440880b0440444400c2c89038080c4000c08940100400c2c0b204c55800005040107024004a6031488003d10240000d15144060744045204151515000c82006400030740a07401c0840095840c0c0b4200d81d90040e40c0d203441d0716094070300a0035180900030709018401543d104124540d00c00701000800c1c40808940e0105006c4048500c0c9402c3d281000700d0b120030755a80501000021007090f6600d502d0250f240e08000b0303440c2d40140c07001c5000c02d10b0b0841410007486280910021100010094000f4000071028440c03d0200100100c080043c08c002c2050f0203c4540302500000304c400c2d090041d800d060040794100308036a2601d40003940c000c1c4004112683c2d10011550f44140c5c0224115 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 227252023 1250 227250773 227250799
    0x206040213060b0a0201060302100f050d0b030c090f060901171f0e030403140601050d17031b0d06170a0b0c0a0e06160204051305190201020a06020d060f08060114 71
    0x40c000b0320407034100ba50442000100754041d6a0b0541025040d24021611101017900154007543c2d0304108030b800a01151b41480b203802104448da009000b001e102609540034116808001403094504481c40c22101c180507082c0406802c28440c5e0901428000c0c1900b034803002e203c0315043e45e41c0c0c0f0b02d4048190540c1043c440316107480c4290440b82d00d043d030040469464503101e203030031140107030a09020301c0c241c810721000040c1441d201d000e001346160891403900c48044415062901944000c1000c05a807001e402c2e025940da290000401e80c402e00080002186410304604809141c524910400b01d03610079200c41000c102d10b500515000b0500605a982c8d5084c41002580c20031b0580700d4035688201c021a880c9040c0d180f4070700d80107086108807000c1001d0707500c0d2029480c1c9a5180130001d003440e8011084400c0110900303c0d0544054014012a540c09980d95a610103a03031107558000c2c000ca80750340c4104041c04001c0d070a40c005e004664003030030440d0f0411028107006a821640240708410450100d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 227253273 1250 227252023 227252059
    0x1051e01090f03032c0f060d02090907030209031911300106090507050a020a14030d0e030c01050c070b060103110904050f0601090f030f11010315090c020d09050102060402 75
    0x401404012665542c1c59681c0c140a000880030ba686140041d20030180c0101c00c62981401100d0200010704074100326807400144681c0b0341100d8024000f046e800c00c00b8480580e28203404600c501040d030340241c1d448048806041c18540c142c0448040341420212040019510f1400d1b070500a1043e1500b540c0d0080d410304055000c00d0045140100340c0c072204a003241d410042d001041070b1141110184001e898081e0100c0726032181b001c540700107030000c0148000094100b028030080c090200d0440b810011003034400e8080b580d40100f0003841c2e600005085166500c00e000f070f144c0c0030781a040114189912600c0d00c000d0f103080281034504261740c40c1071241007080c80100750b0342030b0140a40200f280e4501200c2c1454002416a00c05011500340c00700001c086010300740795015258070400c441c805284c1e0b562880718600d044240c05060507102c03404c480d03440d08281c1d00a00184405900881c20302101e41e00a4205040d07001048100309800e8802c0c81540d0f00000c01c245c001c0e03030545400c00d0300c18080200c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 227254523 1250 227253273 227253287
    0x9040506031501031506050a030b04060f0b030706030e01060602060c16020a0909110321040b03060301181b0506041a0306010c120905010e0306040c0e04050a0204051e060901051e01 79
    0x20000c00110030b07000100034009801c11300a0b00f44496074080100c2520358040104000b481d200080114002c040001e00140850702714034204442e01b5000309200e8011000241000500d03049000002d540d1113580f10445000d02811005000d5800030703281c02d09086c52810348610846085003103031040b5031818011500c1c1e141c1840c00600c0c440008001c2d1010500d480e40e407840184000510a10445500138541c001c1003590b0400000c0303040303940780341928044822079240c000821455155588a1540500024500d5281400f6201da2041d50000300c03203411000c3c02c00400c3c2c0105014079001c0c00180071410103688180c040c90107a2031082c0d01d80e920100101d17a1135507080320051594156507560140150800034160a640302601c91410490711502403503a00e44007103070090290354501904220585e4002040750f081801803059400500842d0003243c01c0e10810b58200207580381d095a60004041c0012402e500a50216868035695140c800040c0c000c4101c940c107a60003600b2501c124941b6030040310 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 227255773 1250 227254523 227254543
    0xa05011419090302090a0c0813030e060d020301180b0f0108040f150507090909050307110307030f031e03090302070b03062808120c30120403030c0201020c030904050603 74
    0x9011201c04428401c01000c4142c580b004901030a000c1c00451aa90818000c00440c5100c603947c08449540c2c28210902286880c40181d041c0503a1303001c4050261610001401d5000311058056500e503d0f0941d035504000c0701500740011945000c844800582c0da516496a0030042441d1a00c00c41c0c4544c03d2500b40042c5140d4000c10100101ca081000c0e0340d0320341c014134417400c09a2120380000e90798070052400d40f019600010860b8108000b003000180b1036030404500d8510240031186019241e0f5101e20807280c441d10182e01103084e07042d80344034040411004140c0b00c0601c1c5000d0001e46801d50740690703151600c0c000c0f45145040800003a070192100a0001c40350715604040d942c400c150740d42408484143c5d40120803842c000c80c0c8aa0348074a1000c800c4032540400301c03005181075040f101c4c40080b0000200c110050741d0108000450440c20082c000e40412001280514241c1c241890050210b03051101c01c4030a42e4018041903032841c00120a6442840301500c002c1055518500000c0c1000c0c2408 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 227257023 1250 227255773 227255797
    0x207060f020a0f090501030b0609040c090b07060f051303120b190b040f05061e0313150c0215010b04090b030307060e03071505010302130e070e01060e0415050a050114 73
    0x1103144448a0342c440d05141030040c02d9101c1804c403d03229801101641e25140e41e15401203010400c03030105007020780c014404c0311340d2403400d0042c40352900c005907203a51140705c1c10f4030342585440c11007080032964850ba070303049002880984400000c0e940c0180485134091100404e50784d07a010060110f4548080f0401109044100302c0d900c15200c400c00706168025000b412164056000007089500784401105c0e0102c1120200008100c01c0400700c0c101980700500080c000f09001c14100005051303020405415152841c022680c1c412941d00245081983c10f40610013107010401006484e919008a40070b0b941c4a810114403412101d02107071651143c010024045480c0c1455109211004001381002e20702c81c1c1088102d00c005072131040261754080c0806907000c00940072103020102d595200e20412130988043d20380d520381e50703e40203a0106c000d9018101080c5c0680501c51246098400c03050740320904403000c000e0740d0070400800c458041c140174540c10721449207101408502c590302078400b040690 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 227258273 1250 227257023 227257027
    0xe04020f010f021c050703030b040c021203130204050a020307030b18070c020a08030a0203041701090506060d022e0219260403080d060512031629040b15030d120207060f02 75
    0x6040b0007085e950140c941900003d191000d203440138034190052036007030000e41e40100f80403400000e51804d0360b840a004d40181e07108003004c04005032114099607126030038800340140c907403501e0a0040c00384e54804002500c10b400807410b01003015604401160001454900f88100799418400308030780c01903a800440840c403000c2170080d0140d0b4004000c10a8a6260400005070b1720382c0301301d80742a14a45038000f04280c000000242c0382d410189074013400e00340001d1682c846101b000800b540c0b050791a161221600c00b168000d0003541303404100a030f80280e003050403a0a007948541781d80e841503240040310400190000c40d502e400554081c184d90103960030007541341d5600300c8008040010445403103201d016000080250741000004001d44507080503a25000c89503948070380c0c40030310244c0411044a4442c1d001c180991201340d140d1301c01842117108240259050810880030482c140070841003034400d50140812000840d40703d5240e140c024200c4001503250502da1400c900904400d103096400c080c40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 227259523 1250 227258273 227258323
    0xc02010c210b150711010215071b120f08060a0e13060b060a020c09060a06020d0f050f040e01050a0e04020a030809030703020904050606010305070201270206040305060f0a060e04020f010f02 83
    0xa608000d04c102d0703100d5034030450f000c46100c005a0b01e414140b0201d54408080c0000540a40c3c01050b000d140440c1a00000c2d902c10525959019401e401036444800120202c07540b408103900f000000360080320403600c0d00c8125140c1064100346480041140b658152107465060401009400c40c00300c014000b80101d888410040e0025900c225000425208480850105816060603c481e1058458980c0a4072740c41c018000c0954200d0801803000c01048803c000105006010b00060006040c03101400030295150000b046181c1e035054002303040c4941080309200050b17032000707400011a58001e601076101d4801c040040d042411540c00039401000e140100410040c021074043d1042030300362010005a100e04004a00b01d900c946640a10303075100e24120316120070100c0c5048400c80c4000c0c403d0707207019182d54616003840000e454a0042c28186001e0000c81004d5004060251408011150a03442c0a07000550300e001c400510a050100300c0480301c059902c240800c41c15921b4544a980030029 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 227260773 1250 227259523 227259559
    0x150f0d021315170c03011401090306060b0d06080c010e1e0901030602030612060f01060e031c03020702030f010c08010308030c1902030d0b041e05090f060108100c02010c210b 76
    0xe001c00b0100001c800711501c2010381002c00f4058055801e401e101815070382840f0760001e00d0000c442019041c0a0b002d400080022158025031010307000780075001e91180500c0c441c900a8400b0f942080b0710707a030800c01011529036484000f42c209003800321801c1801c014000c0966818174a83c120b01354005031240004070038441d09070020f501901043c0c43ea02ca04c10400b0700c00f5a02c940050704c03004600a95000100002c600c00c5c2c0c04070360290801001c1d61f10f40c00e0341e000c1c0c0910080003441c40700e0100303401291020540c40c05002e08041c200c0044002e0101c15140500102303080c00502008245010200c0410403910840c011b40340000000030340070b40d00c08880031019582c2c1c0c1015440030320003401c05500151a051038094040d68085c1104c0020040080310200b00281000804402c424403425607104e0360404100700d898000c1441d80f018194071443c0a0301803099811300142d0405680c10702180080d185d07030010b540c00c82c0d02d07600c10201c4002000300c0d0301312010300304000e00f180d17010001c0d80314180404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 227262023 1250 227260773 227260799
    0x50d02060709170c01080718030c0509090f1002030406020403051506092206112203060f0b03030304060c0504120c0905130506070509032e0605150f0d0213 68
    0x54603540b62401c04503960240b05141c0c85400030035000c1500140b0b044c45013540200700b4160042d400f0f08006044100170707400342c01015585d034010b540e90940806c0c204420f0034036401030380d042403001c0041c04800000740107071039492412540d640c103007030747c00070000c0c0600c0559416074010b03682c040c040d138a44480c40e0414000128041d211035120f1102c010118403042020383d50203030f400e25610f5175102c1801c0745803540f0000b48840c81c14503200031420844068200b840600c50305c21900e0f030a1048103140d0035800c03c4070480c0c0034620310710003051501e485490f00380e4002069a41c4941e001101052407503807118122007c0c0a19032107040c00c030141424480402070840707000000e450400d0420080384c1d075602c0846106480128010b02107800040c040358446100f107005240d042406400c844c0000040c10b03056020358442c81801d520b480d101074045071600303a1406448014030003161014041041c0c45d5184049104544017000c90b03840000319458440b009406852481a243d20400c941c142c1ea081407400d08 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 227263273 1250 227262023 227262031
    0x312090607020f070510050d0f1b080901060f030210030920120c0a0e090118030c060b01080f070c0302070504050a0608070608070e090a09020d030519021f05070903050d0206 76
    0x58018062841c83c6070b2000200c040c2210b1008200c8950035810410a480300e602c03400b0201521a20b89468580400080c060300303001c504144102040100c4468004011000c00303040400281d042c180e08002050082820500b42d98048075030400440c1041000d1b4000d10515000400740c4584421459003d0859a0110342285040d103990501c0d40c0b40c00c001c80d84403d0301c82d40c244e90240c000c40301800304040100d94180d0003505d04000240c4051007614042601c0d9680d84200e00140f51130440314100300e00741c02401d034800000c3c201030301c15060a486032f413200100100704100f04401a9948000d0601c02c020480040c08050420049800e00304010009441c50340504a018450540001501d9100d5801313140314072455070352a014a03c41a0400140000140c040050740d51202e20000150782e0303004c102c2d01400c0c80398440c9941c1d10005240b0040c1c0c1040b1a00e604103640056002460341152142804c685c581100c9001801703540300c14050380d5000083d000a00300380b00d10001042c01c01d0700010a1409 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 227264523 1250 227263273 227263277
    0x213080d0e0105040f06080603031312060f020703140c033108031c020d0b3a1e020d08030106051c0c050d0f1d060604111216020312090607 61
    0x80740740a84010741d503901c603500c130b10410000040c10401095208110960300454018141c1c0d20306008142070340e003940440c1d0091501344400c4180307601007200c203208500521110286c2581400d000b510081e0044481990104002a0005a60803409802d1048485404010022204076480702151080d01d003004002c0c2281c00b507103005c020405c3c4000100761401c56110300040544040d0340740b5640080d4100c03542140750184c5800c41c0b8202a070f2030709000c0c0c44a001e60612110b0fa2203000d04100c00d150440300a2003240c1c468019076502280c50440301800402110380d217004044560310219502144070791014200800101c000b08074039622000400300c00d0003814011802e404107451060403240900c410302c0215104015840e001203098104091104060310002084440c04030090049124400407425540004081040700d00c0c0c00d20526203514014a40749081c28520018000c118202030609901e01c89030b64030740e420882c0b0030400c5030080300c102c000503003480c2405d1100036078403031090b1413000c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 227265773 1250 227264523 227264537
    0x602060f060928020d0c0203090a050f010e010c11151b0106120f050f070b0409110f091201020c100e0105060f030318010504080d020a0201080f010e010611010213080d 73
    0x1d4034a0518200e0340078408104030824805046005000003003e211090500d1903000d00600b00d041070300d48981d120b80019500030315920310501003000501d00082e04010b1044510000d60005641d1101c40030581c000c080c00c180408000b20f0a0142808041d100102d80c0900d801d5850651100c44c0c1016250300d203c2c01d0000e0110f0500d001d1340c0d5007640d4450280b00580d40c4d02d210340740d011441400a00700228090320075994480b01d04c3c01a203041c04044d40119505241c000b404004000312841014002c88580c0c0100d030500c400e25003403151612070760991521850b07104064044460080d41180d41403006501100d40c145a50700c0e00e50090300c070603800341159528090000f985410003079032001440700004d01661a04142603e1700c05882c01601001d41005001e000c0491410310030040000c4100041e002041c801805200051103120000d102c552303c543c22a004102c00452141c90340e065034810b040034800300c1c0710084498028041c0100d0b068a1f112214030004040c0d001246643c5d4001469941071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 227267023 1250 227265773 227265781
    0x50d060c080f090d0c030e091518010803040512030f0301090f0f0b10050a03110310030b101a450111030405091003050f010507020d030b0d0b040212070602060f 70
    0xd21a00d400c41d0031403200d4128000b844d103424802c4d6090341c3e5441c883d003000c00340884030303601049607280c1c11100380b26034100d0040b12010074035003814070070090200317680902415818481c4664481c0240e00c03600c0d00680b558010303108a10780c240299032010052210b4680c407903071345400c10005850110024180306142070f0a81c1c0c000b02c2c06003c2c203644410050940003c4040d248002c480c00d038450031111081590351340c41c12520040030380085005500fa810403100003411824800c1e803001014045025000f0f048004221108141c00842d16021a0220310303070f205d0075620a91407029045102c85c0700305214848030843d44103004d000754803001c00ca90001721408003c0100540701d0741a0741c540d0b00c40c0c60b40306010400191500c803520b19030260548800290703699482e5038940c50103203900b0004e029a5184c034104043d580d03042041e1100b50006103800d018030484000419500c40d00f040c07018045a90002c0001e0035500c80c4126043c2203030303401d0100e0b0703040c650310480251a072209440113000720701c002c0080303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 227268273 1250 227267023 227267041
    0x7031d0d090f030206071506080a051f0c0f080a020412050a0605161d1309120e0609060a1d120a1b1d13060212090c0d0327050d060c08 59
    0xb401c2e04d07805400c6034030382412030b102e42041c0d1020721046100b054031a14046055441405032a115510880041c1020b1100207144400f42d52003101c500009850240a100142d611400d00c024000d401d08009003d41c940d10300b050064440d9410000d11f40390303100f20800401c807001404101550180300108466152800611a06d0749803c0103400026940550444405903800d22800c4c502d00040800c408903001d82105c10546060007020b40d81003504419480440e50403000110a60300100c0d00e4510703111389600016114003442031000200042818021014602c81c0f500441350140140402d51001c1640c0c50345584020a000c1252611015031080440040c0a40345200346c888030031681c80314040c0d8028503000d1007001803420840130b1807a003c1c9000704805200402441c6031040211943d842d02801c041d103044005561a4000c900c0d01d1301402c04070b81d0020114840b20100800141b450061a550100e00c840701c0d007107140e00501086850301004020f9004128512103611003c1c8280d40d0300c0d0744 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 227269523 1250 227268273 227268299
    0x10050903120d0c0306060e060c1603080306031005040f0b1f0f0906050303090a05012f0a030e010503090616050408010f0b09070f0503041b0314010f05150a0e07031d0d09 74
    0xd00001f240d043d9500b01041d1074018050800812182d00b1240160805000c40020f805a0390051329603180000a00840c2d040521151618244800080c40542026958175500c0300711600050300021a510204118103502d015404104400c03400400d68140c8802c5035007107185881c4140d0280702c1c80c10000141500300442030f41c1c054200209400b1100c1e00d4200151000c20038820703103c0342c01c21a0405440c01c140010700300c0c1c05568802004120040301071801409200ca5800c08034144201401086840c40d400251075620020320b4803c3c01140d1403d403800ea88500603500034002950800c0105010701c170150f0b000303582460040b1280c5805440b0490b080e111807110010900c00201d0410004010405045071000302e25001c69100402590360b0320341000440b200c071040501e0b80d44640021040400301e006117600020540040d000742d0149100040143d080c610030449114003000c0014a0755010344c1c09001050303201d4403021955803203141c00540b200c1d000440d01000c02c1c04818049062042c3c449 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 227270773 1250 227269523 227269529
    0x40506150a0f0314030f04030302070503060c0708070f11030d020a12050301081e102406030605060a03051305030c0d0807030c090501030f1d150c0708070210050903120d0c0306 77
    0x142c1101c9007400d40d2164a49254002c80c852903510003000259a480d017074000410095019602512a081c10003042500301400a8003010007400140107920110f060b1604076015640d008081e05a4001d0502e800e051890802089540c140101d05000782160340100d1280c9034a48140d5121210205c10301c41501c1a01080c000d42203c1d502c81000740a1004800302d000204c0e8401c2004c407410008585507510542c0c0022160f5a104100ea00101080503070f410404070207000e0508003031112500340000301e28940150301c4080101354035a400b180710340740203910000760290484c040d00d607035000480f08140e0301c180410318040080c0d926000181010300c00c0c419120024610743c1d03084082880c0400440152440c01202141b0903540c0408002d03080c0c2d5160080e42c9401c1c2c1d8400b82045a0509503030a200c00310091000d004a641000600000360880d001c85070341d51790485030304081203002d0034112814040c1250080d01803243c4070490603a007100340c1c00740030300c03d050400a221080303e2144c12400d039101c0e44 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 227272023 1250 227270773 227270789
    0x120204060c0b0f0903030601120b060f0a02100504051903170a02040e0f0603030313080903160f120b0f0c120709051002010c0f0819110414091501050f09030303040506150a 75
    0x1b1000c0745096100b85e41d55003180140c5100482d428007040001352942d80116225500580300107036003c41140c06010405544959800820191402e901c1d0745448a0017000c07600c140c10b2a0b00c040c8070406003e00c480e43c800600407a03815802e0f00c0c1c510300590017503015001d682043c08003400054030b0480b11382c0100b1301c180c001038091415910750000304039500c0411001255003600c140107103542902c3c10000c500f00c9484039035a401c0c0b004c0c40d00b410304040000390f8001c03018640b0541102c0c00414000032445030402c3c00b0701c0ca0103805644645800c100c0d405001c81030085800603005212110b50720006030b609440e4111819010590051400ea08907080c01c90b4480114071200c0f980c00700320380a140500c0e442443d1814080d100c404ca01c04c4d860444c0c00880451113118001325040c016400070310983c180c019400c0c2e500c9061802c05804e03c030b04841c070782b14030719040200010349680c101e900e01c070039240d03c0032000d01100d443c3e083ca0314201d40c40f840215181c109075455801101140d03e0210380001c2212028 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 227273273 1250 227272023 227272027
    0x110c03180f1009140a0312080601030509030c06010b0a0912060b01090504180f020f03010c02010516030e030d050903450f06031003020312070606090605010801090c120204060c0b0f0903 81
    0x30000c07441c68240c14020099205c940d007100000403e200b0f0800741142586581da411103481e00f10000340803500c1c0904402d506510502c18400808000070300d0b1810340c0d0001c2e542d40c0e110300d0321031011914407420350001c0c8008001c9110107002c0003004d070000d1040030000d8076090342a980791030074402251019044c800914100e60220000308000740000e01c0701c0c0303001401004002c1c0908011a0035103200f60803560050b0755030300070020782e41010f66210282d190070341b070148440c156903c941641c80c0952202c03204101e5440b004151001010421940c8a0010b62000007a17410301c8880004204d0040d007030030082540e482c1402d85c2c40d00c1102100311140350010b0580e480c608404003071181640000f494a0300c011a1321501002680d800c1140f00d10440300c03030068654032001e134a081b5041d101c1e0796002e070040d40d0800be010702550707070040013032411364500c072400050380201244100c0300c032003e03100f422181e00e100150102d1259445032110300c10754041c003a4903641d0b444001001c0b1040004483c005466001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 227274523 1250 227273273 227273279
    0x9090c050a170402010212030c0a020f0313060f020a0f08041503060806070c1a040b1906081203042a060311040503030904020c0a1203320703110c03180f1009 69
    0x3110301001d40160040c4112140440301d1201051190300c1a1000f81c01c27032001090f4044415030400100301100c1d40380018500b07209110540381c018050300e02849041c03000c060141001503208100c184003007508491041006043c500300241c0940c841d000303200c0701490314101440c215000f0702400d0110781c00340c0700800c4150380c1e014080f40c01d2461403078121030b80400b1109030046401340351a203900850281c0b0040c0317600d04280403c200d012055251841425082075810000081c011580b03058062401d4500390f0b130380d52a8900f584c280300c40000d081c48900c0000c406070005441201c4c0751000c0c0c40c0c150710300300411b041800703242e50329015602c20942d1582c400c000d440321504098001c2c203012943e0714225250820507540390f001501c0c3d141c040c100002e80d1500c0e010800c40724501d015140746007102080c1c2c290030b031a80220300d103080d00034032450a054481c000c0310b104041001c02c0702c19201004003520340319013150b00461007246684a10358427548106149440d50329000510a100000f41d4407000507640c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 227275773 1250 227274523 227274557
    0x180501091a0906040c1406070602040825030c030b0a0b060a0305011404021213050f030a1d041e15050d0b01090c0809280206030c09040509071202041a1009090c050a 72
    0xb182c1079500807d0610041c2d00250460000c0c0c80501480c0001d002a5000e81811a1401100000301070342440e2030b100410205962007800d0f000d40390081051144d540e15103103a42c9c060312110b00c0b983e800540c009001c5548543c1648844e050b5200644483d040b0211041084180c0c000d004450044000032000f00d0b240300030b43e11181910a103c0d209540ca0198910801c1341960048a9000702040c0b0f0b50001012403449440101522142140d003008614008800b810710f45c00404052444280c0c2c0d00e0070a10141000b444540040030000c10782440c0034103134a49280c140700c0a00c9020650350034107410032146401140003520400e07174071005006070000d4016240540070700140010a413a418003501c4090b898480c0114072850550420f5951042418244011118014060342c3c05d600400814000e003420300741d0018106404440110f0f030410000c0600c2560801c007400c1903070180000300300303080554110005400f103070740c1c2c26010000000404410398191103050340c0c06001a6550051441c0c9070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 227277023 1250 227275773 227275799
    0x1050a0c0c05030d020601081c0801091e02030910050f0106081911040b0c0d1d0f060417010902030d02060114060a020f0a1b1a0904180501091a0906040c 67
    0x703004200c01c120007680e40c004a03091242d000075039001600a10014084030000700408a00d800c1c096100482c550b2074410014040748042c01240341ea141c0303501441003120310081d9483d1110002c03540840d030340d040500710256651240910a00b210382403000040c12100140c480c14129881030f00e810032990303107010f00c8000811810903070b80c1c0181d9541c91000c602d81555000b60001d0032203620300c20f40ea0350013001000c0c506145002c0c410100220308403549104880b06011140401e4180c1d41080f180b4141000500305000e00c5d0004410b23240701c00c0c4103444045054000d085840c0c026401ea031071f5008010401ca0721381c8024012210151046846486142407c00050807020110f04c1034075595191011a6424498416019144001c441d02030203041c900100746c200041c80301000b002d001c1c58408828038460300a220301e5900c81c55071400709243c0e07449580e002000300381c4e00100070080c2c50701a1819299123031040380c0e50804c0c503001c0d40c00207000c440005401070089400c4041e441c08989002041c0c0e40103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 227278273 1250 227277023 227277047
    0x5030f070311030a180b0c1b030c0402031005091b07020d060204080d080103150e1002070c0305070303120c110c090405071a04090f02130b03060a1809050601080c01050a 74
    0x444040b0001c04038080900c080c0a00b0380d101e6840e030030054015085080d049805401c06041020108a00c5820120000303c21241c41055419021503510030400a0305058a41d400f05402c11700000402881c1e202c0130b14410b059841c211f07207220341c940f02c50f520701154158032800408905801c000d40400351400d011040c4041c0e00c40c04d009813405448007601410a100040c254011944000040c0100004403145100d18a14800704204200e1510a4103603145507010246051945c0010071009020701c04031200051500241152000b83d0b49190040c040d0700804241c1ba40c3c1c5140c803c0680e89035202d03003401141c1c4003d640040110202007000c00504020141040f9450312583d140011500480001c4900030414402c18540f80c0e0718000600b000c0c0d8110f070120a0145104014411010782c0c0c0c82200e80554088039a526120307941ea0012500c0604542c03c89848085108000c000084154002c00c4d80d40d403044085e00c031035990310101a55600c550410031030214000f8840c0d0101c55219510448039 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 227279523 1250 227278273 227278277
    0xf031906060c0803150a030b04030f03021312020d170301030507140d061a0915130603050a03111612060e0c060f0d020f0a020f06090307020d08030705091003060812030405030f0703 79
    0x59245c4c1500040ca0b0014154012142c01007404104018503400802d0302021501c00c0c1070544c94031110b4205111485030340d0040d1031440c00360030200030a6440301010301c1603c1d580282c02c1640c4140d0b940b0090290f17002484221054800c024010448d035074644c0d1600c12144000d081c80101007010b9885102410344ca01011000c2c0f1071440c01000b4564034138005500682581ca1999102000702d024420300c19020110510410706010040001030790001d05000c005416103420f00d8a2244040d04d0303410854030020466504034141c0e40415a5031240c5103900e61315200788000c0110f109070441c01a1901d2820034600c1d4014020b012104c400e80c45603000f40710103241d00c2401441d242261003d030865400414009005a000035aa050340303420410895411002c068007d608001d0507500080344400e002e0001010040080301140c4058020025103440010090660340e4001c00000010700074001841140c8603841000c4842804072607002c00c480c01190090044c0d4940400301641d04855802003900b181 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 227280773 1250 227279523 227279551
    0x106080c071203051f05060a0302220f0905011d01060e03010605040614030f031e0d090203060403021506040207020a120206040e0c0910030b03060a09080d020f031906060c0803 77
    0x400602e10141d114000900380e2400181420700900e822003c0c0c55030110182004444041403109a580b0010703600c0301d8589180250ba200c40321860000c5010000c0f03240c05000ea10680041070060105d0421340558010301801c0001d43c0e41d408542e01d8011a00f084400741c0540e074001481014414681034003070280c0a400072401942d250003103011103200703a0104601c2c561441e07041483d0b01d4203000c040c0b54900341400171070410340034a128040b0600c41e00c41000f0703812400100034a18144a41101510390380007420340c2c00c1841c2508010b5101c2c00904500b6101e045540d0014907107241c54030039940407036006415000c03005d080560905040b104140d040e0390200d800d11000810000c590f104500c03c2c0030804144e910784001c0f0052040c0b00c81c0c46299201031504022030881103803000194a507000319032000c04a07110791035041c545028030501404e264200e000041d401d21403441140214050014110310004849060b01c0c0c02d02164240e00030000040c0c5007030256004103901c40e000d180c001c1c0c00311081803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 227282023 1250 227280773 227280787
    0x504060f0c0c03080405011b03060f060f050d150906030b0a050f070c060504050316030917061b03040f02040f02040e010b1918230f0a080d030f1104090b030d170106080c 74
    0x1010748d01e402100c5030002c0c0c0c0311041403103015804030041c402040907080c1510801400c0f0740180650041840c600c125035035078005030400b141c41880a030001d22110104200c2c8640300c1c00d15092001c1c04035108617405043c240030500c40790b100121544101d00d036944180800026541b01d40142c134015100b500d240c4001d02a294100f000343c04c2d80e2088034844d880e801b0009203030031500c1c82e200d0b00c1c0a0380810550040820024490140e019040d9034503040c960066682d5202e1030051090707001600041d410506e800c100d509141c08985c01482640c0c841d010b00c0c10140e0340d5000b802c0b407510039070000000f0300201c824501d290314007c0c075003000590705100c84a0381c03031504e40c1d24040d00a82c0e140c0503203528895484409449041c0460001801c4409841d00130403a0b081c07032201650740032046010001c041c1d88454030401c00e01503500004880d0096a80c180c0e0701e55803040d804001d8400c41c0c900c140300e40038a06003107205501402d1880c0d9050007040b00c80d5010380c1b03088015a0764180040c50181c813604100305003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 227283273 1250 227282023 227282051
    0x301051201140708041a0c03040f03120603200409200315070c0b010e04030c021012050a0501060e011805041116120908070b120403031d010504060f0c0c0308040501 72
    0x1462042005076150400752034507052400046d0b80d0202503e10114140d014841543c28074012680d0054010800203010401454103c0b800c05092215000103031828901204100d003502d00c010000103401c1c151000c03064054200b0045981c00035006108100c040361015655100c03004014102c8d100505803102c10004214400b4440d100700c030540d0003d601c42c0a0b11081204201c81c040c0540407050340d42c0c035030b40b9260350081c00540c44400702910500030300410849540c0b08040c000c2e0014030009050101c1c0c107000c940100503182c00c0c002e031004181044d148241c03035449210f07886144c00075250b49604039450981400028010105105480e40341049071108031100362840384030151140940d00341c0d0380320014009011018a070085441034201c1d640030460300010380241d541000308032041704138984980c603003500140781400c041c038140c12402c0800a549901940700d18032941c05a042844843c0304298404119405c030318108001c2168040d6800c0401d11400840d84d200780b00d000000b03101d403042030340d07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 227284523 1250 227283273 227283311
    0x403021e0a06090620030408011d0d02010c05040905060d060e15060f031b060903010c020325020a031101030e07120c05090c03010b070618080921030301051201 70
    0x40d044009a0040e42010608118051000800703140ca0010000e500300a03009003e50110340f00c07140c43ca8059060340001010920449000b03102e010300800460f1200c0305170716001000141d01c0240c60050308002c104890060160b44182c0280359a018502402c080e0070300700030f080241031190008031040202c00018010312030301a034230900700002d10301201289040c03940210010815805885600b566081540780003d11807a11180840c0e1010006464004544103000b1698216403640c2030080740d201082d008401410082e083d1001086034202d107034185403040c550880000d421950214007040032600700783c01e0300b211640501d40462800b903011742182c40d0401a4010380c060b00c0d10b030030003001040246031813000108001d842e1110140741008040c1c0c0366000c14410005802c00000d024420010709a0009801d9003000003851144030403070604494540005607424040c048140110500c402007843c1c0c1038044001318003c500e56820320092103142a021146080c403903480c1e91002003203a4000c08 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 227285773 1250 227284523 227284549
    0x3112409010c2c010e030d0908070e060312030613050117010b18040b1801020304060b0913020d02012304030f17120f13050d0e030d020f070515040302 66
    0x44a1a90926200090031220340c0800da60a02c00e20304880880300b03a00c0d500b01c8a0309024045038001a81c540e40040c3c580e00900d188059140c05030b11108050b00d5044400b42065502520807600903613246c050034482c6007401d4034000d60680c082d0f5804030040b100030005592102001d440c07080c16600240c00501610000c1c4c220107413400c02068a4650350000b44500211100b0031206035001c2c05040d11250342028000d04041c2400010701c000851700802d01c00ca20070202140d1000315901d01e4141042c40007442c940c20094480c440c1c20f400b10344a09104086503a219400401c3c142c840b0380d00354010b5a240b40d5001107007202c540130300408091980e031507000d4801107001d003a4015a1807403070300c2c0c00003280d00c219002c0b100c0390000784404012021124803117a4868007a401401c100c5c0c9911440c40c00036244031000030043d1003110580403445a0007a2030320710180c0207030308582807128802d6040c2d0f1a003003000d504010603070204004010030700c0d0010081081140001d2403070319190f101d070045220100e02c86 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 227287023 1250 227285773 227285833
    0x140c09090403030b04050a0e190c051207080d090906050105030108030a11100e01090218010b0a05090d1e14120d09150507020303040c05030309100e010905030f07061d0604030311 78
    0x1014402c406418056035140703111400161050b0801aa595042e80c042c0340510b5009033007800d03001010300d1003005010080c150810488102c0420164020405202030141c810030a003400030000d413550058041d00e044e03030040d401460510b190000101c41000703070020505040d00c95909210003205451248507144020180007244001d028018043e80f013400603445020f50800000400901a01c3c1050744d41e50101450003950361540030000400c1c055115401400d451081c5c0c58242d8211031030424800d54610a000c140c10f07080c1503031901034039a0007031129203000540c10014400b88003090303807003105994401c00f0f184181d00c40c0c10301d0520403264100c0340200036034000000d000510415200d1207005020031401103223062201030106030541c107298072a031700b804584002c9980c942c0c06441d103100940030180c03c5908480201010340c1d0b8403071440c45403d000c948070098000341c101c420103e010342000c001c3c180915003031a55a00301d076212600c1a42e10010b004540310328041080c04c890001d2944881 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 227288273 1250 227287023 227287031
    0x70302130903030509030f07020112060b210603120a141314010815010219030302121005040f05040b0403080c0c0706030c1413030b10080f01090501140c09090403030b04050a 76
    0x18a0043d0485102800004450384244040c034100903800088994042d03081c6050f4503800c00006403840a03041035080700760ba0034070106110081b05043c0400d60005122007050040f261986024542c4070040c50800640d07a98041205418180c006e9107407070240c0d0226004c041c600582e0b0743c41024901500d4015022079921010058201c0da4440c0302203800400910100a800b80c0d0320f40042d55480100402c440075118083c042814540aa0705544650080402008a80ca40041094018605400b49900c510318105501200c0ea2892042510807a4060b201109507115500c05440e02403005050300b400b0700303042003020104401800500000c0c43d5075203012940f54400071018010750702d80c0703581e007480d2007040c40940302c0c040280d00800c08036500080c4205c0251140c2140d00003101050300b00003042c0c070444494002312207056003e410350f02e00660003004017a00c0820842540c1400341c0380426070080c1400304c01810f01e4042d400030f4220b44079080004075420458040b41c02d0700d00c00c8a1f600b143d244c0c0c0e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 227289523 1250 227288273 227288291
    0x3010213090b010809060109050a02070f03083709050c03030406030c08180d0f02100603050303060901140d08030a140106020d080c030601200106090612140a08030601050a0207030213 80
    0x12034015000d050009092910051410645c03e5903256014400c40a299490f070020454920042c0c0c1200c1405410800c000010019030038060170750071040d150f142d10700580b01003030810700d41c440000e0030a542d00d003940c90721058032407482d440107401c44290543d007500540107010956601080104010105620081000d82d9010ba0103009170100401191510b40101030700c4074504c501040b10025000c05003007942c80d4203485c1104a240441f01310100c40110b25002004c81406070010145115034070031502c40d8026030701c5200d00c141d54040911042e401c462040301c610300140141000e5640602d61100004408d2140351540c0101603003a8052800768001c41d03640c3d214a680054001e9000c1401ca008a145040c00300009151519a080404080c2010405070000394800e40106000f007052080a110f441d8542880026001e20f4050450303a102d408005801c1000c40803a90030030503034220043c18110364400005403056844007401404502502da03003c00140d40d5004000b0001c0d60800000412010b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 227290773 1250 227289523 227289539
    0x904050f06060301020f270405010609140a06020c09040312091a06010905100c0804090f0204060f08090706031821021603050a0210020f06070e0f19140d0203010213 72
    0x201c00742005020740d0040003100c00d84409001202c400c52403015600400403c820080c090101310b943c16180d1083c202000010b2b80f5502000c0381c02607402400030350240341c600f00200840c2e0b0342e5500c688070160f040528400e0852034811450b41c1d01601900b0003a0000381c0c02c1011900f00c962950307048800b1210440004522021031030f0646d8880000c1c203090700d0450800c030000e07140380300c980725150811814200900c208804031050700c00625100c03d0a020b040302d0403c485000e074200d401040d00080d000c42404070264890800075025607111000340c5120b03410424214080c0c238001e154aa54500c0c1c05200b0400280b1079070b40d05803042040c40c80070348000c850074002400e01d0010f006000001203205418004144042800c2c43c0c3c0307d40c111100d4003001400d00090f402c0404281c0d403a80d0500505003000001750708140c0c4019079201c01c07508040c00c090360b401040503c60448c104455071070303003038501802680c3d1480d4405c0c1c102d0f000100312000c5440c41d030b40007900360f900020000012110141040014003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 227292023 1250 227290773 227290783
    0x2030c0d0503150603090606040515040515010e09010e06090a020f070303050103060f020406051b011506020d12050108030316030609020d0b10080403020a120e1302120a0c050702090402030c0904050f 87
    0xf460494666195060500180d961003202130400c0784203640d0303000804c400340300807011400c11003005013051105140c2418030072105068900c159011810411221302c003480d000d0750b0f030b6060700c03540d840e112090f0f204c1e80c0910880c041c00411501c00c03160700300301206c250205440074040c0c0c14460ba901040c41e6046107048010780d048120441c09141c010310040c000c5a030000e068a1103449080703e400181a86101c8042c09082142051012803c5660b008030f1700c150301244902c078807440c1d5100c0004118042060604070b0b03200344a403610540091001c281c0500d803020019182c0300305450089115500c0740c041d8000c9030300c003103120404155180e01d68181c03801d08100216034802d481c149410f1a180c540c5001e920340949850090a603058100fa020304180140f80450200001070950600d80b071551074080003d40c040002c7c15107000d0359000046514801b4050f0003070064031aa0b03010300b0894242e09002c43c5000190040f6803501689000d820540c49040f030041c031030ba0142c4000e017058824507840c64100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 227293273 1250 227292023 227292061
    0x50412090611100203060d0f050321070807050901090f0801150b09240d0f020a1b02031e010b031014010f050108010e040816080a0306290a02030c0d0503 67
    0x4000b60301c46000d400140481e050203005061400903a0300c0d690b0740b000443e001c041980041c00303000c41e03007022028028000302602581e20380c196480c04010100444055419003160342000044038400005d4a5500c107502800010300181050020703952210385080d100240c035000306205e81c3d91380c01600a4450000b041000502a030540c81c0d00d00b084850229100001d096040b4402c02c4460004102c008003860840744040c8c2c01c00820000c0000e05000341001c0d50280d082000025040c3c1410001049503a01070380380c0035402001032100b11325000a180b19403410040c010402d55030361903a481f950300c0500072610043d5644c03400041090340300301d004809032010b8114200180709402e00344101e903002580c82d4152240032640341d5650b0387d189070140e0f180c071464404078444411401038000304140074025001003880340d00c4c1841110f88400610030f40018200044496103002c50a140340c0380303482c00041c8140c2d0f240d031054a1420180020040c9003da00303018400010340c00000304462810048030454007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 227294523 1250 227293273 227293277
    0x2040c0e100305040512031b030108340306111e0301030203072405070c1d0a0515010804060203070201060f0305060f06010504140f19080304140105090a0e040c0302040504120906 78
    0x45410f140c0c9030aa03444c5c80b40704d80d10318500c00000c04545200123078000500c075070800018442d501c1d0f841da0389054440e4031129045070740100400f8441c0807115184d2440d4044040d0b035941c69030322880d5072074403c00340000460301802c0800c20040c200e049000c5001c1c455080d500850100c2e41c9515500c1071514001540e4042c52490f0110804004041c10540c40f5003014a83c42c602143c0f1021707107041c0044180c001d07a0100c2c4036803035400744035100003e424505a12070113460f2010050b5035208000c08403541c0045c40c1907400145071000084c00100d16901443d00110780c1e100000d0050784500e2030a41c03c00e1940c01c2610303540c1c442000c200c0e44614460358076a00803c2841c00f0790a00d8680110800089034910040e4803a0a4140e0714101c40d0b1950603000e02d070030794846030304180309036208003a075200d41c4180039000c81c03055101e03000c0103154082c8044450440e006400308007254078000c11003600f581d0203030044448140c02080080942d4403030080f00e00482c00390b01070320b201451000c4003a140c5842540084c003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 227295773 1250 227294523 227294531
    0x1104020a0c031101150e0709091a120309090103030203070605090114190b0603072a1703090723010f0c0b181002040305010501030b0a05010b04090209010c02040c0e1003 74
    0x900c0c5903201111401c403035418242004480514080c080c0034280c0c29910082c0700d80040d00000c0c2d4032191030001c07800345c2525190740022a40380d104040c2910071800d8941c00c549031001074910b86007071482105c2c0110000c0c00c26242800318210001d0613048081c0c0c0142c1c0164008100c0d0020300800e0700c1020b4005074804020002d048503040c61100d0b0f41401003626168130060350081780d5800844e00902c21400b401484c0641d64900014042d1080c1131101c45000e620319145500d040041c104905050200e07044803100d4200d444000c5080000c3d88010700b404200d02912200090603d00320f00300f541800581d07030207410301108a00c001040314040c0e02c400c10030040645000301c00304889441d80c9400a00104854071111030001500f40b80500031400e106602c0c3c80010000280300c0c0640c0064180d82c45400602d00e20303290449041d0547c1d900703002c1c0b0031240c002040100030800c803d40c000c1154031818108105001141d4001134200d030413210030301e00030409030132541c103592800c00003080c04c41c1c2e081e0800704 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 227297023 1250 227295773 227295787
    0xb030921040609050d11030115090c020c0d020609010909060603020714060601080406020901140706050403020c011409010513260f011a0d08190f080112030c030e04180f110402 77
    0x1080d480c01441004c1c018518883c1c0e80044c01b4904083d80c0989a019009008400600e4190301041542e4400c103002c50b440c00da030f48a0018400308224000c1100245442c500240c40c0d000c02007a540113000c068140809440b0000c1c00c2c01c0d03e4002c041c0100615140180c0718501403d2520100403e450b0903d480c0d04800100103030b0303a80007880c46030440e8010f840181c0342c444020040e03030082c4601e00900c00e00e40010a04d902008004d400091140780309078280d84590510200648501450403000c0c505904140400c40d03403544180007421b11031010600a03c202039a802c80e100000040a1354840b65404851448000100401c44020a0710380303000204450060b1845082d0510080d4a0040c8074084039280707001845248c2d42640e03882d156800101d500300401000140c9801144910070010840203000043d6080c0c1902d481806c9079015100e0044207070b51a9000c9865a203901d0310142d02c1907940300501c01070055140c1c00c801051003070b04040e0452025080000f05903810300021072046004000203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 227298273 1250 227297023 227297027
    0xb060a0203220f0e09071508070507150906020c0c01080c160c17070602010e070308030c1c020a09050102070902040312110102090402210702210c070b0309210406 71
    0x19040ca00681c040c1d1590304a12600e048180141a0310a20302c2c40d04243d00460001429035040d40140070340e03021601020386d6030b424200c09402e0302e590b150215032110001402d9a028030001c00c1404d200740f0035810001b07010303003001d01100c40b5a1400d8540c02d5000c201c2e500f0881c020072410000300c0e02409c010b50b2a00d804480089680b14118030800803041e00f521000800003030b040d01c4800b41a40f50b01e0000081c2010300c1d501d81c1d0310402d100e200d0066003080f94003021200301098010a0725001013000d460341d40ca00440c0c90240c1e015082c079014415540140c0c1d808074010b44040c0824401c1590b410400c00c0c87c01000a18261458000f00c0010b8810001000021b01c40c1c20145100403d500305030f003602180101c484d00a0181001c46904a4000604000c242440154455141040c14402c0004e5214280d089950b42ca110942e1650804045a03c00380d8148010180c1282c280503021140900d441d1401d100c041d81044d55014030560003111000d0946090001c0f400802c41441e11042c01e0034500000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 227299523 1250 227298273 227298277
    0x80c0607050a020a0308031f0302060a030504050a14070801060602060915040c092a02030a2a021504050306180307030302030a18050d021c270e010e04060b060a0203 72
    0x505489040001080d10402009025008110360028482d410b030030364038104464207600c02ca40170f085c100f640c0c0490881c04104100d401095030b4015103564101000d034001600200343c041c0c01a60b10b80f1612440100207000040030a10005c80d070000b820502c0e1070301e0304060954019810040954000300304010791140c00041c900240070300a04000c1081d220b500340024201c0c040e4000e40341013401c2c0446070951074511500a00c0c501100c02401d5018802d0141c1203851340245902100014101c0d403081c2000031900e4034080b550810103a5211140d00b5036400036508000c08284a2903050000c181000305c0d140c02d0085940c04000c0000255003d140788010035142d11861000405050380800407a01d491040e07840b4078001c0781c49a000b00e900800f941405591118441c08007001031003010011b140e01000b5002d41040d2549070303190100074030515400b4140f00261550081c1e00d40f0041100040c0c4000c00001850007800d1000c1c0385230150402c2e0a000c0151410721078940e0081d501080303045030041c4c2c0001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 227300773 1250 227299523 227299543
    0xa02061c020f0406030e071d060405100b0705010509070b090901061d10020102090901090605130f0e06010e0f070c0c050103020c0c15090a05030c0105160303022701030e060108 77
    0x201490824519460680003401500c01442c00268003160114480b0b4055001960714003810f01165800382d0b03105450900c00c21168000f490071300c0301c880814001d0800c0e07000103420881103000b80460f01d840e034105c2c0d0081e03000130302c042c1e425a446105001c2d020600b40610000751035020b6480b4649640400030450004041c410541007080c83c403007280c2d001400170700c0c2000703180008121900000f00c14400030301039001141d000e8440c0e002c51000040e5500184120002c540d8080d0002c1e489025044110b0018119039800100d42512050052100b010501a15010700011051503809041041c280101e010b0000c0004003402026014403021500301d940a0003101c0003442c0144c0e65039104102e19040404440480750007801600e854a143c44003240500003442041d18030382d120f03640d6074082607a030720103c42c0c5017408200100320060100360404040300301039009003009468103640e64504c400000c2d841a500c81d0070301d032241d4404e08943e418011400d0480c07090005003095410042c0316612480006c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 227302023 1250 227300773 227300797
    0x405130506100f110d030603120801050f120a0602030c1b01090506011205100c2307020a140111071203031805120c121b070b0301120f060605041b0e030a0206 69
    0x36149808a500c280c0f110420f00458106891702061100700c041d003e00103074003040f200c0c00714201d441c0c019035110b02c407014122034004002031000071250382844540d0b03008984503000740c010f8061900100700240001c2d402140c84c2c0d10a03980e652509410044206400002440d0603414401000081100054107a05450501003004155903080c03038902d1134110441c2006c82c6440c00c15980d24046500202040c004089001e1102d03035403202025401113602c02e40400a40c04100e41505002c107420b0300000b54044c94060400018400c42024200d00e004076550003641c4100e10850740c401095454058004050940c002d400001a06591426100c841c018a4406046808a01483c02190420148426900e4444600e42c0d030703a10003880074080b011441c6811032510524000207a0420039900302d80c100c1300d0900c0071718210301d4540d9802002e40300c50001945c0d00ca0f12001d006c0b685d40d513144201c1094002c138007000440c01520500140c407000701541c855110740c21880c540400b6880300422210082c550f9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 227303273 1250 227302023 227302037
    0xc0628021204090507031e0903081302130218060c07030515130b07140a0806030706020303010f0b09060415020a030e04060b0915120103141c050406030b0d060c05040513050610 77
    0x9108030f0052001c0d0078425040703e942d07c1e6019680c0e030580d000c518040e0096940030429034814401d001c01c078012481c002c0d0416100441c00c0184070159015060310012116a0310720362010500184050700440d8903403030300b50002602041040410009000a41610101320f40d441c0390000241600307110108002d09000f03003180004649034801c1d800304120740c0d01868016112190303c0c2c001001c03200304503212030003403096000200b80d07980000103490417540c0a0710450400d80c240b8803160700c81c0c1c21150085070810f0b42171002040055030541c0d205000c62450b030040800781100c0c100108083d00c060030383c03802281b400d0380074410a0407510850342c000905403880d59140320500c948481c0c80c81801c00e89071036013100034004400c21000001d040041d81c1d200e000c8411890000d05a141b0058580400e0720219104000821005000b504544080f0300c004169240c03500d42ea0325100c00740d41290341c003180001da00143c1482185080c3c04600040910000304100d6860044041030788541180680020300120b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 227304523 1250 227303273 227303281
    0x5070201030b130509010227030d0c0f0204110309010b01090509060114040801020a090303270302010c2a09060b0f072604080606090717010b0c0c06280212040905 71
    0x140c016100075203544214200300515010251704c0c000c1d0449481c10020700d581c800a04413403074080040700c2403000002d01400c0c8001d000c0b4825500c40c10000c900f150b0580840c84207201680c0d5078400c41800d40481300c09aa41c03840d04043c00c41c00c56940c030080724180485010709201036101d1b00f54566000038203003000282c16190128000311801280d00c0a42290300001d0703c01c0d10217500888042c1106c0c405c3d03d580c29130058091200d54071400e00300d0000d032401941c180810140d84105403015180d40034072070108002045100d4101005104400c051003240c12840400c0b00860f50320030a80207000c88299542084000d030035141d028130420002034902c064403c0d000303180f443c030138010110300000d91045c0c03a174071980c1d03082e00c13629035100f120000d00c1035803107900080955000311042418105900c45441240c0e090a03841542500300c1041c810f0248980d004007002502d80341c2c01840c0c800007040400c40c401d05803040035440c600e02c910014085412507071100040a00000030b9405a4035598408949540c0e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 227305773 1250 227304523 227304529
    0x1090b07111c200f070501090305060c0d18050105090715140a14030f0618040302061810060b0705100c05070f03030b040501140a06020d020322050d0503030f10030305070201030b 78
    0x1128880003040c416103c411803070210000241c54421036800401d58010340e54410040d503012500e80710180081e04490b00144800d10080010700c4001c0d48044001540d040d80307030032000314904804080760903a40d69001d1144200d010400c81000b44880f148443c0b4000d180b110040c4403000c2040c410301441c0300441c2503c0f00500a080c0c2041004241001d00c2c1c403450000d5001104000940340360b400303580028072034003000e41c1c904403170341c4965019001032269899491044036604018030304003005001c0c03101140400c41c4c40f40a89c80003080d80f1403401e5181c4070241049424280f030046000129483d10307412401c0f00f0340090513a440c107500300c140551551f02034201030300a07146403801070740e006181c00e002250590301c805100040c008240d841c0320f440c64651170281c0c2d40e030030090100300159105000c0074031421406412003c2c3c4d005030054508035903a844021a90b12000e08204803266000071041014440d00201515403080001400c2c0d00c0b140d2075500c003d03249214030f40c0003a04242e200c03048010161 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 227307023 1250 227305773 227305787
    0x108060a0915060e06070305040506030a0b030304060507020906060711061b0105070f020c0a0b030a1a0a030b0412021c141c02040503010e01020319150b0c01090b07111c 74
    0x884201c00748a0045035031404218550a8016040814000c9001e46602c0c1130072800c2d20080740d41034031490700d4036040804219a40c4c0000381547c1702c00303480368051482501c0600280c00204000d85070682c407084644104519003c3c001c1200307000d00000d121601c0031a100c00c10099004a0688031140d40c0c494110031215440c042481d003904039807c1c1402d0110166001c981c5484040090b820f0b181501100d00c108266488240304d8103254410600110340b5001190b0320011049461203017204c4400c1d00000404c18410040c1e005880000740e0002b0030017440349402d14004401da00344043c00c501020148203406201d00c80700720108200c10100d18020440300798045840302c0d1240f1400130b14107003140040380082d5009000d8103000713508200a81c86042414001d0768041ca0100c000ca46075050100401c000a01209030501080c0004010004800002000070842511140c0c0045080d08681c1400c0010b05c00140041c820020208104510444049005002400b0410780302400c00d40b0307003400321100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 227308273 1250 227307023 227307029
    0x10e01021c09080f071a240405070e0105090604030507090b0a12030903030509120115081b0319020d0803040b010e061509010f0e031608010501060504080a0b04030c0b1905010e060f0108060a 83
    0x380d66010700c100c004003072147c41c42d1500b04030304c000c2d1034110200034130080d14001c1d9608404a2018850b240380380d801040904a540c80241c21107040542c4c0380c5826240800c160300140d40e031944c0c4d04010074103060104100026004050300c0d000c5c4485507076802843c4455910010f000c01c00d02060152256403407100c140462503055000f40180d03c1020401c0d0851000c07845051f5141c4250016000d01c0501d03070052510000d4020058812400e0b001450454420340807812079102500250400004260002a601941c05400000103a604000801541d210302405a80c89240070b9117448075050303d10001c403091040f0a03c0c0c03618001c030000350280d50540300011807582c10f0113944220a07452444600031402c40304100000c0c000303640d03541030a440c548114054240075030000302e00007001c5419a40519000f902c00d140c9684038151984510304980e0041c0d80c101e000c3c000d4200c1c41c120344400c600407580542100c810387c5c01c1e40c0c1000c40c00242d010035926881410b010a43d4005440ea580d014185801 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 227309523 1250 227308273 227308313
    0x1050c1c1802100201052e0b0f0403081215030111040618090c02160e010803220f0b090405070806061804110a0f110c01120b040b03010e01021c09080f07 67
    0x41d07240c483c8806400307040d003110864811081320765001e0314078804c1c04e10030611072880c90600480c01e05200e06403125501400000052190401c400030000d418080201405c00010029026a08008400c59101d07840081850300c0790381000303403510408402e0301c01c139022140306041246e0016800b8001c004080300e940d104000c0c06103021030041010b40c020070b005400c030802110343c10140d902c0700301d484503d800030b0144c203030903a1003444900380060714003810903280d50200d0300c540b40781c4d0303a00c1449419a0302c003900305040705040401c5803141c600f018040c0329000003180c10981111301c1d000000c19200d0094000c0a25000640181ca11842d03c442e404115102c0000c7c3c1c0640daa4610041c0c094034019079442c01c1000148140840d641c07101c0040740703000c010f2005941e100080d8054031803100141950411103036106a450a508150365400d1245081e01c4001e14009600d5001400b030002c0610700b4294141542d0f400c1c040e803600026604000c950340380d8094007034191039a041c0d00b00003ea1032000204800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 227310773 1250 227309523 227309539
    0x3050c181f0305060f03062406070f030c03030e03090d12030f06030c0e0105010f0206041118040c06021006050607020d050a0219420516080c01050c1c1802 68
    0x282199060b000f4910500701513030040c81000901040c1a92408221039030410344000c0034245a82d50700c0b0100080e00b00000500041c00d0201c0d9440703418411011900850104401c2c3c4008000c040d010300076070318000c11400c0a1818484000041003840d0b80c4060014200960460b40718156402139229103141112254100000c0e078491500c40701207881c0d4011130f1411f100b84c0c4000591907200302d10307115054001e54003410381c586855807606074402d00e050b03811360f008640ca030303045080c0940c403034000d44aa800f404869030224507101020342019130150700c24007440d0408034240030320340300c41f4125002194181c40c046540e080b13034200349043c03a1002400070b41c80381070104009030340c20085485005a8510346201c00801590401413070240c5500310502414841500c080e6180d4010344803040348440c810b0410358079008000c54801d04409003000c08503080c140124014480803400d10445500000300c4c20401d1600340380c1074101c0c154500134601110816202c49a07441e1984030000d40043d001d40c0508206 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 227312023 1250 227310773 227310829
    0x215131128031506030201120203090c041a0a050a050f01110114010308041509032a08030a0201060f0b03010e011701060801020f030105031b0603070c02040212011203080703050c18 79
    0x11052142d01c0140c0740c44211026403440e02c69580702e0030044030360507102c58182010b02d09800010750030081c43e40002d0b0180403c104003a44036401202042c4091240c055030094a41d02000803403030310390b00054003502c28007005201c0d40c0c841038106041d282c42420100b001c8104044054050059078034400402342d074400000080040040143c001d4611a17800301400400c010740031603000d82c0a10005c1c0c8070454400c0007000e041c0035500c2e0312440304008030210443ca61610210b80c910761100c154000183e6485104001081c030342585c0b02c02429549422602c0d65150515504c000d89040c01003070b584600500361030400080942c00000103100000087d5101c0e502c50402c0651500300b442628001d002e5080a841d1441d40c0c021320751800c14000b0704450a50302c6500d400c4440e0000103400301c1e00603500b0002080c440b405182d4481c001d201e01c0e51040034682c100c2c030b00144076280152510040c5402c03c010f112400044900361a03003040640c00300d2420713840d40400203541e140780300220541e010154040c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 227313273 1250 227312023 227312089
    0x80705180a0f150809030d0e030d09150605040605090a1d06040c060e120a0308130209010803040f0e0403050403030c020a030b040b0f090a0c0e06010c0c0b03040302151311 75
    0x6001203074140b26014401070016035051324105002c84a0003800d030002c10070441d20000d503a202d5801c808484045034141410f61011004882d141c1d00b059481c041c8115103034040b1000e5000c1c000c0902810744091251034075003400315149480161130301040e142c4030744440e0303070701419000d004102c003a60404441103410703e424000c503014002e0140b0800503484070b8549085050001c400c08105011400609001c0d240d074a081b141110090005091380303c2000580025a603180f80c2c0902900c0400d01442d0b5503480c01d01103646108203584031150603031040c01040003090700075099070122501400e01700220802880000e12081e002d0b000117140090350300c180004e00c109860020300c00d81c2d030040342001640700c500542c0d503203500c0700c0401040014001414060483c1c031070022a009003041c100a090f141c0941d960381d406007074070b80086401c0341d0084100010b05504000c44000000302c0b1800e0902402c1c035580c8000403180c0b138040a840800000080406900c8040040c40c0010303005007003446071000b4450f0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 227314523 1250 227313273 227313299
    0x7090509010213090c08150102031207020309220b0f06041217121b0f0409150b0705061501050301030c0620032a011401120305041203030b0108100303080705180a 71
    0x103000009942080010701c0f4007800000402407d130140c00a40c01c12417400040d0015a800502c5c84003140428003d03058607481c0c1070b00340401c845802184440c980b64640021046600501c2998171504d4081302410306038944000b190103548002c05019248186820041003128820000810280300042c0007419181c0c85079080307000751042c0c100b1303103a288840103161010b8010b5007415a003058081008001000e03055000d40041c40099500c15070241e994500c40302503400c111000e0301c03140c0007442049865800043d00b005806000d007800c504550642c3c07901440500c2c603015100a200118150300c84c903524805180440f145100d040343e50b1000c24280c54400c07848000c010b00e84d52660000844845041801282d10160055440300340c247c0c60427642c410750801404054041c890104004a15601041445d0300c4803402070310081442e0513854001013900c00d008021039518507403100b040c40029400030259400a0091500c1911001a41c01124080c03626a88181d40050182030014602d903000d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 227315773 1250 227314523 227314541
    0x21090c0314010b120c04091406010f03210f030c052b1a030309011b0602130e13050c060a0513090c1116150903080307020a0c0603020c0709050901021309 67
    0xe00450200c0d0301804000b6840e960030782c02c13503044011036106a007410b52107408901c1c022014a800c156206000d90708098003a004100031001001051003030120b181e050704012100b1035510b05249421140c020312001046200b981015101c0c00d0b1801e119200c1d0302075071a005800c6880c8082d050400030b030520349100115664080504202640c01e0300050003144958074a0f014000e149804030000045501288203c2914902040442c0c0e0002164541c8040e01d40d0038001403900c88620300f0101032410140c001001000c0700313890b070312200000403004180d982d8080419141962501b05110054646000c3c2010a00c07050300c10002c001a5100c2903000703412051000c2c1c4030100c4810200d00340e00d1b00c0c2c02401020450201c034183e0204004818440d245c81d03034501d90f00c0c1401c20781307843c2d0b51b614a241e4415190072005038040f091500c02c1c00102c00c44d03180203200318142185005a05038046440300c0c01c0707200e6180217580d01d0000825040d02901129184000d00648401e0701d5241c010020003010491 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 227317023 1250 227315773 227315813
    0x3010c0f030605040c0903060e0319020114060619032012040c17030301210f110306090d0905090603010e010e100f1109060306010c0605100e1621090c03 67
    0x5000035403400d0a03c41c03801701500d03907540c1c0c9071180d00795120000603021120b154112071000708032112440315040e00142013160294008983d03114000d1000709210382c0980498487d070f1007001401b4070003d61240c01c0f860200347d410081501040c21420064422a4001c4140010030009001c0440010008014031991068101d000c0700c1d611410481002c00c1a070058804070707070040006000b008031450103c0c2c481545080301d140d8050171580c41d403d2544c142035086a0740c1e1a01c12540c010362038180401c0364000e130346400401e00841d07030020041c0340131064419140103030746070310200d00d894070b082d007000c07441500e208020b00405140351080e6564080141080000c035180145642032075146001745004215800c40f0907003000c1c406c4041005660001d000319052203294105880068880e003e03680c4201080419804130034900001b1000c0b14400030480d9801c8181c2204101c101c1c0c0c0c105030481c1c0e111a541a0b0700703110601108046000307295103440a001030300400c10000800c010208250ba85c0c0041c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 227318273 1250 227317023 227317031
    0x303031905010e3304060f0302010e01021225050307110a090b030a1e0b04030e1e150c12040f0512061003150f02040e0402010e0d080a0f050903010c0f03 67
    0x543e951200164050354650a00702c1d40e012440722a400c5450955001c549030550900709540b648000340480700c69500030800401d1032a410829580c00044002e0416001c1c005002c5003c0014905082841000b00005e40040d00d80d00702210034286004011030640d009088a9680a0a0811222040d4a410000d01c202100c2c500400c41909900464000c08d4000c0c00820810181c0e94892231681441440012000c0b0741141610100d625a0b080501840c000d40360b0383c0d4003202d59001d000300c006071103507078807000d0038802e800602c0d5464a006c0c1c8801c0708036200005844945c42a0031900304881c0310181c2d50300c101c0c049000b144071045940b251046420449001c5000110300484540340d5004552107190000030311010000300b81407072903c408651034081c00040d409245480d01080b030300312b500301170006040032003088115604401c0c01d00c5a000300321070f94451000580d0b12600d07039105a280941c200800c44001101c018082c200b52444154010000d0012074074821008141e40e0042034000006420 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 227319523 1250 227318273 227318279
    0x5010f0e03070c0e0a0908070312050105121203040204090b010801051501090e0a0e0709020a2f030304120504050a18050709121103030f122406090f03070302030303190501 75
    0x3000045a618a60002d4140d04035450304207008000c2078010103002603141c803002c1c0e04000541e0a03005100c4c0a00c030761a00c0068150340384000e42202e4050308507034000c1d1400c0003480022034001401001238140a1011075072507813a440490040e02102c0c1005000070108000480c0c1c0341d034107400c16442074400f00c0360981e800c1d145100448906c2d030035100d5010941741c840080307424080d0701d41014401203e04011618001e54076800030080740e11210100300050040a49624034032004070040c92049094a07200024041e141040c80d102d02c4003900085c501d490b19071285220300c5c0594160750051200a040aa200c3d80d501c14000340028482d11911000d4030f0540000c00044c0541a194156022280010301c1c100c00d503600d400d108200210303000c0c0e2500c41404410107966070319000b0400c40c00d510090070154186200b48540c0501d038800300307006108030b841380f8401c2915014141c800d4948122030800b4001d4400b03000c00d05101e0143c2004e03403d8000041041104004207195403550440d4140401c0142e036 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 227320773 1250 227319523 227319551
    0x403050f010216030c0f02031209010201051303020c19031505180106060f110115150f05040302090a02090616050313090915091509050c1305060109150c0203030705010f 74
    0x110301c1c0c4801d42060b64107000000032070300c44c00d032000880e41b203660089500507940d000680303400341281017400329200c0098203140c0e03564280201034011214110480000220340d070041d40f500441c00745540980410009a20001400e01e1050005c64001c0103e2811806030342140c0040e25044134107101905d084080c107000500140f013600d045800b00e4ac4c510450502c0d010040741c844400040850856488841c441070192009010074000c140070144c210400f2090f400140c03e4440d0715002c0c0052002c00d01081025854100840c2d0303120034200c000580e111401000a1428001c141c05c09402c0c0d800820020100b11002006000c044440e00e420b044440ea2140c48005950350b458004220340310b41500d503041400d10341c1105021500ca82944486141001021003c40e01d024038180c8450b8442080540542408017011030200111642481685030401c006022184548140c0c0c50840359041c62080061040481c203900365401415240c1c3c0c1c1c1c440f070503c0c0340030b40a0b600303255640600e8854030030a021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 227322023 1250 227320773 227320777
    0x813092a0e090f0601020a06050f04020a0501090b0a12093302130e0603010e0d08060907030b09060d02060d06030b0103020907020601081509120415020f070503100b240403050f0102 79
    0x4078004000c02100d03510310000d48004000686468190f00c03d00e80d4040000c2c802e40a0710740300e400c1c50680403042d40b40a004100c07000744a80c1c44107050102d1a4014000356601800321130320030440e8108190758440c80001c0394002c110304240a4a0b10080c0c88110a41c0000b10179504001420724282c012900500e4040808034415450380120b803440003041000400f900507000c0c0d5012100600005050401c1790355141050400c40320403000601d60020001c4602e41040c41a8000040c1d00e400c010303009001c00841c0d07481d08007400c040d00c18000c04912804654400c022142001c0c0d0501c0c0503c4401e0343d900d0710b056641d40a010891040d0584400594104d100150740c038101c601c020001c0c00c0d00340d44450342c0f94050b42c1c06040c04085020703544c264032403e00080c000388010030071114010544007000e00000c0c101901265403030081d8012550802890340c0c0020019002d9848040001b01441c64070002142c80c2201482d5000811244d0844002014184003a20481e80218203980324682c040c0ea4040c01c074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 227323273 1250 227322023 227322047
    0x6040b0403031b02041b083715060302070302010b040e030405060d0603050307080c1c0909020c010609090c0503060a05010b0d020306040216080d06050904020d0813092a 74
    0x204418041000801d108507840c036540318181e07640303032080811034002c5000d54a00464400c0751803211503c52400703540c01010113031702c4102d4002e4402d1030004402501500075500d0b00320280402c411407003840d0307950103900ca03040845081445212844e9152400380c0a500400420350240d403034400c2046d154101070042e44c48a0b45658080e51401c0c0c2400f04001554000000914881d40d48040100000d0420802041a0b6000e00300780c940f01c80444050360714258500107040d502d41515a001d0b4005500305110030b05440a40d180503031240740000c0890300400007a0f1111b1002030a050124081c006165841c00a1311010b4050301e090b039130303010511400c0c0c5000b8410321041c00801c0112401081003540070f160415001880546405100021340b0800690800141ca402a0006c0c00000078400c41c829040105400d4520100c2c0b85419000148005107146000c1c16000000580204004100c640c02020308075080301040720340070f0300342c186441d201e402450903403280d1541c00d060080d43c01001840c0760 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 227324523 1250 227323273 227323289
    0xc09050324130f06060e04060f0b1e0f0a0b070b1b0a03020703050910090e070201110904020310030b0405070e06011b0201210906140f04050a06090507150201020c0c0604 74
    0x419240c066151410b149100070544001401200700701c0090490b00860300200202100c5109504240c1002d03000c40f40c1d060604c03192940340c80303008030040d10340680e4150014040c41051942c030b405c0b00085407072541d00c0201c10b0313030010040402103401122007000c0c1411500900b81451a03076100e904016001540f0700716025074030024005404014441c2e001002c0c05071003880d0890418008201103151019100c0a090104000380e205009683e041c20405034814441e04c002e0044001c440741a50b036134403e244489009a0300000068542c0c180c8141c40d07401143d000c0ca01134030a01c1c1c07909007030f611403a080c090b41043c4d64885000c1082588031b49a0307a810041200700028201c02150b0044d01e614213a00f0300900c044010402405201c5058419408590700803200801d08035060b1080140e4440c00821100d071300c4c0c00000520000c52800281c00001c0340d03000740d0010342c040040c24094a013401c2c5074004219005081c040310b006a5040d0041c0850150342c60441d40c2c1450750104001280c0118001d00c64 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 227325773 1250 227324523 227324593
    0x30d0606030204180c03061a071a0417130e07050307030b01080709050405060a03020d1a0a09020a05041d100204030309050301050c04030b0c070503031302030105280b060c010906090515040203030a140d0c090503 92
    0x40f0f420070b140000c1c02045010002c4003034dc20f9481c4192440303c0d004407000008141c011082000c02078050191100506007464908a42d181c5a00701402594190180e0380c020799440c40098500c0d19510200070246400905192030580030745060701c0d01c0340c0003610030940600f518000c200c904400d03014180702558003c0100d1496410042400024100e207a2600c100c02c1c4003021040d0185400c0c0b0920705000480075026942d0303411810007510091413580141e01a07071602d82042102640c560590701a00d03403200075815141c4490403103a003140150f1300c014000c3e00000003070200c6910204580060030740700750002e1101e40e0b84c0090101f00c4000f0b495100e1000c1c0108a03404034417414503800511071240040002e0304090001d0300303c40c211000b00d070003114032030340d100020300034000100031541002e04856000d81c520f14180d03011a0301c038001c25a1000603c20302c01c0c03000080c002d10b8400d03202040032a11040001c01c22001c0002c1c6403080c0740c41901d0003402840c01300f0034401581c00c8440581c4200b404008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 227327023 1250 227325773 227325803
    0xb2223090a090605090c0a0b040f0501050705120d0516030911011b080c3d09020411070501050a0b0d0209180c090702030d0606030204180c03061a071a04 67
    0x12000c0c0d00c0081503858119601c40394500020881d1203130a0007040d0b094001d044a1000c402400329064080d0025181da4209202c10072400800340d515030191a030078070b0015203403110b5240c00703031408104c2c108520229801250840c5154810342c400ca2003141e60303010704580c020a11350194100c4441c8a40941100680d218424032940544221004054203010b2a045c0c240c15444016590f0410304254078550000030300352080718422458607891701402410341500d0480c08110400110301205030000b4a0340396404802903603207590114005241e8010881d68945161815a0080108483e8020040d2901c4d0142c0790ba0b042508024002c81e0b03024083c40040d03129070901c1c0b0f01c1000f51969001c00d40c82024000781c0c150f150500918000da556400660721b41c50401001402c3c1c643d0b0b50088000c05106001c00c1210702201040e01004d0340201e0300c0082d01c224034038012009024107405c10250041c071054401c205184a0004000080c0183c07101c03010783e40c0e5201e11011a000c142c8014205c2c00c40854a1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 227328273 1250 227327023 227327029
    0x20112091a0414010606020a020f180f1b030717090102030c0405120f01020703020a030e0904031d1f020a0b060402130303140702130501080c0301060f09020901090b2223 74
    0xc00d400c03d0044061851505082080d1400c0d22072070b42081d40140c000088290440c00d00c141f00704901c05045a85035094412110b6003030a01c03900138858010592082d000c101c44c510a00d150000101e1400f6216590781303840310001d0800491717003184d032108801c1c3c600050601203040c4252030042580c2000140741514106c1002400c402417448440c1c140600001420390550900c01410b140d44260050241450b241c180601400d000700b04d140e0190024104000009500120304420041c0148620f01c0c002510804103250300316952801000e420610340580131560002080b2294034070078035941c12160f84101c14031041e4011007e6000e040880035409200080c0991007655410640124183c02c20b1b050380c0004809028103014607202032760398001070181c1d044c244070844d10380c80143c0003880503a00e429040318107070030701d0700c50110210740c04280c07108980c3c070402091000b800300c20041900c03104c0c0300d42404e8124207410411400291021400114402400340c10034601c0b5400c030040082d031031380b5028 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 227329523 1250 227328273 227328323
    0xf020316210501020409020d0b150307020606060a0c0210050c0d0e311109120115050f150d060f080d02060a02030406022205091e0103020d030306030503031302011209 73
    0x1222155002e22021070f40040500c048d1032506041c440101d410900d020922001b02407040b200350413103008100300001c2c1e9800141d101d40229003962616502d02442108840c40000c0c980020b40c8031481680a030314a50f80440a4455010103200351820170340f03c0c0c2003d5a00030590307001c5c0ca800c4002100d0b0741e503040c02d90703080401c0b040702c1030b003c4100d16a000301c00031411204e13041c10300d072940070000c9403201150900890071601c1c1180300008100b11505e6020740c030107001c0c0c14818244a100c101503c400c0720b0f1117841c481d1509a60b01c2070002d0f11407050171040703c0503110341c0c0070301d02050208083c0010010000141783c4501032180d000f5200c6a20740355080f90295000600c207075007050b000c102540080100030120501c2010580050141d14180380c1004030085020784110407d485685603e180c41561500e03050450354111480d130290700302481d081d80644115440640a4040072080000100c4208840b44c859072003680e5030504254110116421900003038005001008171000307280c03e840880c1e403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 227330773 1250 227329523 227329589
    0x9061209010609142e230a030f2d0b01081902010507030503060406050a0b120c04150c060e03120403091a040e0601030f1a040b0a03050613061401030f020316 69
    0x580100714803c402d050f035007400170540c0b20300500605484041000342d01c50003070035880e940441e007420000b40b0750b8582608201c40c1c0b44001e4942660111310659922102800200c01d18420180f24000300c0c0701e0500301c1480304c091180401900134200b84070043c911035103081a8596050311910700301081a1403c9038682c10040090b0b070800da0700c00c0c2c0400c5a982e6844030303200900009403d9035803070502d8020419006000760241d4000303c2c0038002440746505001330100660071502d0b040610480c41c7c01d00c400034094004c50b0340f4850000040030401c801d0000039030740c4a140291101c1d8046562000080c50607441c041200e2401001848184482d8819450a68000d5814900499510362204558044844088403c0780c00c0400e42010111030605002d024040542243e1694007a49503850305070305c4080061182c001c2c0c1075001864403c000d000d43c00910245071240c0c18405540c1c40745007041c980100c07880181d119124242c021240c071039a214072001601c0a43d4440880e85068842d04101c40b54400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 227332023 1250 227330773 227330821
    0x14030403030b150703021e030a1134060203030402031009020315010806010f0b07080a0c0c1802181c030e0a03170301051009030b07050702060906120901060914 70
    0x7401c02c0c1865075505646402120341c841d0302564880840c80e0103440c05050b041400c403480415400da454000d408815a1440e4006081c444840d44107070b8401400c2c0350384154141c0302400700288202c1c0f0048801a480c1045001a01b80a030076501c1c1c0301c044c0e03034a0008440081d03060388030042038030601806800c04090548058211403e680311a80c4004000c0310903000380c510ba5014400401c4122050600c0c0c200805102c1c031124a030003c1c1e9103c40c40603201da010441d09020002520004001003a002d2100034000195001a44e000c00c040c1d80e000b80d8009460155416600c1403210551700c0e1a264840c2c00d001c4040301d07803503139103116542900d1000e24290040c3d4070403a00c103400400325190000c01b8141d211400200d640d60340c141810821040314400c4500100306100c80e041c00041d42e02600c4507040380309420466201c0c0003030b100080291045000098000802240d80103071148100c0c5042e0003009400e00071b201003034660303031003508565190712a15020b11495022404003a501900380100500316 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 227333273 1250 227332023 227332031
    0x30501020a0201061d0c1b0d08040b0606040501120b01180905060a05040b0d060902061b0109050d030908041404020d0207080706060e0603030d0b03010212010f0f0602070b041e03020913050f0d1403040303 89
    0x87c4154140504034060700049804002044100422641c2d496804801255424109801c2c10002060107400c0d07010280201d075640703d0302c01c0e5680100d80b891a810030840d1008145611011f039400a80b400303440480c020800345202184900e010301132410781801c09070088000c500152a1400507003050b140aa8210200704050b50013140c0304011018180d5815001145040003883d0051070003103903d065208052800c9648000141e961048400b02d0b05140c1d00c080c04258000c00040003441207512442203941700042c10803c02901030007505a050080c14108074955072055521600d0204840503940f41d0010841050744121503403210040d45000303800107040c1610360a800d01a05000e820070448081d00307070b0040080000070380a58020b130440f031001c1c002c4e4a15240d6044d00c1130049000740e400c1e1898101c2d0003042600802040c2c2c0007142c00902000315410980300800c1c5481201d41d09640701e001e50387d0060f050702c10006061414001d1959880c540d86c00316100b030f00d81500054001c904240d12 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 227334523 1250 227333273 227333317
    0x3103020402033103050919181406030706050306010f050f0408070810060503070e0424060602011d0c0603041707050c0a170c040c0504080106030501020a0201061d0c 72
    0x1440c40914811404508882c0624100740c0d141d0803040000601030305000c004448000000703034000280c0e0b04a00d41519450f50300600803103125640d01d49074000c0c40c5230b500c801507c207500801c50340018402c001440100c082da500c82800b4542c6500b040d0180070301086042004c80c059501c1342c055800325001d5032500ea410070b9054250808a0742c4140d01444242c0c1c086202813282c0c02e02030150412185c41810108910340c82d0601082d110a20f612038040c0e0180c00c68000b0b01845181c003c464005130003496800d140d203070410b0301074000740018019000113618100180ea40c1c500070a00305443e100600c8000c0c200744401c4400c001e0a640020022100241800234121400743e070900909001846034001e4048111200c040c40000e540075440b1440d030b40c80445003410103c00c0070524812004d03059601003561540090180d41c20f11a903400000c40c0d602e0301c58000184031043d406400a403426500a01c5484da80d50360700700da059100c0800f82c4840b00b26034045201c03441d8034030042c521607040034104421152 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 227335773 1250 227334523 227334529
    0x80313061209050a050f2e0504030e040228031e020705030f0a0201022212031d0a17071a03160e1e030622030e18010303110111310302 59
    0x104045080341c01e584100302c1e0321030801d4280041081e1024022000c044a1030304044801c0d405400e9070b14283e140c8e80c881c003090906110748451502c50102400565480903e8031013007035861055102441c2d550707000c1180510580c0700b0300412142e10300c3c0140400103105007c25400095200b41e2003214540300803c25140148055006000b82848903000140c071a40a04203c46c2d044030425141142c2d41441c80d003e01000c9452801200300340e0301403900c804003490002c9000da007211800f5031550b22000000340000c03500741c80d20001c55115040c10598142070385e6401020400300d001030640b05045000d1001419402c050481e214035000e441c40e00341e040a00c180c0100c0c9403908003244500d855440c44600c11071909007041800d4000c2a20441070404e01c400124219a041b0310190040c10404a0514022195a1028405d01e14070700116440c5641d40d403031601404030705a1420087d95035003400403030415140f03104140c603400081c03004400382c5240c16a17000a1003001280c10b00003589074620020000d1b1b1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 227337023 1250 227335773 227335783
    0xc0a0c0b0c0d09030908070807050901060c0c051918020a08190204180501031a070206061201060b030c120108070b0d091e140709061406071707051608031306120905 72
    0x103806921060503a50918131031601b01200b1b600b01500a27417001d0380400403a1904400c3c28110703091840d0402c40c2801a103014011400541d0280398082418140070003e1001c080b40134048440c1403011006c24a0b004002c2e200f41d0055600140c04514404005460321420245502445071b12020061501d9220420310511186550440d81956910b2005004000c5041e01d001540b41c00303140c5001c09858080741c0296211002009103000b0000f5644c0343c024480250803950280070100c403101e890345031004048880c2d800120b40c100c3c203000014000984c00c4408036a40c4160342403014030754038008624201e240509201c03001203441720342c0080602c10f0303081502d01c029011413040f4110540d400411102c00c1c41d01d1001e03009002c0880c944401000f20f43d101c0040360061003000c0c1c07034032034403005142400000e100200a03213260011000034844100b15020076042d280c4146070403010308164556036580c0d641d00480003d04160304032481e082c80018054550100d1300c3e030b402000405c580c680d41d0f486074149 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 227338129 1106 227337023 227337041
    0x71407050607120204050d060504060b060a0503270d020f070f0807050d0201111504020301060b03010b03040204090c0b0a02060f0901020901020a0809030a1e0204050c0a0c0b0c0d 78
    0x3003e5406a40013408014110041c090060801d0405007070100c9089550710301d0700c083c072555072404000380c42d501c911a80c0c5903030856588007641c4840300803156403100750b0f441d840c0c45945043c00811258607600c0c2c0703d80c0a40240100c1600092811001e5041951503002000c0c0074060750030f0014000d011504100c0785807000c000b6500058a911200c0380c0245040e010f11543ca54040340c40c0c0c04024096403081d0000c0080c1d6540d40d6103040240005e0242108001040001c079015142c0380d081030410700e001c3e109640301190388000351076180e84061001c4d000b580040081140016183d2900359100352040000e6103081c00b0b0b900001e480f0000707040d004044540c0800c0042c090b4504000709126282e21000c22801000f03149164240ca5002c0c0c80304034442c5081c0030010740c030808803d00f60351780415207444801540215a41b0071124040003032110915403010700c44401c0b022050f01a03070041d = true := by decide +kernel

theorem cover : BRFrame.Cov 227158273 227338129 := by
  have h0 := BRFrame.cov_init 227158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 227158273 ≤ n) (h2 : n < 227338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
