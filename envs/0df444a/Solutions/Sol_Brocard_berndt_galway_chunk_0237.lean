-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0237
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:39:11.092172+00:00
-- url     : https://prove2.me/submissions/84eeb088-7a41-4058-af92-86e9496c17dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 42446047 ≤ n < 42625903 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 42447297 1250 42446047 42446101
    0x2150a0206041509030903080c030409050405010f0c02010b01020a240c050a090605030709030204020a0306080609070f0b03090d0807030906020414130e0309040f091b0314010c08010b07021206 84
    0x851030460f40c0715444100d600341d1384005545082d40c0e9094065400000a0f00e02c80c4014000811513a8492282a001d644030760300000e00c601d03e007916407003940c00045010b403d41e4500080040107136004101140c4682d800b003d00d2290b486e0908c01d40c03000c1101584c82c000c9007407a000b020b5140a40104c001d00d25140c0c01d440301d14000e40c0d600401c54461101311080300c0001c001070402c10050800360080e0120455a00340890120340381d10074240750110407162000b02d0b078007a42e01040b115807480d0080d27025000e00d0700c00364a54505060380c03580d20040c2a20300810050030000203004580309070b001921450b440801950f80d0303640c6101d020610700400e0b909034407985181c0320f905141400e61003a41108072402c40a141032401c0d01c0100700040c565801143d020541300c0160000040b61100c00c0f020800030503c4044589081d0300300b40309400140041c0100c036070b05d407840707021825810803002811950a4840360b50b96241d0303840130031200988648910300310f120322014056810b02c0c04203241d401510a18036 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 42448547 1250 42447297 42447323
    0x50f10080613030f0509040908090f0607020f2e0807031820011b050604030314090304140a030605090d020c03010204051305070504081014060a06081302150a020604 72
    0x4103030303214031040e10840202c5403840c400b80c002034000c00ca02c1131104954200907040c800f44c98003280a4034200b090464a2644c005091100351801c0d01001221a005a9409060144581c00300f040e40c0e0090b075840d4420b0180d00e480701c2604114030705861300c0d541c00c891a49a1804218000b030a100342c295039910100341000032280e181070381700c04404031850f086000c4484000782061101e44140503268401e04000c50005a8610758100e100c00c080000e10a000400e42c61805040040899803115034140ca400782d2102031203440e00002041c0c4054403008030083c1405078091001510a01e081e03803000384800c0c1400e00b00171200c0340200e400180180070b40c0a0f20a1400100b00301400c070b01c07580c021243c1c4900c034000b02e80030396051980540d80c00850307400c06501d883e031034074545860400c040c40c401120546a2900004940c1140070043c0c0040c03099511044650500340c02070326000e4000c0a05c814503100100e900c06555403040c882203509170074202c60740d1302c044060000f505c482080b10140c0300040d040322 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 42449797 1250 42448547 42448559
    0x605060904020102060403110f1213050108070c0b2701090606081204060503090106171b0402031006030902012a03020708030a050f03070201090c0902030106030509010902010210021309050f10 84
    0x81544155030584c060102e035503403554183c5103034407801c110b1176442c8110546041d24400411220043c14844d01d5030648903042030300881c0c00500150040d1b410031102c1014032860303e400c0074580510030390000302c0001541d038105418511821491801581100606500307650003010b51102c10302c036014002c01e001d0f243e2a50001ca40d20180490402103030b840c20041002203a02c18005940c01240140010540c2c55642c0700e1660810380380c03215040705801408408210040805035441107050507502941035261021845000184602c00d078028540c0722141c8030700316807007407240010620b05d00021122645007020401c80c1c207560000c00b14094450700c1004034031543c0000642d04489200c0c0c0c2d649103441400540d10a1907040a071075841950348402e00400002c0307800300c0034000780ca410400140c40b0b40c54003000900340c45020707024680b541d26000c00030b00942d03400b10356051440045078001d0380d00c0c2c0035042c0c0d550540126034003010740d1520f001c0600003104002d50040d030150b10f0302c0b41a1031526490b95 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 42451047 1250 42449797 42449809
    0x5180103050f0a0c02190602121003080a0302070f0f0804050406080606060304030f0c080a020102121e0402060306060f030f01150207060207050d08190905100516110a0503030412060506 81
    0x10b0745a40c910003100000810301076076a0803401c2c1070701c40c900c140c1d045101801554400603a0744801180c400d40c002c80c06d83d507a80b40c0c0764485640003031900402d244c201d245840707604291040c1e01048c41055000110350082c0201e158884000d40c0e0301a10103010040a0704048030780e908a40030341c91095040000004281c107000860501648004003a585585c9480e54283d42c02c510b06000d400502424200042c04100b01303102030301e0b86104907000565a0190a0446984d118000b8a1200754a0344580f422800001c04981180d01030303030680e03090741e4a84914000070418000d0070070810000c84004100300f041205502c05a040b105148403801403440c0140040e61242d000340103100050380400c00030032061401c040385505c3c1034014481039143c000540d865101540c0d001e4a03070800705100480c10801c1c0d06145440110305590340c5096420036281004894024070000310152452400420014041d640d503c60352000b4100181181d61319a40e55501001001000c101a41c4040c603240001d01603003440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 42452297 1250 42451047 42451051
    0x80405030a060e1911060702040e0609060402040507110a0b061c030201020403060624050307050913090c05031606031a04050f0a0e0309010909020c0a0c0b040e1b0405061b0106060518010305 83
    0x170f44c0501c580c0f003000a000450704035a100b030303034443d841ea40075840303458060210074010300724200600058646401884142d8102800b03070010001240c0400c865541b01140212000d9402241022a03880e07440000e60742010f11080140702803240140a0b040540550040003142d224210070b0150701d80c0c4290520004208680c1005064004811031800d107100707000031342e8010854103000e400d003640040420b91000d195442c1c4003003075503070b01c1c61501030045200020004040840040c04400813601050702c12a02c0c0748a11070900da04c80005900080190700c00b0030b10310002a100b00154503001d89101c000100545080c01c500b45810803a00c00d598000c0111480d02c00c3c1030312004002e074a000c45070002588140c0080c1403a0064603039110009040c840319900514072100203903201c3d410840b90251821024120b11040c50300034000c0361701907900f0f400791005c54204480301526030b04090041c48001c3c81480f80c8035003a500e000004035400341c1010241c0803100d04410b0f03002c00c2040303400040d0300721641 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 42453547 1250 42452297 42452303
    0x80f0a030b060a0203090607050a060513060e0c06160201020c03030a03140c09010801062d0807020f010b0f10020703060618060509060102070306020f21040506071404030b04080405030a060e19 84
    0xc00c06c003035100c40c24843c008000c00d601c60ba0403174140c80c50170f0311160b007111825103903690f54150a03001c1c02c080c0003c50044041e400b00107c0a000941a40d800003820303071140201c00d0707034800d108106035029a8024045003070304000103400d4a9803008580002002484101501481d0030809004146801c808800f92005144107031110030b4141d00b0b2140580f010781200d0940c1c00030070480000a100c3c0304d41101150b507039645640340ca280608240c0c50103800c02c9240b4118840b0790703140104004050795840d1121290100580b040028020001d00490510440b41c002825590803c900000c600c21581d40a03114400109020040251618100325084005503419401644582024000318025a0090000d0000368407241d00d0461400000c1c404560b2041c5d1080030700c5000381c2003005104040c45220350107a802e241840071310364800f900d40001d00440c000035001c01d1801d0b0000741040b410804440160000600b2100c1c1000c42d440d18a0103400d4540320588a405007181c000d080d104859101c410040d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 42454797 1250 42453547 42453553
    0xa030c0c0512161a04290f0402010c08121608070e010e03031e2d0414041814100c141e041715010302090606030a09080f0a030b060a02 59
    0xa0264120079045003007080e803100c403c9807040c0c00140d6040201d03111214000c1c054602840c00d8181002a640000d0403000d485012a441050303003003801c0c503000e41c004840e410300e03941600c40d800100c1c1e00c8032085200401d01c000c0051030791400303592082440d00c100501d584500c0c250343da030f84044806042c25504c580208020000c203600560140286048004020b821241030605041e442d80221080c032011801c905800200d00c0c8208a04e501c11049600240340803100041c6080d0800c200c40c0308a00c207003042249090642020b9546680080c00c40303040b419611020714145040c004154200d50f280c0d0100c600c165503120465919501500340c03c00c040e501c0300f0301c90702050300c0244166442034416440340c07846c5981c241282c0d010304000c1c00243c00102500c84c2d1031031864105c0c07840e01070100d40c1c92407920358140c01007005907150101c1d00d507c84d00589206072640c60341c03905080901414040100003000114100c1c800f1001880070313040c6503005503030074051800340505205517481644100703401a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 42456047 1250 42454797 42454813
    0xe0f040c0e040204140102100207030e010804030306180606020609070e13020303120703020c07091811030a02040c030e0c1503010e041e0501020a0e040b090402040b0d0f06020a030c0c05 81
    0x45000e0344125042000390622071003240300d410004040340d00070b4100d0744000000c101720034010350741080020391070382010400b14a80900d94070003410b000101d4135501d040000200010341094860b030070400040c403145d00c040c01420820541d54000d0034040c0074210061280748000f800403140000c103001100c41480c4480d855807144198441d100d2070301e402c140e07010700c001c203c003c04846104812510640e42941c0040c0c41d01000300015007011800e52220210701d082442174001e000c1c00c44602a03507260310100070003c580c01940071a05118000f100030754040d00d08018180c4007501500801c0c0302d03003500b5058411440e04441004000700c0c0c0c05e40003941c003007410f10040c07100e00c80b940800c5030400c2c007600c0341c181e981080507007424603400b411408407200e94010400b50310040d04018280c1d82c0c10800c6500340700850240c00403518013000244080e00c10350303d0b82080303c15074171050242c0001039081581411411007a041120280d8003150480d0002440c00300600207075403107128010191070f44a40508254 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 42457297 1250 42456047 42456049
    0x305031e090a06030c0201090807050610060f080705090409050a050d08090106080a0f0305070c0f0e0106031a0d0c0504090c0302030c010804080a05090312040312140a050409201201080c010e0f 84
    0xd0805d400c3c2207056650b212500b50100d5245d00240c03c107580314400416070781c41c0030a250303145071049a003d002440703a404401620140c1020241e5880706030791030480d0304d40d200e0800003805440c0010025045008042414040c007501040b240d0040481ea01c4a000c00d0302c581c628142220301c0d0340b0500d03489402c806501170000380c4116841140343e0007403a1550130681140c1340c1c04448030b031952100c9042c00252104001c40d05640070110300610399070404002d0580c8600f001204103034900c5100b4170803940b1083e410b04006058900c0d001030900075000704a482403d24011807003140340d000c01e82c03180c4980c04480c01691301c9480b985205650020025003461180c1c3e400f0390b6160003070464658140030380000312074890711060107080110300901000c0a0303201520409440c3e41c01d040d02e51068480304000594186410800b180c044031941c810006440d210401070000303201c1d8207150f55100c15400070f650b100b1a1a9100c519042e0f40150341035888002004005490001c2d42c1d170009500502060b01c94450303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 42458547 1250 42457297 42457301
    0x50705090f09060a0509070503040b07090303170702012a0e090702030405010c08041203050d0f0603080f0d0f020c0c09090303040b130312050c0a0311030603070e0c0c01060305031e090a0603 83
    0x6070f0180400b0585915080040d00c3c1d00000c440d01400a0004010001801500080c40740c00c00514100046480d044d1b0300c0081403501a1254456504030b504017180702103100754841c0f420b0b21102c551440b5000b00f00c00d2807600402010b610600064100c080080d098a4102c424900406090700118a0716240000640340007144040a030359503e400d005c00074150444140d03000c0501e100383d540d544e070350300c0206003141101e52007407507191980c1c50315205000113082c58084403100110203a99035200c0301c0c101c80d42009806100c2c102c01407140007007549151161b001940b41d440200445203c142c580c2c6090009a0b00d00003107801070240703103641000c5955000b4a82030070092038001e01d0156112203d413100c0100340c400564081d90060000240c0d6201c40f6414450340d4008980340030458039508101000a9803600103004101031032b0b20840c007092048000d03208503020045000b000307000840d5241481c0d40c60342c00c031610404200c85902e44104003502a5000c03a0030861000b002c0e482a24140542100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 42459797 1250 42458547 42458551
    0x6080c041e0e0a0207020306010e0a2702120319030902040e01090b01030b0106051204060209030a05060a0c0201050604050103020d0b072303040c0801020a0c1e170904050705090f09 79
    0x4025808000105540c01a00403405100d440c0c810000a90340c40d041c0c0e16061480024030041181d4410b1002c000166004219681159422014010745844040c4250010a40012240740301e009100c1500400202c1c2c4407036582841c021209410003a1810041c2c036128400c1d21424038030072050003440f00b001800307648607121041c00036100161042c1000c980e2800c40d84d41d100c055440315201c5004000300800c60003418098605841c0040c24101b000441d035030000030142000b0b1400c0e4001c584583c030350300e0421042003656041070448446052100c0300310010949501528019420b1100140340e030704150180a04880e8050040d500c40c0c0120344681000c010043c001c80104012810003501042100d064402c0c6104604520342d960b040074507000e00460300344da1120110741d005000702070045802181a07903480d0380143d824a00c5014030103907011000c8400100400c015005203410300c06855800c042c1411810a41c3d040010303441d05542134496001e00301403154005001d00301c0f050942445041e01d5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 42461047 1250 42459797 42459811
    0x5060c0d020d0c050306030c01030218150d110307020106050a050d0f0501060803030c0924160305070204110a020c031204090b010201060503010e01051009050408070209040f060603030e18100608 85
    0x504100b0a02c4031581070300d0400f050800002c1c008001e0001074078040c030440c1d04008017400c086151401716400e9010b59883d0036026031090301ca000d04c03070944190702804c950304800c014034104001d000e910340459a0740c0082e20000010f61070540b003c526810007014030b10544074024001c00710008540e4802d00c00c100c80c1d45040364195203076980000e0182c410805113014140fa10099038403410300300244007000402d00706400811554007854060010b02104403820842e07240d40346840d10300c0c6418140c600340f280341c030001e40052030840201d00340d0281e20003400c0e140d80d240c1c0c00e0700d10b80c2e50f50200b01507071000c2c0c440d2001d161610800c070030080809298418422400180000724060b5501c400180c02c4502507400c03200c0b82d9448800b08032480780c5050340711000c2e2451a400304014101620f460031103001c1c04500a014030102d05c040380c02d0100c14140500490350100342405000c0e00d034039000f41020504441103004480307402c03421441d0b0340805102442411180c00c0c2c410442d1400b070003140d90301d801616407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 42462297 1250 42461047 42461051
    0x180a050604060c020c09011401020111120c09060403080f1c0b030d0806041104090c0f09080706080408040509090f010b0121051302060a0f020d2c0f0409140d090305060c0d 75
    0x8185c441e100c0103c098000c01e48450160518038414001a080d1840c00c9400201424100155081c00754007070103083d001034000c043e143d190712541c80481c03020302c50754002908104001c84c03030501130011000100301d0f014159004900b08003e1034500025214920380056154100d600c0558203075204803101648040018804152000842c001c000c5c154440d42240d607070f15440711440c2e100c5a410514040703460106190410089191a01454490480c3d001c0d03642001103080100d018404000141c402a29009000800c1c2e0b0500c42d04050382c80013076000300f000650a03c0881042980201e040c2529881348485204000300b10f5010300004000c0104020f42d0b01c105080700c0300150701d50170f002e8940c80c02070740c070382125840701d02c400a4a040d01100e4800c040041d0304010203c0e11302c0c0940c110210000c00e05d195284601c0040001c1c080001003042103800c02e1070140c0c280305014000d41c20540d2250010103640109020000448290b401c5000140c030310b40c81000403e8003003c0c813500070705074003c0351180 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 42463547 1250 42462297 42462313
    0x150301060504060b0d200409090c0e070c1202030906041406070b071205220308090f030d0204060e0a050a0608040602090a0306061805010e2205010e0105180a050604060c02 75
    0x41c00301e0700d59030031985540b0313008200008804614840d10001400180b6a44007005041c802d01c80341f846940100e40016071940010001c210408403a0805003070010003620f03003423030071402c014005c548810081e0f40c90707a81d501c041420540040300321100c1c07400242440e49003034207104d52a90002c41ca160b4054010a00b00040c0002c80c01c1c03407001c1070250b04a5a5074080252102ca000300c1611005444a1103581020080c0c600d00c07940103040950f0180c1c9410b049149546e100041803d020710544030183c60b0000040e00b40506c00264010000d0f40c41548440c2e0340a03c541c0c0a02225941a000d000e4110250500510565004d100d659034010310920002d40361070312070400b158290182d036004030382d02610764a05000b070701c0301310340c0c1e180940490442c200300941c0352010048003114090910030000850745151404000e03444590364015070820300a1010b140070030506070003080b0444140000340d824035002c40003000046808814960400010035141d03d81d912084020008050100103504c40d11078 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 42464797 1250 42463547 42463549
    0x130509190f170910030506031b010e09040c06090e01080304120521070c0503010209010e041a0d12260a1508060f0708090c1e061b01050403030b0a0302091503010605 72
    0x71251585a0030001c02903103801000091103800c0105400c048141401c6c00708114081d00e00181e2001e120485184607101068181c0045c1c840915882019800c028002d0411050158804031030f8101c601d55629454655510b032817000000601b8010f0740065001008200301e1612448038100805d4090000d440c03404100100141000550009010003d103001c2515000d1003011040a0f0003404241d0083d40343c07031030300c4000030001d540b681c030a54895035031901c40380302030400302c8540206410060901e104500440c2000c643c03100091403540001940c98241072507001001800d05544200e41c892001e40351600607180c8041d21002c80d609424801400c800103040000700045e5024100090120401c0d05050000074091400142004c910b6402100c200303501340ca80841c1c103055140c11003040c011402c580c000040c458440c0319048400781811803691240040107601c81401580700ba242008428800d0341440301001e058800070307610030b11200c0050b18507080149490079407080240001401d98945c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 42466047 1250 42464797 42464813
    0x120403090b0c07030209060d0f021207080a0f02120304030c0308090409120f020c1207030303050a020c0105040318080601060e0904020a05190302090604020301080307080a110d0e130509190f 83
    0xb14218071141d00120080095003005c00c1002d80001c01510b550030714108a8480552148012500034080c01001420314074808041c070052024011010644c1c5820038542446e0f000c140240300c06a115005011050030002c10000c04c583c11281c1c00380300c1da100b040c50340e2100d0450750807115203150416101e07031920700014070448498101e1400364403800304806c5d100030000c0c40c0c003400400c024011100400d14003082c81c0000b94401c101e91b814503011559554003803208001c2d014401c070700393f0361f51300341820701c8101a0400030f00103c1c156081c240244407552006c030580e03500d0003071040300081f40b0305154459442c2040e541c12503029002800c4603281c65980c001141d80340c801c4402280180d10554018002c43c070380b142015400c882308131800d41c11941065102910ba2190100062801d0400540d803a00d05001351183d1146040d40c5040e0340707070070342c600001034001410ba05400744280c0c000458081c05001911030030b070052950400500a1004101107260390401180c010f440c580000f90003640014241 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 42467297 1250 42466047 42466057
    0x70212030703021909080709090503040504150302010f0e01090e0c07050a060c030b0d020303030a0221040606090f0e12090103020f031302040b1e041a100206060a09060308120403090b 80
    0x542e001a920003d120104c03600703201c0d03008400104a203510040000000018110702a214050030004a403c09450420f146100315031180c0d401506000c2c448010021548001084038000e0300d402491200c4100100c410340b40c140401804103604510a02c01c0342c4c0c140d48269841110010b41754503000498540c90301d0420b41d0f6101315401500d544400c1c92007039050044070001c0a0a45070071280d440c407640001d8984c00014002c42c04640d0118001040c4011007c600400c1550200307a10f80c0c90070f16080c80006801e04d03000710071800f800c01d04104025010b92041505241404025140d1000000d07001121079024040300b90400d9020b00c031005c051042200114011801c00c094580340d46400d2060000380c2d0040c40c01d482c0301d41d0005120041440c2c0080284c1e4118004480000c2c5042801c1806481046e80100c0f00780c2020b0400810503045400080c45c0e801001c1c100c1d60702000740d640e100402d00303440841c000182107601c2402554103107012034482541141c440c0c1810580c20351100ca0381c40b02e035040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 42468547 1250 42467297 42467311
    0x30c061c0507030915050a11070201270b04030305030405061b03060d0204110a030510050102030c030f03130803010605070204060e06030c010503040204090b0c041a0a08010b090102011e0207150204140907021203 92
    0x1360360288090748605102390840320050880da9170030000a80c0001e0305085d15290f001480048640401d00741d06074040c0440c001e0400c0d0340b0707015121500c0381001080341d08101c40c200c1d0740e0310483d00882e100346410080012482c0002450a155698450a0040050044000b01e030042d03241d030034200e000d203040c0010b040100303c140ea002031185000390007596107080b00c0d440a03040d17400802c40389c006494040121000584112541075032500c03510b502101a51b030007080a0240140030002203941640700e401041080e00803038060140b41c0d00c40b01007100381d800c2522495030503800408800c102e540944091a8000d000520006031111282c0300c0ca07044410882d0302e0303a507048000405120702680f0340004400144100202414903c0d8940041c00b00c00060080340e00100c000709000c011a031003500108c0006016201e00d40000e100b0642c4000650000b8200b12041200c00803c2000c1030844d1003940c00310344640f139866024829640a21180c0000035001c00118042c0001080c08408030314020750040e03007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 42469797 1250 42468547 42468551
    0x90b010210020316080f040b0103030f020c03010930020601050d1b06090612020901080612100e030a030612020f0909030706020c16050103090507090c020309130209030c061c0507030915 81
    0x4000c0e100802c85c2200901e00b41001c0c0d03458080c0408210b82d206c949064a07814207281c0c04500c8240c2081e49812074200c00f0991640c00c1c6110703030081044041c0080760032241400700500e0680f2480070b4a86a074862035030080107901c0040100454504041d680980c1800f600403100c40700c981c030900c2c01288c0c0070b642052000c26103020382000407960040039101d0490803a1011800c102c811307000200510710280040d440f5000c04000341c007001c02c0510803001c41d007207170071000c100707586a0010690b00c1c1e4000100300004685001e0300012800e400b01d5810012644c000e204030f6041031058200940e1400150080b0380f107110500c0042c0029115200030407101a50f4070040c04501c51103040003500b00e0560300410b0415003015010302c00a4030004040d4295514058042040c0d8000d00c0203e00c7c41c0100c40c90294818101e20350752401d13540c02c1d8001c0c41c81c10019416280303828541e4050120300d10900301c0300340810386d6103250200482c415622494020019140120b00d40071640c80d102d007126684003400e941a5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 42471047 1250 42469797 42469831
    0x100603030917031801030e0105040f0209060103060f120c05060301080a0c0504140f060102030c071202240a0507050a020402030403030f0b03010e1203060411030906010306050108030310090b0102100203 88
    0xd900210028001c0c00c1c0c00201400300c090300c005a5440c1d0007035428035100707003445100440c1540e009411205040c02504002c00044c81e050900c0c10108850a80c141e014015160105d50594403070300404054038031140c2a055103078600380f034070b540365004408295a046000b210115040e50b400d00158028080c10004202d0b4003950b007840045680d4650000c3d01c43e0f41351241800c080030010681507848482d4804120440d0b464000607400c62045809800550041d00030205090201e400d02030003050095414a00c40e500c039400c9a03810798103141d6901001c2c1c0c01803000004040c440d41c02417a02522030010780321812220750115069070420740d030403404030747c0b1003801e1668420f007445400e200aa04500074048290691081911481041c811101c0da580000015019407181d42000303041103014482650741e40f500d94005d6840f20030a000c115000740c2400c0000800101c0001524000c001c2c0c4942020041d2404440e0340003480b9240526040d03004103559100043d4aa2020f14443c18124001c0031a003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 42472297 1250 42471047 42471053
    0x203010e06010f05060a270b0a02010e01050a0b09060607061103010b0901020d0207060522080703060209100c12110c040518010b01030908070b0c0c030d0c0809030901020a060209040e100603 83
    0x72a16a404c52409410140440c40040e0b5004844a40c00007501000c0c040004240c103c2d40040d00d5260410903010fa8005621212a581580300607420580303a00200115281e2404034815960441103042e480441c05002c100175113041001030410b6849481c002507941d0441a0351140340c0c209071f0001501c1240440e500d2100d5805002d0b4580181c100d1002e41541e50074640040c1040c09480f6065180f034031a44620101401c0100c0800080c180304421202c90b1540c81c40d1500203580400d000314044c200c048540009103010b0750035540c8080d4411440d0402041120007107a0000c5008403407841c9114600841d80d15440f1803280d240140c4a004c800c600d602040c0325203609407540501d80904042c40c1c03005800106202100b650005179000544c0fa2158070741902a91141c0161000861075000001d0203059100d100d601219000c4c007981c488903550f0386d80c844243d031203001c1c041842d40542c00c415000710004508d035000f0003181000620000f0203102d400c60092404103a104880d0203a40c4e902d600b4014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 42473547 1250 42472297 42472319
    0x90f010c021b01020a0b0a0506030c0913020a0e0c0d050a06090c02071a0c060402060702120d2c03031b0715030509010615140d06090906090c050906011b020d0203010e0601 75
    0x8081000c4c0004c1c9800c81066403164030101c0010005a012179907400410b0080d81e0911503106070700d01c001c004020900b844c019019070a002400104d00c558242200051904440a282441813400b04101030400507088500805060010b10301c0090343e80c4c2c0e40010680010f00d204d921203d591079801040284d080941f54072110040790440102000c09200692046000103141d9a1242d8140e40c0c2d241c641d8914030200e454880100081d601a0040c411240c8000358090b00203103061115400d00f800d07002003040384600441181110f02d8042d00100030100d250b10701d00d01481c100305c0d800000c0f160844d94901e032100803c1513180050f4002521501401842c4009006d894007412519001d520a560071160160180310810308101942c60301150710b0b802c091301540554014085d01006001c000d450f0314002d002040d4141c1c00300c17159208004041602c1c02c040782041e00c100c00c1030715010301d8003440e029000300b4810070560484c2d0150a0602032030050b2400e020f00020105824002d00081d410925017100c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 42474797 1250 42473547 42473593
    0xd0203040819030515010c14060c1309060509060f03070801110a020618150702011b03060504150b0313020406050d030806030d0e011e0203070606060908010f06081203090f010c02 78
    0x204141c2000b0174040c0080d2104101c0614900900f0403a51031100391810f1803050014210701c1401d070107040e04112100012500516401c0d85400000840c0303038907440c029040340c945000c2c0581024000c0c000034000e040c8810b03101c240250040881e101540e4890780c45d42034030800d00a90f500707200c000c15210502501000456000028000c000402c0b030081c040060b0740e403650902108158103c1c03408150064000e500c886000e0514461341c8058003403841026000e45564441c45000d1442d1244016403145052489030507513440039270785031541d00c0e00e15150300105c841c614160381c041d40d80d040000c0c3d1543d5462102c140030b0b100346c50f104141c0c540031080505084000f1030a4040c4130744035001c039905030307400351390180c00041039030850300c0d640720b2030310102d1031070044803c000c050504d80f0b0300100792603821a00348001c940c000c100a21001e2640003403807081d01c095200d11203e42c0e0100b0500c42c3c82600501c05507510400300c0088841c030400400946094030700e07112120000da08080b4005c50281c50038070f1003503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 42476047 1250 42474797 42474847
    0x41d0106080d0e0d0203030f0901050d3809041502040806011403070b0705032505060906040b0105030109030c06052e05100309020306060910091e050907050603040f0303020d02030408 80
    0x3c0c00340130729034010070b45038400c1c500c10880c0c03104005400d038807681c007800581e9088045504204041e0041110305481c1004180800107a07003c2440c0358152480c14000322440c02401400849041e00c0741d9171800c000e50324030700303522503200d400340b101240d800340c10050503000781146107034140c0c80d07108802850308203021a0800c2d1082a800c03c56800490000070446400f104000d0540e0001803182c180e8480016001d2401002c81c01041c040c4445c000300040c9090003240102898115a661502051300b2900c1100e00100070030b620104007000f00311541d0150b981712003101c3c240800c480346200410303c2030708007540c40b890358801c0f10000c0c055420b00100300404040315043c10811083e140d00001da4640c00203004c1c42c419038250700042c40d6020b00e0071f503400003001403440500601900034008807000b801c50fa1141030640ca0304001403e803600c0046c0c1d03107045402c06042c0c0c0c0d00d035841d07a84440320802d001000a805140e0200941392a0a92900c0194461802205055203c0f50b800c1c2581484000c013407282 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 42477297 1250 42476047 42476059
    0x60509010602071415120702060f060a030303050405030f030108070303111204090c0c050f010b18070c0b070c02030a0f12030b03100e0c06040603060f12050705041d0106080d0e 77
    0x1409000c0c0c0004010f8199a4102c0c0702c007000640c21000079004208803403e540100b080480c0600783c00030707502c83d41c40c06044a50250340b50390707546240c0c0341c111100848005078403007800ea00400200e802a4072040c0c0090081c005e1300c0c03810700d040c4000c094640c8280e0003101c0b2513010404c10018544c2c00882220443e0f500806400220442e1054401502a602501c0e83d0b240d6204604d49915002c1c648000c1200d501c5015034100004c481c0450f4001e0002428050107210300c04265906820340f000c0480c45003c240c0c8072101103e9858072461040b100040164040c00702501c105000b5990422600088622541482e01000e0080c500751901540f1080154149410210010002e42d000b02e6503840091a2a400066507003603030070028603116000c00b905800c0900020f0214603150b040c1c000d00240c40f4080342480c00260f60744a07541e429804010060519080824144600d00c0c0c45d4010b03d0b1400d070400714134000d0300b5460300100e007100da0030340c02103105034451000f44180f82e4202c4428010200200c407c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 42478547 1250 42477297 42477299
    0xa020a060305060d0303020c030d05011412010501030807030509030a0804080109060c08090a0201080a060909050105060a0608150405060d06050702010b1005120114010306150809011404050d18081501050406050901 93
    0x840e140031961300c4001e0a00d80c01082c6100c02c03007400c0043d11b00d525071a41040c003440d603540e405444d007845403010303da026903c04500e113103107407805019442c120395014021525120060720100c0d4640c0020082c250300d40100d50030100802c00c004003600191001c00c00014522003140f814004480b00c1e02314000070b1100f403008018010001040b58007030740fa0282004001a80e4680326a0021b0096401c0280101d00d403d4210040c8141544031600c076940a9400c42e900c103456074800c1c0c80740c06084416031642010340c2074400550405800c010b4001002800740c824403009541c811090750811140b840041c0e41d5030080680d00d1070201d0344074120400c00d05240c1e01e0601c0c2402010076811050058404418400380d07485040e0b4807a0780040002c1c071203221880759a0000c0c00f00100b2011342901d40c03000315800d24900c03044444c400d411080c055a8014000c10160f52492800d031003041c40405603c4403001d00f40c000280c0300c4002d1102c00f1280704150509601c9604000400045a6990700007a01501c64800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 42479797 1250 42478547 42478549
    0x30406020c1006120201030507031104080304150c1e0302010209151206090705180a090608060f0a020f030106120b0418020a09020307090e1f0902031e04030e010c03110607020a020a06030506 83
    0x30782c0c03518091702844d0100d041d542d1040140c0280011202481414900180010394642e0100c043e000b900c9104240000c0121081d01c1100c480001c0301d000740c01c402c00d881e0032318a050f101410404d04207100340005800d00a81400203480c0e0b855025010fa203a09000030b00c03a400780035041c802c2e98004811110810f40c4c0c00c1c000001030042c0603800c101851a036890300113003003a546d41c0001c20018502298180055901c41000300d03207800702500c00078113141100010400608403802551140500b081d80c95086a180c0001242c03034070720140c1d010104035680c000211451300c5030b02130f445030040b845c04400b44a03100c6d841406180c5c440b603032001c0e503c18414001d11a405a1184200701110030914104869841e01c0300300d009055101c1007442c01c00d03001c041d00019a582c85030007451040c2240c0a0074503500011825035882081c2c01c68ac01400a038082618440940c010742840c85442d01a1030802c3e80c00d8040c149007450036209580c2c7e14056070164400004514046d10840043c284900c1c0c10721807820020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 42481047 1250 42479797 42479819
    0x308041112190c0308070c03030207060c0f0f020616060203060102120c0a0209040317010312030e030901080705160501020d02040816060f0e011101050f01090e0d050405090c0f030406020c1006 84
    0x40101210381035003964080501000c03c50540184d5002158075603509010301d03042d80720b2586444100c015004582c000210280030300141c1c05501d810a000d0008500c4030740c0c41940542d03c0c0c8004aa0008041c0810540c0d00046003807040d0140c03081c5001641c1c0c0c1040400a0701c0e06015484010a4000800000e2903103900458040380341903055504043c94ac43c0c03868141c4480c00c006c5031a5800e402c1e040000002d01c20210340039100d20380183c41c104000d0150000d1591248290008c4034040f408001c082115544200003d00800d2400040c01d0480c203000d944c2c050036640403009a00c206034000c2028405603d05100c00c00c4007004811008800510b01100504503541140048042c0b0468550303141c441d90180b111401c202d880c0720001c103e24541040c0504206500380102e940c51803810912a20202000488090b098143c0e21903a09180c80d0404101d1039a4008048a004a1081c40400390103407461000c2c6004034866040561034000d1099418a0304484940a00c400c604204003000b20740406 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 42482297 1250 42481047 42481063
    0xc030e0a1a0a03021603050a0806010c03080412030f0204030b06090105040506030d0e04090b0f0403020c011d090907030f031d060702060301050103020a09080f0c0103110f031f05030303040308041112 87
    0x7010300548030200b0900580090242c0d10240c191902c2c0c0440040c20154060000c2c011880c4544500308030307444040045913001e820300300c02404107040c0304c0414041100001290341101503494046003d4111004d01000d0380c1140d48100c4541b4004400d11074240341c80b0005601400301502e00700100e1900d400000e550311441c40302b10040c0040c400c40c0445076250f540040c42010341000f207261a078203106803405609101110705a005001c0d04a0f03100466200d07642900301ca110314003c6072a0030642808204030240701a00c042c0c0c562141060000c00100c0501920500502a4403a002e1210640c00f03204044c4800c0d40105d403282c501040900011b070359100980381510300a107001a2141000d03581590150f0705508030001e5445080c5092810b01e07c0080d8090410383e081e6414400f0303442070003004500d4012424111107242d0203100041c00001802c13101d40e81210050601d603503c645c0c071030110782503600a40d0183d000400302c104100c02d01c0b00c0f802c0242850344041c2c6015201d9407081d0309440d21200381c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 42483547 1250 42482297 42482339
    0xc0304051203090a030f110102010b01120c170a050603100e0d08060d0c0b0903100213030f0f0b01080102030601031406010f05130b040e0a0606021902060714010c0c030e0a 75
    0x41c608030240300d042001079036034070344000d45041c00c0741e80c50b03083c60b500a94414400710f40301100d05a85241551044c0030b542052401030b110764100c1c00100910b0400b038107a02030b00f002003050801d507041440b10b0b10000c060007030001c0b00e400512806c00f03a0a0505040300d08956502e520b00317150115400800005011892000c24a410381d0700da106d0400040801c80c9440d03001e8048040e52700003007041e0342c52500401d403841d41201181e00302c0b541e05501e00b0036070160600461008800c0e500400101d501c1045800700c05100701d01340c8008000340d035205811004203030809913240e03601008000343d958051207010b001204c45000c03200c2d289801c40000b00111035a331040c000b040300210340c01c00e805c81d440045030041d205035a0119100ea480c0c0c50000b0000c1d030101c0300384003114103001d0002034081c00860440c02c3c19082c4024070f0800c0046809000c80781e8010f01c802c0302c0c4032408890341300f1105000e1107200c60500580d41c0301010840b00e410300425905228006900c00d01010204014605d000706508041c111 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 42484797 1250 42483547 42483559
    0xe0702030307172503050703060501180b07030302090a030f020a05060304200102070906030f0b150918031b03090306090303070c060f02040b0a11062802070f02120d02120c030405 78
    0x60743c4110200100ca00a60309030200c04060402130755190582c02040c031509080c4e034104041907a400c01114003507460004000642040b101c18411066004010601a4068100586480e40c03070300201d5110801c6070701c20303144201c803101c0404c118a4804000c000400f07003110010305506103600e6000280d42070341c02c0c000c0390451a07001c242c01c03a40240300c0c1800400d042201004103550340e080c00308040e840400102c4940240341c002491150040110000c1c0c2c840141900e542035981e10074284040300c000d5900d40980c0b0090100203580c0740c06005845103c450b1001443d2203140c071800741450584050444d0b44a5001801040b80c01a0301c5840410035540008003c00c0d07030384840c07040000901c25a00485101c040020b8040e0000c1d4101c2d05070300c0200d61344022100c90356584c18205004000c0c0780316070180c070001070709054a80801d940250008078000c230600c3d0104100c0350700107000d04034907031541800c80e009503c1c01c01c44540c05105504902c070a60260038540300341d50043c0c6460f44220701074144211 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 42486047 1250 42484797 42484801
    0x414070824070c0501060b130801020408030a0f03020c010c0903050c0f0108060f040212010801020a140306031f1d010c090609050307030201181503090b0a090f080307270e070203030717 81
    0x43c82281261519900500204510350321418049145e84c8410b04150300d055040c0b400180c6038905100315001c0b108440041c500340480356904841000c1c2040b08102059024402040441d038207216404001555803a150348452451901504004031503c069100305090244031180d40d810009040d031000084640c00696019100014001c3c00b41081c031202c046918000802c40700780550040000d0247d0380c07103070498184c85203880901c62008450720390301a00040c041c191404105d60791410700c1c1c1c0c482000406d020304074028000801e140014445004da44039002100050b81040740c81014050a151a401d0b1a0801003c00e0b9120300034400281007201072a0b0441e039090452240708080c1014042104041e20382e05001070150000e01e40c281c40d10410440424036400490c4900280940d2028450b40030060716100d06131603800040032081400802c088807000102034071140407484610b9485500c0c2a42411720120660900502e007005561040007406400b0303400590180c22050703003000542031a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 42487297 1250 42486047 42486061
    0x50601020a06090b011406040b09010c1509050c010e0a0b030103110102031e0a1707021c09150c050105010605040302060706020c120406020d030509010b100503100b030414070824 78
    0x7004850300041d140610703156001d810003040c83d007014100e40d002c445c18858101070904010301841a0312490340c0403841000706103095401450109070140c020140c90041240b02c80780b82c400d8400c0e80c10f08032041c0e00402402e20066820004004503800309a03070038000f450900608020794803041c0406084260b0f080e05200c000c1e031081044441c105440c000780c81881d1880c045161040d08a01030010114080b150302c031000c0c440310f0080d00d02c50352442e801480e01181c1e04040b034200f2054a02c0380010004203090101d9002640e004490a40d644d665481218403a03505000d401c440068200d0000c000c800c100402c0075950704400d40e00d155802c10801641e8a4154064a28110000d5144120302101040010307050350041042002d45240d92414403081e56650f07121800c0f9408001c1341580210004200d600303442c4a400034680c048200c03103100340ea250300c0b03800014040e00102c90485003808081000320408400748044001010b0480040c0710101c1c0030b101d05907070100000b0541000c003800f00e001545d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 42488547 1250 42487297 42487303
    0x30f020c120406020c040c0801060c021f0903030e03030703020604080c0309040f0207050606030a1e0c0906030f0c0b0a230d05090f011a06030f060324060901120b040605060102 77
    0x14048184044545410781c280700d0900e590003a101d240094054025415034908003070041450b40c0e49960381e00d80d40c5a0900c0310560f4103c12483d410381c2c120201d08403039a01401e003c2c4030401c1280d01501c2d0350b6011032440c40c0082c400c603140445103000340c00500c0048000381d000902c0680180e400480b05442c0ca0036800709914500440b00d00c1c99006003000c1c011078208485034010080749010310152099a95240141b5a42c0c0d104000010140c0d0b280c1c0c003824155124004540340c60f24801c080143d41642e840a1001c1500d400e50002c4e0303865840700c2c5090081002081d000320081c6030040d03d041c01c01007010800341a85c04900700c01c585122610800b041e0300280c1e00201c0e2103050000808000ca07080600c0819940c4180c0d6403491100d43ca44442c0324502021000440d40c41c1000a10b400d18642d5404442000d01c9006403140d90940724003400b084410100d43c28000040230aa900d02030149031032410888004410b03481400181003400100002c209402504d070f900642040c0041442d444020040b49 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 42489797 1250 42488547 42488557
    0x60309081206150301091a040203040201120b060c0114010801060608010602070b0f040306050f010f14030606060c010e061e0a110904110417030304060f050c0d1a0d050319030204050a030201030f02 86
    0x4003043d001001103a50070704c0707900401e0394a04985c0f58044c1c64010005000c00c903c003e940282c0400c0224952a09990160300710030a000009400d59051107041011a42520b03201c244504c0f034000a0750040c040b8140034441d000040071640f800417815450450042e449130300038040c41040d1071002540090442400049800641d4822000c10207846c0c01c2c45401c0c2d170410280a420b2944401882c0060b03004450207420100d108001c003c1e01c1c1c0e68413040c0810095a0080c40b407c4800e540301e001d440c90315001440320078400d0000c03203c60344609030348100c1052168002400c0154152030310842c07041c0c907034844d0262110a50141c0300065180700c07894881744940107540c00100c981c0c00342401c0440c001c9010000d1401984511018002d10b0043c2d030f500025144201d9424815603003d10904d00c0391180364000150004919140814407002c40c804503a410b000310344280e075103600c00590011510003202d050f05407484503240c2142460f09040004110400510003e41003580701c0b501420b11181c40c1d4101d0b1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 42491047 1250 42489797 42489829
    0x8100c17091c02010b041d030a1d0d030203071109070806130b06031305010b0d08030c1c0228020a080a0f05090406030302150a02030103050a0f0303020c0a1407060309081206 76
    0xb049041803150002d02800c1d0201d01a40181e04201d200c0034004109a0b4600200c60b08101550400c11001401c481c107290904d02e003200c2c4030704103030240a1522552550003905010341d014695903800ca04040c1c954801c29880e080c0100c1440701002205503000e0034482c0c200301c0440300b040e040800c0030855006031444101c03580d8882400014011042c110660102e4820b2041c170090015200040c2044024210307080c0240c440503003000014081c8070500c004061803c041c40c40680050b074420401001c80e040b2844010000740400700e0800c41503507100b61010707a08400c2c40204555061076484800c0c900440c04440f0901006007001e0704024014419030b001c601c000b8108000306070f034038200290344a4000480070700703410f00c01d0085480392145000b124141ca402800034104003119a44000003081c80c2503041d000c05500348080007000d032050000710310640c0620184503a02c00ca0480840c1004281d42c440028035103400e04600c00252110f040d6041040310300d4502e42240d440c1c5002c1041c0f001c51a60380 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 42492297 1250 42491047 42491083
    0xc030c0b070e0102011a03190c0b03040813052e03060506030a05070306150e010509010c022e03020702010912080408060405030a080105060a0813150e03030108100c1709 74
    0x10007081e6025490074400c4074264004d0081c0380c80e07105040300c0c4486001030307160183c000000c01e4a16254010040c0b0a452252003103080f07407a50380c1c6141c80d964100380e5040b2030701d4200207410398520768007801b004007034041141c401d0700262100d008404078000320061080d80540c400d0020003028040c1e0302200c002e00c005000b040d07403450044c10800040100700c40b80d0001c00c0c07038000b0216104035030548040f0104029101c000d081e1a002005441e1500f1180840b4100329004205d80c00686451818204100c0e081540302000c04624006800314905960910708052061181e41c001d46e030f00c280e1141c120f440c58580f802c0450840d0038113400610481d0410403c6210710000d0200b0800c0020050040301516617070500d1590301d4904110b46031046440b030100151801e00402d000295042484a52a11408425601110540e060130941e088045241c0c681d8001200410400000340241c500c60102c80d01c0c03c0201518200000c3c2030002907540140400781020700090800c0e20400004030325000c08616 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 42493547 1250 42492297 42492301
    0x405090c030f06091c0203030f0a06050604060507020102070b0a05041806030803040305040305150103030807030203130512070506010f08032b02070b1906031e0620030103031701050a060c030c0b 85
    0x180e03603441058503000e00b00d1045041da0719600581c5c030b00c2c0a04c2c40180ba400780d0302e591070f6201c100702410400341c200f808041d604d0a0029196407140c0040000700714a0700ca00d0740f5602640006418103e00f43e10120100e2400c1150186481e0301070200d4080d140c0312202c2e46205016510704c0c5001b410260001032050b02c000082c88249034105000e0400c6034444c0086410045080700b403a111900c013848020082107281012030304d840d010790081e5a00100c036010192440115031501460041c2c0b14920f140001d0002a204081c0f21081c0301403400b41a2160b028001c00b8a443d010569074440c400071840c6020320b01804800c500c0307c8120f80300c22000404415900d440c15810300c8502c0344c50698000600b207000c2ca120080c810b0b01801004102d0b03400403002c070b1980c0040102140c1500300d03d0030856201c0e0f52038881908008243d403100c4480c401100c1000e440358114075010308034104817441c0c4551a90700600400c42caa03120b8441c0e00641d85c0300c1c0717002c2e4060000f5140c02d698810802c80000c00480c00c00003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 42494797 1250 42493547 42493573
    0x601030c020c18180a0b24030706030204060e04020708090607030917010209040b0d02330418050603070e0105010f05040801090b0f06011d060f04030b0a091506050d020405090c03 78
    0x16114000c0c1c2d00001e28500c4408060b80e0340740c2c0da1171014001010012500000b4410300441450705041c0988a0103014440f035810000a0802401d50002404203501103002d0001c241d00605850701908155000c600d44030040e00c4900450240203119031144500050301c000309842108480c0007800240300349600ca040818405000c0d40212140b2401a45001019a65440c00011603284a5005031a041d000d07030703181ca00114400c800103103003080342c0d002200c3c4001401503d0010002000041171215031034001d005400141d4501801d154801c1d440381e4414010168104c040e1070443e070090903c42c580c070044500c242c485014a5119618651801d200001400402104544100600642e41c1a90381c1d0700e00040d03400900842000c0340007805101001400c0c1014030051410100e02031905041a94943d00d4030820305086032181e802980360048102040040916900e040103100403d000c0c0500700030205e00d180c03c0100000e8810f984580100e075102c40305000080c0600e00c09429203401d0030b8052 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 42496047 1250 42494797 42494839
    0xd0e030906040602011415010e0405101509050405090a0c090c02070308040909030f0908100e011512050607050f0a0c0c1e06080604060302180915040f02100905090601030c020c 77
    0x400041b401041280040d800c103000c408000c040c03c0341610360640740303134841d001d00008100040855030000601000071a011010140d5035203e907881c1d90310041418202018082176038409001549594803001c2814001f40010103440309840600400113801c406258040703150000d154005068008006400f1490541c0343d0000f1024038069101c1044c2d000d04140300b101ca01d20389128078035040c2c00404c008503000c4210b0304641b034103208200020403298070400c25280c0d001030a0b4440d200030340c950800c090070843c0030b001e5650b0100890030030b5030505003503176004451841030f0000f40080004507601c0728200440901e5400c042c20302078122022071500c44201d0140f1510704d0041201060403040095860325003405040d080e264068203100d01075001000c00640010041d1a000d410300440c900c0220740e90b02074005070300c0380c1e020721011611080341d80144600044401e20741c40420025500911091f210030710030640000c0d0070310740003031802c1c80d04400300e050024814180c3e0303001c00e10440c46280c124001c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 42497297 1250 42496047 42496061
    0xb03070c050c10050a0e01090b0d05010f230907022a12010b030304120f0602120105040b0301050f010e09030409150305010b060403050a03051803030c0105070305011205030d0e03090604060201 84
    0x19801c980c40d01064404000000f0040580306001803010404030f0b84042c802c2c00044000c07501810b04001894460358803d4180c0c0056440d40d142c40c0d60b6000400038030300c4030316045004144a01e02101720269000018200a40c401c4515004030500404079041c0d9100b04503008598074076000c990b49241c28400c8010701d0b01480c9000ba441180c58115016a00c0d40600c1856040e6030700400a40ca13041c5800d8010526208821080d00c0c03c0119620040c04900781c0e000412002e42c074030404500a6042c001044100e41840300c1c40c50003a032610003084440001d1203d5107054441d650905481651640c0e22a41780d84200d4000360181406c0514803440108000040c0c800c2d00d10401c000e00490000c00184841406140f202a1035607011088608c04a40114000c00000c54454900c02000d01c603031000c01e245a000358a10b04903a9075031010007a2040c0d06102d46030162180c182c52544001090304e0f132030340e2802000c1c0502c4502e90745500020000c0820012610701302c10203014241c640740d50f400081d00030410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 42498547 1250 42497297 42497303
    0x804050705120a1e0203030a030507091d1503011118030d030203070f050309030d0c0203120c0309030a080c070b180607030c0504030311100f020c0705030a120c03090b03070c 76
    0x124040031640c0d241c1001190308010b5803a004110b500c600351100a4100c181e9503484681103481030300800540c406000401c00c10201c0c1e10049900c0c02e1810f03004040c41300550000480c5003039401114110540320f80c3c01038000140700c1055440c28941e20010703005002c130031070112891200044061001110041c140b90140048040d101c020740e80381025030980c44116040030006100c80d400c80c900500401c06142c0101d82201102d047c13200803042c3c0030465040b005d4480150b4004501e004c078404e4508059036024603003452103410b40c1089071503a0703070302d00894501c8000c0c48403000c001840b00038000b041d14003440e0007007a0031015040c452101201c2c0d2510340040906070041d8000240da080c040d009032081e04d40c10369101454980307585c034225102040c00030b10394014003c604041b46550001e000740104d0035a1000c0050303071070703001c2c82a481c0340c01015400035000e50024610b800226581c890000e12640d65170810801d2036219250032180400150803110b082803001c000d001040c1d61182071409050300c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 42499797 1250 42498547 42498553
    0xa030305090303040203060403141c141302060a0318060515010807020106050d0201120e0105010605090a050108160302030907030b090a02120f0a140312010306330b0a051603080405 79
    0x85071691980c580c801210040e400d50f02100110740020320230002604000607401c10242003003a015820202400340c009001100d54031007017194004548143d18030703040420840012071203c1a5404150701740100c08410040c9a80c4401c9600703c82c80301d400d400d41c841c1d40404100021b00d440c2c802e0082c04131044100500007842c6c0c900190f52540144249029079400620b030301da0341404c80c1d0044450342003000001c0300ca251500d0311f000e02c4402c00d005280c00b0344941d407116510b071103121040c08000711150b8850342c104036408003803192401103070400c0680d5000340d1a026950756150a1114a03001013a03100130700308081704080040509000c81c0315010907208035080c1032140454007074a0307a26046020303385980d07004601050002900800c400c4605103d410559042c00e11289240e2032249003680107507403e586505031014090f83c080c030050f00d04010f030381c075801105014148142c0d1140c12806201c0c004800090044503080c02802a500c0000e0004405580a840d03440e00410b82c19050b82d00f140c0a00c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 42501047 1250 42499797 42499801
    0xf01060c050303060d02060c0f060402090610090b03060a12030207090f0614010e0a080a1401050f0c0706090f0b04110a08010203061005070606080609030703020c04020901050d020a0e09090a030305 86
    0x9481550003458540d0400010350858503048104115400f0f041400c036401030341009036202508003402076040d02081e0801824691070301e40144030225000405040c4104e03440c12406035503580041c10b0200343c07180c48015944a43d21040821107000d269005143ca1003101c4003503404156000580405440f4110401d000c05000d404400b000d035003090040c2d51031600341c1c0b4203c00c03442d4400d551401214200521030b404265035903407858140011a2001d8851050707000300c02000e078201340a5940c100c840034102181c0d600d07128020108078052100028880303911648a035080c0078009546409564009104c003000342494904800c40d0307003c24500a000303121410300090148010703c252803140001500c40040070305001ca044640707511540003210301c283d1b02c180104050303038200440751003545e4400056558074414100645400003500499100d030340100031200c400d0764813200713480c0640c656413800b503125900da0000340c82142c00d0200f9150030000ea0740420a00d100000b400d12800d80c080d45081043da = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 42502297 1250 42501047 42501059
    0xf1909050301090f0f21020d0206061017040503070519050f070605040603110403080406080f0a05010803161a0a0c030b01170615041809030e03161701230f01 69
    0x29405894020345816440f2490101017120403100e070450520a29900204c07490180488040c507000018440045e4064020b00400d00d404000640c2c0150b030441d007655240740c54800040090f8400358084060403001030104042050400036913800540c0f00007964504106001d0402003c0c080710b60a46035480340d82c040600e60f00003c104041074407010350340e4924081c202001034010b0702032240110040320742048004082043c4402500242050366184640c50809202d90721200b0f0005e00b000a100e45440d0041200c82d20000071502c400300134800e0700201517814100130b02e51544070b2000b40c00b4541203e042080d050891b501601c0d4440c1681c03410881c040e00030004440107460304481e000b0190440000c00d0540c0342c1208504803060780c01d0307034152500b919422a0f0239241000c000390300d41c0d2a2034220304410150068219a00d116041d0020603183e03114201e500e414101714440c1e9223108448942410403498290010101240c0c442441102d840180c0170004188200300e4074005036561440004c00c1c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 42503547 1250 42502297 42502301
    0x3a0b060109090e120a0c060e01020306040b03070b03011203030605030f07060f030605030a020d02040e12090a050409051902041d070e07030e03070314120f0601030e0105060d06110f1909050301 84
    0x10f1004a1004200382e4204d40181e104035070040540e4001e12484200c1000007a00e24002c4454030b40714400050386a00b420b03001e0209a41c481c000c0d0a100e500b10030b00a001a0650100ba2411170382d242c4400c9103011302905040e00140380030741009805015144041c02c0c03109000500c201101e43d139988a6200f141c20000441c21034181b0f01603030341e1580016100102603c0c0811701d038030819000800014460300001100ea141001411160754140f001180d00107051070320060945c024103042c0d8003485400113507610700742c4516150261084860142003150159202d541c001c1d0320340c00c22416102012090030030704030381d14440e5124004142908100040d0740c1d5100c0d0060750340303000240c0d0007941001180d40c2d065882010418200d56072030028000a5607240c950003100d4050752007146405424102000018142d4405001c0e0804983c1440140651515440201407641380c10410000d144070022600820380d100c1c055003103a10030808500d0040030200300300b0707c00c0e05451a4891800c0680c0c0c480515007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 42504797 1250 42503547 42503561
    0x4140c04020427020f0a2a030c06020715050117300c1002030c041d040b010b09030f01020307050901080f040302030301150309020a08010b010909020304023a0b06010909 74
    0x9540d0b803048054000c0740003907031200f000f581d001090140c18041d050a00010340e401441c803600004040c011141682a074020740e220a024140516032040e07801038070007501b445503403100205a00e5000800c001840030f640d003516001d11200c0401c1c040d0796501e801e0388a0790855103680007100d00a040410403940001d01105107000503010b04481b50303011041481d00280c01190480f0018054032140c1481c0909a100851080d481c8640494585003082208603400d400c130001091196a50000d100c04144400d55050440d0650015076903104e40b20b2010a05101e85640c00c15450f40c0003109009030310381c201025003048882a40c45004664818004441c2c2c6a011307a070180140e042000103100c020342c01c00600070500800d0601041c2c243c115404161403403610360003070880b80d5682068084942c1c1c0b2800000050120017400d60031400c09400190000c2c1e5402c0f078400d25503021a15031940001203000314401c02c008540c00410382031480c14044208101140c1c5180018100140804c02d43d405e441081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 42506047 1250 42504797 42504809
    0xe06070b01120302070f030b01030b0f130210030b0d0f02190e06040203070e1201051008030a170601021219170c0a0305060112091a0a0905030a210504140c040204 71
    0x40c15034607141d0010070b10206450240c04500034200f02046035030720051031400079841100850129855410f001e195000d02400c094850140b22041c040c004042c000341e2004030350112041c03844407030214816402001d001c88289d820112041e80e05060041d1b500603005c40d1402a103180d8007c81030b041c6040c90121103405001441100500840e61605159015540c04526030030403600c40311184000a500d5041024078402c0c5030345070010400b2054008074100c000300034200c01075003070080114018003508003207042c4400044e00c2e000009ca1582c400c11003c454480d0103020180e80703002c080820400100c0080340300000c80e48036000652b1452482440031700c20303600745a8090501010f001c1c00c901500014040d0350410002c64183c90901010303104481010384101549605080c000f807000c4a9020001e00c1303414080d1800e070083c00800c2010003150544075072443c0006500d0207194125441000e8140500001c614100400040065111040c4203418101d402c03a0301400d561000c0100341d02c140d01a078 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 42507297 1250 42506047 42506063
    0x301050a0b030a0204030b0906150306060d03031a090115110703030801180b03120d05010509040302060117121803010f0b030c040c02010e0d020a020a06030501060807140720010e0607 80
    0x401c03951440c100a0764110f4201c0d880076252680d02d0b105c40d00001c400b611119140e4100740140f02d407905a40703007007616910301600680b50038903103400040e8100b1403000c006802e1503260511403040c1820001025400c40c0018020007695840d0305904554030721030869400480c142c08202645c003180041e001c02140d50558406003aa82805001c01640da2640e0300d8488082d01c80075a00c140d6036044c030210751032440301400f1540791004000007a082d42c0040e84040c0c0a07010b00400d100c00710b580451560706680000341c0d42c1c800c00c424002040c1c030f4500d203881d94800c942c8021070710400801307050741c0d02980c604080300284052816090a8422281c0b440c1031b003541540440004c4c5401d0815800155220005000019100541c80c8005007030221010f411001600300001440451401c03080d050050005403030204040d60401d40042c003d0fa802a18400c2448440609085140b032241f00301d61a141d8011142c4407940e0f141840d40c071a0380c03154141b203404610340c0b0305049507030b0400c0d205a800803a000421 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 42508547 1250 42507297 42507299
    0x20601060818070b0d020910030509010f0e030703030209211e010b0a060f17011d070507110d02060c0a0c1a070201080c0304170c0607020606040e061504020c07060503041203020301050a 81
    0x10720541c43c5d201c00610103545800380010700040e80d918045940f20422624041200d01e04450b4075421a4081d0018220146c50005003200c106400415640c400d03506040050b6182c485800184010803c51400010289142044000e501c40854900c0d040d14190319a031030349005660a1609940c03200c0c2d400382c3c004042e46030401401e032107441b100048082c1070800030544110340d980042c10540c01d81101d1500f000340d6501c0c0404980c1c098045500c018280b400c24105402640c4402201d1920091144514101c40358807082d543d50307400720303003006580c1e07070484018483c2498803084146452243c2c621400049140b140c0349041801140c814946c160b462012580d0b0302c11001406401c0508180d80104103018428045a141c0d0b00074400d000348007008040d030f40303031042c0024500f00000740444c1c006d85c1070100d00c4d079400c0000646503030800c020300040503411915102183c020700441d10420141e1140500000e202d6800400440c0142e000c1c0300c16140380c014118003030b01a840f0a218054000c08100e070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 42509797 1250 42508547 42508559
    0x90a1a0a14130620010507121a06030a0509010608060106050d0e120a0210060506090f01030b0d0501050a090302070b0a090b0706020706090b01061803080f0c03160302060106081807 79
    0x814120160003181142021010401c480b1410829000b0b80007090741816030115158002401a242e0002c142c0240040d103041100205100060840c0300344190319411448403550740c04403c00030424029080a481e49414540d030b5020f80020340b9101029440d0480201d440303a40403521b18103850503a107982c0d20b00017010842000414480410004c4c50181100c1d1000c903003000c1000b808205600c1d4028170803d07541e03e03010000c0ba034640d44409e1041d10100490b0b10691503000c074240140301c090074002410131030030b000b042804603889401401940780c40200003040d80d0580c4424582c9000398200c1c1d49081e1145000c1c0b00d680301d83c0b0100001f092408404005503000540140f050501ca0840903040c104199159825924240d40c21111050786800502c43c03554040d90790400c0111040210700c01d2861921250b01e54415001c000301280c0001030002c800031401c10440d803021242142c0c0200c0c0b02141d003402911342e28203020317030b0700050740c0b000100d00b9540741841c200040121980150005a20305a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 42511047 1250 42509797 42509807
    0x715090308060d14070b04060f03020a090504052a030106090501050c03070b0907030b0108030a08060102160302060901050403080c0109050105090609060f0601200105011703040b04030206030a14010902090a1a0a 92
    0x28404a41c20600208404d40e5043c0500c1040020100403104075102d504162001c1c1c0544601030030482018414440760a0319640300e481d401c1100c101341da00107100c0e296118000f150a1352514644900e811000c40c9404960b041801981224265511681c0d11500d070801100c8503c10324401440c1540280002780200e06401085500710384810121100d8a0307490362070100c404c0c026485580b26030000f14801c5900c90300071340403030761180d401d101505000b980c0a0000040c4401c43c0030190045002040d403003002e900030f00448000d140c00c1004192601c01092156000c9e29071204110b40650030500031030300c10782c00020301e00d0284042030702900140d91423910504281e0030061000d410800b80d800355485282c0b840c1c00e0100380050600c00481c4541c103041d0380154016041e14540c0300703a482040100403503180d08003500c0c1940e0341150055030302d4032000000809002461150503061a40304000540500550f00400840c041a5500c49096680d01c0012000011041207001c50020810640032400d110b9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 42512297 1250 42511047 42511069
    0x60e0c031005191a07080304110301110c100c030b03060406020307030f02070302010e060f01140d080702060f03011a0405010e100306080d0509010207080c0d02060d061a071509030806 80
    0x105181d52055a81c4000203031512408050a0440441841003401070806480710074040d0104c4400c420702e07107115540d070610b003031000500188c5100d032040c942d400d296800707401100a01c5100d0750816107a45000b4061a2100403800c814080185004c0b04000100d019000c2c1386803005005001d014182c1e142c0d00d84401961009103e64101a9140d02d410807803480ed20180a200d0300039800001c407050150389051078014003802c28951095038900401541032014034091480505403040310348040c01e46420003003802060002035010a001c101c403e05206a00040c6041f102000c1001d075902842c0903580e1400d10440c02103070700040c1c2440740c180442c10910000b078804015454001812035076a048035042c4400b401400d0b0000b480041c461401e50307410450a0090a4100c1c040c1c00f05c10071101c0064030200e1400340090142002190018811b0a254030410081c40c0080c030040304081180800c18050380048021a150007408000c940d1501322441100c01103a41601c82040300e85404040103480c82c0c0f9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 42513547 1250 42512297 42512311
    0x90115060c0f020603010306020c211806040302030607031b031503020d0f05060c190504050319080d06060804021215011701020f0d0b04050112030801050105130504020a0e0108070201060e0c03 84
    0x2c030301204016219440198001c600a40006840d04a481400d0b030410150085120801404a0103984000005400c548001400403210185072a80c9408519140281d0380065854012039080015081d0113810241c0749172420410300102c00c50302e07207040e070860b009441a0304135800340202c180010309180300e000e02c10318081e868803040c0c024190f40305490a18203c910541c50b43c00469040b016000741c0c014240980a0740c2400760030a41040046a6254542003203c41d00551003605a400d0200c2401201c800000c8243c042c00f070300d5100c410142c1440d60680d0101d0064040c6500c001c00d080012416088441d420240000e0a034a072030301d00c07450a003045150b241155400c000b503d113411200c000400340e4281201000c00d8092000c4d040008840c01644613100e583e208043c6100000d034011844c9042d81c40900b0840d8549014604506865105400254015100050a01c0740c9500101210041a401d13070701e106942d61500c00880c01c0e242d40c0d220303c0700900d5400b0301280c1407103111000b840d84201 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 42514797 1250 42513547 42513563
    0x3050307031d0d03120606030b090c1608070606050f090c030615040b04060c02090114030a080d0603021e04050a1107020d0f060c08040b01080a08120612030307030c08090115060c 78
    0x5408000540a0f5064a030890214500c004c07880322090b00c42c001c01e0000c00240c1010410701d90f90002050701908000c109260f0010300050f503041c001003c0e0903007914070b504655441d4407055a841c01c2e000400311400341034414845045500100d05c0c200000c984201e4a0417146810340d100d8906101d032180341910380324126070382801b0106d8060b0b01c020250004100558696802e11010b00501c101d000060700031071194038402c0020002ca4500050240d0301d5544003c030305070f07200d4401000c44010011078100a500c0b800c1652004100043c251840d0203c4100312010031168031480d00d02030031900640320890248005000f11809071410034900a1454040d40101c6558003041d503aa1048074000e50030000030410380400d1205100d0103a90090141c01c100303009045c0f40c0159203440c0b400740500d080000c0351450190018085440c5d44068491966034802240e0722810412005405000703c01c28a90001d03c881c00011b90600c414054a50b084100c0e189039945903040480407500c807102a08142c0d4001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 42516047 1250 42514797 42514847
    0x4030201111315020f031309050c070c030305070f0c0603020403060c080702250f0906030507090c081504020d0603030206060f09010b0406180e070915080420040b0d11010f02070305030703 82
    0x1d002d2009200f101c1d61036030680b030045d040098007400c827180070700400b400d0242485400300080c00096988280e03501420030644803840ca240c038200541c0c0e5494001c0407494804000200da07509034010703005592003440c0601c8081c0701e24008175561242183c8400060344000359500c00b503003851000b01e1000c62051910381315a07444904151204006ea48a403002c10740c2c3d82c0c02002808424403803000a40002e07441072040e031200c124010804400074144105800d44044920201c1ea03403541211800b80e40c0060900205d507490a000e500c0f042c088456a0282e50701d04000000352503c0040035050351030100410382072a0400c8800c689a0402040c4407090121180b004103c100034480d119104655643e504a0b0160a0005000c1c0c0400080d03a040f00740304c1c0d4042072000245841e58180898038034120540c0004043d500014050644421031540240040100d0424030401054880c610042a2034090050464240403a6603d0789440094510b4000748419000030380324403000206041b40f0050940c1e64 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 42517297 1250 42516047 42516073
    0x30e0d080304050606030d1d061305040e0703020910060c120207030516051806010206041101030f0f0f1503050d050c070f060c0c0807120b190509060403020111131502 73
    0x1691040d20252104c1d4004010407691380782c1001402072410b2280340a0000d01d200000c02542c08071400d00c0e0764480c210202d1001c071007a5008441e0001030038002c00c240140150a0182900c541c0e09001c2607004601d448002640d0302c030031403a80c8007140c2c0789035151800c5155903115003002450f1401d4101c01c50160324000408230700100300d8011b98400b0441e422440601e810200000c81218150012220b04003608015080c4c3e00410034990044c0c101d05685423080030301004034000d001e446680c19113a0b00d1b00c41e021262614941c0300081f04190160301704841034564410108030030842c800100181d2041ca40098540c0c8110b01814042c01403104440105413500c10015441425800c600700003401100c800c0103202002150360024a4a4005010b5090414074144c0030001c01280151540c002c1002051425010074208141c0650900d02001039041c41c1c0407031600d410007a50305034015820140500c400000c3c01c01101c1840030040c2d00d0324481c9181440040c6044805860501035000e158600c1d400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 42518547 1250 42517297 42517313
    0xc02040207170c07060f0905100e040906020f1c0b06070206070f0b040605090d0801060807050a020f010c0c05070812090f0609030f100e0604050d03110c0106060815180103030e0d 78
    0x14090003080a01301043c00c0040003002c2c1c034110150f003410083e0040041040f03469185005990001c50f16140c118036050b000850060484041d00500f624400200074241c2c048250182020090001c1c0a14084001020f10419540d9840e072490703004004210031801480c1c10001030078802e201d1072040140500903182c2c12500c040481e02990581e40f58000c02c1700d03503a014070005a880c1100e040c07215895041ca2001806150010300c00c10a00400044d00050780d4001c100d07681d1810001c10090280d0304c0c80d81c0c802441e5005000b011180c61244000100e50508041070000b00e03d02400c2e01a4288210b04042040800c01c607134000703030040b00c100300f2080151002c0c40303031180c84903060b0002c0c5940f001d01c036000411504e580401084d107820040500001400102d82c961800500f441c0c041a4103840b40140e141c10f00c1a130614044135841d04000198140d000303e00c1d80e1044546280344403115540806207c1030714107142850100c50481001880024017440071a0002c003400780c000c000e410b2641c0e8030200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 42519797 1250 42518547 42518557
    0x70201170405010b04050f100501030e1006030807020909030406021c050c060a0e0c01030903050f030604060518070e010e0d061113030f2010030c050f04030305090a060f0c0204020717 80
    0x240350f944580c1c0b500e9080c201030080c5030700501c450008203403928100c3c00c283c2ea104190b000c0c00b070406032211814000c0da14104600b058a00c80400304000e2641c5e01e14141c84e41c0d81c0860002c078020f4003c80c1c0029000d100c04404d880447c1c44a0f0042d0500d070380ba035404c064109582d0407a0070103004c0f040c071401255031020065203118014100b0002401c0d500d04100300c5c80c2040e41e090b5103041600381091030001960000690310031140c0314070810384a855541c001000b40c4540d0f00601c0d004410601101c1d00b0b01c0308401045d0080d0381c40d403a6a580422070000455507010500049900190701e040d2100001e541d662000581000b48440281016500d19560b0940d00299106403200501e80d0f8000084c0544a44906908003401d0703800d880c100580030106610803051001a01495591101e0605d86030052044030038400c40300c0a02540d6640740d2a000d08141c00400c00240030300a000c80100700e140c0601e0990300b07281c00c2d5489100501183e6401c010295100300000c44400c0404e049103081500e8007070180c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 42521047 1250 42519797 42519803
    0x120311190314060d020f0307150818060f010b0304060f1104050103060f060c0b0714030412030506010f051b071503060602160302060a110309091f050904170702011704 73
    0x2554400c128008003a582c480c9698440e038070032841841095580c01c0c1030341e00c0700c0754103075202440e6514010009081c0b410720360100e042020608621000594407403031031441401801c5008400550301304120340d42d1b02c0d044605120703903088200140000f500c0c2c8409954061300c81d00000c03450a0104030900300387c030011401007069800100d014005980c040c050a0080d02d40071444071921442c0c002e0042c1491810100a080d10701044045100b192007106001090004109416540d003064900309020b440c5400300580000d1824002c201c2662292100c10f0306101140d980506018201001900442101c2d8803081c00e41f00d26100014481e08107404214183d00e0707600e0008080c0c0c41c204000c0d0404a0340124408803114001d42840140c1d141c00a50749071608501e481c0c000140d903814068503500c2010180c076488001182044486448145440070019807a8400800c90f039a07001400002001501e006007200d0103044035403528240400038001d103d00524010b04049001043ca0302c00c04da09640603 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 42522297 1250 42521047 42521077
    0xc0903070e091b030c060a050706020a090504050f040b0c0d09020904150b0105030702100203060105091f02010e0a030912030e0a0b0301080c0f03060708060f030115090e0601050904120311 82
    0x101600c18001e6055800c0c3c1c82200b540c3d0040c07100300007500ca0404041091140b0008161503a10314407407030a03a440142e011070119a00d080322103015110605520800d4407a44c101700001e1459001e51600a018551003461454162100503d552403500840c01c00300b15035a0b41c8031100c01594407202d07450302031805028060000c01d500d810050540360f0250443d81030250420502880b2540020303200c90440b0111801601e903102d400049a01d80303c0e006447d98042c80b003a065800d000c0480302408100100da8000f0400c41691506254444541c00380281c0841c0c1d0101c010405540609100d80b8201d2091800c000c884600500082d003195003900710b240c0600002c8018040050200111208400201d075510b4210110310000ba68501c0010314002c04c0116580100c0d440f42c072000c500c4e40b5500c400034020301a500c080700f40c6100b4500503200300039145082808020002c1d001080c0f0505070b40c0301a10403100d80d911034a6400f08180248401070070595510420102054610060b080d040c1e08180b003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 42523547 1250 42522297 42522301
    0x161b030614151003090305120405030903151308030402040f020f04080d090b0d0b0d050d02030d050f010503030301030b041506061d01210f18030e09130c0303080c0903070e 75
    0x1c0290582002080300010800902820440f0750303038900303001caa018240c07901242d00e0240307142c1100e5074058100c4840c11604043d06200810030040080c050348541502169500f4900c03100c1e06034500c03130994440154445122a91b000b08050381d005691050024001007507001c0c40710010320807a4801d5004500250003c54241700302d1400780302d180080d03141481c5c4440c103641020060002032081003540c02e501da54803c11100f032900d0f02690940003d4106044d0740501818440c003035201e0303000c484c941704071a281c1400a454000088180e6040e514044c0056041d84e0035a61528031b182c0010b00251859031041c80061030414540c00b40002601e4290381d19024244040180d01031030382d00130300e20350500505000868402c0c020640c85000b0b01d01c803640100b0101c0c82075071401d00424030009518a2540d48601c50801e16403c40ca11034400c81d0f042d1200d415940c0c4101004801c6020740300000d00610300028100046441350900603001121215100d140006a400082c9000b4441e408a00c044000e802 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 42524797 1250 42523547 42523571
    0xb040f05090903030405191b090e07060309050a060504020307030611040303080c092d030102030405030a02071e06030b0103060b0703020601030605070309111c0b0109060317040308161b0306 83
    0x1581c00e801c004000d0096045092542c1c40c2c988520310100c500181294040701c1205101501c4171031640510014950f590030b58407815000003400b0142044580c501c50f40c2400542c1900c40d100e81a1f02903007000280c004203015a0310034004e020083d200780ea0511038201c010007c90454440d6250150700001c0c5155642e1544c600900b4180c00100b040907812802e0140455980b5460f40c9a1031001c0d2120341c58080300000300100d03411a84c1e4a140301e80541c4007000300410804c0000081c240103c0303075000c9421469a60700401d0702c122200c43c2646000b80387c800d0030030009000e5000001e80180504020440b20b88502c1e401c0707070b07503005800290f005a102d0401001409081e2144c0c45d0030400600e004d01c45080c080d219019096483c215003801500420142c7e03060300b41c86040044019403051110005507543e00c03998014202500007502c070482088840a1038514620482e01229840f9140504020b0168500ea10500300c01d030b403d0701d04c050042d412a0100c054214410080d510400000a60500700740b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 42526047 1250 42524797 42524809
    0xe0115120501030b0414100f0e01050c0c0d05030601030f09151a15031e1305070f0e06040f0b03030406030c0e04020306060f0c190f051005010506030601050d060b040f05 74
    0xd0400c41185150a005001050152014503403260308130882d4001035200c0302d000d9140408020008003130500e8200301500300200c980007000c1d001c1d4440000e001549a0141c0e1024034030602e40aa80c582e03210261a10429000c0c4000d598005814100094030020150031441624000d40f0708075415050a10110600c1c8018403c80001c0c107040c541000043e000c050100d8000e41c034040c85814558001300004001c8620001282010001000030030f805052407540402c0403030001074111100e0241081c040399000e08030295500b1207050500c0b01d00c890b100d68060100401c030f810030003030605403102d07011001038404200a00007449166000941607007502c0000304050110f03000b0b14403039401042400050342d91041a40c2249803141800f55480460b05515464207240c03446464006201c401c0d01300078007151a80d071032903650090080d6030100084901c3d84044405c24003034941d20120920224480c0d5101d0340141c1034034204e1840000d006a00c942036100103401540c011140380a120310b050100341400c6d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 42527297 1250 42526047 42526067
    0xc090f0702010c08040201090603020708090a03052109031504050307060507020705040e030711010311070c0e1e0f0c0c07081209010201110408070303080a06030b1509060f01050904050705040e0115 86
    0x380c5096401814507500003048d4803045c1c1309640c01c01d074010030090103001650003100c54241c0020040407040341d80c4d01d0b195880d003442200201648000c00c0209001030040c00445040c020700802400340d41380300c5110034000e02c40141c804e603034a1000344042c40000302d85104040c0920101d07001001c080b4505020841036a403c01007084850300103200c0c1d40002036039404000b02110003420007007903500d02001100d085001f81c103030142c8903029601002030725211070346184e4010700c480c07484c2006010000d200240403640543e441c00e201005d100008410403002c0b0040c0c982c0c90340d00c1c01994000c40d5119030075880c001d1901d8006103004000100740904c0d607024464900715100e805502400d00f460220b803140c40740060300c40502803250110006a0386019680020055030b8041d18a245508224082608000a146443d80104445401704000d450801c808100c0320405945481c80c00344007500380000340070058401014040c041c000480c4051680d0341c8a4060701c103801c41c204920380703000002400d0b1100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 42528547 1250 42527297 42527321
    0x405010f0305060a050a0e250501050301050d1103100c090e060a0b04150203090d0302011e020f0d09080705011b031104060f0c030c0206030a0b04050a020a080610020c090f070201 78
    0x109080420024038003180d1030354811132107100010303507550302000d40001c0c0540000c0707004980100031184100b0002c284080d0350540b02881c050b4509625080150b8030b52000b80149640b1200304003110300015a600c2200001d2100501074131000055103003010158bc02d00300005001c64621030050190311801e10103d98020412154507680e0313480c0c0f1072001214400d900544140c400c5105200c900e441c001c104881010328051710a5441c0c2e402e504009008101e8501125803c5442d0554220a0b588900030f42d408028550002c51401c420409000000c001d00b007012180520107120040100b202807165400301e10b96040c0c200342c0d40d40b1780f52000b0121010a503414400f00c40611092010a90285c500d0041d03050a003002007119640e030a007603d0f108140100294012000410441d040c1407582000c4d24242090b0350901c201d03212000640c0a902506c29800001034407200080c0705460b1903018003008030702900503220041c0c40e120100e00006021201494500981c0c018805411760900c10024800740d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 42529797 1250 42528547 42528569
    0xa061d06090c060717070b011508060406050a06030b12010207050303011d09060402010f1e0f030606170708060a030807050d1704050a081e03010329280605031605040501 74
    0xb03800001c0513801003801c0074010100380c8030040800442e1404840c3c800e60000d0201c0394943c1e41d501800600c0000e00410400601100045941c600b403502941060b64002041e402440e42400c0088ac0100920f0300071692010528444640e103403400e04c0200241800780010f590b4a60620074403a1078036080d881c1307401d40480c0041c20407159480100b4001d0300264246440c900140800b0000c81d98031020b44080d0620502c02403038180e016410010680c0c2810a644050002d00d503500c00c19140e00300410b000e503000c1d10792440002c0415100d003138060790103d4001c003800a00c580303a45951042c0e410042c0111600e6002c190712841d025002a1500300030080880b07000c00c03e162554916440c0d4030300c07000003000080041400f2201403204c603076400007005007110664032581d407401c00c4070640f41c80c080c2960100030007050a011040001171114414175480002a0040c02d02c0103e1503180a22401c501851640c4c44c840482c20740c0d07080c4031481c000180707a802c0090301381c109820001180c006a0000304119 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 42531047 1250 42529797 42529813
    0x706170f01060e0f0306071701060c050c040b12060903030103030806060c0d0c080c0d12060b030115120f0606030203040b0105041a1e090106050d05070201021e07050a061d0609 77
    0x285241035040d054481c1c1d460141160b0041074042800c40244200039549809a5001c00c03040d01d0707001203085d44c003200791169250540d980d0801500c0400310000090b019410414446c0c0242c00c0c0381d0000102458050a005203081c021040e181c103181c0140c80785202d641000004005050303000402a0708510100da80078030304000a03254554581e001000c00c03090040c0c8160703490522802000707654169451100f03031144508140c80c004c2500c1c1521002e40c1100340380500c0843d072108030000f07490686107603000090090240c11416203c044e281003050b103140e5101c1d42a14245922401110018421500c01513124100343c40c1c42e0759030340c0c0140c00041c003861422045240600c00c03400c00d0000c1503000c0c3c8044400c02c9070800403058200b00d4004658110280070000644143d104001b0710b40c10856850401030350b160b0070400c900303038401e03501030400b130224156200e0b541100b00d50092154922400403210403103010307a075400c10b030703500e00b05010078100002426001c1c200082c8034040c2d1104109028000403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 42532297 1250 42531047 42531061
    0x1b0506031008070504022104030e030d050a02010509061b07081c020403031d01270806090d0f020c0f040c020c0d0804060201060501030b090a0914060a0209040b0303210a06030212070617 81
    0x40300c60b20f90841f540f500c41d000031030185405049280710760b21000e030503940b0010b500350300640568006403440c4010340c40e100001e400301c030001c5407090142c0c900b03003210301c00220084403001c550f402440003594040c100300500040403841d180351841103411443d004d41c50320310b581006012280070070441d440f410314070221400e19030f071300000840c1c1c50403d088249245030070703404c120008e05200d60032a003980c1c85844240800d00200243d5102c0c680c89030741d0b4602c0d481c5c41d828400ca0b1620300c0c440103540c01100c60200304141d4a8180c1202d05199054412500c01c81c000600042600d500e401e400c1d103080c1400a03007032107001e9086c061180501000e00f014040086403402003550414010510091a40c0c0c0d2510358080103440d451941e6500c106c181100c20380d091081c0719200a40c802922a03104038a40014a00b9504010003614003a103010207108440501c0010444181c8000500705225955a04008401640d406001b039201e00e5041c4020443c0d241021006802c40c080414103035444240b5a02700b142c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 42533547 1250 42532297 42532327
    0xe0705070b0c0d020409021309061502070501080a090b070c0302100e06150a050d060e010506010813021908121207020105101202010207050604090203060405180a1b050603100807050402 81
    0x1014a140405076030f0180003421400034025501b06901700d90000034511041003c40a040c0d0503124598801c01c117080c0d6400d02f00145903205410b207070140e00012004c0141d503020300001d0383d0118141c1c50100c1c540c0750581c1c1c1e42c600d420003110b008002c03030260031414050642c100700321000c02302003d03010080384840d03a00f0b030350307450300004c20105640081480d500300c1e40c0c4841e18454024503000c0c0c0a40c04110700d07032130444040d12005580303651a42c42c001c0000c0182d84540d003654010b107451291100c03000c089030244100a1403201c0c0140703c3c0d260301240003074071403010000744c8802c06000a25549a014001d0104442c44000c1c054100316810b11007403012011412201d041100c10340c0300400c2c0d05101501c0103030704003d4141d0100c0e034480310220f00000c8240203500103500c0343c80b0481d030800499942c0517880300d40e5401c0140c50141540702c0b5102c0c40006401180c030f032100c1d0300040c2c403c0c0380079603980c400140640d1040b02c8800d54804000d5080041c40c808104001c080c1500312029405c02c046180301081c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 42534797 1250 42533547 42533551
    0x120c03100e0606251502120106030e0c130e06100302060a050d0e0607030204090509061504020d140a02040503060f010b070b0a090f050f0c0a030f06020a02100c08010e0705070b 77
    0x2050352003002080e425503480084850038250504c040640010030700360351006180c40102503928907a200384aa8085e10f09200300c0302c041c03080c000340c51000e0f400d1075802c40007020315041c01c149500c580803111032969601c6070001d1101030b2440b4003143e0304080002c51030034984041c0c100e140c42c1400d41004d1006994000c16142048550304c0c0c005d4507030040c6002e00d07018212000d181c1c41c8601991061040c00c0da4181c005001b5160002e506201a84401c902155165000c64821222050401003101ca03072809030010414a00160340c0801d051a100c1420704a500c0c083c1c501d1b000590b400207041049050030303c0900e40c000d0100c29264115807420007003a81d5480762801c0103050403420000500d0411807940600d280541244890a034100c0602d80940d840104911606c114481c441810b40380d450082c0d04101660350110301c010180126913944400b070b400001c0e03090300358010b1401643c03040507107120724500d40300305035900200c2e945805850000ca0b807002d000c8004010b01000140007240d00b40d20b04507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 42536047 1250 42534797 42534809
    0x6090e060c071a04050303040204061422090203070b03090f0a0803060409020d15150f0807120204020913091505131209080a05061803040f090209040b06030c120c0310 73
    0x10303654090700e1510f500d40c11003002d00381c94090300c1c1505000a0010010265108030710a4401b000190786030349032101200d8200220a074000a1360310ba800c03003043c4040c03d503500e4240101c8042081c4200380e002a04208694114000b2940c0100410079a01d9007000100603019030000501070510403500d901c0387e03030300c001408103002c0c9448414080131915034060321528560041140040b0b14000004000034029140440034025408100441c21845c4028810f0403510300d64014840070f40340582040c6c6041d0a07410691f400365080c0640c03026602d4020f494107260024080000700c0c0b0f5203615002c441107a08000144002d03151004000c0b820b0700150603406026008a00ca14402c03803040310880d010b90f841e411a00503805020301e282704001c03001802c50f025400c485034821006481e01c01c0c440e031f0380c0250b104c0c40d803820810420170410300034594001e08140c10f024102240e14014a0081080351307201b546c3e0350641c0070740099a042c50b40c02c100c00315074100c3c603903007006450350410098120440c441c500602d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 42537297 1250 42536047 42536071
    0xc03010603180b040b04110a05010f0c151b02060714030121080a050a0233070513180b0406050a09020d1e0e1009050318030a0b04051006090e06 63
    0x4503125154000082000d03a1000360f0b00320701d01d41894001540c1006450071664585503036285401483c00ca141c910540e817043e0b440e146084c22598045980c90b012400580d00c0d0400c103e08507605980c94000c51210074814007944604200122009141c543e0050113031082081c09c1c04603082d032000e68011a81154082c05a242c01a82ca20718240c0d03040c8004080144083c000051321030301c8a4100010348503002c0540c00384c54407604110403012081c51880c080081d0344e00f0006ca44460460310041c8560061607524083d800c0010919076401105415000040aa400842d01908241e0303280995103062030151003e011083c03900d004185410068020403c5c0750360080792410580c0f5450b4406019410f103011070012060700ca40d100c4008000d9440300340c426003d011340c2c20012401c503014078a00160701c01d0085103002072601e0180b620805c01c0041c2079240c05500b00038404905140c0003240114010303405031400d08100803400d001c451a0354020b000060510005031140d86010600340d50080c031800c14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 42538547 1250 42537297 42537311
    0xf0403060e030c1b030c0102010e0303040807050a0803100f06020a150c03270308010501020607020c09070905040c030605040b0f0102101808210a270c170102031506030c03010603 78
    0x2290840c040c0040040f428031602c3c8051404120701042d9a441e0801581030300c0d42d1011200049082c0d0324448805039443d8010004203001a8607074004033100d03401031041da81000d03420350301e00005600959001c954a400d0035003e001c0646450f100400174421400100002640c5680e1040b200c2e503510300c0c03603809036920304245110b0380c002d030031100704082283d5500f40c0300681050951b06d4907840140c141d0001e0718030b0002041950001510502405494000f40060455030303040018000000f080003082126140380040c1c152680d01801103102000e88010600c0c03802c100910003207501d000c045502c100b03280030744250184d0300403d41501c8482c1c2c0030300104034014041c810b00d045000c0100001c00030000044c0e2055000103565400e100c0c60b10104242144d500c03010350300d0041d5181c440b03881c203c901700c621640009400744544401100c0c85005004005542c40d03015034a00b020260041803540d400200304403030440003201a62250364100c80840c114109070704900114001402420107042d95005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 42539797 1250 42538547 42538571
    0x714090f070e0307170d080417030c0d0908030702010b0102031306051305030a0311070f05060f031506030901090314040305190602040f06090306050603060105011d01030209030f031c020f040306 85
    0x440c2d070640d01030180403960300c41d6462089401213126110314125500403d500b0070541d9116040e02e50045410400c101040c201d00408910f160748042d0810b9031110007000114884103081c020050f01d64041d0a815031240b5241c04041d0a541500d588141150070400000e030125002102d40740c2510382500c0c00d580c0340e0742e8000104a4841c07064202c583e0610440b441c0c0c10801d68172800712140241907005448030681d492010800d170041c0c0380a42c1358005000e12200740d074004050040c40d48030800004505000c08035402041c0907034826515046607035115880c4005054001380c3d000381c3c0b4040c0001582c6000c0c0341d070b00c800d52a0300c6002e00c1d41c03250f2a940c804100900c03045806070740241840b80d1031b8010380340d5121406003031090a0710007140c0390b1b424400062483d25000c55242e040b2003060311814280401600000c03a201c10030805a414194240120382c0301c0d4404200243c2d844200744011076943c40004149850801c144581d00d1070301e401006800003620048003a24200c1c1d90100d0b004c184c8422a038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 42541047 1250 42539797 42539807
    0x6131103070315030f0606030314040609140d140f010e060c030105151c020405010305010503030a12020a0c0506010906050913050a12120c0e1311040b090f09010608090714090f07 78
    0x140c00508203442ca4005c50b01448065030114080300c0c4252540d88400004480703c90301c0d802288202404030b44002002c1200740c0301031000710301600009000490309035140c0d580c000c44441c21000f28040327612000202d40025024404d400056580d503004081c42e140c200c14039240b81c8014020b0500450621860f031703260200da00c0c251061038140300115807403e032941599000030342040c402c4500090a010000409040c08401c881e1f5200c01590740d601110400841d9102139406030003003a00b0001c540308640c0205009202d05406455010700118a9070302e08001c003c20240d024207414400840008003000141c00064130681507540001c060381044120f200a543d01580f280d0001d02e014103190324040704540c0051401e50252084640e80d0310300e00020b401d18102c076000c00d480d641d0f1940820007803001c403111101520480b00c000f0180240d03c2c0d8200040b4030b040d1407e0f4840e00c04900c0080034081c0a103400c0c0300e081c002d032010410058072850326000240344898040c141305004141c22012901c1d40c0d00c14 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 42542297 1250 42541047 42541049
    0x30a0908060714180d0b0906040b06150307030509070b070812060a0803070f11060d140106020318011202040b070c240e060c0c0909030a031104060f0f02010209030106090506131103070315 82
    0x901d081b81d4030b15001c2c2c04241c45501c02c036070481d00800d0000000b1b5880c03410000b01034913084004665800e5544945003034008200141280340d06105240001401945131802031030190b10610b581c0f9124506031900c01c4110b00c000e814a4480c143d000014081d41000005940c030072504001441410350060400170810a8054006500140300244201c948407440d0403044068070008554019a80e032200e04076124051007034540c0401040c03108182d15584208140248120041001403030290740e20001241e651090008440a02c82202c0c00c0140b400ea440080488241e100f0002500180318107000b050072074484d55051141c94003241980402008008030103002001618103286420a03a501640e0380d040a074040c1d0000b418030080d03450100400d010341d42210566107641d0141c151039001a90084580c101c81d40842d075090203200c0c0d45a03024055003000f0b2282504c0059103003401002d21484016108030a80b10724204644204451003000450380c0c0b0014500d0001190b001a901d00e211480113 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 42543547 1250 42542297 42542303
    0x70312110301030803010e130503030105010e0a09140601092921040602030105030c030120070812010b0d0e01020a0e1c020306010308030601082202130608030a0908060714180d 77
    0x2000c07002008201980c802035051343c84032565441a0754500b0300721043e595103400b0041042d0000d0004000a5018082c11459550700402d81d030383c16501d840020045502162036001016807103c103000555030020001d101038400d185550600880c1a101a50411070b01441040500d00c0050341c0403066405548481d52400ca4140301600341c145030a107800030b9002070281a229008010503c1542d1405100364000210100440104459000e421800f0351f04200d0701a5408141000b902458809200419010706000c443c815101d104141554045074041d07120070a1a0380704029030700d00c4682018180c120649c1c115029050a00e070031000c1c500c0c1c105c5140c0025018443d0300c00110400180c1c50107107100f1102030741c1e11429030f603400c0004c2c010341101106c050480010011a02d000d4142284107009a0030a56000b051050703403428650f00d1640325503420340c00228203040500c101c42c018481a078102003d4501901c4846000c0c1c151021440ad01c3c0c5000401c1c040220081e1b03803600c81d0b101007106aa0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 42544797 1250 42543547 42543581
    0x80318010c0c290a0504080c0a03110c01050408060a1d070306020403110306010302090c0906040e1609090204060210021e030106081909080901050711060d0906060909030203070312 79
    0x403031601415942580d90101c58000c035200f815000020b001c09141d40b0b40d0520f82424805490f44514140100302c042c00944448504100c288050f450401070740e0b520b244030790f560303041094001d030600d41010312a90a2604120081000308000340d0002906500018050800500130300001c0700040280c1079030121282500801000100707100e1940e0190085030300600955103403800b440200364540d0024000298440741c0107000c50356500300300b00605401d0740042c006a00d006d40312284652041b03c00c03202034055044c2024008455075011b00a0350042c9580030301903082504220010b0f444000c3c180c0c030b6610043d030100c1c1c40041c0390342001110b928400054038080d0b6a50711410010904001298820003803200c548641914424a120b0840341c43d0304170200505110101c2c00440365603004010580d62120485640c081994a80c2d00908c1403550041000030070307055510b03001d000d03100d160780031901d031500e00044000403035004170451380701c1507051902103514822810464018140040d007022900 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 42546047 1250 42544797 42544811
    0x605010b0c0708030a020607120204030b04060522020a170a080a030b03120910050702060705071707061e05211302040608031809151201090303060f030302060408031801 74
    0x55008402040c1e00c0d04100c0039038980d02d4652100035940e01c01c80d40c401c00183e00480002d14203a2142c0d4040d0928051680d0251134070795a512a0040c040041c0c400b900c1590380c460070711008002c030300200b64005440c0e0491010044450b000031700301c405c451041c08001c0e580a40c0703a102c5500284801c600c0349601010494035140707482c40c014018400070100174043e10441843c02c0e43c00c0c60f600260380741c040f4000d00d003440001c1303018800c139802c0e049514101e81000b401c0c405030340041c0703083c4100c1c006401c3c0110104204407829080034500741d150f5004a0a1100161040b4084c0c140c0c4244142141d902e03007480740c1c0e1403044e580d40c212030001002d83c0034a20035000041c013081b00f0503c54255080ba00803502444500d84500019849110340b020303050355a00c414000d1341150400140d0b465002e901840116000c5650702c0c003140036030303811a200c045d6503552503111504041e014465040030348210405800b40c0c605554000c0d54622000e80042c101c1c0c600070000510b044194200c0020b071080c0c1030000d10000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 42547297 1250 42546047 42546059
    0xf03030c0a110307050603040c0605070c0305030304050d0815010905060304021804150c1b0204091104020d050a060f0b03070c05120f070c090e03091c020a0b040e060306040210030b0d060501 83
    0x15003103003030340c2d02e10900440d10001114508001521b0085400903030028089280000c2035400d45d00c02001180c820307288510000c0491802e101a500c40c41c004d202902d00c41c0f5204000a1003200010141010105089601d03e1140d9121091005817076040c1e550305e549807220b00002d0285480301c6411105d00d91403804010030440025070040410340c4540e424004c0291740d01066440d101244090120b010044102c0740141c0703000c1d004641100c3c0a1750300c504d84000440041003d0368030044d600f00f040f0f030300c8409201c0040c607903128000080003030700c2c85241e42d54140310b281010391201420768400c01451011441c00e00006000442031661503e414030340e10070007140c58101c1c580102d901034a001056180003e0100d84602444081c641c0395005945031540c10390810010a044010070b091083e007510740040140c40d52403091000d0f0203a0300d80140c4503464056110452800100014000c0d00002e0030b200040e00d4410b20b0f010707440410304010491455190125286410000000d403549090400005103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 42548547 1250 42547297 42547313
    0x1b11100207141e06090d080406030b190e04170405030d0f030509010921051207020a1709010909020d0f0f0e0f0c180601180b0315010309110f03030c0a 66
    0x840b141410100140400d0504004864000103020281c6500040581d21145840001000103401c01068583c0030402c41c0c4601000d13802c550000c0c404659a0350074100076203000030011000880e81c28041c65190f0801d03003038070104500030303100800e2100324171071032800c81188000740c4014140207404c0380c0501c40b4101c002000302040781c42e17050201f840c2170302080c40c0c0700c010b004180352690004030b540303900310b01e0030b071800d03240181800303c901000018822001c0b4941c1c4800700740d01032100d550003000f0040c1981810b000d0303520303681d0101a90842c10440040540d0f00880e10130101c400c500d40040c0c07030b00c105c0365880380505034020388010b00c01e142c500c0c0c08404a0341641706450303507403605003101c00b00ca6502416990321401c40040d980d1201e000300c011424618148520756100d90185440c100712440085840021642c0e50060400020040104071000031459200c80c00c5c500c0c24603080c480707880103072942e421110b00480b0041c0a05070740c5440c0741407501c04004a400e90440c00307040760362480003030400e00c00e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 42549797 1250 42548547 42548549
    0xc0102130e07021e0106051807030507080708010302040902040608030304060603050609030906090402090102150c07060c050f07030f0207120609150506030d030b0d0804060f02060601030c1b11100207 87
    0x10240d10102404150005100c010501c20b584a80041000900180081c0c0805201c086031035150340d00d61304c01103140d44806001400b44500241010303200d0401d55000343c15103400a0080342003240b12410041304950201c883c0d030440350140c50014918a06001042c041c100c10f0300250814030000041c08104143c0e64056403c8a0261003a240d00307071030b40e4460302c1e282d210f00110703254413a005118412142c500340e801080c000038140100e5800303007400a035500391341e401160300c0c803418500824000180105c03030083c240c0c1e17800149003480c80c0c007804030410220340c0540d0b607000d0104048042a50007260003049854040c1951249040204580d89030400140060490441d016906001c07411880d103a1070003400e00801005010b0615604c40b420200e0003059602142c0b540207414080c80400f240341c0000500c050320181e5207801804610820203032a10030060001410140340103956a07000d0f41c00704030b9095600450180740b01c5074400d400c082c1c8cc20024490641c3d80a0446c500c0414095000a2260 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 42551047 1250 42549797 42549817
    0x19020708010e120f04030c06171003030801031202100213061101020406090506130315020d0b030f03030a02090a03060e061611030306041e05100611210309030c030c0102 74
    0x41946880e6010182601d85103512819503600040200d020742601c200945040c44145854606044c0d0300d8582020348002c81d0700040105100d8003443c2e98210084a0103640040c00b460594401451560004d06c03200c41440060321100e00310601603071940c824001c1c80c0c901018030300259100c014104812002465a100b50b101040300240e134560910010300a88040381c8507134550281b414545001d0201550054a0302010a441d0305000b100151044000d402d18920788480161503041d2810b101080b82c2011824a210381e200820007058a4000030450340d0140345480096100c0e1a072602050100c1c03450b0704020002403c1c4400c03071903088000100c00344900e031144e0800301c0001ea261400d66036040c906024120341d400070000104a4103041d045068a80c0d5041b41000c0901a44044002161401c1d12003542c040c0c00c0700010891950b01843c030b028100b24140141c10b041c5c1c51494494070501520382d180607004004800544c5052052044d5425480c41c8001d40e99205000c0303100078001c2d40201084 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 42552297 1250 42551047 42551053
    0x9040c090801060e0c070609080d0504060203100503030903060403030b011404080f060c030c0409020a09050d0c06030c05120f0c09090103060608060703060303020c09040204180302010209040c17040b09010f021902 93
    0x7410344000c10711314014a012000ca51510303981d500c072200684190a815104c051080120144462043c1f0406208030700840300140c0b281821038045201c082c4981c00984654424030175400980d60115441d50440e07414140080d000c0300c50300058920700326200754101400004180014030500125100c400001601d05882a40c0d45a440210080c00b080c0d13410805000140010f02c1010441e6005000510103801d28840701e680c1c60001031000006801c088840010600040114035098000c0a00604d640e0408074101414802d0402c4110002044002042c2e03214001c218040c1c1c06000704c80d48640c0141000c0c13900e42c0c69041810260810784601c0701c2600c100c600050b881442846000103603541903014002c280345060810034481c0c8042c100361703449942d07142481b0340045042024045071303200350009070b107540d9000300b00300466126900c0b01c418006400034540d282280607078595030080e80446c001c8a5522404041801460320101c5192007910004041269241940c0304030000c2803140e0071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 42553547 1250 42552297 42552299
    0x6040b06030d020a031101150305030d06050307060e060912030c0303010303020d090f03120306150323040c05060a0201020d0204120b0702120426070f05011b02090a0209010509040c09080106 83
    0x28907030340745080c800800040e0004c015150020740300e03030007040701d0f100801d0001c12024000d1801034000603103030348105d9950f0701c00521107800083d40d000d04001020128081c2001d03c1ca403800c003404030218a08001d10410740016100165076652907003914604a040c11a41ca90059100d840e0707881c1c0c0280030540c0544150035410428030701c03c082c1c42d8152040d0b00e416098240c076542c1ca0130040040c0452100501d80c4400c00843d044162408080710504603030380100d014822000b0001851030440c5828003000d2405c0f00b0403021580c98106001101c81c1540c2841e0360f5072011138128020f0040c5451148041c0c000a400608807c81c40704e0514501d005d4140d000c040d49602030180e80da400c0100000500b001d0621003040004520003500240074100416100031a00d0a54201d040c0841a000b08481c5092002d060003c8e590214502c041c01e414000505a0480e9540004142c03a000500d00500103400042e0005240d114109507a200d1a0181061004100b0f041010740010014002c50805610f0050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 42554797 1250 42553547 42553549
    0xd06060b0c10020a0509040507110a060203010611011802060f07080304051f140406050601090801020408010e010e07060c020f01092102030c010504030314030a0e070b041e0311010810050402040806040b06 89
    0x100300c45400c4002e45402c6c2c0303090100424440503040040c101000c0c0940121907426661051148213980c511038900182d40b98101f490141101b45285d0210f004c40c0e1420304816420040c030341c1002051038045a00f140c03611003024002c171086c03050402c02803007840e0104c180000c110300080c0420f10b2281c8802c1907440016059443e41c126400101c00500c9000108045000b16002da4081074000c1d0041c94002d11030b54644010300e0030390b030095100c111942e46d2002e0480100744284a40845c1c0c1490f8400750001c80d1030601c00805c0407008003000b80c403c00030038903c1c09290703014103404d50041c140442d4180140c00340021088089500c0382050340a8002c08107044000d40c8103508550580e0307815252103800034052805040d19410042c80c9031000c03565440d1313102a0031000c03c01c00004010540341c45035260b0909083c0c0310039070494107400003071703103801e090500000f07000350001d01c448a4207180155040c1c2e2064041c1c1525180b583c05243c0052001401040d03110010034042d10031070042000e420640c444034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 42556047 1250 42554797 42554801
    0x50a090312090303020409111201120807110a120302011514150318030c070317070b010506030709171b09040b06150405031203060102100507090b07020d06060b0c10 72
    0x1580103002034091030010104007002d501c07a0301c51034000d00e401400d16846080c01c80464480c0240505081004507180500e00c139107070038282c0549201d529602d20701c192a5035007030444c0201803000380380c800b0747d50206020303072103244241006218448500184101c5030070064000d101e01c0c107215840c0d100710300d8007007500c0005040d80309100344040c20000d09045816007255040d0000b03041e104802d51800803940b00f00c01c0800c060810340d03a040b4003402090345107240103a00030b001e000d402603540000f808080080f50507881814111881a503a150740d0340c0d690002240c1950858000510f192440840e20403440400a0080d100e1045d060507401c1041400c0100031020108550082460460300b001451500b40414203d100074121805031b400c20f0345840001e400c010121012480950300842004013030740c1c1c1041100b244080e080020003d50402e000e000b80714101a000f6000400c03000280e0900310745980c500d2441c0581c20403400c121280c5c0315616443c0070b9220744c0e1300c00e041d440b0302041c01017400481c3c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 42557297 1250 42556047 42556061
    0x606080f060603031923030105100f0e041a12010209040b0a0503060402010309150c0206041106031003020f03100222050a14090a020c03030406090c06090608180c10020c0301050a 78
    0x10300540c2000b250300050440840543c0f910010413a28051110860300804180c4100d41b40000d4096101d605120a00402104811060302000804440201c0030741d003010011482c50030507100810014041c1a20307101065024036010b4002d0350b07031b4902504081040d0302a14005204031418003103000d1201c1003001c449018029164560030036000b017001507010794007215001b4443c6008614080e8020310b07070022690880900d00158000710200400c00031041c0700703000c10082c201c1c1d245041d42042006000b40d01070600000f406251a0380000c0c00a0768100441803a503660602c0540d0b842103a454041244010100b481565090808000c5034500d409080750090f00d0510718150f8207070340c0070020407542c00d0300070f840440601d900b0000814218000d20086121b503006000120f0300e1051840d1484c03899106901c580100842c0720801c2c028560302c60807a9400050041c45041c96422440d02d45041031126540b196206401080c404070740d68000c210303009094000c40003040644d40302c3d0040d50a442c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 42558547 1250 42557297 42557299
    0x15010f02070503070b0c16060e03010b01030912080a0e07060207080f01110f0717030403052a07050d0203190b1602030f19090801020406030e0c0f061606090804030606080f0606 77
    0xc9070090102002840146c0300c01380c02c5038100c0d100c541002002c80c424800b1908110b000944180210340d0b5424240504031a2034403c1c42c0801400746903485100d03198042d90382d00030411905401042130203402e6008840c0e81c403000010307203c100303641d024040e5a85866205107003450041000070100c00d04c042c400d5868444121001500c3c3c522108000c60040e03214070070841e80005031036901e2a00c0c401001c06140302d140329495055a0324802441c0000d04142048400340706010000c141100820204a110071151b094840d01c00388400d510020342401c03100c0c200310306103890440001b000d010540b0780481c020b980800c80325082041c0d080003286c40307100d0221110003840080202c2c206401242d528a01d00000c64640342d2101522101d2040c2a42e005a00900020380c482d01e0143e4490f00c01c0c843c3e5640c90508444071560340e0303c41c10110390780d40542c0070401200c40c420064141130120702d400182e0b1207a8064020b40e034840e00e07440e245c00140918003d00c10144a230841c00381ca801000a215801090 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 42559797 1250 42558547 42558553
    0x30903020c0a1d1e0718180b0102060a0b010203040b0d090203150f15010e010e01120c050a02071d070c050f0d0c0b1303080c03100512070303020c0d0807060b010c020915010f02070503 80
    0x14a20310f0554a09030b142c0780f424455160040e00146c7c5c2441e552031203242c240c100c10003080303104008000918044029140c600c1c414a0084410416a0000308441c1107440a000d00382d11141c0981616008104104010750540100c28040385017410b0400d846120320b00002c8044103548801c040301c551101c101c0d0480e03011528021500388658000c026100c1341900524200040c5504d8040e59070617030b101f0400540100c3c0000c14070009043d018072401c3c001d0304d440004080030001400d004a103200d4058040390030b20100d46c03140d0b420320074103122107181c0b10075050031241400481ba20040418400c204180c81650000c004204400c00030b903451800c06e9016520b08990340c880041d800856807025101141c2e10910798000076403901c5e001c4007000d20210140150040030715608000e802c10007078104252241c0d003485e5041c800250a4003e071552113400500000d400408900142c5d900c001c0361102a5000c10340701c0130403c403d601110541150802030342c071450a10a410000d9a403a242e5002c1c66915030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 42561047 1250 42559797 42559801
    0x140108060604051b07110a090e061f030f0b040b010b0708401706061c02030304090203190c02060702031611060708040806010503060402060a030903020c0a1d1e 70
    0x12030240c01c4590484840e2018102501c07a407144822540e001c5c54084a00c00d41201015101d8507140000c04c0003040020070a00403920b61300e03142e41d00d4150080c88d03580030020480e541e905d1003542c00d81c050040c65001074982802c24413030500c000320510407101201c000100030004501070344000305840f011035200f1061401c14407690500c40071004120302180d05c500b000500007120540c1910603950b4109a00404c07502c00e802d200d840c0903d13030040d01c03204483d41c0c8880300740442a110104420511103074425900c041595034800681140b08540c00758820b50700100c20b0060079803030215005d400300c6030a0000c12401d0030954047c2c0c1c0f0350b00102c60083c05a0820301030b01da84038203054850345405d445116252204090440083c461381c0116400f0703200d03054081803d02441401300070507800742c01704038018522417030b10b0760000300a0310811940104140e00c400c030420405008119000b40d0180061036048400d40791200320100d040c28146030716000e041c1c0000704541004803603d0b0380c003440300b140c0d07032038115 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 42562297 1250 42561047 42561049
    0x1110d0902121204031e02150705070f06030204090f06030803011404060806090a0c06020705060901030e0c0301060303120c03020301032d0602030712050c0921010605061602041401080606 82
    0x5001540e016600b0041e00086500020300902808143e4100c008200d40c80e981941070210304281724619043c00c6901403011400569120916035481440240c9034039581c1e0064908242000d00c50f038032884240304854000718415800d90050b1040d6000f440341003025000903005030b010340fa041c3c071001d0104078041006110000b021000c02c4003441c00544003080d8140c1c6c41c40068a4003600b240c1110943e0000711000c02040f03c1800008020032483c401445071904049c00555140314445d10395045c1980d9980d09030b0080f01c240040c00038041c0080c0200010b40d0f0340c0c18094a074000c2000e280c44100e2038200c4c03100e5050300038825281a26040440e1100b240c0031050b020301d407002540c1c0184001d501c011110000201280001c601c125000c0e554070390105600c1440b14103440d4003030452440c60000340059140b50720344a10780d080078a22200c0682807181388a40e07103401440d40343c100b9038100c00002501c5030031130803410107504441d01c240c07030812031610101c44490104100380150315058000a01040407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 42563547 1250 42562297 42562301
    0x2d070503060f060c01060f051504150c12020a02030709020f0409020903070f060509091303020c01120e0703060e060f06031504030e09150111010b0105090d080c0a080c0106050301110d 80
    0x80144050042c201510b089000654560040268413034244c0d15100c0502c80c811540f0000c0000301300035501031034283c800d00c2c00f01000d40102d0280e1040d8800c000c202d20926031042e1583c0607035036005a411501e84444510080d198802e84509038001d00c1201d0000039568aa0700c00c86280044144125040600f40306010001c0c2d0700c080711842d4540710f45c242c040b54000c0e200c011600104030307645a8a54a940e00c6060100c4890300500750461440001000030101e90040380b0b6114a070070174601000040714031508000100421048200b1600c903030007020003000351550140403d20000c600b00c1e09543d440306a80150784104407100c1e501500701c0d5400600e1134030744042d42901700d840781c20600800c0e8840d00210740f4505088420074199a0310110006941d41c004940a000d031140000030300c542000c0341c0c00030b00740d48259106140071740641140c02c401d01c00c501044d69015440c110030303109140d51900b442c4085411003e0059815481d2250004462405101e0300c0010113a41c0f001301c2c140800c225200e00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 42564797 1250 42563547 42563551
    0x10501090e040609081b0115180213090c031508060411010f030b030d0e13060b1801050d0509010b0109080f0d030b03010f0c0206010f0905040203030403260c062d070503 74
    0x3072003540790001800060600b00103006800030744080c6c00188038002e42000c1c20b50f09026803070308442c1040322003801085501010031401201c40c09003d0707030391382ea40600c0c1e01005081c2d901c0300c4c1900d480e1110403030381c15a05400500c2e1745102d02d04020440750300d841c14580c60707110039100280340080f60354440001f0b501a00f140a034541450400040d03a054013404282082e90315202c000c0002c6280c1d0404080c0d20b4112441140300c1c140c50320800c8400d00340103244480b4407500c1400544855410b6566140b40c1c419002c0f505881000720060181c3e080c01000c40e4040e1a07140c0d030b0540841d0840c60082000c0400190300b441901000e00102040781c402d601c00e6000b002c02d40c284641554a8040c10100b003801c074001c5021810980e03000302041e61402d0900d0380e0500c071a401900c00103040c1814000940d40c00416181941c0d0028040040401c910101082d640c08003449070811400100303d121040001140c49842003d14241c2c081d403004900701c51a1100b860182c0340c18000786140c020420992054011b15 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 42566047 1250 42564797 42564803
    0x41101020a0c0305060106090602010203070207061d030109060501170303090a020f0a032312040605070b070c0b0901020a08060d0f0f02030c060403050115090606050403060b0d1a1608010501090e04 86
    0x5015075031292101c41c003440180e0815601588800010030545500c03036500c5c00204001d00c021411810807000013500c0d80000d110300310410800c900907605150801550034420f58004000b00300040d00c61800e031018102c00d114a170440150a403210100d0b4402004580c41080d401300502007800141d42040404210480c0719500850710200200014000580408414410364500141c110885040ca49482018940d041c0140010702081007119008001d60301c07481c0d03000d554000e1540c1c03070359401c0341d9070b07030034445c01806c0003108606124615070103500511030280c1030341d84d8049a507584024009540e0010340002c100d5820f0506401c02300303003070a004600c1c0920080c10f0300c2e50540440d002801c243c015400960304c03039640701400504809102042e00027807420701c1d420b1000f580f4088018145008a00c406400c0a8580456480c0f40c0c2c0e490550301c2c3c0e0a544002014882c461040b82d240d80b014003164165415164441c141d890070b405007218034100c410596404042504151040c41c0d400c501604c11 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 42567297 1250 42566047 42566053
    0x1403012705100c030504110103060f12080c01090309030b100e04060b0d0209180c1206190b1305060103050714091e06040905060a0b03011d07050d0e060114041404110102 74
    0x1540d8400b00d000d00081c81145680109a6080a09245007061481c1c2c07202ea05062070448100401d591070801c92085569141e10711190314030504003900f070b9100b2001250b42551901001c40c0c00c040d041040038007a83e0040d41071a585c0d6840d4506c0b16800c0307425010b401401081c4100080001eaa0707a005442140c00191403100c0b490941c4e070206c0c03031005c42500d0f2045050850004c2c0461001c0410a40c004000b080302c030190591214241c25440b24400b611040e600221405a15609002904010020710002d4140003030301e00040d0f898002008182c03821070001e4141001310315114400c5100381c1e400c40510280ca482e00700ca00b0100040ca9000c2d98400403413403201000814280e503a0720190000782405100840d041c503122041009012170b0790054031207003a081c0018868400c002c1703904910400f183d020424240c8401c0c6c000c0e61140680256040500d081c410421a640c43c0824001d04884410300d0f44510583c481c410030080d0342c40141e4100703848010b0b500050126903a1101450311650600503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 42568547 1250 42567297 42567313
    0x10c020d141501051005090904032316140a020102100c090509040b0403030b0306040507060309080c060907050a06030207050312100b040b04030b07080106020c1002011112011403012705 81
    0x162401e02c0004603000300e40804107401004103042500c003541c41d2180c2850481d00d0703d14480001509110042c001600700040b030342c0301c1c00c10601651080d8013000869404261903000c0403603100b5500c1c0a0321821144560480c9016180d00e00000c1d1034902036505801038151242c410000d10000c00000400b075080000b00c0d13100182d980c81d41c810941c0180d018443c0c6041a1170300381005800d8820160005000764808801c00002c542d000c2110308c00d4070f00d2481e01040c030b65210f00b0240300d640100d10321403056000d40800d1062a060005040044960a8130340380a001c7d0307280c505a0403800f80641c05080c0d03030010807210440c0721350071840c076a01210f080100042d43c1d482c3d0042d51001e400941106691141c001401d00074000c0d801c0c8004c2c1c0c0b001329454240705641c10000001e444040102e09140a01102c181e0303ca00c5034000c0d0000c07941e40300b4540c0f00e1a00ca03184201d00c5100c108080c82825101d00da00494a949800e040c0512034a0b4080401c00b010402d4040c010150140f60460060b5114054050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 42569797 1250 42568547 42568583
    0xd0f030f0e01090203010e0303060a03260c06040614010f030311030c0f071a04031101050304150f1505150316030e0a03031406040506100f09030c0605031014010c020d 73
    0x104200d007104196000140110007441814210b8880036403001156100340204110341c1d84141200d01a654495a900035107a81a02c0c1030f0f40d4a00720465010103e94085031500e0710f094001601d520490003240c0600c010081e860850004903428042d003072041c40c4e624420320100b800380c044184c28080080899140c070024010450409400c20300460050704480004c001c0e000b0b20700006410070b8200b00c400b0380342910b55552268042c100d00f02c0702c1d05100b40480050241f284001115520040d0800b0500c40e01807420b84800c01446100c07041c600e41c034000c1034041b4072030405420928480303c030f183c01e040c81e513140d036802003041108010b0072404141d110301803040e03030140c2404008511031203a103011840703201d45070810040a10040489005610b42410010720740d98030040d1300c48008080c04c000400710a40345040baa204940d030405020060380740170015260340e00c40c000750300c07800c0004003c41300140c940c03040d8009020081c00c09030004035103a8040c0003610b07102086802c2148155411001c081a400b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 42571047 1250 42569797 42569801
    0x6080a0c021203130506090f030a0305092a0109090911040506060c0a0c090509010b030601230303040810050c070c061b12110f0a0503070b0406061205030d060e090d0f030f 75
    0x4c6100440b440c51601500401400b08099a0440010f80152414081115405a580c06a20043d04c03c160710b600105141030020712900741424138003c0c0c0e418000c544002c645181d0007030200c480d800188800000100480d1511403d15407644c03014003851203032904800c00010b40009844d1030380c4071000f000103005412042080907041c3e482070805103100c910b0301200d04110b80d070003820a0b010f6414008810140d0f42d0204142e81540c103d00c0982d107440743c0701030445580103003103101140c15200008001c00c9a010005000c1c25204c0c0d604414801c0d6a12091903005a004a120041c000310032030201740300180c0691010501c500004102403030b807403625200c052045512180700004106c080368400e58902c41030000d024800880c070010002002196216581d0303118041001d4515610710020030708210607900712000a241c04030035070303444018030b00300282c0381d0b405030b943d40c09014a0180b0028500b03044e8007503e0320580381034001d01a6440802d00c01d8450301c0714030745404101959000c41c030182102c18 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 42572297 1250 42571047 42571051
    0x31e030b1c0528140309030a06020309060c04031e02040f060e10090e03090906040603050304180e0c0109050405040501060e010f0303081024020115090f140106080a0c021203 76
    0xc00784000c4007407050810030b080c50b0340e03400c99000090b000c0d0058141c3c20300b450800c0800b15401003e4090405a4000040c00c600503825002c1d40740c098161500b0a0285507000346004920883c00d84509844480c0c1a812620aa100017483c0303d5090402000407240c00c500d503400f2a00180021410803010004402140c0490300f05620200d500f20510611484001c480700c05408001070402203400c06000f01541c1e07009800303483e403003500c14000040481d201c1e904144011030344001100d8035561903590061004040f0604910090700c0c00c2d403490035001c40050b280d03034064410f1315010000c0b81000d0a010141c603008106036070b20b40d01c4440014031034480341e580500800310a0240c4440508628005010050113014030b03503d100c94280602211007071024902c0c4c0101036005c1c0e202d03c1c0d0700c0ba201c16030261114480d0480b20551401c00040c8101c0c5a8004958600d8411b4042065035841c1002c1040b1900a01500d40001c0545000423114501c60740596164100750048030108041140c11b00581d500c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 42573547 1250 42572297 42572329
    0x40210080a0b040207142e090201020a02040203010e0714070b0601030c0c170405131407050307020f0d05180103052a070b01150207051519031803030c08070309031e030b 74
    0xd00340d41e52144030000d00034188000d40300032800c1c4603604071f024100014a102000000340682d141c51040c11a0b008000e03410131107138041e0083d5129a0740307081101005a08442c400085040c010b02031800c241d4240850302c016a100d80d41260b6901c50b040118000d001380c071441000c2c06102c1c800d400100b0480306403101c1050b035210a16030380e076080c030b000d1000c4040ca008500003441e00700138481c50070204c18400706a00c4201868000e403660f4448000300d25020590303003542401d00507000041d210307030b038000002c2012911042d000c0304141002001101121030031940f059503040006484040c004030300c00000d034484178204500c3d082c0310303154030740842d911001e03840800300742100d041c2d05c034110360103010074001080f0443d0030b1800b403025131042200c54401c0789502005c0d058560a880a02800707680400c0c014144035010390005081031501030b00400c048074503000451020000210b4451190161614140c0c0c50381c6c500d505d05051119228501c4448a1260305042d110034800361a51940c0d01c80396407003a5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 42574797 1250 42573547 42573563
    0x307110312030714070f0f1203060b03010504090201140408160b0a0e01121b0201021b03030103050703080a0201060f080a020307090b130b0f09070801030b0a0203070f081005032401090203040210080a0b040207 91
    0x50345d1400c00c03840d02340c6042e040241420042c040095589170003c1d64110341080d80c0229001c0201d10040780d281c01c44038000c0340141800724000c00d4407440020690b400024105016078965100d094001281c002e98000500040e4000c25107200d030351007003e500400c0861004046000122003c44150b052014100070700140e40c0441c3e240d000b070003881048500c8400c460051841e42d41036880b0551544842d00010b05015800550b09034070920075030000d0300401058080d03200c0142c840082e40d840e8041d145041e8400e201b0800c012a0f051800e00c144000c20340d0061030303000039601c40c03000840542401c0390340903072004031029400429141c070b100c840e1182060f60b4070b80c1d40300e60441c41c1546060001502e00f500c02403050082000c00d54000c01414026001d03418240e40e5581d502400e040e0481f4a038004642502582d450284d0f038607011014049403080503149076132075a8a41807020101c1c08221000396226070320004c0c01c40c4540c004c11005400100021010881000c2c01002c101640e00060046984032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 42576047 1250 42574797 42574823
    0x30f010c03150518010302010c110a03140105070e0102070612110406020f0f06040b04020d05010b0a17010b0103140a020a050c060c070201030608010b0f062104050307110312030714070f 81
    0x4055652020b01520003120000314160705011054004441404001e050242084034402030105102103501d440c00001c1c4402541503c034501004803180040d41c0e001c1942c07e081c04504c0039405246aa0410301c0180e0090601500d0007408071b03100705814241e00407050740c50300c1d4094032411540007400035003910b800a0072800990300c100d0380341000c0d101c031842c6a030f002681801b0014080031010703600541c040318808078203501c0c0d06203140100405900c0035400041d04100103043c180e07501c403020049030010000c101c1c00000313000542c00e0369a11140700741101490170008a581c4403a9020b000b0340b940e00d15005080982503a075081c580300c01550100580640460000c0441d85c0c140121000b50404000030701411020300701182c0f142c590303107031194404c000101d004e0241d595407000e410041003000c12602d0b8113040c98205a0707100c0e400414182d80e4244050000c80140c00e000401d0282040340181c51752650f92150300844001010100d0003503008010800312001c80c1c0041559041036018180311003c00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 42577297 1250 42576047 42576071
    0x70206040e040c0e0903090409210206010302010e0307050108040605180f0a05010f0b10030b0102030d0903180f081005130c0b0a02010e0105190b04020d090c09050702010207080a0e030f010c03 84
    0x70749080e07012459034508007040013007020006c0292800c042081d18040f80b1103446203424000b401c0e0140b01403c440c0002e9082d0101d140e800541141202d0003a02c400e009420010181925a0454003a89010403e0000400c0015009512166200242150046089000f08555410411300c0c04601140f980003422100030b2120a102d02d403912400c0480c1001040241004640008821540300041c940da91103450800d134003c0c0204c031450040004200100078a40c54094075010b0900c20790342c9803841c4003201203050458400e08400b5907043c50300030104840080340c208064000180f00441e5071886800c04c000240000032424007409134040c0d695150100c0d914000e0845886210140c0c46038140424420307618111543c481c540784540c0004540040500d003c0f07006031241010b480481c0d450001c00300b0500807102904030039106a030009001c26104c02000301e00343d0284105c06420f460702004001d0081d80102c0450304d28140c042c007510284049009040e08440901102c040440d480740628200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 42578547 1250 42577297 42577313
    0x1c0b01061d0901050d141e0d120213031b0b0f0c0f01050f070309050102120c0a172205100e0304050f030303010b0403060c140705010c08180a021005070206040e04 71
    0x16092081d24004180c3d0b24010018400c1c2200d090041c2411201407181108a8020301004003a94289080481c11405440340c46580340b40400460002900e003011181c40d1003584e008071340000b43c0351600446c04a003503448013a0008040318900b20716210303100c80082c0402480000d0103034102000005a01c511016503810700b45000404080b1050f4944070800560040c804401e5410900c64500020f062101c0e1610074020b11500c84481c03203081d04032040281da607290400a028000490f031320785000706c1083c0b0205c08540b03401c1d10040e052141d00e9455141d8006c6401d10000060302075001c03960a0381030130300e016040f940c141c400300300d07550030018043c03082d03040400714080c50400c242c0041d455036160011030b000e18020303800004d151580360445003000501c224852810040c00d0740101c0e40d02d1005180c003e0003442444082c0d4046007502c00014440600c407402000c4241d4032170b000d40b1a80030540e00304a0304000c0712984d030b4180001032005802580300c4c00301070006488800c042071003d041c0340c104950 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 42579797 1250 42578547 42578597
    0x30225030807091d0f0a090506100518090303010504020a050f0d0501030204051003030e04050402010c050609060f1005100806011211030411030303071713080c01021306020309030c1c0b0106 83
    0xb4076a10b0303180c0113900d050709544000e944040280c07185400e035140d048102005c0d003414000038100e131140d58144080444070700c0000048403c01c0b9000d83e20180d01c03074014003040104840c00000fa40092004220794105a002840d4408082c030301540340041b000d030707020301c2900840502c04115950b20010310031800c1a00c1042c0d000350184c240c41c900c092541c0d41c024151001c0c603074003a0245803507101107800c59000c1c201070010240d01c08190340c01443d101e014681d880300c08881d000c4110300741901183c1c22421103d000015203802070030a509940c12442c0c2660001c0d0041c0a0320304200044105460039002480b0700d407121030b40d1558969a90034a41401581c1d01c038410807540c42504104148100241c02810250180d030702c4498202c5941ea03030742c209103860180d08501500e203810010340000c200806500030113000c82aa40c80840082c2c4807401240d032030294149182c1c01d58004001c1e80010718094909080301e40e40f00821a04480b01da0ba41c03a12500f0007a4440404a03600170f046071f039050000d04400c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 42581047 1250 42579797 42579809
    0x301090c12061103090307061a06070803040303050109060b0d020310080d020d090f05010c020d060b03150117070302010f050d0906090c1d09150402060c0d020c15031603022503080709 80
    0x2e08604200d02d621b03445c0c1c0302d501001007209544580745251880360840d101510140104515160729150070a501c0680c0200c0b02100020b24150001c114401607100b032000b0b58051802d41030034030802c1104030b002944003521490090622850008010b00204030503030440d8003d601070268110601c80240c061401c41d04804e0003903441490900190741d111640c5500c194040765151304010446c1400f4000340100940361f0340501a40c1c0c00e04032554258807403a81210385540d10481803081100e0159115580c03400020300040d16401036000751031152015100c0401684c900041e401c40d1a903440c41201c060650894115001c0b03541000200c40061041c040c0b8031038130039510118070b8000c0040d512810036130204114001b494012400b551145400d503111406071400b00e44248001c0030003c0e545448100d401841440640d41d0800f10314071040c00e8a020305000c80420354400003103081a806904000c0c85141020084040049648103880700c552525000b6154400c60f403c10590003000750040390002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 42582297 1250 42581047 42581081
    0x408181906230a2025090c08150102070b0301030c0603110304032c04050901060311011803140f0d030608010b0d08030f04030509060c030d0507170103110301090c1206 73
    0x9218074560000440d40f844401d07144c1558032002c901490503000a0b5091011520700c26000000d103c52114059103560580e504981e540c2c0a80d1502050b0907601801d40080c0010802c1340450407410404000100d070309414016212000d44a032039801040d0026402a10a100c100400304000341e05031007018810b1002c106007510b14138054078050011410300d02c0d07140701c0301e080b000401e150503614090f01c11400300c004c2c030500143c10110401c6001c0c10040c0420f031510311020840c000f080d805100300035424001d0390b44051000d803071503c4000e00042e14040c10f103064000d442500300304040c1448040c0030f0380c4058030000f17941410014101e00311004400d590f4094100721a0704c10108072031105803544540322084034902c640c0c5d5450120341c00d00840e2281034100303030049401039088a0100107801c00818000781000180d440400c212081703014607000e04a1040c81600500c080303034024030325540283e8003400110314410640d80300300d004c90303075a0f0015100c0000d20101100f046107500428180c0c4002c5414 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 42583547 1250 42582297 42582347
    0xb070e0603010303080910020c01140604060f090b031c1d090601050403060209041506051206060304020616050a0b0a0c020f0a030905010e010e06160308010911030408181906 76
    0x2040d4588818003000d41032140081c009543d207802080381c1c1405105c03241c002e5440e16600b0350414003070b01880780c01c024030300e600340c00095240c01c01c2e12500c402c480241c1030140d8903c0c40e00581700d00520804000720307014000e11202c07544203903e0301001c1781a10115683c2d40d0200000a0300e0b50040290010694421600541031141c00e07a0301400b56006c0d030b500007400699a6080307800141c020042d82007444180a00300800065040d003040241005844040d02489155601001c104e290f1004840c000e40c05074042c0800c1820396445a400d040c060f00c28401c0b19035403080380e22081038184044450340822a06c0340070030742d0354503414000100100d4001d4014004c001e203595019014548601403141040040c049550041e841140c0941c44403001038000360b52110400b5103145098041941640404c4060000240e2003038180300c0c024115210910450031611103503a40c0085501410f015080d081c4544004085035841265501c80c2c1802100b283d900c89140c07180241a01c044140c0c00c5c404a0020301c0c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 42584797 1250 42583547 42583549
    0x305100203070c03050307170106020d030606050f040e06031024050103020712030509121911070612020325210b09010314120d020403020315240f0d08070b070e 70
    0x2888001c140c0c1405d0050700c0c1e079550b85044802036003802620103482d060000000316107401050714030324001156028462552903400a440070f214280c800401e103541080b080000321a401c400a400000c000c00fa284140c6140240005541440c0d442a52008070b82c19043c10700748440e035200c00140020f0a080d0b003049460348030301c03003003d01c51100c0030103064035100040c00400045c00761101c1c20084841d1151688021340d88040380454841c614008102c031001700180a10000507004201c400704d035601141c10036810030700f0001c0d40000d021900c0d01c68091148854403000a02008403034000c6a595000e113030500300d2500c0034407180b084002c03040361178120314130030544a078140d60303056980004e041d051410145042d240342002954200d0740d19a0080740b4213a550010390000c0003220300071012a0324603201c1c03210b404005032044c0c469a0324040c03101c0c015110407590058100c22020020f1180400800110100c0c032490b01415027169501c6000a0120030446181d174600e07080300c000d241040d05100303044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 42586047 1250 42584797 42584807
    0x806100804060b0a0b0a0306080106060c121b061406040501061407030509030a08070c1802040f060f02010617030a030513020a050904050a02100c05010c0206150f01020c0d0c030510020307 82
    0x2070400351040703071503441e181e0040d118000100e00502c400111181d4031000008001c0c000e2007075006004240d400c10100040e81e0f48500c00b4031089940049c50340700740559505003074030351005e5941744c604011102444200401c0580c4100900a295100c06800c6868810104001c95105030061002c3c0a000070114010310032004c00d507034110b64141011aa83c0a130280002e103400394021740140740c6100000d0480420082c2c207500030881c1c0480c0544180c41195504003c268003e0f800740f000101078440d02044054170403084003481c11900d000000c0d12039218884000b400e0451002c620707496200281c02000030754140300f015400360240e80c0442c00c0303501907330004001e030205200c0ca0384504c1401c80441c080c0a81400450b00c1c8a90051580081201100f40681400c4115034181e0346e81d413a140e00700030307101c2c00880c2c0325110718807a203807952040303074030700100203240c21858a0181140b041c0140b244d650b846400c1140c032070900840d0481b05807440c6140c00b6160021080c81e802c040e50050081c004519005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 42587297 1250 42586047 42586051
    0x80309010509010e0a0b120703020901120b0d0b04030815010c02030a0602130b040303030605010e3f0f060a1503030c0305071109040308070207090908030c032a0a08061008 75
    0x1d103000c80e40c40e01c4850040b10a0b03681381c1c11580d4001c6100c04001580350700140100340749003171280340081c0c555440328254128001c1c2a481f1380401d00251621810000315405010340400090844122080d25150030007550011501140402c10300e50a00401e01080ea9603075101d06000d01e00f9030319900641d0701094403140c400e90000c1a890300825000e480314020016400500781c150040c81e10707280c2c2e03030500402a14042c03052038040b030000942c50604d8105110462030303146114210402850105074803040c0c08001c420220f0406140d40c0440c026a07034280070000c001c4884000404a0341824034040080f00d016100d0fa40c184900c0c0324041001030f81000c2c0740000c458150811503100c454034104080f85440c080d40a9038080300c1d1004010070182c022000b580207649590880d20542e440f111844220780b00c000e006008208140005072001800030300460703000c80c0326040e9170321000000c6070b08480d05080c120b0502c2004070124418001e43e07801412594030440880708861400010320001c1e00300040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 42588547 1250 42587297 42587299
    0x609070815090703021009060e0402160b040203010b030307030c020f0108070915140412060e0f19020604090c11011a0a03060f0b03070b04030605090615060a02010e070e0718080309 79
    0x401c10000e08018800c1c00722100842c2c01030711020341c41d580194000c00b07003031a500800c804076080c042400d4460802d8401c2d80d182d4000f0300198040c2ca41c7ca038070b0b05000590700603c120ba00d903482c0c041911340e54a06002514809100ea107566210603903510400200701d00da160414100240c5204110841c0d50000c0030404851040b0070f03c140e564014441120403451018103e540c000300040c0000e5000c1003002c08000b43d5005100800058040c2c040f016255018480c085005074040d108402030003120101214507188010011480c023980d4290139009e0726500e0401a01040c210300c0e060351500030a004032105148030304042919045540002443e0440901015103044d0b510a9045c03229203d55110006401000303003142d413070590380c1c00c80141c141c1c480c4c0400c59055091401042c2a6200010001c0c0907124144a203c80b40b0045024071006421001d202800c640d01c030301108040b1502485000080c1140c1c050248051604020242c651411104458118064140e0030002d0610100c255030030914 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 42589797 1250 42588547 42588583
    0x12a022b08070e0907080610020c010207230d0605090d03090506070507050312090d14040302030d0806130e0a060b1c031107090510091103010b07020d0807060216020306090708 77
    0x16031410440d401074071001c40302d801c80141000d005141ba007000c0d04030301c01c5004840c000e4860b0410704040340c850001f8004036025131310002081c0140c50100d0400f0b2540c04203150313526408003041c0002604002480819604259903005000300030605024081c0e0f12170113820284420046c9648655030341a00914001c10058041680010440c040c030845400319035840300c4400c3c6041c00301c0010303100c04200e45100701003101c503480105482d904d60141d904a03a001400b030414006440b80540308564024192075100d00c11103c824510b00c5a8414102498540c0c4000c0041c4491072400b4000c440380b14409074410100f10b0131060350f6600141036680490340c14a018422805441026881d00c40e00f03070016540c01e4202420800000206520310b0112050140240050018601989402c1c4004e000f290000342c410401000076041c03404c4084212031103424801c0c41e100082d02c510040303811082c4034001030b40d8801e280400b5443e00b04007481c1c01400c00c00140c11100d00c4c24108660b50342060b422004804 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 42591047 1250 42589797 42589801
    0x3070512340312020903010f0c0f030903081503190602070605060d0b130203030d06080a20010503010b130b040308031e0105031005060301060f0816060f05070311012a022b08 76
    0x40f89070701540d000840140c001e00c04601001c1c4084040c011580070131000440350341036029000c0c0310740149081103405803a0340c2280d445002c0408484c510806503d41c052041074000e400c0d01d103000c018140c640f4020ad80c0143c075910980760031803e0302c5025081038810503694001d0400700f150840c500341c2014060130310f980c0c00390242c80441e04600036032505518a0b0303e0b01400142901001c01c2c90105584035038148200000d01030482d8039000f415003841800190b06000603c406490311000305401420710054407440360f03072040e801d441a40030350000c1f18820710101c1805480c00810b00740c02c03c42081c5034940c02e01c40d814100800d641e0550224040512038507080442c14649003944140042d003000c8407001b81680d2500701455480d64400d05500411500b0400003074454861026230503e0a250382d1341900e05441520300f20f40c0503802000c01087e41d5603d18030303140c0344448e101d440c1c1d08042600d0000d85400310300d48400b03400c0010741c841c1c150040c02e541c18040141c80c81c0d800c94030904255803c1c030031150703 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 42592297 1250 42591047 42591077
    0x606170703060302030d09030611071a0405150106050901030f05010b03130206120f1006020c0307030206070809030d0e030d05040f09020a2606100507020306010e0702030705123403 79
    0x20b0025a44065090f0061600300442c043d0300c681c0c5007051742d0007000117100110030204485014441e015014010003c07500314025078a08070410150041e0240c01203801c40324296400d0702c0003041c00e0344117402064001410301e01558140c0200340116a940340108925807600c9440056848014807090110901d4507003103045580e0391090b55081801401150624070300030654800c0b15205503801c0700040c040d00b90024140e480060798041c0c10802401510351107243d5401d001c05070300001c004a607200300a002d8000c0b81d48081040500b441354542e21801d00362180010302d07040c00190304600c0d0405c542080309108003509070a0f1007084440c2d1400040ea91820320b90101d03044170200310030900081000322440b01040c4940459400f50400b2a0750040400c285e41050b185c510440c07900941503040361380104901108002150b038006450300540c0d2800d062944c80904080d511061001c2c0200d010410801d821002c00c5407400c20703041000c207920360191407201c83d50b060b800c0b244005c041103000089040c00c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 42593547 1250 42592297 42592301
    0xf0a29060c07090506120a05070308030711010903020a030305160516020a03080d02040305010f0506030c12010e0313080607050306011b0503070b01030b04150c090306090c0f08030d0509010606170703 87
    0x2540e88284142d03124942c8030483c842c081c110a4840303600c5614640071072800e8003004111030a01a038080011700c5c02c5440c6550300c200b99040180342c2024803440300d0b40e0001001080c06001c0e4140d00c01d07806044980b140349005011607001906a007401d60340500303850882604082150b481d2801025100143d00c41480006e221500700e42004000e080c01081d00c0c1510780490700130b001030701d2262000b8040c0f01350fa070241c442103031005c50f51168580d00c010301105140c28a240e1003070314000c5010020843e12603138010a07155500241043d0112400000c00b0040c4001c1031120030b41100c500d1618510350f00300a800206600c000a80405001c99113980b260304101d02002180c41d0740f036100d10b1b8071700c031076035a03050918401c40121000d50380d24900c1300c80e06100176030038824461004526100e0140090440c0c03541c0740200248030f012603105000b0074001c20f03c0450600c1030001083d8800c0210741d0703401c1d801348230016207001820071821a81820800d02a06802c0b4078880350701c85020390b0f142c46940e1101c00442c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 42594797 1250 42593547 42593557
    0x40905030c0318030c011205041403040b1803070305061605041e03020310090803190b0405090c0a060e18070201180506100501090b0a08090a080a02060f0a2906 70
    0xaa1000003004a08080048064103411030b2400c00801d07691040424161150310846000e800509942000c0c6855031b61544000d8200d4010b940003201c03070445071900c514585c0283c110040b81c0202085a62030600d843c05445403040055002e0200e551841d41d41da0f03521703a8054454401d120002c001c00843c240320b003054138010800c0341e4807580c1082e0031124111036507686010590080c040c41c03040599902440c041c840120350301805841c0b441e50780c600c2c40440c0103620319040c954141c8034013141c882c90350ba9000b11400307400352801400303600b403209c81080400c1403543d105405019602e00e440041c1e5690035031018500258004011705d0f83d540b604100e004000801c50822140c92040e000c41c280070300041c1151088a41d507484514081c4c82da001074072500b001c2c0c0302d03071101034208020074440035100341460780c0c201c1e10b090304a41c0314000a43e507600c0e580d0040c80d642c0006912100070012000341e2048815000714a01c64100201c02c108134840b401c40d06441001c0203801c146020703500c12610313200100c0da = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 42596047 1250 42594797 42594803
    0x30408060c0a0c1b030b0a020c0601060e01090b0f03150d0b070302030a180606090501082a15040e0601030c030c0f0c02120a1103010e030f0403030e04020d0c03090201020d02060603070b03060409 85
    0x25602134480100d10414075140000c0d1694080349000030a0f40340e032882110b0f40e02015500820940c0c1c6409802c032500301c60000c220381004a851030000e00c080140004c3c04080d142c00894649920307080161000a20342e0315110391051207440601c02c0406d42011446070400118607003d81c0e01d5031103105e100d020304400c1400300d0041c4140180782c814410b4a0340a13500b078604088040c000e599807400000d42d00d9699105c0d42c00510348a03005110144085032650030078034806000005644070310661420036070400c1c1d00c03500c03401002c001002065a4148540303c0c903c410f80c1001c0105441d0564020f01d00c00f6404817030b4050080d000e010340190b41c1c03061041001e144c442c81c200e4142c911949040d100e442d007107290840c0a50300b403902210885501200313039060400030b814510b04103451905c04840c008028004d641d003041c2c1c200f09016468805001d951041038098030301141c269200c0c400280342c44924050402107401003c00e101060394040303460811960804123084d00c9441d0a00001e004100001b002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 42597297 1250 42596047 42596063
    0x60f0602030c0705010806060d02031008030f0c0106060f0c1101020a0506070c0203011d0a1707061401080d0314010b0c0f07030b090708010603030e0103020d1509051503030408060c0a0c 81
    0x204254008001c01d001e00080d015241d02c00e0ba20300065407a0503094504070343c800350500c8240148003407039000d1036200903181c0740c0130740880c0c0d039502403400c591091201d044202d0340080d600043d40f50074003944008086038a000310303170300010b43c8000304002c009002c01007004065640300c8150341e1080200e0640b544c1c000083c1c03481c6040020010b091801f013118201d00a5003881d034294644144030180081c146038440180c8200c807020740e124071116018284170344580c0d00030b01065010801621602c48090312803421200c840d410600b45626012210900b501094101801c9012030200045142e0454800201064540441016190814a0400395019144110304001017486000003010b406892528207032210719449e0700940b404e0744d403140400f9020403a401c880c280503512940c020240014130640003e11300102244803440d91402e03501150740320341c841c000c1c0f1484c02100005040300c24006c60003540380c1498121525210302000341880c0b8136140c04a401c14150307000d03500000e0a682c0c003401d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 42598547 1250 42597297 42597299
    0x2010302120a150501020708060604050702190501020301060801090504021e030a1703010302013b0d0f03030605090a20070606050607030809060a06080a0b060a1e180501030321060f 79
    0x1480c0c00810f07180c0d031803030503003c2c11820004095001141002c19140d0540c05415559503101c02e10026010141c0650118840d018008401c0b60b070214889080074828400035030f0369494034400a084200c10781110f0040345c40c20040c00016680c08294080c00c5070090078588000c520f07400044d0034035440d220302a00c28050211820041024200118180c92003600e441e01801030b070402003103100c00b808000b120304100d844c403a02d50000911291240c0c402e0000c14001d54020542c0e50010303800342d003000480c04039840310014020381c582950040e9111f000c940c4100990411140903903441e018022000e080810001083c3e003c0c000c40f5000348001d000091710466444041c3e00d0010590042264451868015030700442c1d40c0129501506080f11001c900034020040305443d140d840c0314020300001e503c0410440c00080b00346107400d2000400e4006500c02800604d080c0410304e0170b800f03440112070f0300d131b16001c0144000780d04a040c10442d0100201c03180c88406e2355200440050100341c2107150411403403c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 42599797 1250 42598547 42598561
    0x321060f03061b08010b07020a0302040f050708073605030f0303090c0a0f05120a0606090c020705060a081803041e1d060a050d0804050405010f06140f160201030212 72
    0xc21401101c0c414102041030b9100c1022041c0501d00e0070480d0000180800010801104190040d04000f8001810505003661380d83c005001c075420b404800740800d480754100404640c00124041d84030301d240c100822500240c1c0300f01d4155248044440250084941d039100c0c5054003c141d40000e404003804560008149004032a603e80044030b0060107480350410108150030409032101c103c0300c2405084c41158104010860f0359040710300b04183d03520a803816180408d2050003000024000c1480006003061403460080c100f02e055004580120410402020180e50142010364404c5644007610390440d04500700c2400c500c66680715040c2c0d580303980e406c00015000c540c143c10480360900114a030485006000e400c0b0080c00322040d5901c100000020400c80c24000340088034507204083c8c1910b45078071a80081c040315820703004055042c652007014410680c01403c0341072280b01e10f42000d8200403162241030058424804840c685600301c1600c801164040c9d01910b4000402503140d070b80b21305d010310f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 42601047 1250 42599797 42599819
    0x20c0a0f0b01230303070305030604090204051f0902090604030b04021f020c0907020c030a0b18030f0a020c0303160206090d05010f0906060b09030312090c0604030f02041d0604032106 80
    0x802010034191102202d00305245182c0150580f4203400b41c0503600740110340e1003d0301e49400040400c1d40050701c0e03098010040e1386901c00da91060506044240204100e25090032104c91300b41c00c0003800070320421019655588060a48003120381c05040700a50765201d10100d50702d03070501032100c48048040003801800c96004180c044042c107054420070035660706c60700201d90721003c0c6c088068242d00a002c543c000316040c10743d829800a400d08203001c3c40f0f01800380b02071550f848107403001500c0801043c445d03074096041c4280c01d0760180840040d405d10009201c01e19005040d030030300920580303000540107a99120041c0c2031a241c0e0b0810000c03c542d8090441c5807024280700541200c0700c61400c0404103c615851013030320070310b0700090019414440f1030601a000c07403401410241903803040d05011010ba0b075035000104042c47c41643c2c0018540024030502091300ca03000009012400c1c55134a09602581c0010001c1e4820740500c0c11004030200038050440c000300c00080749a030b003418000f0105491a0030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 42602297 1250 42601047 42601049
    0x8030f03010501030c14120907052e0903170904110301030b060a151d04180c0e060603160806010c050f150c09010807050711060301030303060806130201020c0103020c0a0f0b01 77
    0x2e0304d09000907842d980044542c43c4c1042540c02d41d2200c14401c0c0e00c072030001c0750304080d408451142141c40143d00d501c00240070000d4004011000c00c5170840a0000449104c204030a2000b00d040082246080d965004000b200d401c60340100d140300841e40c0760407507a03076400248010407030800c580e03900e5840341011600d1041c101c0f036583c00b4511184000a5102e0341c80191004200d851b611651304c2101e143d40490f080518040c443d0b80191500312100c4d00e0220841c807005054880c3c20400b000354500900301c0c04031394000304070912642c814010050f042003003000c03920b501100f52820020594600c001a0350b24030000d1409841c81c444e0780781c11003c03500d002451035400800b541e0410001d64540c07503e04518071941d48203034000741c2d070000840c0d80a070180c00940072507482000c219078182d080c0c1e400f0403290f0b0000d900940010f41c880da000c00c4040000d005094005c000114207014040c81c940010b0b55030380c0964105410558005500c0415290502c14000e85503030045036000581c0b814100340500b0742d82 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 42603547 1250 42602297 42602299
    0x30b0c0406020607080405100b0f04020f0a090b04050105032d010602010f14160813140106050a080f0601030311010f0203150102060907061b1103160e070c020d060c020708030f030105 80
    0x40002107070344c940c0640007140c801c591100080512030900c000c0031015006807201c940c1c1000b02088848810780d114000f4159090b1800542900c410310307071000420040b81c075071080e2904481084207008607603004048a41c001d0400c4104042807420001202c085100000a00010300e000030021418960640010102c10301c5a20300b8080b000f41c0d5256200880001e0b500d001c01c0c0e80d040004c95500301e01640f00303d0b6000c507801000c100980ca81c0e4585d00352480407502d07445066599080240035900e0124000f2000d800604000d0010b0080c10303007010380e0381c80180000340501c480464100b46050007501b016070160100142035480b07041c4040201c3c05d81880510703c901500074900014102500020600304544065640c00c0100d8000159103600302d052101c01c3d606201000780c0b081040c1c1b010400c2c107428991480201c0001d03440c00e01c5c000c204e504081d003504200411012814003680d034005140c04203d80004001440c0340d45240143d00d40800c03688a0a800d01000c18091080802071000c5d40c12640 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 42604797 1250 42603547 42603553
    0x3020106091a03031b0109120e09070c0302061f0f0b0405040b0d030807110307020a03031e03050601050a050903100c1101140c0d090303060512010606140702011e0504030b0c040602 79
    0x201d4100380303881e40b0305400e81c040c1c0c01d68814020482104040103a400c0c50312118000003030340358616158042420501158240803880e000100b10380e0f400c1a507503050b840f2103940b0b083d015103410359030025220720000e0280c42d0710089034411030602c1400038100c1801406880d4801340c45556805140c5a290014803405104501e8545400340303505011201c01d07030711541030381e07800310a9440003000d40d040350b0101b08050341c92109000c242c00584510003003801450083d156211141080c00c1580081942114a00d0805003000c0a1001030390304401510800095420708030b85a03103030000032910380501c2d42000321070380e0300700f05003c2c1c103598000c0002c20b1010b4101c802840f0494201d02402c6192200b40c030812100c0c5d00810441d955800681c2c0456034252082c9400b0a00599420000c2c0344101d244001c1840350355030f003000708406078000c00070f903040c1d0b03c0010f02c01f4100440b0b500013034111010020300003c8a9540484d590345141700c0e4017203802650f40000140103504000c00c1071041ea8100e0301403080944 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 42606047 1250 42604797 42604811
    0x314040f0e060f03060c0307050f0a080105040507110705010f180b0304020a080a020d0b090102090307030b06120a0b0403030e100213030330021c0f1b0f02030f1806070302010609 78
    0x3c100410605101d0300050000c1c101912280e02043e0306a05c014410010040c0c01e0100e011400c04072002407031030300c00301d0396242007650404040104030b46016026a080c00440c0c4d540b812030440110310300c000c0f5602400c0c03800b52008a20000c0e180703501003070008220b041001c20080b0385c40c03844802840c091170013075400100c4103454140281c1d860580480196000403040700c3c0000107444c0c502c1080c1d1200000c80098100761080001c2840c002440c0c000322644140c41c03042114500704078490441e04020b804c01800c8091650b1541c3d0080c000241c0b024040503150111b40101103010805009040c000380d00455440d002081c03d000082e01c0e40c04200c0000d1000c4541c502c6101e400e07075803408208410300c1000b003070304000f51952000350b102040010311000f01400c0e4402100c10b80c802c003410860f203071802146040c0d0a40303000c003515102d20009414015940c1c1c04802c2c2c036500105940b20b20403940031103561031203000b1171080c001e1000e10616905ca400041c0720400c241e819007004040381d0401c00188242d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 42607297 1250 42606047 42606049
    0x6030507030c170303061504030f030807030b0607020f04050601030902030a0b0103020a0e0c0a18090c090e070903050a12020a0f03030f0b010809030702060d020708070f03020f01050606030708040314040f0e06 91
    0x400f900c00380e41c4845500500103e800d070315006004009007020141b00310714082d42c0765508039146207652415008900314100b001045505402448551b0701c045550500d84a00750b40040c810104000280d400741c0c0e0b4580005843d40d000740c1c401004c141d002401c40d0340d00d41c4180381030000000b0901040340074000f0302c840014024480710041d805900c642c15514201044504100c0c1c20b481403590040c181c000d203620000311502d591103015488181030f6500070405042101009000b00041c01070070400281250070408104003084010140e40e01c640610402d06011008901d07100740d91101a049503090543c41040581503070102000c010b42540078018040b595006450691040b2442c043c15001004468014500a401800e070200881001401c01081c0d898051054010010440e00445004410390030f02d44c0420a01c040f181242d030080c003079460150f000c00d042e400050005014400d00401040c02c050180519000d820740362468617840300d541303119401140322140f04000c1d40c001640081021 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 42608547 1250 42607297 42607319
    0x20f06010e010302090603070906090e0c0f01021e0a06060e0702061b04090903090902040b070512091e01020c150415110318010c120201020316110c0f0d0606030507030c 74
    0x100e800e5980010349503883c0d5000d00071300000081c045c69145c0543c11001c44d0000d49840791101514540c48006918240c00a404c0e1a00c1c200038806840f0380d9000440c1f0500e40e07800100c002c5024510714142030f4900941621610303204092200400941c2481c5002c01d111025500c1a4483d154940c2180d00948421402d200381c841040c40e20705100100300f00c01e1043e0714054014070b0b40e161007450441001c90b5a2aa800100c0e0450340280c0c4582000050810034440100418000010890070326450400c949000680510050030b260480e00581400c0da604e5030f000b0b00c00130108180c080c0c80c42500c4094404410059803281c090852192440d0210261591107040c2011007116081f00841c80c002268200c0400480040c3c0e015040040086a100004101c1c0d5074601d00c0344515000035840b03040000045054400007603482e0100102c42400b00925940011800031144c1c042e94481450318030b040102c0d030000c0300307680094105424a08004204840002c01d80c04603800340c08501d42d0141c440044d840 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 42609797 1250 42608547 42608549
    0xa090c0c03120203070c030503070e09090a0605160e10110d2307020114090f06070303020406020d050306010e010305060102011805030306030714010519091211010e010f050d09080409050c030106020f0601 89
    0x8009410560f01b00c001038080c00085800201d1801c3c0900080040c100141c4404021500f40c00c0640180030040f0820190b4017840c3e4003c1e120b181101c1c070a040c420302c000e01c0c0c3c0316032500d035134402c40303182d84d03061401400349003146a076002e6042982c840718604e8101400290915410f410304441800416000c4038030003099818040c1c1c1656514401061103031000e160360015011954440411040191140c0d9810001c250003846520f025840d01e2424001900300320040c0030403800d201c4200204000c030780e4081d0b44116400e1007401d00040f95115480102e004103042d410901000b40300c10007440500c0310020246105480480848101c0da403550900348aa08000d14420301040040c40f08020814440c4803070085030385203140c141c001c02d9550019004807291140280c660184042c900c18042d40c2c4a424005070703a60a01302103071404840351004000c0d105006410210540d200d207004204101c10040b10018407150302c00f44600d080040c03801e400c40d807080c070400c0050f104442e51070303c01c200e02092040c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 42611047 1250 42609797 42609811
    0x90515030718020304140105010303020d0f09030812150603010815060a0b070f0303090b0a020403021c03080c0c010b030f0102121506030a09020d0203010f0507090603050906060f0a090c0c03120203 86
    0x40240502c01e403103502035040904225544c0134580b101a4500e034092140a0007180250300402607010125000352045c80030901e00d004000c1501418400300355408212482c0765400000b07220f030303a0b8034850f64407624980a216154080b10000c0002103d00340021242342d0452005201105031322628100941400e0034070800e412a1b009000d030002160103095040b0959000e410003140c200d403556612440b45904484040312241c0c0400c0c00d205605209a0503a02c941419040b0018035005407006006014018030300040c803000040e15011500084d00811502440901100c200400d800e040354081d40042c1c0b0a4035a00300d244c400140e9814114022015400b03000c0c140c04d02d10f03140c0d000e0a01c082e00740c5207010b0b42c0040f0207000310001601d092182000d40c01081d4070001d401e08003000020003441003030b80540c04140c10901071001e0070301e000c07030303805d4014200710751020800134410b01040a442c46a809248501d160100e120324a0740c021140d000600c0c825542d494000e208200c21000300e010580740300b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 42612297 1250 42611047 42611069
    0x1090608010807030215040e010f03200325030f06060e090a0c0303030c090b070605060307060c1a070c0c09020306031e1b060405040603080d230f0601090f0905150307 73
    0x20005400d000c00000d9803e1003400c0120720300381d20307004248e8003500213034018100b0b9150202c0420522296060001e52480c01d080d40b20341249409000968031001003c54034036000c1800e070541d00200b015854a070003154400c0740c01c2c01216036401e00c1401001c103807280c4070100e1600130014005101c00f0840001450303011501c10342d510b0650f10110300a10f58006d0315402d000d40500f001c507414080c1006490140d04c03030b04010503a842d05e40245800d00c3c500ba4064028016131007104c8001409844116609888040020301d160745c4010317040b00c254500075406000304409400219a076030081d00154803c120540456108212400d480160341d519800001419040b40900ba075400c1541400e2001c02c0c00000d10032805c0988900c005800c94040d54012a010707203002a11503c1410701d8012490340212220b03113592042030000b0700f40d5a61070f00402e0550030442c00c1c0c2c00550103a02460300f090103410b550802c2141c4588540c181c070001e040a031610041580e0f42940300c9001d19000aa9400359a41085030b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 42613547 1250 42612297 42612299
    0xc0405010b1b0309040906090210021207060e150f010603050c0f031f03120e041103060a030f0302011b110c0a080d0f271a0304080306060d0f0e0c01090608010807 71
    0x1a0200042242260b03011400200803403190350b516030058030141400341000280d041290b2040000107103841060740c0942d00400c401f140b2485610050702c290582004011a0300b18540f061300e402c003651032001a0002140c2c6003448460900751449506030783c7c150700c04200944940348061501d02540c0c4103204c40b0481080081e2100080405401050040303640c1c0303849444e107907031304d0748198103003d070941000496103400b400c0c41d8a07160140c98034011210008034a14100300002c1075100c441c902000d050040801d00d02400c251007540310842220030207000c03c01e103110210005210103104c4040c0b080c203110300c0c40745040c1d0f494580c41000480b17105d82c0082c2244654a0030a0303030f84e1010080140c00784000c0f80c100702103070401100c2402c0400b0140c04950203c6043c82d4410b0035010160309101c91044080c4100400102d56100312074000400702c0701240c4030b400c18500038000e0035030702504e41411030401c5643e10407150b0010b14103840e004242c90710b4140d03d449460072920b4500901c58500c055000c010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 42614797 1250 42613547 42613567
    0xa060f0b160305090d0b0c0a03060b0705030403020d1703010b04090e03120601081b0403080307090803040b0706021605010e0105041e0201081f0f0b0403051009030c02090a06080d0806030c0405010b 86
    0xf0052180e03090143c0b0180d014041d5441d00400048101c4131035924100002d0886c0000d03506200d540c001d004940c03a554103018241e11034a0781c81c026030000a0140c04920303145010b0040840c40c030080038128803503c40d50303580c4a241d622483d410a216407020142014007524401401100f0344902c00c2000941000c1c59442000445020038080e090011410041d1100e0794411118802000030394001d049141d81c0782000e070b100800c0360072954000e00460300107110900c40c01c8116412620350710341000c405a2101c0d045440880b601d200b501004080c0e600e801480798a500c01908240e105a004030100310b8900341229038104004400800203000882c04800510060300f103800b441d942491881c040301d81e050b102c00d45065950348a40001862500102e41002041030810180500e04007642081c48160b03a550740c0604103518149000344a0681c440014450b80d034540e00c480000c04500c01210082c410450000d0641c2c801501e829000b8043c0340707241004c42c2054018641201d01c4d1020080c0380501003a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 42616047 1250 42614797 42614807
    0x909050c0f0d1212090308100f230112090f0302100b060403150b04060618060201020f0405040f0908030c0a090504060509130303020409090b06090f01140103091401050a060f0b1603 79
    0x885000f051140c41e49400901104610541401d0391087e12011850309058042e038280c180b517640f1131180745641c103206005101c0e441907001c400b060304500140a10060342d0050f03416030040309109100301c1c0350081d140c00340100801c1010323000c4e001c2e40075981c001d4008401d8105031400c106a040c0c0001080100300005102d15200881c40791682400040c0c8008250004040d581c06500440c00100c40911207012103454051300c0f001860300c0d00085203041c141c00c040070298041c40c41100c0c412039541c0715551841c1b0950b00143c01003030744020310a5413031170404503030740c0650421401c1c1c0e000100c018034041090304140c4500c9040d20401428010a0b42e03030806042e0800c600d48000702c04140d000d02000500c0c000c00c2c00b030092100e2140944181a18081d000d00041d01c0009100c200b2402c1c0c00c070010000128581c0708480c80380800c0c170b408118090981840380341841c01a440041e00d621b05010000003000781d900110965900c0d0f40020045540c91050b0354007400b40204248510440480c8040083c0c010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 42617297 1250 42616047 42616073
    0x308090f04140c12090303060f010c02030c090901020d0c0201110414011110050f0a0b0f010f090f0e040636020f03010f0507030b01020d08131a010909050c0f0d 70
    0x80000c2030b002266042c040c03807401c05035200c4210040c081060f84848440c0d101c0355901c61860030045085140a500148051600760f0700035060140f10607240095484c184910010141d010b000360009080c420f6541e03001307500c024000d811440c83c0c20922a1018810b00820300103200c608110750030203081101490182800241c0d00e0b05000c80c0522941c6081020300010b40f0b46481008001a0340c5012400c0301035108000300010302f4a450000c002000d581c0704600000865420f291100b0a406402c5040e11074441c1a0480b0010356038802e00082c91001d0100000d06c60b6220390f01c14011003625a000c0d5480e544044080c650a42110380c26106041c0c0690070401d200e80001c18080c000f0a60002103400c4851a0742c1c0c8000b001d0b103807820094a43d4140c003620204507000c1c4005c100b48458550f00810b0a0300c0680440c10500c0c51488044c2403110403110301e50821401c081080d11540d4a20745c03540286121501100c0e18007a01c1c10000c1240380c620920000d00390084c0091a0300b940954405440f4200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 42618547 1250 42617297 42617299
    0x40b09010b03070609061821061503060510081203010b030c0706050901150807060e01030203040609060c08041407140f030a05030409090606080609030712020703020907030504030e0103060308090f 86
    0x41d541000d205580c0410180e4010500b54840c01000b0341061001442d40c0001c0700e020040d1445840304000c2441c0e90300190b81940250034499101080310325103c80508000d054650490040110100502c511079002c18040d20002c8444140242e9a82000303403903544d0b2042c102c10005c402d10041203c42c01d0800210f60140c011400240781c24040d58802c01100d506503550101a0342d100240344040c4d0b0103440c184060800100100149494250000e09654458080d281050307004008101000f40036041881c039a82c0c00702c401e01500d104010f000303100410842e01034890203507000c2040301d6400c020460400f510940c5d048488904410403e0140c203120480301641c0621850070014041074090000d0400362010300c03030104030b8000505006040d6005030300050030642000e010710101c900300000b1201c001c2d5110803890459688010306909141c1c4560000e90003440150420a1441d8941c2c000b501c1588262101d403030010450307004508442c400c0c0002000c01c4420800825240b9092001c1050254 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 42619797 1250 42618547 42618551
    0x18070302010f14040b04050306130803060f040908041d0a050108060402010807020307140706140909060108061c0807031b020108040305030a0f020c010605030624091302030f0c0406050612040b0901 86
    0x3c0036104440b9a40d006522110b000f00e0b000c1414000d51405101c00780c0c00c681c581035206c1c1a4086500d8040d0140300c0544007510078208000070981c0358071590000d05109401540b800d8460399580c0065401000001e02d941600c1c415100007041141d442c441d0a0590b90380c80c00410309552181e0055070302d00f5001d0410f0007548000d1103c0d9000880030440e5030f1000714598090310310740745880009051004140c01c030290501060040c0440c60306c510f02d010b98045424039001e03255445450128a9407a580c0010000010300d80058105100400e0001c00359140710742c0d12172500010030400101d0208001d80024002912980490042032040c0c0c00b550300301c01917110020b0003201d400d01c090204e92010f02030028694442400700010b03d020b000c442d51160010400d01d608001c0c124070100d0703200310790300b00c03620841e0103d02190281c4c5480b404c016000781c0c06011107210031660b1604940e580002c141c1c05204070300b800c402040c0780c14003c1c15141c801e1120001900d0f5521265141c001c01900100741c12001e42d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 42621047 1250 42619797 42619817
    0x303030b0f030303090703030e15090405040f08030c0310090923010f0911090703020a050409020a0c021012050105120c0f030a0b100602010501150903120e062118070302010f 76
    0x142d070a0000318014026440184807040c81c51030040d00019031503074500d11600f8810400b281d500c0c002422200910002c41d400101d130fa499141c103620703600310100050500d060101c100034060040f88000c41c0988030840054800c42d0b40c612503882559140e102c02031006c882c41c8007110b440b0200c08240301c0745400e2500042a840021a24841100d040ca034042d115042c001103c80c020b03040c262041360304410985000c0d890301c64a1070010f016132041d0b22408080320b43c0000c81d04022403064000840242d030003080041072441020009000030b07640c1480442c02854000000350034640702c03aa514614070004050203640901c0020041ca0f94503104000d40c25004a09800c40003c25602a251041001c41040180e0505010000742180d4058204042d845042c9101007031580d0031501c08006c6a90120b69404804404801180d11100d81e012040d0000004540e18900580c0c6880000522040c0310010300d1b0395495810140d603101000343c00c05100e400c070a100340090b522489811040700424100041e0748 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 42622297 1250 42621047 42621049
    0x20105091e060d06030b1e01031b0803040b030106030c090501020c0d0f0b040311060a150b0d0f05040303020c010b03070b04052403040309050108060f01020607050a02190c0614040305070303030b0f 86
    0x55010750300d9600c040b540d44d01e0520401002c000030300d0300107946201c4045000542044251300c1c420600016264104040d8074064107508038007400c1c0a0182d034025a510f072542da0104c402560400c1c0900008681840410402940314110007412101c05034000c1808030300c44020310500b004405400d4505810320307071802c0040307140521158000c038030030361b20440000601000706040c80d201401d0404440e00703180c2e50b0200c0c54403a200e400c00707591042100c0c540d51001901540b005290903050110303458208010441415016405007504507070796002401400140300c1010388940441c010017500040a000034405401c105031665003507610100011102000c000b0a20b102c1c1d0030440c1c003180014010403061115507440a03000f60454030a0750466507400d52180040c1d241d49005007181c04002c008100c2600080c82081000024000520300c81c081c1003e07030030201101c500c0e500902740030589044260580c244800308a9003200e4100300a45001819950f049002e04038049a09034440c216011032459 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 42623547 1250 42622297 42622309
    0x303040c060518150703110d02060a1d011a04060f0b0f0901020a050a0b04060b010f0e01080402010e0a0e01081603080708030a090c08030901030b010f0e0f120105010e100909020105091e 81
    0x4010b5103481030303450710510306e0b0050550a001c0c0c140c40a0780c003c0c60300c0704c0065800050b403035001108400003050500503400030640c501010f0f4100b90480d802c20101c451540200c01075140c55001c107403424050580c403500981c0d0303400501d22640b4040f0b01e08000850035406003401038081c0100c14415500d0400d0180c03501458101507840640d081d004407424841000498481c0034003082d0700b820600006034003941c018006458118046040c8416040000c04581c411451220381810042c401c3e411507864020000d040d52090094080c3c6104d030f601d1050345251211031210172250302951040c9002200d80d28141c0782c0e0005004500216140c070080d400044402c803140001d07014400045490f0142540010180c4507610007032418060072000502d19240d000c40030451031481030721226540e11160010903000071340c540c0340c00c80c1c03540b07040f0001ca800240c121101d4020340700401c004001c1d9454a8206048418203e00207000c644200a041d041d8148159452500e030b600076a03a807890345062000c521 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 42624797 1250 42623547 42623569
    0xc05070305062806030c0924060c060608060603030405100e0d080c0606040506090115050408010f02070c0602070501020604060e0c100201050a060909020f0d020303160b10080303040c060518 83
    0x200c0c01910940c0e800d00c407008070b148241802100c01d010f00c412445c40e11403800c0301000b4005c07640c80729140d0800c5540300301d41c007500f2440c0001103c020a0820354a8500406c0c80044030b000b01c91140c1010301c00140b025000903a240500340041c080c52520703180000f0041c008a01c402d00300c007448444000858107507962144d2803501c9014000c0e841d41d900c00145d1507414600000c0032148254642000e1002c50345429141506440c104940e00504884405050b00c1d54061036105003825820584200112074640e00540130940c4101c0c030100c081c5881715002e0340c80708980d01905006900207000140400c8054220f2141c07244280140d1b070080365141c0105100c4010100c01c4000b41c0c3d15001440300d00d901c01d22401c4010300e1850b80400c60a15540e0007d42e003d01c250a51501c10360001140d10150340d0140308403041203001c9448018030490030b00d411000044201c0e03070141030340f440440c0040c0c00000401180d02c65035200c04140d113400e08004050765a500507400340003c001600e401c0c0d48403030b120702051070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 42625903 1106 42624797 42624811
    0xc030f0702012f1c0906061706130f02191e06020703120e130b1008060607020d08040f03080d1505012307080301030b0603010b030118030c0507030506 66
    0x280600c09141a0004521050004040d141d902040380c55220f00024030601daa82d161070308000714103048c2130201da00701c0b0300019122041c41c0112404144500d116201401098022403120500d140c0a421052407200003449012800328a1b8052035031071016012419040100080d1114020712000704000d0940e000c4035001c1c1c7c000c8082a826401c060244108603080c8181000640540320ba540e009480031555403000710310415a0368801c10000e81464501681c640c01d1040e40070511006a078072442c140000304409140c0c044440045014040450321040d160350b0a008490b280c8105404000300c0442c200010707604040e000305030307103809110310b84c140414800f0340c0c1c418415044018900b03030000001200b0442c403044864014a41170780208000e06001044c07600300d80c04402e007050040c44401c41d100009105686c400c5403144208280d8001c2662982d48501d0110705403408 = true := by decide +kernel

theorem cover : BRFrame.Cov 42446047 42625903 := by
  have h0 := BRFrame.cov_init 42446047
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42446047 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 42446047 ≤ n) (h2 : n < 42625903) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
