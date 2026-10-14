-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2460
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:47:06.87379+00:00
-- url     : https://prove2.me/submissions/5dd5809d-2dd8-47c4-a186-729ea7dc9111

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 442266187 ≤ n < 442446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 442267437 1250 442266187 442266191
    0x9060e062415120114030f07030209060a15030506010318050703290c0a020c090402011706011e080109060806100b0702030c1c05010b010207080706030e070905040c060905040c091404 80
    0x20700350030640c0c560b600a070801c06500d00d0f03010040024440000c410070441e801500a0a10700c200b80914a60310100c5000c001c0c440c02c90100040e00e10340f61595600d00a007401c40b483d08903000c000d0307400b800405041d40e09500081c00c10a21000c41d001d011402209990b100c401481014615200d41a00401303d140f4601c8202000030081d6001d81c94407282c034000c2c1034141c60f0984e40c62003c0b80c040c1c58141e01c4a00710340162402810000540e07046000ea01c02c6150000e034151440d5140310040b900c0d8681e24460b0b5400e96404640121740c10b620003400340c1600d89011003000b00035100c5601543c0c5110489544000a00985082c0507122089024080e0184060111a10b00700f400000030300150b240ca00340748440e0001200041842000d010342c0000e00ca0a001905640d810048001d491701d945008038003e25840e4042207071410000c10140700204800101001103080510b44504d010189200300400100340d602c003c01e02e40750074824031040164940b2102507007841c2c0038041c003001d20240c510540c40b60f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 442268687 1250 442267437 442267459
    0xd090618060b04060b040b04230a030302060726150f0405130201080109050c030606073e04050c03150a08012309010e0a12110a03030e010c050903060f0417040909060e0624 75
    0x10321031480c2b1794041c501c0303038000e0041c0b46051034004081c42a485001114030210840180303800100103e0300e0b40015140003080348158181e4003168040880904640e005454001000303159001030b002a604140b00340d84038540c690340e800e0300c0026650103840c1c0004070b000804c007064851410314024035050744034146d070518526071112104044880302c044450070b0140d00781c62a002c180d04a52052003d0011075007005603040071450080c0c940001032030300200100c08994840a40e0b141d403102c40c01420140d0080c01365250000b040c01d200071054000c6d042207422080498035103035042c011034002c209154020484504a074170340402c103680d02a03188007400340003070b06d8541b100002e000c1c8010450003624017080c0503010070f0701c4908503020b0364504000c020051000103150368020800b9500070155071900c2b0102e407100d0074030b00b180c0b81c0c10342a50100042c0c0014001140c84d6190000301440340690b004000ba45001c580e107d8903201c00311507200c4100c1141d01c8241d0240704e04003034903490620290000d9886 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 442269937 1250 442268687 442268689
    0xd0501021b1216170c03090a150f03020a180f060219110d020a0905150a09020a0507020405060a0e01080d0210060b0307180f09020909100b0d090618060b04060b040b0423 74
    0x607889045da10380650400908110581090b00d20325000f0702c41d100c1c820024650310240104010a098503c201305074002400c1e00e101c1d4400ca159040302c032120403c6203041d541e10001142c1072f0500d0703c40c0c4009400f807424480d41b07255004540c28140c80d044454a01024203510800100f01c0103190100d903c0f070044003020403440d28910889110b07407011000300e1403106a10017000494070a41d441070303091074010001c40c5003069000c0e050700c2c01598161804100d948680d070000e000003a26810a002810a500c00095414000644240b1a51840c3c003500d4010102401c40010342d1a6401070070b425420410114103c40c0c0308204000ea00d12402611002168640c07414504201d00c503840041542d4002c00da980940c6044100c150b00200c0f4042c3c1c500d1528139045d9850624024105183c01e02540c0704155024052203422000c0500d084500108a10546160a00040c014005a6801036241807004125104040100d030b094840007004c1c01d09003450320040559002c42201c1e40601860b044680c6441 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 442271187 1250 442269937 442269983
    0x8040512070b060f1912020a030f080a140304030c0f03110d090e0108060603061b090d080c0c0405040308220206040303030212131e110d0501021b1216 66
    0x284030742c1c200a003d003819010400844400b8840c44e1054003040c1800c1c03250b00c81909840e040b10404a21002005a507000146e0007a0040d8800b801c03015100360700c1070802400c0d1005201285503526075411505084c150300000307000482d401004036020707024038800300d00c01c241c029006920a00d0504200e001000c1c01d24281564090b4580104410308010304c20341782d268070042c2c0507005010040c0428603204001944d2124080c0082e8081c0c00c0c48a2100c030286103907800c071105036402400c9003105412602d401400f59100c22040a003034050343d001c80440d480c09000b402d028517015550b01c4450b803180390440c0c0c00d40d9031000b00380781041503021045005848000240000b903003c3c1c1c40c016100c009200302140c0f0143c00038511040c1000d025510000200c4400f40050001c50a449189800015141a003015200c00b01e410f58001e140b00050000c1100540051400303004007005899442d2080c44020ba0b10030592040381003080d0184401c5141094100c00112007038000e0022016001d003540000c41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 442272437 1250 442271187 442271197
    0x8070203011b02013b070e16112a0d020409051b010c05030a120b040203190c050f19020705060708030405070f08031209010209060409020903010b0603090d08040512 72
    0x90000c054040c02d00c9996021710074078805a00444020301c0d01001e0103100700900074410200d0301c001043e071103c000000410000040642103110002101d4188800c52981d051903104103c80003a8141c0c82d240c58810380401c662200d9460959480b010010100e40c1c91042c5070400340daa034005160110240251b43d80380034941809002e40c2c0500002d00c00740146580d0f002400e64a20b062041d203441010000b5030010446007a0405031400710b40040d2500c0703401000d41201d29040390312a001105201100180c0001e0400038280c100040003644844c050075102030043d10303801c601085080c80400029802c1104110b241a03070391068406450325000020319075007001d2030507500000701008001c10010104900c9010301450314848203400d1900319220b68920a41e0301c002000700520011816501094065840c0c02030018a0a0b440343d4503004614025081a21054884e44c00e08040d1009401e21104890051140038050505252060780c1a154013038041d0084039280f0a04440501a05007440980 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 442273687 1250 442272437 442272461
    0x150807050d06120204110c03030c090a030b1608010609050609060903030c0a080301170106030809040905011103010603020705010b09010807051005070b01150815010f0c1a0702160b0408060604090807020301 90
    0x122458002c4c0103210484d080c1c55194142010100065074203034a002058076484070f942c1003480c0e503400c1018080f400210740c030750008080c84850030520110344400448c00359404600da4030a0101d81c4e071408100c404040034421913800803c00c001c240b00e00c0c18040028002c440300542180d20303200c023440e0710602e420f81c0315070140e480309808801804054100d02c0c40c1d101c052483c80c020f108050842e00d40c58002d200d040c01043c811a0b071596402e040090a401c4203003500490240036403290703920400900a9400340404559039464a8120705652810300d0780f540c141c0710580000e01d2860708101c1070240001155075040180b00c0103114080c00244203450207400b034000c1000b081c1c221004d0701409080e03140d0142041b02c0000200c0f032011481c0c3d0744510b00e00c19501e0f46103132200100c440390500700c4403c0d50840c5840406484801007000f20b5400058030010390400c11f4020000790b40d200071503682030041d401120b040750001e40c0428154501034124885d6540603072031141c81e00c0d0961380000e08480780741e0486 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 442274937 1250 442273687 442273709
    0x3050f040c0b0a030204031b05010f030209010512040f050a1b0e040c050d0302120d0212090c1807050c010905030c060906042103110d0507030b190312050f0c06060316150807050d06 79
    0x24009960702c85017680d0541c2c503e013410b5060481e2140040c00c58043d5049084780d0800e0000018240701c40c40410075142a04071040d20300d040d9013400d01c040b030f054600c800080f589800c2400002e82040c145465842180c02c802059205414401084144000184181e085206903808441600f42c0000200500711800f040143e8450501584d0600c0b00401881d1894540088c185c403811a01e0f01c51400250744007140d49105150399120058445002d031504401081d0301c0c028005d03040040010050585140020481300380e42e50f0b910016607520030403900140b140c9002d42c9040c805030020900600c0900803401c010500070501c2d0440f8203580c00100706090280c0d251014411a01e400d403040d460410400c0d1030484802d000134400c110320300014030000f4410030142c185050010b00c100c042e03d6010341d45107440755982039204d056075a2000c041c0c9900380710b03010f00700341c1020342d09941d544e50085401090506a038490103a03010b6895031401004041400400c2000e00d19085d03240c401d49010700510584 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 442276187 1250 442274937 442274939
    0x4060e0708041502040b092806030204030c05030705031c14162f090604020409050108030315061305040b0d02060408011d031216032004050103050f040c0b0a030204031b 74
    0x40b1500c02a080003040107424810042031280d02c0702002294032042c02a23582960080914404900c075102c4d00c030901840c111102000328060740d150300104103c0340541c480e03c940c140c40e981010748880c0035109055060f440507809107903c043c041c1d1891803d4600b0304003001442001d62407042d5a40c81800562540011388500e0000c10440c10044407040b05800100000b01103c5003003000c7c00104040007070711406411000603002d03511501258064101d0b44428480b03569120000c6540c0d400540f6820303e0300000300d00d05400ca0800304103482040d2800d00241d2a01803410013400700074086210a15080880e8140020140e220750008000a2280c840002080e07070200740307140c903c00b8400d44181110741081203000000c1c0c42c644142d6800c81e481081c904400c1e4440042600100700d00751354400c4000048509110000d001405032086540a0302c0c20700155844601d0490703600030448006103c584007202c10320407522150040c00400005003401843c054480d120b290620395548160064410400c42c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 442277437 1250 442276187 442276193
    0x9030f0809070b0306190513060806130201050f030901021e0a090f0b0304031416240e060106080a02070f0f050c090f070e0f040c0207050418021e04060e070804 70
    0xa2855803101d900d802034200076040904144031444003400082c4174038110401c4203114000c03801400000d14000b81314681080b003940e85900506040d21401e055800760300300151125080a1045015035416510706190511481c102040c6800144c0441460365091000c281032815440181d28100c0d4100c124075103480d1b04410041146242d5003140001241740e03241005103210810a81e5007040d450b0802d00f00c2c0141010051206014107400b41d943d00510040d090b06010300060110440d0300e04e040502030f12003490040d4003d41d00031505540301d603071180300104465441008402e42003102d14202501e410303007a03100e428000c100074009484d90130004110b14100603041080b00107856095641d11045d140c03600c181d10700380100500c01014406070060312401683c60030140c01c4000d81c02802003000c5210701d08025a00c02850160a0250340781102107010b000c0003c110820f003d5008148280a9801d1191109200c40e06c10072250003545071440880c0d00c01001040a01c00c0e0a07695803800d044c0303081c0c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 442278687 1250 442277437 442277447
    0x90c0504060617060f0d050a03111c0f0e0604170601080c030f0a03180b0414101b030c1109041412090114090d080d060f0b041409090f0109030f 63
    0x2c0c1c065814400e41e07400342c264102071407201071303441001201ea5943e00121107000c180000141d0360028070a0007003401001c10180c00249c489030318000300c000c40d0200d01d00c800000c0410110440c9400106189030b100c800d02c41e1003040d04030401000a0301150400356036000300c1c84c11060030000244a0f40203400140500901000361a4500d2000c50003440305c0261450020349640700e8403006820032540001c90560503041c04050401050800c11319030b910341d80c0c2c0d11a040f0604803500e801d0700c500e00c042c44805401e486280d000f45402e9020b010841040c82e195001da0703e6801d070010884a002c1c8003480a141a0b85a1004c10710850041084032480ca110b03100c15428500c01c83c81c0c103408844140080c0c0c0440e44c0c40280e25184081810125983e00e15075000208451480b00c401041080005003007002200c0c20380095040b07a001c02c2e072004481c0c0d19100642854001c07400f0b41e0400c09030180310a40d540c07804080e61600710811105445000e4244165942502c00c0040164049043c4440442480d5440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 442279937 1250 442278687 442278689
    0x150b0301060b0405030f0714211c08100e0115090902070305030106180803090103050705070f110112020c120a09080f0a15050402010e1504080f070e0c0a08040f080c01090c050406 78
    0x14409014110b00385103061400d5448c0d4103070f0502400b413840f915550401d0808200d1418401101124002400301e100e0300501024429440c00150444000c2000ca25054403810243e403801c681e55046170b801c04501e40702d0b40001c0458002000305c800c00000e18050540700a1040c02e000750b55071030307580d810800050180d2a038592520600d4040000801084202100740c940c0d030802464045420b881d03064084625000e414130103407840e850810010f081241d21803510803054030a8071285841d4043d54009000c0f07008003106661a600000c0418140d5040c3c0001000f5882141c04c025945e10b03210359406140420455880440c0c0d40b01c09480703418480f4003060040b07501a0010180b00a1410303a0000702869000c1c801e13503008c1d07031071545500d81d03816454003690040c2000c4412901003811118025960724054818002110704d40c4020a002107180400c9031010f4503039465020940c2c4031540c0302c01381590103900903615582c06204940510200b8020200818040e0800440040c03c00701008121241 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 442281187 1250 442279937 442279963
    0xd0b0604261603170702060c1c2f1609050106080604020f1608090d050615010c0c06082503090515060d0201080402040213030f0606051804150b0301060b040503 70
    0x410b000c2c900c40009403a6000541e80d0061683e43da03a100f229045045003c0c100c0025401440400c004203001400501400a010501a5080300e0b13208100181d540003002411a58010a0501340201c000303003420814004103c29000c5442c5801038840e1071032606803c1c0c00c50411a85c54000400a40d540b00e0141904004216011440d161140309402200d1141c2488891040c1604001e0410321003018280c4510000c06003040456400511300705440f080c00302c1e4003040b100513030320007081554400d070429000306500039242002c803418102c050b21202001040f010900f040100d244480c1c206998050501aa640d203021a884140e841c0c070f0350824050340182030074840710310100704996890742032400940b5028200540c1646550000c070f8040d201e20303da841842c00703280c400002001022407600741400d004a508010703e60310341041240e01046410100c00e400308141c08100403c88140d8000b03400f922000d00080c283d54a40301290035940c0503401042d801c2c9004c103041029040c140103800d41020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 442282437 1250 442281187 442281193
    0x301050108070825090302090a020711120f01020a030c0215160e0d05061302010908030c03090913212709020708040f120c050f150d0b060426 62
    0x2042000080c1104070041c5584100840d074808144100115000500c621265010104120340203034800340c42c810181c4407c0340102d4001e000030315007040610070303a2801c6a0003126003400004040030840950200c03140c0400710f001c4e001200c034991500348003c280900c01900c0105804080f2600607041455a02c58401ca1034001c07401c11003540c3e04010440300d030001a0410395019140300000c00d55411400200901a104100a2008000350b01c00394960a6100360b0394900400e803a20354640d00c9001d0418040880d500610444403d45040c00d4070035809002c0c80304040400201d521810712900541c2c100442900203502c0c4883e0403580079242a042511185288041c0c4103840c1d185000d6905600c00c0c1c24000d41d010a00704100840c1100320780c000d1880008454495482c3c0c508000ca40e912800101c440c00d40d40800081c041c145150129418400203180500444580c1006400c03507100081c5803110b81da0341c07101c0d440310b585d80801030005840909a508401c26901c0321788940329110541205440e4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 442283687 1250 442282437 442282439
    0x2090601051206012006010801050a0c0507200f0315061003060f0b090d17090a090509030a031508030a0c0203012f13050424090b0a0504020702300105010b0301 70
    0x500c42c0d075446400000c20319204445504800f02101c088490307081c90551070007030b43d0001505000541106001362603600c0200072151704c010b42580d89120301c9400405244010048201d0303162180c445c400d01040141c05441c81c81604030000e400c10580c025a030114455840c18084e0342d0070908a40320301c11906090400103641881d2038403c07049030b14451504008000948200305403107220715020030a60145900074110700d01e070b02003603894104519650144480d1600020035030114012140601c1d41c2d117002d5468071400101c01c501030100652004a06504000001071005d000c000900d032941084e59203114512880c410542507402e12a800010f0f100140b40c0b0040c03494205241c0713413032030102044a80d51001021000700401d17400d64008c1ea440781c034060b004540102c42180c0b203c0010b540440319120b40381c40e000d168040b0341a20841941040f0440802e00507801c20382c0c0240f41c110f0004051400604080913441d2089007040d0302613004481180c0e03070040b5400c0c24040c0a01400181500a0541d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 442284937 1250 442283687 442283707
    0x8060307050d050c1903150501030b0a0203070c15091403120619050a0e010306150806060609030102070803040f0c090207050d080a090c230f1e060d090507030209060105 74
    0x2440c02030003800d200710b00b0842c0740810410304002c080083c400103018a4107031601c6859540c40300056120036a040040301d0940b80b142d0751144102d41c142c982c0320315902800d45a0a02d042c2c02508001d04810602450340015000b15244040c1d02c2c0b42c1c2d007506100420299103500c0e04034441000d01034080c849a005110382c6c0301500c11023111a500031400d44483d00d000c1036154240301c03502c41943c84a600400c1021021401b4501840c3d0581643c3c02800280001100c110b0030542e1094075114032100760300084082075682c60128003d00790b240f0010005401d017103440c1c68100340350780300351811038080c071507080514108141d9100314030051034600011800c0c52115101c0ea603e6078000041c0c14100304000c0005019131080d42c5c000003c540e04072200c10200b503120000000c4400880c010b9580c407031038200c2c00202d01d00e0502c50805001801624042c61a0404224801e80300d00154910768002e809220a000ca00194440d4820460189004051a52850050001072400a810305040000030010701d000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 442286187 1250 442284937 442284943
    0x60f030f1b03010b09060d0c0902031311090f070e01051e0306180408040308070c17010e07090b06160303062102040c0c03051209030d0f0504020f012303060307171005010501080603 79
    0xc0420150341c42642d0380088d261a071910440354010003801440031040c402d50400c413018446030705101d4050342220445080802900c00002c8411811001c025000940c0c1c4500c140754954003040706041560030440d82656200b000d01166a520444100c0801000010b2909080406816035112034a546504198580042510403400090b2485200140000030030216000034001802411a0b6040840d0b444034820702038121104890003d100d08400418440258411014200c100502141c40c10300354624040001c00c02c40415018140c1d5030000046c02040c048500307900b4441c084041e140502e00307104200854070030740c29000400c11004000d80000f900001110025146654401900c7e41c42902440c9907120303202e9503034401414115407003501c030200c0d003246000320710865007414280003140c0111200c01001c01f44100002c4c070b0904040810400c0f0000b90341000c806410303501001d4680078030303001d41031400c1b001030038a5105420003641c100c018407030b050140c0800d28003178010f820b1060010365 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 442287437 1250 442286187 442286191
    0xa03050601140102100908130504020f040608040c0504110406020d090b03010b070c0807061706040b0f091b0a0f120b0307051207030605040f0b070201091a060f030f1b03010b09 77
    0x20340c02d0b09905101140b030f802003040b013248914040090010010515028003150402d02003c88210700e9040701107542d01d414020f54010300c00e0301d8446030505142c60022110184080c005a0386400643d1010820351268080e003004144080030555a403403414000a16050803401d0300d000304014907400b032000c0c00c1d02d04102c0c1d045034100f60600f81c41398203905054402040316807056881d8442c0d0302c1c000a002c0c0e01710b80c03944090040c1c189242c24540d01c08062109a0704808210303030748140c0384407203074241e460411841900854a0740c0e8034000e85613000411400c40c0e02c0900540c000c141c1011ba040951075002c0703501902c41036180c506111980b5002e000c80d03641d8140d802410f100e02e24156595100202c10001040110340042080c40ba030300f05801d000300d5100c02505d01395030343e41d1180001500745005000c0d0706666980408011908841d0300c0e82d69040302009401181d1203841520710310b404d0f9130200107030b85410550b9000781511044400c5202559a001180940070303034103106100c02d042d65950076841d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 442288687 1250 442287437 442287449
    0x305040c030209092401051002071a07080705010c031508010903080a020c01240608010806011410050922050615071e1b0302040506010504150e3006060a03050601 71
    0x46056244c2c44081e5040041e0700c03401c2400c424607040c1800c01c007142018524100c644c1555088a200c00c2400c049072984e0090040304030500e5051015044452458002d0244a0152516a040c0030969a5a500750b8a85410703c030002619800c11031610010031400c0d000070050000200000e07102d594010345a580001d00c2c41101580c04900049000d20030340006c541c040d000ea9425128241560001c0414855070003024009410300340086140c2c0000100741781607c42401d0509036640000341040422550f015001b070030400e09124800c02c6072505643c41002501608288040816904902d07040b5040141861300c5440c801210061b600c2d025801c88140f141c0100c1c1083c202180040101c810b0780c8400c00003099a0b0005114801006c508000788055174400c036000d0100b901c41c0340c0110b07000c0c041e500814000100b50307507040074420301400703080c009c10101401d03220ba1942d1001e41c0a44e01d8044103900e0f524000400c6001c5c111803c240503081c1d025000321001c90380c02d4195101c01340c0d00c1700140602 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 442289937 1250 442288687 442288699
    0x9060f0a0801092f04050307080a061a2d06161205191b0506071e03020310050d110a080a0201020708010203071b0c08060106120c021c14090a0b0405100305040c0302 72
    0x3070071300c1c40b420b40c00301c0300900400340c210f4a030241d48a028690302c1108404c107030b0b6010324103400440309001c0100a0b180c5030800074000c00988000c0c1c490b41000d1191343c60000300c0c1d1158000c40a2054070740002401c04c081c0007c0c010101c1e007141c1d00b0401c600c0019400070304c04102c4104240001241a841d600f000300f80c01c0e10b880070308990210a00b0710b44803040100038115220b880c0800c80420f0b1b00c4410303108101c004000b40c100614500e01f043d01a8002604c01780d1055031090018007649c01d0031043c807240d07103003d03418114030202e005001c905501717541e030007480240c1c000c402454299601000321307000134089000210300d540390900d8020007103811441030b203902c18084906501032090140c24400500426000d4075041c3d6560040617000d20a0100032120345800c0220114481c0d00200e00300540554802e5500c15058255108171420b401c06040300300352850604c21508952160381e1400040e00c04088010b6403141000c041180d1000c241c00450109410302d01004000741d076222400f0200c0f40d050300c40c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 442291187 1250 442289937 442290011
    0x120106030b040c020f1213170102091801081e100905210421020a090c05030106080f042003010e0a1101090f2306070803072706200309060f0a080109 65
    0x950007c004250b00100000e100716882c821074030410f50050152001c01c03181030a8000e5085403e141c0071034241b0800321503803c05000f8807103072805180c1c0c00740b0002a00c0c00340c451031914488401e0464400a4054030a40c4c8418900311054152900f00350005040c1d103422402c00303103818a0f040e030341d91544040c1340c6c015404810070300854455036006006401c800740d01788060703004007000500070380007407080f030001514031800f043e01021442200f9000d030b90018200c3d03a01103c52103101d11b0005561b007000e50150740e10b92400e9541d031000d11140241c10300c9929491110b00a0000041041000c0c0e001509044480801040328002880000001e102d1811280603003104090000da07950003140d902400410340041004034156001c181c0040c06078519440c41000848406000e29458050043c1004503421a501015000c1001d02c84ad0301803004008981c6020892808500c1d9034100e01d10282c03410700c01149441d182c680205035140900700d40c81c000c0140b040807500c0000c2040b601c0002e68854105001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 442292437 1250 442291187 442291207
    0x90105040f0612050a09121119030302130509070207030b1e0c030a05090102030601050417120a02060109050601022a011709030408011b0207030201110102120106030b040c020f12 78
    0x105603030040c0840c030180c04140d5660316015180035569908089490b20340b40020744d030782025205111000390050210302030014000e0082d1000344000542c0f000e035110b84402101019010540c1283d1644642e40c056140c00c082d95003230f001000d66400070b600c6243d0b91b908001c00140e00051080032240c202070040d035240c851005e01c1451614180260040e083c00c50100024000342100660242c1c90016080cc800d54898440038201e000c00e03a84140002d401708020040c0c4339000c0003e08811040d80188c42a02d0318418100c06a54032219118026802c40e42c0104a807492601c910350744250b0038000f4000e15141c00320070f0040c18202d41c40050051082e4404d40c1520303440307110705c0d039030b681019040c50899060403140260f40f50050b210f1402d40d90b080c0f00b40d000107180117510040040ca030700d030018188035003154015038000d02c45440d00e03401594203001e0408800b0304400c1a90080010f0341b40042d07800e04003000c1c0019211880300100941d03000014008000000054107442c812085a140e603d8120800d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 442293687 1250 442292437 442292447
    0x9090703060b16050c030d12090212101407211107050f0303010f170d0c0807060203040c030b07030e07050906030a0c03150b0a0f06050304061b0e030f1f020901 70
    0x90072000c0303402c50102e6070800e40001d0800e801d100340c0c043c504543ca6080214105507503242403004100000d06d0504100e1881e4015801203201280700600d0502c1e840c0070a40d106280c02d00c410400880b26444000b400f40c202d54001100f0b800240625000350541d40811001e80840380c0070071009001c0f6510b540420403a04c4a40517180207541c0301c800c6c2c40e049049458400d613607070000c3c0298070142600d00000643d442c02104041411421000901041ca18000b001d94100305501c1c0142c0342400200301c4000014002c3c401148280d10440c218100e6500714148400305050003010141410700c0c3c4880050b0781c0c50002182d200300c0e40100c6103c0aa0356505001c28281a201ca10082440031040f00100c01c00c00c0030740740120801c0740b141c020001c00c0c009000b0810b040c4818418109001e010b042c0500c500d80c4100c0086500038015000820400558448044c2d8100e00d1507240001907000742d0760050030f10f01442005024010380f030046c89800208011400c07005004444810002e03400694429980d00403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 442294937 1250 442293687 442293689
    0x30406090f0506010305010c0306060e1201090f0b1626060f13050610051e070f020a14030f010204060e0609031c0507120503071706041401170f010c050909070306 71
    0x5111000340020340b80040d0784400c2800212032035400c000d91220301a03c01e204900803529255100e1400ba0016010f105105546814003895035481d81c20f0345022610300b9018224440c440c00026405281036180e50483c1c40d20070350642c0c10496400800c4c2001c0014803601180d801019850f41c609450700d00c00689920221180960802c1c44950001c48621159001c248220812b03a0002020580c01c0750032101c40c80b54082520882c0002580380491901d044040d2040c83d2046150349801d0b48190000303510304c2050b9200704001914030071108110304083c04140f0b54400c02000a5040a003002d5000d40800d1110718001d0099002203040e98403075a042012590700c040e00e43c41401c103c13610300c40081c0641e00040007030702d00205998070b25440d10310510403244203150680c1d81e03010b51004100300945902001d000c8990040d15082041c03c0c8010120040380284241145090342e0f541428045040061440c26141c903030345080340c140038007038000c1c040365812030b0121703805206652410415001091031b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 442296187 1250 442294937 442294943
    0x307020a020916030509030708071209050d060e1e031815070c0602190309090504050f010c1d06031006030b0a03050712140303070c110109051509101d0603040609 71
    0x2840061000780d03e003007003c140815803250307000e01403039071203c40c8241e80c0d2143c844000c00c800c000300980d001190110280307180340c9406190100a5a51300d40000c0c00c0d04040c0c0d441601c0841ea184800103040204001103601c103090440c3c88407008650118a80d01e07800382c0008040400c0984600b054640d0782e06064054040032440c216403111440e080080070403015015010141c854011503c3d440b0f80603814038910740f07505030b490316002c40c14000b10b8405040090001c5881e44102c01448001c404280030b8007101c010240e0b43c2c0040c40b000c0681003a01c1244d034400181c000e503820014808400e658002c0c110555501c0d0502140c0c0031082d5011400c89403855201030103030302038003901041d4a007103c04c00c500a01d0203445120160800c0e10300d01c80d243c0c80140ca40c0d001103901810340a00040031210810b1810405060140c0c3d215913890108501d04010b12071150044800500c2c4003140c0340100c070000c0b850b04d203031070034180148001403881003410994000328466a404000141001802e41045600c60381c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 442297437 1250 442296187 442296199
    0x1005061309050f0c180a090f080315010f050f2a12040618060f2d020a14010506060d0f0204050d0b04060c030e0d140c19050c10050f0307020a02 63
    0x11480c10300507142c80308407501c80000c3c0138510f983c3d81e1900c0c02c05131070b00210307240966003070072601c50000c00402400466011103440c500c2c150784d00089003031280950b04c5400c918600c0c00c006c10700d45c0001000210407524807420302c681071060251184103003040d14444004100416521058650111034010100700c85458900c1655411240441d1041c05031044440c10b898440d4003030180c0c0100281c075105800781d400007c101c8014112643e109507802d0300417400311041549400d1020411064a070040e141c0314000d84e014400306030030413160054107250200070380001c00c028205500002c1091080301c5a1181c070580310501c00e00219800d81c11200104001020510116154500171a0000c001c403802c0e90700501e800881c5448600038003c2c1b400e01c0310810042c01c0e00c03003001c1900391185424011065244070045c0480d0b000300c6c0d000c0200c0c440821001c5034201d00c03141a03240213032034140388001f011b015100c400d07001e140080e007100940d1498021445040d80340e075a070348030881c43c02d0007192019602034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 442298687 1250 442297437 442297451
    0x3040305011b031a0906010309020415060c0c0f151812030c030e0307140409081201030b0402031c080a0b062106032107030503271506010e0310050613 66
    0x40842c810400b2041607a8034240103541c030090071000481440010b65400c00100d40006007a50f00c20f0b88103910282c4010b0000900d507103201802406009150003940102e1091901d0034284044401c079103009009400f01c140c02241440094010041460b104a09101443c6030146285840070000e80c050058211111140d10786800c00034990008208168041281800806d00d54240480e00006407046d50483d00004107480d000e0100400b034010b0140d8080074140f00d039948524407440c0e40c6000b54050000c00001b4100f42c01018140000401da80b10307019039030b4000c0328100341c02c2281c20b42c0c4554a0500001c5d03100d03502000c80e4451044100d8280c0400044040b040f08413050040d25000e01c800740e08640709000441151a81c021008a41c3c40300ca0405112480010740b0900003541d01036010f5006080341816500039241200d402a5168440c0c1c21003031034920300341031703030700049600440910f04070be0030070001d8002c281c940040110881c0a10303145c0000405030345440144580447c0552400c05c250 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 442299937 1250 442298687 442298711
    0x1d03090d02030f0a03030213090c0914010e1906030e0f060f190f0e01060f0506090402091203031303020c0f09160e03030a030605041a01140a020a061103040507050603270304030501 79
    0x70348c400b64403000805102d8401094202c50307485040d40c5180a515050203880c02c01060128100d0f0f080c0e038540c10885078281da003183c1d03290360402682c0c0b10f80100f00c8070016800c2c0300d0050243c035020110100315501c00043c141540c24001442034022091002e00300d07854a0301c070b5030903107055001c00d14102410300f8030f00100b0086906600c84200f0b010030500811a1743c2d00d4003600d11200d0168031416a0224040c08150114506a03002386055071004041c450543e203070400c8141150001c440c01d000b0940400301c0740d02890f405221045688404692040502c01c242c400079480310006003414001040d4035400442c510701030300484800b880d000341104d40760780500030010042e0040d030041078080c60910031040c03148032000403c0303009100e05071203000040c044030602c0c04860700001c28580441c0b0580c1d940501042c2d4a105031074880c3c041403081581ca19041c02d05a1501030150b00903406000b00b0420000009451081445500d01840c0610542146a80914614020b5400262103946408903202c84 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 442301187 1250 442299937 442299941
    0x804120f14220801020a0e060f0706150f050d120804050a06061206141312090f0905010e06010c08090f040b06040e0115020703080a030c1209060b041d03090d02030f0a0303 75
    0x42c0403042000a40d42c25101c201ca00d00380e000740c803900000701d100084003220900d014405402c80c03600310300e03090f402d00001d6101e103400c0d206142c07003241e4025040001481030b01101003104020300800d0f10484209103550350354040b4982809480002c000343c85000c1030402c80b092016090780d5420031002d01800d80c40b2001c03e103109000789011070b1698640070211040e9917100068502c6600d55001e03020290400380c4800c0200c42203d014002003050340c0c8008a41c1b00e04409404c070186c407000d4400101d540c10301701e442d510100f02804807818400700300a0107000a00d52011240401401d42d82d42c0e11244a41c80490041c00004141c2d5074484c00200300801c0710703480462041e04a440c8400d125420400c2020b00340d071619601d000c0580004002c00c07000c68120700a40220120340c0081c50403100e548001441070040f1203604074201c81c615220340003c1c03500c0c5094060400408201001084401405035545989102e03060600f80510040081c900c299034041c081c82c007a0b020301c071080c2c4074805090300d40100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 442302437 1250 442301187 442301227
    0x60509030d1806050a02030c10020d1a28090608031801110a261908070905011e030605030a0b04050d0c12030506040b2e0804120f14 58
    0x10007441410103809100d485448502044200d44030315504450401d0011a0300390b004059940551008010b00008450700300000700003160408030050700e4025884500050703072501124041890450b0303d1600040d0385000c0004201a07000560244240321611a4010f19001e907001032095490302c200010500000300c02400da900703003c5403402000255800544049003e00030022059108801d0303500020402811840e00d00809800c070b00d810204503820900d250b01a03c1401c01401c2560070064000c0c0e0000300158100210303040c02000c090825000070071610800081c8030400d40e05072648180240694031003409840c0c05000d40305100c0b11800c000900c1c038020782e011900b40c880c50101a034041c0c82810345490060384920340066500181c402240504030280501c1d17401a50352118000c03683d20040a50720350070421411009400104007044180305800c0303440310511001c441000000740ca8005040e40e8405d003414000301100c0e051104455185030040311145966001642100d2401d070542201 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 442303687 1250 442302437 442302439
    0xe2b030c0e040f050f280509011515030e0d1407020a03050307030c0c050301110a0e0f2116031e05070b0304080304060513020901170a150501170c0a030b1f060509 71
    0xb14a84500c0c5085007038414183c0c017494000e14818440d401c04071b0a81000343c008140300000725140070395829010b0151010b41c0300034080d00786201c1c0d440640b0340602400460094000c050304074943c0714240074046529001c0c2c200305410000916400b1580e40b116a0005990403c1c2241c0d262042c1e86009444100401400c3d40c2043c007822000840e841c4c1406051250580700e103039941042c46c1d0740d1003501c0540b138842840c0e078012202e10b12007550303880701d020040b9204044146420b6200c1e20340b007104d00b807440038100c103650100e5440041c00403a2003c600c08002c9408601280d4024210303080190030325036190448a4050b80000034001030003400005036019501801c01040142c498404005070b400c0c2c0c01c503009410007100801040400590001205126040340540c0c40000e000c2c1d42e4240250201401c1c59441c52f581c100610080c4e15074668160070400c20f0000300780c60100440003540c4a10716120091500e91480001050011003600030300d90051581020118030f6240c034005401c07900208041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 442304937 1250 442303687 442303711
    0xc1b060f0e030102070b0c1e0403050d1d030a03180e0f0609102301030c020109150216061404050f0a030518010c1505070f090e04020d020303070507090e2b030c0e040f05 74
    0x402c0300c0c08c000c03a0200d0f684040188100b45d2003040540b0640c03c80c11200e121001114800c980949060100b1047d00744207a6480c40e101011980540450342c95400c5154440d1000f020082d00f55600507205400440c1210030321710759034a000c148103c1c0c03030361900504059a040790340382c10041d450040c400c4641310b090f04c0074054085102812422903010f1403001d004221854060844000070390300800b18000c07600c3c03521000c20240c1d100c81d03040c1d55406102c6002c02d03500c1410003040c03010501041400c00740040142c10346c2105a01c1c000c2540c022502d84080300c00260000780826801a01c16006d208d511547c43c1c5040c80203101c802c00140030444602c0702081d015110148802d00c0342d01488182d031401048981107071929004e002d00160204400c9805102c10048440030030020000c00000300401013001c01c40380f80c2c03c00a281007151502240c80901081d2030444551004083d4800100c4290f00d0005101001d145080712201c0010014a80080c03401404040b0a030a98004074882c1c0342031601 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 442306187 1250 442304937 442304977
    0x80a0c0b0708071e0623042d080903010e0109030f08060d0c030803040b090105220f0c0b03160c02061803150a020a180b0307050d0902030304060c1b060f0e030102070b0c 74
    0x26803020724a43c0b1b0012002000c1400000c002902031212103c4254025841d244451369211940b1211078107054203840801001c00d040310180f5003405400a50a50f40c40244503036080742c0e6026204241000120341400140c80004a40c1d40706c03510180440c0360080020b61078161f590511940540c02650181c035903008000010f01d002c7d42c14002c00d0300812440b0755810103014100c038280c8140381c00c0788013142d91407540c5240c1004251825000000f400240407440d0342c074105040c811141120040004082c0928540f8041c013690725541900c610600d944041d80e02e80c400c0c0030009042c4821845092041141d45091045501640d03010b0501100940c039050940740e510341c100c908030461803290f00d112060800c00111032500c680d01a045181000c00046100030041d80041c0c10360f00960020000201e03029015130901040c0300030302d00031005078003084144a0901c1c400030402108540b2002c103000409c81091a00d031001d504507000a0b40000480c0510300b010160700005500c1001003001100761518 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 442307437 1250 442306187 442306211
    0x115030c0903080a0c03090509070e27010e04020d06090312150f06050a0207080d0f0e010507210c0501060905100806010f091119090f080a0c0b0708071e06 68
    0x200480070b880e00481e5290a200c1100411200040400412010803004010010b025114240064010110740d25005080c1c901041071002c0c1088601d02c3d0b41221500100318605d040e1080d080300d0641d0485441c01c881d965503400030425600c07840d03200405191801d201d400502d07500c22811306000c001000b080c05101641c3c035240000b2041d5014940481c101c3d82c0c41000304074000c1c0014107001e041e90040d01e80c81a40e40e0780581c207024001101a020a003412507400303583d54403804220740c40300c003401d02c2414880e2a458050220704100700a410042040c142801218041d0803107400c2150302c00024008951182021005450151101100800d80a801003000400403c5042c140d0b0442015139020a203084014400341c4107590218504510400008000344440340075061842210307240c588241b4076020001c5584400c0b90f1141015170403030000c600000721030500c2c51088482c0140c416443c0e0009081142441c4501a40145482c3c0c100342e0000100e0390038607011600c80d0085400700300f4145110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 442308687 1250 442307437 442307447
    0x206180406050d1707030201140f0a052d0a06050a1e0503060606220509150a151b0819020a14030412140f100603021e09190e060115030c 60
    0x242c0f00034903002d00c1240c404c20404806001c1e103a401d000b4400400c040c03541c0e02100301444011344010b40814194420465400d003e070049907004850000100c0f100c044440700350505428626580286020030030124466801503041a0050100140740a01d0560341e0350038000307a40d062401041d08000c001400007964a0040b80441c03207000041c140a00d4248a0b4102050400d408209074482d001c5084000c50f80792140421300344a0a504d82c007100c4001c40007010410f4500e420362240784414110b0040702d403403d512080402e100d014214100c07a10006910b07102d02c8600813804004121072841580180300780d80010f01d50022406007032240034040720718502580b6131060303006080500d5007848401c000140c4000c141b040c4042c464041d103002d0480d0746029401c00c0580101019001d848100078419071410325003c04042c50300c0d52819002c00341e40300104022000090841c180a840ca030b00c1401d14a8581d0400300c120708188080d90407540e1100070440498075200e003c00e00182c0f401d1401040c0e00d000d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 442309937 1250 442308687 442308709
    0x20307180b09090606070807080304060207032304090f060803070c030b01061112070809030a0b1608010e010b0f0f03040c03150b0102060615070609050304060f0f0804060902010c020618040605 84
    0x140c501100c07951070341300344582c40e442214110b404000820016021950071406180100c0c4111409a960441410010300c000141c81c5500c81c98a40c6030f05620b02071004808590486604900100d40d86039418122001465a5405485540170003c0e0910800005440b140140c07480b40a403001141d0301e541045401041564410450b6805084501d202c2c8000e0340c00341000074404c3c0f98103032504140001281c00d140e8804030459200f81c02c00d040c041d104130700c005111515070311072500103a19032401c0d4004150850601c24a8440e08000818409400c140300840d41002c440b6010079580b0308140c905911120b100744810b0310703100c50301c000d00c5050015601a43c10200e5050f1300508050719080c0800c1456640401000c80c4602e080100c0030006c1c0840c003a121002e0f0141d4003441e2150700d03011010b0704186003d17042d2010003c4050a9140c810b8000c0234070f540013031b0810702c002192003403880161202a804100a0751007400802c0d1099054561100c9400380d81041c0e4043c0602ca9039141400074207224 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 442311187 1250 442309937 442309939
    0x905010611030f0405010e0f040e0d120b0303030604090c0308070b010923190f09260a0f081e0a0905070504020a05040605070f02090f040c050901050d2301020307180b09 74
    0xc20402004158400c151031f20031108014030304510351001200040c01c4900c0a108140305400001c00444940d0f00700c1c8075110741c0e00100d003041c001c40c1e01040000303480303200c000d281e10b01c81d5940700300c00702c00e020251880101a640c8452841da95807a40d0400c40351400003449114030b890300f000d800b030190440e41c10f0340086000a0010994403504c42c4481070b400f01802c003041c00d42071580c42440d040c401803a8000c8014841c01020464580010390307540d21000320000b1140040d1400c01c20940c0f1116034803184600c004282464002119250031140f8603211040b800f401d15590155811f00041c400715a0240c4512031254046484042d900d005100690140e00412408030fa414401007040238016001040f41610030460380d84500c04941c0007441c0b230300c025100c4030320f2000c41c83d040104018011b200600603040440c2c00360320340d6150000050010480b03c0e4020000302001007800d40c01144000b2000c985905000255100c0c0307040d0300000e0150091040d281c0c0e00b5a030315400014001307409012a08030030302c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 442312437 1250 442311187 442311217
    0x106080f031201060e180a09020307090207060b040e03090d03030f060f05031501080c010c150501030506040c0b07020a090b0f03060403110d05040b0307180305060f010f06021906051e01090501061103 87
    0x88200d806c2011180108411007082c0c13100d01d00d00060760188118070141001100041e1a1072213410144100c0b51003100ba40d0081d45090400b00e440d0000006541481e02c084903d040000314510341203002e802d4000117540303c0d900344440407030b02052900303108060303401c00e4080300c42500d05c9010700140315100703100300325140c0c0140480880c554801c2c00c1d412207981c01005900050300c030016403c030494000b42c1c0142c1c0c40e604400300740002c01c25112186c20041c52919410390404440e80c0008040d1149481050f000f240e035040f5125581c0c0b030b0044c09c10009900202925034515160802600181184203c41514095100d424802902440036141a1000c0c240014155a00d0150036182400c000d41b2440101c40100c0d80080020400c002c1c9520501c00d4203c1b602d210b51500c03c0341c00000c0348542150041d13400c2070003000c11282408818810032a04031102048644500c0c2d40111f118a40c200c480c0c8880804400101c0c102800d030300054102e0b03410765103018504c919040e189440780100094094445 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 442313687 1250 442312437 442312459
    0x6060d0605070504170609010c17071d040504031106060a030c1701020f040b070213020f030f22080702120d0807080c09040c020c0901051504090e0106080f031201060e 73
    0x10300103500642d40302c100350410781d1400d601d4018820788070001400025880e40b22000f00041e6041c28000c3c2d00d05100c2c5810026000348080c0c0c04000030303500003031100081101d03506501c550000768490541028202420801c218200740c100103048801780c2c1c85050399846403002040190404080c0d000403250406101c039403150900040c440101c60310046400070350f400303100a1700144074000082c03008201610340c4580c0d0782000e1041c0700c0c120308203a45003501c9901c10f04c111148000303610708980d4400d2010042000715640c0d441440301303000c648184282500c1400000c10f04101011009026160088030501085180d640c0e0080d44d0710034441030900054100804101194003c160080e0401442d8100714102402c450200d82140c0114403900f006038040c0344140c20a00305602a5805000281d801b41d040c0c180300001c0035081c1c0725510540c00300550395000130103140d2003940b15401502100e4152450a40d8a1642c1d60f5603801800b800724582c1410000014100c2c003a0400d07004551024001000d0700c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 442314937 1250 442313687 442313693
    0x309030a1209060e0a1416090b01020f03040602100f021602010809010222030317010e01170705041a12010203070c1203140709060e1903021c06140403080906060d 71
    0x803184a4004039482d4892140e4800200c0f940500c903818501e40c8020113000f215410007040d043e140d00500c1d00386400440d00290103020050910007501d896800100710303000c0001c0100d01d80484202080d81c1400041400303e4250360104030201c03000d1000d041030000d038406146100c100d101c0c2e2052440010800140c50780154054110f407030717026074104001810400e2034003905a00c25505895a010000e20790780a00c205034020144014400e00c0900c801c406605180d190b4610340018000e4800707042040c000c5241c0709008000c800301416001d00144081e510340c07001c00702c0f8401c00044051040c0405421551140414405c3c2e03482040b00d41d65941b0880ea0302d444a100d50780e00100000105502c0300c0c0c00d000802482c4070000e01030380441ea03070981c03c1b40c509000102810203004020784031340c1d010a4200715000c2c000e1a141c0070381e070301160350613009003c1100c40e18041000d400002c000608084810301c1c1c100109400601c10344c0203460360035850380c0c0c092070340d6165182100d006a00042801c001008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 442316187 1250 442314937 442314947
    0x1707060f062c0f07120c0206010611011505060c030408030c0106051507050c090a02040306020315040e0c0102120a0e030709020a0306050603040206270607050327010203040b030702011b170c0309030a 87
    0x49281400c0310344403c44224442560404a03104015032300c41c070300400403250b02a891980d0504158003c1244c581e001d403000e2841c8540e4403415114540208000e0360516052003154000d01d945401c49a0b00d92289080502800080c413a040c403c0c000d4254110242540d0022504210f5011001d41000d80b0301c0810401405030181c803800c0903e1382170002000107055840214040c00001011550b0508200708000030340e0f612a002c01469084900b40b025141d80000c2d108101c41d84050f59140c5443d05102c0445500082d600a1a494415004001105461603000b010b81d0411a0f41c14025140c4031130511010340300c1a0340094001004214119100e5030030034050318a0318001560750304420a240c00209540c20482040d50b0300e4100103002d03c04000c1c04e521100c0d5010300c48001074075001c9110000307912806a03200c2c03945103450000c00920301c0351003940010302d80d240e5141460f000c0e849608008201041c4d0710b2280800da054280421508035202090700c0c480c0400c0d100a500d82030164000f110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 442317437 1250 442316187 442316191
    0xc06011412030a0c0602042106290d0203030d0903081806010f0b07060b100905090105040c08061002011e021b0109120c030207030c030605061e030a1707060f062c0f 72
    0x40d40d950301f404040380c04148150310858191240c0c10a10080325181403080031a00058900780410901e58405c034540d940c45020144158411a4440303500311032400481d05601c1940101404c1501d442106002c05030403ea89a0260702880c001200c5c1301407031400c07550350760300a000d2071000703460184080141d511644018043e1034400c13a0041030488410f070102e1300030551200500080b800707149c014083d80c1001c00000c0d0041c1811a820300c803800368402c1c0580b40340b00142905015606044098150324000d4200f00e500c84980e0580c05001a800c111481c000d40040e00d4098010b1a4a8401c0b0500481400b8008002d0740284d003400e00c40345080f005a45150024100b18254019000700001141c64001900c000f1400350740042060714000c010481409070801000e001602490a50701d031944001501210003030f84100324280c03071303001903000480a006e1031200404e1281030844901141c003042d0014000c1b80d00e00302c01c038804000c0058031003144003560000c0750940c2042c00300188505464101c295 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 442318687 1250 442317437 442317443
    0xb190518060f0d0c2604170c030705060a02090a050d0507091a03010e0f0105060a0e1302060409020307090326250f0804081b060307030e030f0c06011412030a0c 70
    0x2902d405041040340341554034103a80080411000b10200159982d1409261706103031360030442e0324182c54160382e030050503c0448407404034040081085021000c04101316601150400e08075002460041200c0c0e000e90305c80740c0503500880d1015800185400d010905c56525640080648403c034103003c0c0c42c000405800c030b80301c0b0303095410010f6911a6182846400d805040d580c000d171040c82480c00f000c0c1c0c00e550014007110f0040e641d000c0100200008100d1503a00101900c00000100e1309900005c0c03658000c640006120758400030920880390740040e0450122441000302e48084009040003031100d40c00060034210065080060790361601d4811800d02c3c0b4511591400903080e1081e45800160250121085175004800581880840000c001210340c40c88180ca01d0f070180f80c5507c0124180d8000a40031034245230321403d40c0d90240d0028020b90314a0442d416030203031a6050184801e50700c81082c0b02d86000d001e00081e206481d41005401070403a21004802545410f004080031115030301005816 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 442319937 1250 442318687 442318717
    0xe040311071e0509070219060c03140f0f07020c01020a0305030a2013050a0f0306020705070b0c03090a1a03070807090b0d051512190204060801060b19051806 69
    0x4100300400310310219000304102c04800907603080c90240301010b0320181c141e00555200b460301001d0003018503140d0003007660201d00481d61a80c0c159055000d8400b6505000c845641641042851003003110780c81e11941e410320700740b40c0c542c803050300c207030388816240c00041c3c0143c00202014000c240280c00440d00805148400140020100d11054859803d5400e004d8640400510402c502500c0d040b4040905021101c0c40c9002d4948030744904030030000d1000030215500403815000384035003400410001c0080b500c540303540f601112412502c1c0c3d0b10201620b0700c030760944480031800303002e1052200c00c404d4614402c0c51075500c0d0706600740c2d41000d0040400d010421140b002207850103510004e01a40360b90f00310003090301d04200744995404500d110f410390203080700c0c00d0381002c0c0e10000118886000302d80e20680d040030180b4004076010340700b15042541598202000010a0305508008002551480d4013116650f03000d01e504850f24860301c9915445c1c40010808240d040c9004001040246040020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 442321187 1250 442319937 442319939
    0x70501061202031b130924050709061812050f01110408010c02030304021806150a020303010906060f080a3603081b0702040f3902071a0307200a02010311040e04031107 73
    0x7c81001c2c3e03001000d48503500c3d921a0180300030140c2140b500d0018120504040c1406000c414410031000005d20401c44001c203036080d94024002c0c1444022441d860f64002070101c032020601590186d44540304641c819803070000507401c624404000e44c1c1c0070700c0d4002d2200c403405804003152240f05030007030322044d40008500711158140d00310000800504c0c2860f006182c580d0b02d04030104041b900564400814072101c51103030481c0c01d078043c040c2c40c0d1003140760310005410788440302034802c40c000d00803000b049503885280d0680415114003001000302d121f5624141030360707a01c1040040d00c103961801400f110078203002680c014034064000310380b56282c0920026156141c42c840c040b17082e803440035011001e00c44009a0039498a0321701c982a0032440ca000030440c1d5450314010100407410341c20074456543c000b01c046102c80384184803070104000701580c2d09655080c1004c050791a54502c1c03d0881c007080c80c000c3c0000d50780c00705006070780458241d681d0640056071382e9101174400aaa008910340240100c0e54 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 442322437 1250 442321187 442321223
    0xc0109080f070519050a0e010f0609080312070219030210060b040605071103010f0504080901031407021b060c030a08091c0504050405100305121c06080706050f070501061202031b1309 80
    0x46c0e100081c096080d403550907500d081010b440502d0303150412420040506801c0c040140000110780350348000c03845c54511a610924201d003401060014010840c0c031400d00c1c10305142d4001035200280500d02420050a903032001c0b00480342c4986d2069401040040c01210302185d04400310005000c40a0700101b00103000f5250351040381d00c1110100c032500001320b0020392a59042c41341c118007130088824140300d030611207006580c1e5001c0304288801c4c403070b504131000b8864440030142c5041c03141500440f07449114008026010f103200b29003120b414803032040500c00c40c00d494070001010f0000381d02c920b0b28003800e04052002030100240040e507086035010307000000074004c000c00040c42c0d821903401074a8070341003000368180b418030f65503841000742020014480e8400100ea540215082820131035900c402205c100f02947c02141c4019007107520305a000100106d4182040441078400c4065a80c000c2070a1307201074152441a41d80c641201101002002c000300e603510801469014295585510304041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 442323687 1250 442322437 442322449
    0x5040f121215031101090f05040b031e1e0706091701021905131d180a0503030901060f0506070c0b090d0501020c250803031f12050c0109080f07051905 66
    0x4080b420001010820420502035001c03600c100904092174082645440e0042c00c210182950164070300c61a07a0314410b0200b80d0341000b10500c183c041c24080309944420441064030b800c042003a00c4000708000c1c90100510001081c4a810f40b14a070720b074400402e0400815101c00b4000b180344004e191360820103a56800c1c02c0120300400c514580e911103079115000e115010044800e540000c6459004061203001d00c82ca401c10294006000b0483d00f070210340540d0705a1400740103a0010340a40000024407130460310640041c0285d5400320700701c0b0702660303541e030500005100300c043c068481100d080c07060140c407800c40c000701152240185500340b80282c40d25801d089a00c00c0c0000090355001e107104c603a0b14054030300769a10031016440310185652618100644074407005001c100711011680c1c038240110f04480b03240c0c010704405548a00e1581040c43d0155580441000985c0403a10703011000030752044c00a08140780784c14010103481d119150205100d04410b6070810036100c102c040c0300108550300c0d09 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 442324937 1250 442323687 442323701
    0xf0609060e160f081207060504050114150f010503040b040f140d030b0a05030a0c0b3f152b0b270604170c010e010f0f0f05040f1212 58
    0x40c035840c81480e103010030f400d48107250b0b90311108107504601202484003600d07070251000550040b0010945641c4c600d4100d0041ca00d07600ca11001060100600103c000d2145155404802c26074a00c0500d001e04070040d9030502040354010441882c9100150024000540c00d0310524400c104203400d80010524040c01c2201c0803846000095403a4016002840d041e805070009140030350140943d404c1c9034450f4945811a80910014400d00240800c03110072003c200d24020b843c1c800b44500b150304820135440052100100d00700102e0b00d05004140d618107400390610100000401c204842d81c12507100b8246800d099a00203a100518603080300400c000f0619244503401c004e02c00c0c404c1c0058044410a0109a10710351561540b00303004010015910356924100000301c90300d016160200c000b81c150160100a03010700c2294200785810a41003a2900180000000100705000002c04007400e00c4c1142c1040380d01501641c101c20004002c00c07100e0340c0000171143c01c0e02e400040c40048119100640d455 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 442326187 1250 442324937 442324963
    0xc040509010b09060901050303041a190c0218060f010c03030906051810091211010b030a080904110f0d1e061509091406040b0102010e0111070c0609030f0609060e 71
    0x168030542e255458a10b0700ea59011500719003c03c0301d54100400320b0f5482c0558000c0e00c038440303410000c10a540d4a0a0251010841c003d41c250241e18034410006010301d000c039000300e00880490400c0140c0ca0f0081d580b140c403610f4007501c242c0400041100468000041c001d0a805155641c070f440c80100e080350150520880e13194242e064801034114585282001134040d1242c40d910b04402100003c1c200740b80080d510f0403518105003002005200d19005203e482a6542e1500c54040510100f00410b8042d24010000300c4040007003030940000b48800f8494000c4040b01d0f40d208000c402c10101080d4840c800030310100034241c820a244560381e10803101c00350042c9500340740342c40301d0b101c82c0c1d5403000d0910080d003076010b0140b01a039102c0c00c8100c0d4072007025050a00c61038880c1d484682992003540000703d40c0c03001000030b0010300001c15148032076500030f031020b070740c40392071981d02082090040750800d049a500c83c01040040640f51103540c020b04000c1012529691070740c02c1e481c0c0900e01008400c6007520 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 442327437 1250 442326187 442326191
    0x60f0f0d051e0906010603050c0408010515120f06060d061b032408061503010f0617100e07030b1f0303031a1c14010f050c04090e0105060603180c04050901 68
    0x2001c554402400110351002e030402060b8508006010b540460100d0440320242400319440d1a440301c1b007041c601a0703400c4000a586490204848203001101302180802c082d105e0f062801031480150742ca6030b035620610542a8882000328103503003405030b045110903005500009101d41d080c0c603140b403074040440d0f1000020b91070b2030540185001c07034180f215205402c8454800da2078039000e04a40c54a0004144201003030005450290a403000e400074100d03940801003c01a85440b00f00002003020b0640702500745100300a4200d80f90003e0307102d008080c001c00300080180d1031640d9107152032504002c0a100001c0305200344410400480040e40014510940380480d001c1d40300e020100d502840244c000340301d07240d40085a800800c5941c00000c0440c0c000728115100c42d0380e0500c0304c2c05010802c0d000741000d45040d04005d40c900a035000b81041e9003142c201800501320340090682614820b548a03680719034100046826240d1040320650340010b00e0081d03540d42c8085200281c211203046030300e01c225035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 442328687 1250 442327437 442327441
    0x20c030c0a12051603051e03010909053c0a050607120f05070e01050f071b080d03020408030414040b09010b031006021f051305030301030c030614060f060f0f0d05 71
    0x101c030ba03009005551030240b800300d050070500720b180d802c0c02441e402c001d401d1100000d0302d03c803201c810307805515520100305c440540d25656050003500a10100c4070a490030f0051200c1188031500401084003070407030184604090550300481c00b81a62548035801c0410f1150343c403041c00041051050302d00c44c00851b124828003c8051059109a45018022500c120310308020804015046214000340320403e180140d00c030603555003900000d10404d14040d010340d50381500040720001c01540007080e1426801070740c030030751074400d0180c00343d0140703004032440e9400501c02409044000a24603003500b80003000882c0480c460000720b507a0101c01c0e0000e5100306400001c00c0100b006082c446401003419100411031407289510821842c0c140840b00341407141c44001140361a0300c00550342d10402d4000d0b05880d42c0c0d503500d1420072010070306c41c8011541c041c188900f466000341010309040c407500c00905030300e0300c0c0c03d52081003101c19400340c082a50741460605c0782d19040e520f05c0000d0300100317000c13001c006014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 442329937 1250 442328687 442328693
    0x6080706031109090c030a061208073804020d06020d050601020d0c02060f0c0102071a041101030506060706090507080307050312090a0305040b0903120d090c1401020a031101020c030c0a 81
    0x140d64082d03141c0c0d2201000f001815020b8556002850b0300c101c06002c4180c890302c984105102a11760383d48401c8503140840ba40030148001d080050003d17070b21074160701315407000c4207a2444100c000c0b41c4a000d0440024a00c003400380c00e49420351a8040d1000b0801c0c2c400d103071681d4a0000f02c0c1c0103080c01c2801d540d0384108020300c5580410500a072211241054000704c00c0a070300040c040d120301c105159800e08003240909075044250184ea055507440123803c1007150020107420802102100e082c0c8242070081e8850340154000c2c4a00f0340130f010058141c0d403a204180e110f03c005005080c10031a8940302c1e03403c000500310300c144068641d00c2e100c1e401455031511800c40420301003101604e41c4689800100404c000260000e045600700c943c4011801c0e12180e0030b10029041c8480c8240c8541544000641000025120762100100034840c2d80390031541a11303000701c030407043c00303110300796015030f00c11000c90000c01d001d01034180302c1140d020000340c07a00c1da41000b00e038103541003848020000d602c200305003c20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 442331187 1250 442329937 442329941
    0x50403030f0612052104090902040b1008151008070e030a050d0905030f0102030708011a070f0c0e09010615032d050403020708060405030d09030c020d050705043801120608070603 78
    0x128054400b605e190945421807101c000e10662003890440c0350398805020442d11241c100c2d00b25004020304001d651128148050320140c0c003124011001e003a9902d00d002141f52006618000440965440405540300c1c00280c070100c18842260750300d8460003488500188081011061060725a41c0c1c0c800614034080505140040001c60341070030364014001c000c0740e03603440070119044030300621032910018042c1d4108002d504c607140c0d0141c0701319010388100c001d00041c081c81c64101c2d81c0c0401440e00075a5a0300002d801c880c0c49000f05d0765120400902e044005120750408240d01400030840340095292a20307106110017480500350200d601c2d031040006058040c40000018200080a404540341c41da44481d20b034401c10701e000c0c1c051a5550300c62030605204c0c00c48844081da02400146803500d0f14241a60b40d0f02e01446000d1089041c8001009000c04076400000010303820034807010002030900780200e4400c416540e40d810000505600340200001c0e01070350b03008141900241180d60300785170340141 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 442332437 1250 442331187 442331203
    0x70b040617060906010806010507080d0c120902030a0213020412200a0605030c071a091006060e0a03060b01020f03130e0f01030203100b030c0a030302010e1506030a06050403030f061205 81
    0x501d0405100030810b1a0b2500440c10342e2103102403a06603180d079580070060703d1a000c2c928002d041140f000c9003404207452aa8482450400c80e40c4031040c00c054031800c00c2042d140301d034000035050380140725100c0c0181090403030090090103550001d42403584802070903072100c00c80c650603140406410701324811203004a20b402c0c109241600c0301e0683d5400c03c10054620300c40501400c10500d00000d1005c24000c00c42c08100c0c0140d850f0b04c8240031130801d10083c56036440c0841e081004a490031100149550007090080c003040e00140540c001240f442e2a43c40050040c0c4c0401c0d81903004590411410759400e100400130942d5a104914800d400c1c8004010444001425007100314003020060002d0b80d0002965240b400c036401003c40c00000380700100341805505401250040480d02e00441015010b41000344010100070031a03005c110341403030040d42034105503400ca4140d045111b8070300c085449508595030150003400e004c01c60340f102212400885016a0041700d11543c04800e50b001c010080c05000d03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 442333687 1250 442332437 442332467
    0x30f030a060b090114160611090907030c020d12090b190b030c0d0f0c032319030f08040503090d140d0f08070f0e0a0b03102301050d020c070b0406 64
    0x1828040403d0004c0c000d0058130b40b40344443c40380030030080e814801c0a106c000b0250b900600a0103805e084154141551b080b0b40400f503c1540a0000102400c3c4a44940684200715034001c10400030031940646401c075451b40c11864168031001030101040525031000d010b0590700c030790408480c0f4040c841508580c80002c000344a904145c03c601510341ea44201c02000d190050180b9042c1d003064607241d0f8011041e980000c7c60b0407414aa070700c014021440c40c10600c02035000654030300a1501d000e403074207100030082c0140812496035180c1e00c502d00c1008030b60790080c49602102e241400b103800103000340c4001d41c0308891443c2c240b02c004090a400f440303180d2001a060511300120b034003500025208880c010070702c0b02045005a00b0080da1351180700004085c4d08061b1038080003d0302c40745850303000e80c001c44465803800d5150000242c0c0140d01c00c0d580d0380507006c446401c1c45054928004503296808003240d4640640c00380003140007110300303114050040500c508020798aa1030410060b1003051422102 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 442334937 1250 442333687 442333709
    0x24e1306050703020601030602031801060602061005180103260f09040c0c0f12120504140c15070303050c0403021206010810022a030c0703050a02090a09120818030f030a06 75
    0x85001130780004000781034039440507001d600c076921003144049c551038110a1180b250b003003d00020340309402092030350182d032088442c0d40c000707902d42c01401807110303582c480020140302860040012640751090705140b038602000c142c0d03002d429008002441e030001c4d40d80802c00c0ca0006140c0c440e41c0341030711032000340060034140090042e0f015180c0ad0181120f03d07001074440c114141640140c0b030300c100382d12102006048400c00542c1014108569030040c03000f005011881070401c1c640007454014110207480540b0941a854004195421030250001411000840a05000120040ea11440d800031200b000c1c82c010b11656141212403403500f202641e099082a10401c0741412000300f200340d43d07002e42c8200c003080765200d54082040c0d1462107020010032245c0160440071040040215007140c0300c0c0e0003103510340d450742c45244404044484164000340380710001008102000e001c0c01c0c02503403040340d09034007010b01c4450314842821a4803d00301460000c80000c100700691429104a00103013400c2406 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 442336187 1250 442334937 442334947
    0xf09011d15010c140c060406050c0105010b0301081902150a0819020309070b090f0607050a1505070f2d0201060f1212180803040e010303020c01024e130605 68
    0x181103058034581c0905020b200085900644c98100405107050700301901c503035511760307613808003c206410095007084994244070000502c51011410b4030f0507262024081c24100800340c114031054001244120707001070b107043ca48000742e00050050f0944075011f44912004d0314114510701a9202000d24100c0b082d031060060101d41d8200044550a8034a07100030140d490940400084c800000c1010050384944002940010000c001c03401013041c81c03003850103246a22642c3c0c9801c4c16940304881840028040c0c408040c8032a00c58021001c0300c2c045000c0d401f0408c07400200440400c104811036001507911076004011001d146040f80005140b072a100003100c1030355941d00310602c07107408111810070442203551449040c000010000409000b400c41c3e82c1c072940e0310707903414400e0402d00c01903001d0b010307601c000c103010350002c24121009403444c100d412444c03441401488840069050040c1d00c0414500e01e900804081013180403880182c00d89251a0710302a110004102ca5a8018508000003808 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 442337437 1250 442336187 442336189
    0xa090302070b18120f06070e01050d02030c070f031e090b030106180902040602100f020306090f07030902030316110a0f0b030406180b060405060307120605060f09011d15 74
    0x1e10602607038010080b030340d43c41e520304010a00c000d2801e030b0b60030340c0040c0c1c950034428000d2000400ca421485054180d8109035285402036070714001111100d400715804200200b038904a5a004690090850200034104181a1200d40c29414218001c4011504010031421110508400d51490016928001e5159410325103200c45c54081849a8028020200102ca00f01091300e815480030f402c025204540310fa45c0c6138002507403940446001c48025242002d004d145413640c3c000c8901c2220003614940c9591280c0300b840008581c0200040d080540d116040c4005950030300c02002460000840084400301505000c400950181501c0d4031840f8640e804101c510000f0381c2d40310845010b808019240e42c0c5505041c0050030f1448a010241d44000300503100b084210980540141010750301001107a076504103042c3d40d034000d4000e0b040b00325044016400090740c03580110340d0120001d840d0704803007454400401c0c40341e0350130b8010041e416003c4900c030084000c00705c14143d003e090094140b80d1140140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 442338687 1250 442337437 442337443
    0x140f06040c051c1e02040e01050a0501020d08060301020904090c030b0a1407030e070306110c0c060f0405150d06030f0b0a0902010c030c1b090209031b03070b2b0902090a090302 77
    0x101c0112450074a20f086000450303103038080c4031210610000003080f40640e05201c8000c1d485800b5802180841200108041c28100d011100f680c6040e0003e000e00c1004c1036080e500110020f103ca903243d1340030402c80302c07561114000c030342c202440384000300340c0e0609610b002a14014000c0c103c0d00450b150212788010340c0029110340d0340000c2c81d401c3c001680250114194108000c0c1d400c0503114500b407405000252a0710001080b4041d80c56081e560581901001c204292140c0758141c0c039610307020b010a012928096811846108032141f190380b41105c420314070720a4505a51095a680c500e980d1500c091040100c003540d40b0222108003086210105d50000e05444086d490141c10415185846030400c00b100c00c044407059040003082c90300c9030f600c40030b507c081d5000504880c0a8042d158041c100074001d001d5520310000c5c01030142007214101048034125400018514070b0080c84801482c09100d8001c825400130050700001080e030b10040d0052010900e0007030254504107252031245c0300820343c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 442339937 1250 442338687 442338697
    0x90908070f030c0b0f040b060901050127030204181502071505150d0b07020c0102060903030105150412050102090a080d0c03050c0c09160314090c04090303020d140f06040c05 76
    0x4210140100c10900b400c80380e5074030350100140201380710018080c5101c2e400040038071071407045281c03003210380c0e4030000d01620950a10500f0b012486ea07550036641c1d0349820a40308204103490100100642d80d1f0340016041e00c42a150501d000b10100c2140000c1c05105a00008802c4c25400107620b04611541d0300501010700b1340c83c2030740d515650004202286081e9802c01c01c5100003d00d46d280798406403c107091200401c0c0d800b41d0151140309031214040d4004101248500d580340c0217036041d68071f001c0034440d4100385071040124151041102103180d580710482c80700b5260091000680b1241c2010520440c04c2240c0c000c500c1aa10035a4405411a80f01c84c00c41c0c03219505150a0752210408440315140444a1300d501d54030104480c200310151a070982c443c4034088240e5010301480e01296001501d061061303d50703e00c3d039044515030942d64200741d00700075034107882031038010303d0b1134541084a0b044074140002e074526800c0200c1403050704d4828180850f0020f01c00c8404104503514a14064514890 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 442341187 1250 442339937 442339943
    0x312021c0e010807120f150617060904020f0604080304050f0402180411190e1504080a0b040302120c0d020705041503150902091617070509041a121609090807 69
    0x7242000850135440307404080c4500c02c05401c00d02054074900750b150b000e0b160070080704404229840c00003c04034450801c0c2c03020f03000c4003c162140c5450341d00501c00c00c448018030503600315010703800d049100e8075004020401848088003940c1c9488c145800c201c1c0c40b81094a1482c400d60040c04001c40f00088640c0481c000c45089400268048003800200346034000e1078191401300111403050003000b0b0b004440041821001c507210b128451003442e00c0c0d4000e0107140039560710b030b900000d402d10010344c0440380d40d83c1050083c0102d4111000c0c02c411944544d104140145903600000205a8002d4040181501a000460741800f04c01c07800c05d4080900001444050714500f03400c144842e103040c060380064600c5402a03e450030f43d145c80003140d10b41041d4462200001503004558107040841411494051110f65031240d2070400f440c800c01000c1c1050b4000000c40c01c20503200300003070b03990b000d1004030340c000510f014000c10064040d0420307101d4110f5019407411820514603800207003000044500d403540c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 442342437 1250 442341187 442341197
    0x3030f01141f03060501080609090a080307050d0606030605010219110d020f040906020310090b06160213060f06090602011512030207030c030602040317120c031f0312021c0e01 77
    0x480c0c20008503000082d1002c8036803200c2003032481003100e91640010050310310a80b96040c0944401c41171141c0f074a811200700c18a5000320f030401d0005000d440040d50000141d244c031509190100710490708490080d407048010947e500001c0045507010f00401207120100250540000d960f03488100c042010309100604c030f0114003008804642e180c4040040410000d03104111007441450400025401614400209131440000194503108c5008004a103030014042600b800266245400e070300300c0c07116040ba4031014100e206a42e5441c5442060f00500c080005119030754500440505110342c550402421a4100340c600c2001d084e1181c1050100c0f05003144010f1241c40a00b8200d083c08069003005101c403001c01000418400c1a801920560780a0013091088598210103175945200304040c2c4802e480401c000102c00252070790103154070500050105030090401051702c8141010f80c1c00481e1804104100001425030400c04120804600240d40c8071554800c100500911000d03468075040203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 442343687 1250 442342437 442342469
    0x6061008090304030602070c06110a051f0b0405040b040611041410050408030a121401060c060e120f030901060e040c0905070519020c09060913061d16150203030f01 72
    0xc0c404000700e0f001580c0140d811911507a00789000c0c402c80301d540c82a10300250025030b039111900c0004c250744032255480002400c83c1c00008000c2d0f9091021400310b0700c6103ea540d5910032068440d4090a44600d02c504070001003403405150160844114058048440b02d061000b44a00c2c540ca541c01c070202d102c110390410a40c0004601142c96120340e4002902a010100b4042600e582200302c1c3c03260b2501104d000e01c6580101c2207180c0c02c1c0300f024860714002400c001c00c803d0214009a02c40c02c032a00003d0f050f18a004485c101d00504c0740d22400d4625081100081040b812680078491040179110042c1d05400310704054890f61804070007409480d0034581c1d41d001103101603008000b1500c1301811001168146558081d01a444604040045004809590002d020f40c034104889c544100710504903c528a1229250a0001d00240300c80c041401032520051641f1407003004a500c0a0003200e440c1c2d0030850400c80d980d0584034414030400207540c008c1c020b1140e483d5070a42c0403415075985ca20018055 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 442344937 1250 442343687 442343701
    0x10b040b1806070c080c03010219031d060c040509010509040809011b0203060c030402040510050a12030c0206040b09030f010605010c030c030c0b01150212031e07050f030906060a0806061008 83
    0x407030001007200e548040300268150810003c8400e40c402c4407001c81c140da645203202c40c2494240c4c40340c1d0305a501984100c041c0c0c0c860b00c03400b2394000c111001144118451103185011480e180090507030301c2e152a02c0000ca402c10403440c0c0220082d014080c15242c0c4884c5041c00e603903001a0f40110303581a810700c5a00b0141d0742003008201400030456070000c0499200707040024151001354010b58040e4022418400050141d80903012104201d8402030100030901c1c0c5407025960074488012070480401510a45010242e582e45014102620200d60450343c0d911140b001c041c0f0380300710f12644c4030703c59060803810000c0d86e80201c141d8000c0d6400d4180054101c03083e140440d060000a100100900001c1002040030380d0b80319108000d0300030755002c07580c0307921041003030070800d0004480e4258844140c0c001047c480c02c00c0d007659a000080c5050440c00c20001307892043c0c8941040781c3e0114903600410400104d480c007104010010b21315140580207509084000c1040781407440407034414070148401107102 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 442346187 1250 442344937 442344967
    0x112503030507020d050304060309061a01080601180b220509040807080d0f2c0a020f130216080703121e09050f0a0602030406060b13091107020d0809010215010b040b 72
    0xc21617000081c0c80d60386480f10340190040036040c00640f0b81a2900ca201c0c107500c01014004010550f050712030341600e60702c2100440380d501c402800c0242882000a00055102c099400781402d20841d44195030204045009400c460543d07602080c80f4204070014000458445400c07143d41c180c200e124190344401004d000c20180c040d851400e6182c43c0351021015001800c5440d800e070201a0010b4101500c04008429542c0c101d081c2002e5404054a104180e05140200303501040c03131200396000d4101000e50505007a0260301d0b280c2a40c4200000038800d08050f407240c1e200c0000c9540520401c03019000002245030321042446416100b641c0304980400c3c01020445e540c2d207120100d04503079004e0700625009019410545044400a040020110302410004195040c515a004112001500d0200e90f000604900310100000a01c20840500542c8404d446941c1060056041d19620700f40d1000091400080350b40da02c0d0003103001801801080c0c4c01604031001c03144a201d41c103032141462000111 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 442347437 1250 442346187 442346209
    0x1b120c1b03120d051005180406060b0a020c0108040606034b20040216150203040302030a0f0c0b0c04060807030501050a090c1b0b1e06030706110307020306010611250303050702 77
    0x150010707142240000d048890f456039403240344100c07422b000c501d07940d2a50900c24000c11880e40090382040c500242d0f41d52207198540e038020701540b03000c03031010341d00e450f0000040c10340038a191900b0004040605400e180700150200303008031406010320008840f0f64040928084c4c98001c00c03000d44403800a1204c0c0000f401c004110200801c00c5554a60b482000380e40a445403000312210011124101c3d4461014030a50744500d4264000d1403a000c0c0c1c1001c01c4440459581d404020701401c0c1000c0804036410703040c134034410700c1802c9002c1d81c0c032403e20700041c19002004100c40c04150615005000d952510f012040840e20b2003200031440e000c1d200020b4880502d00c0242000c0005158180420301079106841400b580050b4085400d0b205001403144002c0402c03202c25415610500d420015a0b1181410700c070310180100079682440140d0b400a820500286d010b04c0025002d42c0035045150410f002d240c040c00082000244000346242c1c000c000f5000c18070010341030003070105003a0150348135842d02c90 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 442348687 1250 442347437 442347439
    0x3120809160806010512061306090c0f030501090c120512030705040e090309011e0804080d091b03060b1002120c01110a1806030905031b120c1b03120d051005 69
    0x100e00c841d2503403441981e807002403051500c6070404131b81041c464840460710f28020550900884034140f469150000908030501046881e410303090030000d4403c0380e11862070040d512a5001140508140c1411904988903030802c8507013151000c90b030b030001400081c41e440803038042100142c40f0781d87d074a8142c07160300441d404800c010100c0002c01c0040c01c0c011004180d1041c090704c0354107045820380035646001c80c80440d00400319013214041030101d5200c9004e8074154400020110360312070305542c0c07020300c1400e200a20208049407542030003003102d1806408030802096944840302a84100b0080d52449440042c851000d000036148141240a4004403412004103a40c1c650f10b5050100050007888171460781d1611450000e0007203042e034868000c644078290440015820040c080850401200d0314400d0301805102e4440400c40190030714020740002200703c00035000d0000995558140d00390300e4040c003031007a000302c040c03030724201c010109584200246c1500040e00d41d84800f40414502c06640100d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 442349937 1250 442348687 442348723
    0x3070305070302030f1903050d0912030e010c0503090d03180206030c0403140307021003020c010f05090a0209160f0f020f1501051e01050307030b040209120f06090703120809 76
    0x20051010004001048a00c20380484042e80303e00c554641d115078907030842014901e491011540030038465000f07803905440301000000da180312581d401080d042503c3d22080403135124032030205008000e2250000091490820500c3c42c500b50034115110300003902590245990f5072288100c503c910a100700c00d503a03002d843c09540341050305081d001a0090710088400c000014940c442040020042e86c02e1990301a1401415503044c1c9010f40c06504518124002590303030b080c0f800044501c50103090300a078045070240071401c03194010700100d0a001854448425213503052802c4040e0301402d40001000203240403d000200c40300100d00b4405400441d900074814400c1014010000300401c60413980b08070703040211400e040b031003030720507030800840303180810402e00000c5c0101c1d010380c108060825004000600c0c20ba580c1d000520000750182c0c0f5140c7e180d20142e20703050000800c00c5516001820400200b030385900e1070f1f8a40e00010740004801d030804c0007120204001810030000c110050442d00d103030f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 442351187 1250 442349937 442349939
    0xc1223060d0f05010c0804121d04021b0105070302180108040b0a05101d15100c0602090102030c07090b0a060504030f030c0f06020a030e1c0801090c0207081b180606090f0a050307 78
    0x1032050401387d0341550452400211003500d14011081004101c21403001c0c80c440712040e004010007500700c00700d5403118008403540480c0e01802886031314842d14650303e006031200c1078256038104000007081003605008109082c030011903001c4101581c001c2031300d400410700381d4421980d50034000641e4015806280000343c1e0f00e10840748140024490083c85200c0010310041c42c0420070b14421030110080440e4000056202042140e001441500010300489103000c20241040c1d1070200302741d000450082e9180b0008101e4a050710303881d001002246842d0381494150340b140c29001542030030080520800c82c44c46010414252804500036405c60411501ca500c11781c40a4040c0210031b42d9052140103040c00340c0801220440040c8024034140d5961540b170f801c004080d4000c03c11094480c4c1948610200080c07001001c1200454030301500c5602c50341c0010800601001c1905401203080201c00700080181c0340e11118155034140c00c0c00c68100841150480220f012240d10f500000c0c0c03d0b00030303910 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 442352437 1250 442351187 442351211
    0x50304030b01150311270a080a110d1509050c0d0605040209010603021306180306020c0304140312090108070903051b2d0d050304090c1223060d0f0501 66
    0x500c1c14102c8000300207902100301a980110100e078450800e40b039201c90140941c46810380341c00f01100542c0c4d00d00104144e51460100052034411190388110302651000d0291800c008a80c07504100c01002030341c2803507012250355603414142c403041c07c1208c0440d81d0ba84401041c407104000d03000b0043d801a051500001f400d08150014160480381a80118050400050070034401e200312032652a60700000c1d2117241c00c101003110b00040c090340d0032031008028000440030501b948000c00c2c0040b211001140d4451600c05140200301400207a01e00c84d0b0000c400700750078000181e0450310b03600003d10384581d003507540700340c155040c00d01c075040a4400d1140320b0b4003802e140d1564800420441c401c403402d040c0080d40c0c5251094070880c01100da03c2c00c1484240b0407115085c00a141994688964281c904043e01c59642d0781c02c076a0b021100d5000940d02c00030014147d03200b8810b490201c070b401d1405440c403001c480082900c91001928840c040c01003c5c04450034403500d44a01c0f001241c1c004024040e90102078 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 442353687 1250 442352437 442352453
    0x12102306091e1915300b0907060809070e07030c020f0703110103061a0d020c0f010212071407030906051c0203011e0807030c1503020c150a0e011404061805030403 71
    0x9000c43d007003070316011080c0e154a030664100b0040f1031000800050313202104200c2e80c0300c9015440c1d00b0794400403c08002002030134044040c0c0c450b405120043c84450b00d070034002060041c01070301e07405043d00203c1e021b1100c2480308c1c40055011000b8140410049502c4100324600702d01c2e12555407645c040c00310040f0403ca010a120050000c0c241da05000b4942c0303030703031500310b011203018081710012904014410f40720f40f4580117050050704202c295018009069043c0c0d017a60700c20040f01c12100c11fa101000000c58225154035052000c44102c1030510f886582e014180e6a6617000300000c1c4078011802c0b8550101c0203009c00300f004601c0030b00f5500ea580d6401c0e40c0201e0b00300304000104841000b08003140d01a03000602d081101e4100001c42e03111441c011006241080032803581042540030403405054400411050041d8900106240719500d0400001c1044901e80c0c01c0c0e911190341000341a04844c00d484082e66009a0400c1000039018008004048107440300e28005165004c003040000600c0120 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 442354937 1250 442353687 442353721
    0x60315030307150f020f07020f010201200a020d0f0e0d02060d020d0b040b0409030906080403030204050d030e01200a110307081504140601061209060b12102306091e 72
    0x104084c0b01500b803000c440030030780c0a0341041a80e103850070702c000f0015241181401403240e07410b0000244030030b1343d1171304000c0030310329642055a8500005860115130342d04100721081d81d0418900070a02034201c00005241030b0f124002144560340d0304400c4801e5680b441d0403030b08000e4500504654030707034125180c04040d1000780d040c50b00c100d180018154690416004111950340e15075503c20501c1d0a000e0227880d9900064400e0302010360a100200d510f8440309569801c1c0c9010392107001d403031000c2000040111107808059107800e1440032125103003580004003800c505034012441d81c05c1130100f40210f45000d21a50100c21644610f180106055048018250140d40103030444183c00d4400403001380c3e649000c1c881d4400081c4991070002103004694032050055101d9180404c0c28101b00c0300041944040c1ca1070552a5003181c400002004598806c050243c0e02d034900700d584140141c1c4a0b0b0b0420b8000809480c0038010040001e000070011020240e00c5e44504828043d00381020070030207000482c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 442356187 1250 442354937 442354973
    0x1020c03010f0606111c05031902040f05132708161a070c03090e0a090b0403021e0a120e18090601030b09061006050d06050406090e1515060315030307 66
    0x201780d40c3c030904200801c1d40302c01c0300500210801061800305003228203910013421250703001c210503044188000303540010002003d0326292681c0082c03c020400c038409240e400c4a4403a42c0c5011010380e050340080801c038211000400e000d40740075160b03040c0384c007141c03040603c0c2d01a120301d92450542040b00d0405540700b20418440c03890b1140d5100e0382d0a031092a1050405404619556410040326141c5480ca0f54400e03800100420007014541e03032180131140a490407800b603040040405d81012100c40c504288000074801000d5240090304e440600c983e440398540d00300090390b800c0311501d845613210406168170004001010b450512185a00c40f802030108480c855000e45c0814040700c40000c881307009207885440c103c0c40f02d15100043c0e13809d5000d01c14410600f9120080000d05680d68480e410007080c1c1248046100010541110300305002c7c600f00e00c00c07842105080c00610f0201c00600414064103440940e5a900c4400024811505140c0da1a905100000340034003000184600d031217410300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 442357437 1250 442356187 442356197
    0x90e01050405251208070605090d0f0e0a0b0a1808030a0e010f020607080a1b09090b151b0a020a14010815010e15041208070c050306010317030601020c03010f0606 71
    0x1480d815a5102d00340b00c0c03072443d010040d40724051081d15030003150450050710624585244c403001e40e403140d007901c4048610680d2500442d42801011b0b4228100a00c42034861500510307004403c0009860f03c031650041520003407010880001d00d82c020450255260104a4004040c6a030b600040365030354050f040700400281076810003030f404c2d405054458000100da030068190b940e40e1800c1110815002001d1002d56a108e516840040c05400c07404035800d06c0964404072442e09004a600039107020b0025a805215030702c41003200030191a05640d08092529200c80240c0c001071368661900c02c008101a51181000074000b840054400c0340031a401c8080c5c0b1f4104055480400c003010a00050015a01003004034480e002c940c50840004500c1320811101c1c2401c060301c0d040d103203080959599003250002c40025070302051050491100c002000b0480060000390705655410000e2a41c24040656805011010841a81c001e02204940309000b8000704844c4c0040c0c901940034107007d00c41c0c200422 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 442358687 1250 442357437 442357453
    0x20a0b0c1e1e13050d02041d0d17250306050411070b0901270206040f0f0f0b1c0f0212100906090203060609090601170c070303180512090a090e01050405 67
    0x146250003a503c03c81d2480000c444114904014401c05e00440340b41282c2c001e50f1841302c119521680703040d07604802c01c810024410900c030814060541d091801900307540d03072404010804007103980c411807a449400c1c1e030b80d0360f8281036445030258050800c64121640c01400c00b440134610003070147c003600b60f007805080d400b20a0f481c0c1c0741c00c207800c03141010803d0404640401d09c101c4010520407001841a00c0607240a240540e60420750702c1d810340c680c0092240585d080010402207907101c0c1400040c01c4910b402c1d606e0400d100110030b0340080c009440e0310901f07440c2d0140c0c0d020f0700520350548a1608148900c0c1045141c01424142c02c91307541c1c011003a800345054000f1403498650300c00e49100c0e02c00502800d2420008204005101600404060410004038061080e5042d24100305005000f80503c40351194001d180150a0b00c260f00c00e18641c080b00815a10040b0b4400190603944400e140c0380d00e99520f02000c045140d5111540200d8400741c140f103000d01114005621082c400ca001e0b0040e41e02c84 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 442359937 1250 442358687 442358737
    0x50c0108010b0a020703032708060609100f1503090510060303030e0703050c0411040f0914070f020604030804050c0d0c1503060b0301030b1321091401020a0b0c1e 71
    0x5003d0040d042005070b0002ca418000a401544255010030103500007554136860318003000c1d80e0310b08640040c5e0b03840d04113800344400317410701044142d0826601d403548601c0d00d0404100c44040401c910401c0183c403440790070300600c14000e620a2101d16082070654010300403a6030404043e212030300c021400a40350031402070404001180b0031094950120150175010241020000602950511468250000c0000281d00200c0740d060100610030040041101041c0004041801a0040100c030520226042d220281540800d00c41e1340a0b0341801c042419854509100b031902e000403602c2030304441f248002e41c06004c4225035600071070329a0f11101c02071f043c42d004200c0560760a0711030825264414001800050401040c00b41d03c46601071000c906400d0540b902103921325020b0010040d8141c103480c1c5542603620401503009850310280025181c425000000e50320025084090522240d0394081441440001c088030310011000d014680c0340d28448118840542c80902050130200500a40d8800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 442361187 1250 442359937 442359959
    0x806040203190f110307181a030f1005030607091707050303041203050706060b1b010b0303190c0803070906120b03031803030702040f0506030724030902060f07050c010801 75
    0x414089007036400c0040c0400c015010140405807070f018001d03600c5000c003c50b076a01100155210f0b92082d81e40500c03101040c0c1d2610070030f18680c0c210900003aa4903220040b281901001c40b900029203000694195407408010942440c03c1d800c425810300410341400901d40d4441400400d4828015011100e10501140c00360384011911449406400900c800c101140c0c1c003070351a28000d4002d007001ca00d081000d0b540d0900b2a00c1c0382e000003001410100d130340500803464030860a081e103400303002004020098000a0f41e40d02038024a44410300003101d8221040c3c2c13094884450305640309030301c581c07281405000038080c9c079214029807001460182c0000f0180810f401a420005e0300600030b0340c5408000c081d0301a1008010b24000e030180702c1000182d0040c0c880d417041b9918000c0b084800540f50a00c10b0800d81006c000b07a20031620a20980222001ca420140c4c1d10303401860942800240c120603480401d40602070038a40b110100c5000c0f559006020300030601083d880c0003680c41942c160303203c00d42d8041d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 442362437 1250 442361187 442361191
    0x4050102101503020609031203010f0312050705121c02040803030a0513210e100c020a060302130e0402040e0d0c0210112d011a041523010512090a030806040203 70
    0xb00402c100b5410070260078241c00a20003903030080d00b92080c040e401c144040c460f0740f0a900c9042030742d420207400c1044c80907004040000c1c4200e880c0c03d0b0f00d81180303030705c1d01580c071046880b1017030700301400040b10f031412406400c003c01c17031020034a002c1d5203070341c0d40324641c3d61260402c49691a000d424540081c4a251400d080c0b400b0701c0394450a800707004240309003060b0541c014001c103182800900342402040355100040c0d0014500d059980c0b22144103180f0602a507941541c4c000d0051500510225440d03415040c07450003a82d10589182440d5620b50000502900c0d41000300c04003801044000700095600445080009000b52400c200c903419040c4110350400d00e07218a0002a00710137200307000402c51001c115089010000940d040c240c00034001400c4542200400013504250124807903141803900903040000320104d900d45804d0324258082004070210908541040300c0e0104c014002d0307000764184c801900002c04a6002490b00c0f4040039a41c00b2a0030301034001c81d584500003004c525090084034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 442363687 1250 442362437 442362461
    0xa060f0e04020f12030f0904060e0f06040c02031c020f190801030506010e0f040f02010e061308010b0406260a0b04081c0911011b06020a0801050a090e0c22110405010210 74
    0x262071b0100e401c0c1c2441c080d8101d0384005510640342c3c0e40000c1d0400840c02d40600420b1068544109401d0030002c0004440542900c102076400c113103c00181388045c090b009401d581c00c4000985c0d81ca0b8903020460441c03003220b050501c400c1080c40761554259000c42540d05a82c40345048074423598845459002020080f514a801139000c58009400070f40800090409280306040110107a8680e0380081c0458220b880311114a02c0c2d8241c0801aa403001d00030700504503415102000f6003030800d8680503403840d0110000d95000440c110700454039400b0015502c803130780c1201090200c0d0410345000261a4031806a401171844005a409a10f441a100e5480d040340c0c407000074101e0016000066a50581c0c4a40c9500104e84896010010038103d000a01c00c100c01581c4403c120340c1024104800710000340c121607401441c1103d800018031001900d9090749900311503010285c14170094280c0c848182600c0030810f541400080356814072910301410648030f00340c00b0f41d0200c0180d09081d0b070450310310410403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 442364937 1250 442363687 442363693
    0x3040806070e0a0806150409061808090406061803140f0303012304020a120e01090206130920120c041806050405060111060406050604180b0708060619080a060f0e04020f12 75
    0x403440030b14042c7e02023020b41c1d201b44000720b0308000c0f002950040e400a035009a0700e00b040002c009655190a02c10b0502034840c40c100400c0400141004806540c02400001c121a41c190700454461400304010b405113031090041709c1d929a1920201c140c0e859580c030440800a440c0d0200c0310003031801d0700948199061903500c140c50045a11071100c0038140030301d00c83c032a6540e41c114110258640d04001c103402d0744d1182c4507030b291515003280107085400d0312140290000d0451405110883d0202c202d034002143d402d10079078141c5640650349040e2040d6400036904880e401003400c85892185c001c1c2040300e20444003000169942c000650b4040d5006400d8403203030b0401c0002034001070181d0701c82038010342d003d04002840f1200010070100304900d1807080d00d09120602c02c001d1455030042c6141e03442a8180c4000c0d040072a01110003401c8840440f080d41030000310000604850801d9115500130300e1415403e18080b80e03075070140075100005680aa004a881da042c01c0701034100140b20b000f10752821402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 442366187 1250 442364937 442364971
    0x930030c0c1a030a0c211401050f030d230406020f06071404060302030a020d1508100b0d0209060d150b0103061403120a0302070b04061b020a0201081803040806070e0a0806 75
    0x4040b004052642d24101480540000f00fa88545040d11444200a4601000071004200e462108500005a09c214840c1c680440418041c0d01e000c114031104103218288040806201681c180c4111038502d00c50303e02c900302003000950300d503000540291000000c41a10f240d61035844080321030911600b80c2e9254100200005c005191280e4011503204040090040c102993302d4020320551b90800800d404061b225401403042030403d00c84141603841c101010400c00f044500860180208001e010f4400c0000000240341619030080c2c0c441c400303500945010b60314100c04074080040460103070050010b8604000031660869180114000841c018010f1031001108803080c1226800f605004040507020300143c0001080d90302c46e94012481460003007000e0380c0c1014290140c010030b80041c411580004000c00141c1d80203920190005c1e080c2160101c6c05401c511801c0c40c5202ea40e01c042d178039204000421589550250ba2201c8442d0200d5001c2c541641d10009290b841006990f40e520318000f84103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 442367437 1250 442366187 442366201
    0x9050303010b070501020d0204091b020304180507031b050d060e010e0121050a08040302042702150f041409060307030c23030a03080f10060930030c0c1a03 68
    0x1010389911413007400054903180f114800383c016600b160380440800b54462040c01005040191610800c2045100950415280a0701c418000011082c0d0406c1c583e030703c4001c25146480382c1c102030b400c078202580d00201c00b2540c51000f41958131601b10000154944200030420b40c143c41c110034120f0b511500c0288040c4d0078110b210750520403040080c00301b60312450240c80055000d20803114118003916889440d2440c5006220a031480010b180c9400b850140203085078601e600c45149070b154041d181d60840700908058035070684500e080628004402060014400710480303400d0301048010b90700008251162010b25549500d00d000c01485e80c600b640007484000445048104214000b041804034011203401113400c04030305007025000919610308010312021403032042900454444080e60405180c014001c00647c42030007200e000c80110341d0f201c0250000300700f007907207040c1802c1d2042e180194545000742803030002d41011200ea41180710b0020b0450b203950500d541c052000c4403281e14540c0c1d260 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 442368687 1250 442367437 442367459
    0x102030d051e0108070e0a111c020423120105040507290c030d05010f1d10150c0506070314040803070309120e0f060c1509070e27010905030301 63
    0xb80a48454200d10001e0100401c108282d1402058588064188981072002d04011a05c0082021ba440743c20107564079039413000c100c102d030310040c90f0f83ca005004100d00c180f090f0213803040ba8402070074030800252482c8503540300803644040f07113000c9405030590000c1014203400d8031021078001d840d64100710400c00400324041c00400c00c500034800b261041d2005010034400541144690060680c0046010841e0440d00d04c80c041c050924600d0b02c25855107070001219030030700b80300c90120305502d040c0301250003001a4038170328000d4030306c18080308052014400018000c01c0d4620341900d40303100c2c190100d498640240f103030009162103d0b5003010b1640e116181e42500f85d1003e050f9404042d540e80e90000802c08525020810046a075289110f50743d1210801102206000303a441c420390003080f8403200403400040c495000c0040703d14082e41d03a9528498a0f040a10726444528440c0c0300c1000c0107000701c0c4600004207e03a40280510130111010110107088400502006045500410042c400d4507010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 442369937 1250 442368687 442368691
    0x90b180304050d03050c0f0a02061e04120308061c050c060306030c04150f050103020f09041107050601060206190506010f0e03010902030109050604031e02030d0f02070204090309140d020102030d05 86
    0x601101e2605950380045840b0810419080e4006640880c481c08040c0040c420300608418500013000e2002150b0009009446090b400720304580889049442e45401c072801d4400800794043e00c822080d0180c1000f41200000300c51152180c440341e030740f003540070b1282d02c1400c445c5034001c0700504004181e00280285540040d107010350511404804141d655160300840c080d04095040c81c2800d54500300008042502e00d400680c10b060040c801455610b03c000c050701c2c0284c0c17003203038046500d0705000080c50741489060f2018125004800010420b40c0c3c00040710350091890b982c19036400c1072110710705011a6000c2c0c80ea81d00040f01e01103241ca034144903030b9200089410040000400d070381658000f9007122800754044445411000030842410b810a9000d080e2480a040001c1010f6903200000d407281704100c0011010b42e51038a02c042200703880d5055800d1180c2c0034008001580c058100946501860305c07a18509100c60300110010f8206801c00340710843d410b030001e50900300c1849141c0060240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 442371187 1250 442369937 442369981
    0x3050f040302130e0d05280918050708010605090d12050c0d09170604020307030b0a09060606020105090705040c0c0221070e0403090503070e0f04051c03020a030b04090b 74
    0x521021002d81d88120b200300e03109a034544006444440d2052107810000204208010310500b44126a1292450f420880545458191880301d54600f95025110240e6603000340190450300c1c0300c030105071025580800e016002a0b02d45a03540ea84e140000c8030288030b150700054200103c61340020000700c440000034007484613410302c142096144e000803450300c44882108000500d0904c805c10078400ba40700d0280b03001010704044c1082d440c00c0e40200742da40d4501e101c010086240b400000310307403016940c402d2060540c0034000b800110713640c0c10020302818040d184880b0b14064190001110704d0b1620400412900c1621a408194265000c0103030401044a5020750016111105c20400780184000384c0503000010800c40181802d04009112038076640156010b5030100c4004e00c8500c9510503216840a810418212165074502e0201d0a142481c44a8000303507016014005030700d40c042e00074140c0701d10a0341e004c00c0402038000030001614002c010181140081d00c1c04243c3e0b030b4810080d09501520 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 442372437 1250 442371187 442371217
    0x906121e04030f500c0d140708041208090303040e040302060a14070e03030f031e13050303061e04050108031909230a1d0402102c120303160e0109060c0305 68
    0x81c58803a900313525881010050082e4001045050a40d908060f402011480e00d24600c1d0404004c1d81d01e03c0b58038880c03401507500300540d650001e41003051080c00c035040b529000d000c0d241c840360b84001c083d20030001a03800301c0150182070001076074081c2d03501c50728200d10b800040700c013156115042d05841e40e07407521220301d4142c00208480002c07690b040b4015400382044504040b5080a001da4090300e07414094155808500f55120001c04110004242d0340c00110440d03c0d40c80c8820008001068021a401d40030703000b44c1480000107400c400030026108071203d0045d00000c02540c48004c90320300701c0390302a003460350b07040c8035030310411141c140424850050003508254026403103206a8514411885074200007000c04001c2008504054144640006241c245113010148080c10320b98003401d03e41411109680040740440c80d0740d02c0d0302e44000c0141d0b4030f409a0380d0f24185414141d50200c41d492000001c1451850b500d0307040e510564100007281e01c19030301e48180c21080d0303408940a502c03182d4000c02d004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 442373687 1250 442372437 442372577
    0x115091a1204050f01050c070c03030315051903050d17272e051501030b0415090203040c12020310020d06090507110f030906121e04030f 60
    0x12407a5040381c000c6004100074070300c8107005002e290a540009040905045007480404001411800c041e000e40358141800302e42550300050101c0b00401540c40140d1256940b034406030491440b8a0510a072405a004d440341648900010f5807065035040c030010690707040300001480440007002c1c001844c0c40c3e00e50040202c2250380e510034540864130002400d0080589000b04a00840c450400c0340000c07400710600051400a21880c2d0301c4000e450300a041c59220320900408d652554850000000040c41708001c068603282820001c0d0400c9804032003107214400081003104441201008840d4010000c02e91403420343d282c50b02030b4118446600c0d00076240c40c00401c502d1414050f65203d022143e6400800081c051207451500e07610b007215038125041002054603686422007200c1d03150502406107940340d00c035107801d800c1c82c800c0c614100200100d42400e100c101507012091314400115551459206c9600f15445103011a48081c100010101246d99510022624086c41c00401120007030319618 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 442374937 1250 442373687 442373707
    0x42105010b09070216091e0b04060803160323040b180d24061a0c03041a04050316080a060504020d050708010c17060d060207020a1206140115091a 64
    0x2c08050f60244050b820a10301c0c440b03a03030880e42c07041000708600142405010512032030701440300b0031000301001d019180c403407400305501c3c0c2c1d410003001486404201c0c4d41d900c41c1d060000300a4446c11004900040e0556a0f10606807151040c21184080c1d14240b0351030a4507001c100d51581c1e004070581d401c01700c03290800f00001d956006140315540c2c082c1076221000c1151507544082c5140c0c084060001c00d2420f801072028840c041c0c036801d9250a8518042d6580c0b006507261851401694400190f51721440d5882140900c202c000e041100c4040d000c460740e40180100901d01540f00e400342d920140d001c4c00098011441a4100f190058000b42040f00c03840901c0e01c507181440301030f40201850f81c0d181c03610700000d00e60151020140c017180f13100001040c100f0034002424008885405406c1e2a0081080c40075591180c51080c018200b10b0030710820384203030745030810203000303088418003078404420000181c2a00c0072003182c00302400d81d6948514642412406404018401981440c2441c140590380360 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 442376187 1250 442374937 442374949
    0x20a080102040e07030b0102211c0203090304030507060c080313150c0215070905010e04050a270b0a0b0f10031b03050103170a0801062307150c05042105010b 69
    0x90620703091880341500d0000005011b07207900d40c0000d811075000d110090014025010411071004040c903403641c0e0b9400000309002000c16000074600d070b1a100105000c0c0703401002004000300c920403c140e0311856900e280c103543c082d40c2400054110b040c2040041e02e0a40401c0c0049603051242c000c000480000480c07410132140f44220b1980940e00c440b480c4001d141045015076807259440c03404022139410040020000071404800c076004613110000f0403044046030700100400310311034400c040395a0740500406007a040f400015101c1c065060040b90302e90307000340110041818050180c0d03150150314006d20414040801e040c104059940141c039012504e5500c031014800102d0b500801d255040d41890b40520100c031943c1d0202071070412847c965190042041c50440e405820080030f800c0e80c0c041c044802600c1495074000c014030015080b001c00580198805021b128101c0400c0790241c43d00d03068071a4030445c010140a411000505140304940421722004148540000b05100b00843d01040d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 442377437 1250 442376187 442376189
    0x170106030f082208030426011e050c090a050d0c0905270c0306071b051c0f030606020c041802060310031a06061b16030b0a0c020106050901050904020a08010204 70
    0x100100700145003d42e04a03070880091a03228442d40c81403185103415401c9070399100f1407081220b03800c0b0900d108080385201c40424030745c10246000034403016420425000740c4ca40c00c024238100e603911345004510300c8504141130754070a03d0040c180581d07043c01d10040003102d035404c5400301c524400000011072502164010680183c48485200b014503a81080e03074072101c0d4014003d102c3c5036114484080d0b071580d00083d40c2d90480c640303040480c5110180103820183c62101c6101810b980b18801c50202c0d05070540c018680e00c1303032099648090915080c60102c0640302d07284140001a8440000300849152961052005c4800303d5504038192a0aa011465640007284d800000091001007001440b00004110100d801c007810005040d12301040020028012100240d0b000e40d000516080c4141d01044482130418150325003051442c0e49262225100c2405c8500440c00c90038902d02c2c48241c0d00500441040c0c9400170900c0700944e08090500c07008880041c41070780c1c80b1908005c00951101e00f0302c0200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 442378687 1250 442377437 442377443
    0xc0609061506020c03031305210f0d26190605130c0806010807081515070605010303020f03040302030a06200c030304171c050402012604020910030c170106030f 70
    0x28000c00c2c64004060706002442d10098081e4000b0483c80c02142c034194120340644100300ca030740000061032a18105020140b10121005119103072101000450000d2002c0d4103c10580c2e404503440c40800c0e65415001e00440a030034103070003e602003600d040d840c54154101070800c1c0301c0044c40e00c1c1d4620000c0c848403010700c400c03031060b030340d5014001804c2da104002662000085c02c0150b2139003081c0f000200300b04c0005000c06900c0203e00c1030140260b540700202c00303c0b1003082c1d00c800e0b101d9207207040c0000100340a00c000c44c013622540c601a240403c1c08030a031411250000c0c0500140c0507640c80f28006440c0b20b990703a5a40c0401d0115428401a600014009010400f00156107034a403600d40881404d5903006101420882401f00e8003a100b54030100190300c40600b40e000c19103031030301d10050380c1d03071035003805240071010380e5400c2c0d115001415550030b1322807802114030305080d4807031689280480410b4080541400322840080c094488506c041e443e0100c01c0760b000041079603482c0c03210842c1c00d403492411 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 442379937 1250 442378687 442378721
    0xc1b0308030a0e340f030b15090108101a0901150e01020307170a02150c0d060b090315070c0f0b06040b0f06030601210534020d0c060906 60
    0x4049050498071410343c45030000801802c2103204045611003c0c444449440302c0a0940481841003049280400d030082020303228803500140ca13441c0c4100c3d440003c40d150245240048407030400c514149445504031048440030303162003060412910b02a10f8003010b1007165a11498450085171112000ca600030120200b0300d502c900b111280c014500611840e841e8110342c001e01030306020074100791191545003d0610b015039a12078801050782407070030700050402044ea4140c00c01c80700d005034600800b0781c0d61a4120421650341c4030b4841410a0260a40103a050b6004440e00004100ca025800e60004240d0505002007405a507138556194204031044488400103030a01110b800c0c24022507008050844800e41c40180e250040342460200401950401007041240c09180300b031203250034402482d81c1d03801c0c0400d02e00816480c43c0710303500300c05400d818040d800c00c421041d4440142d80365400e1803980070307058046042408440c01e120510040d10941c0d41d41c2c202c42c002944a100d0b5016680340c20000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 442381187 1250 442379937 442379941
    0x609031501030b090f01051504240807060212070c0e09030d0c020a14060402090f0c0f07050a0b07110c01030203071707030501051003060308030c0f0408030a0804061503080a0c1b030803 81
    0x151a040607040700b6068596070400c014840c8212910488c40080101500c001a48000c060448400c1d9560701075420b030540103d000106402c01d01180c648203440c1c00e5001c44404028600c40111103200e02c03100034101c0c50550380140003a0542031225604054420203d074181449002e29004640000b451030016900540050f0200324007104001c510072580030143c000303490150082018180000c0c00c400c0045d10500004c0d03902c030034020994070f22032242404944c69200d00c1c5003c0da0f90340c0489009840341c80d4007a000603000c0d4840e041010001b000320001c0d01500c40c6003401035000c2d41003d800603041c043c10f90300380c400c0005111419846041160750100341949480284400c00384141144010142403140c280041102d55080f00d4000d500784503899600c006409205d441e5020310b070030080060100146155260b039009803040d00560240f00d0070030180d00f03071000801500d440b46c440107041000502007004954019041c00c01d083d8094010103c121101c041070004038502c94100b02c808990200c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 442382437 1250 442381187 442381201
    0x3021008190912031d030f0c06060301290303040b18090105040b061b12040f0e0c1201050d06090c0b0a0215090a02060a03140a0e0f0c0a050609031501030b 68
    0x709129114489400801104a55894241c50409118035501c14151a6007009061445104d036603d0003008000559403034055160416009a00c286540200303441070101040d228503061150341a23106240f210a03624031081051f982d01511440311040d410300040c000011b150314840010b258032801c2510015410020348200011608180c1055000c0c900d4840344d40560344502c0e00301e80a03090391520310301400d100141c1d09450464001e594a5803050046400030720002d60303804020a071164030344450925980c01c000002d1034000c20102c540d000030883e004000c14200405604030180c0540c002241c0d24120741c60312240c603d210352080940c0c010004107031840c640d0501000441005841880031b05042c0b4661056981c1d006543c040c0c401d600004400f07103841e0180c0d004803401c0c0c260710304c111940d14122529000401403a44682601d0240324150070304180041520501c5240c02007518440034202402d00805800110400c1d41611a101600c0002240962a240218425595112240380c040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 442383687 1250 442382437 442382461
    0x60b03010c0c020a14030705130605031203060a2607030b0a0b010e06070206030c13060804020a150f0f110303040b0103020103380112140f070f1202090a03021008 71
    0x5076a04201000007204016518091a0300894000f40801242c51050100281c20108541c0c402c070f600c105452061103103c00f107500150120341d41107042c0c503031318006aa070b80c11941c8012258942c2c40098844184005002c0c00080a07444840008009038040b41c141003615000c0190419103c0c2150344041100d2440d160007000b142190038079121900ca151100859480d01500720000d11650b00400000d0030700000009480410075254000703020395541c2c080150608034161011f0b40128034849c030108801c1d94a842034001c2c01c040e075a844886c05030156003200c8807040341d441075040000620343c0b411550020001303140110b00480e0000b140e5495440023400302c92500100010540318880842d008480f4140800c3c1501c82e40d41c0002c044102c03100040304c43c0900301c4058403101d85400d0303a22070301e59100d0f0b6840d03100d20a180b0303819441e521640c0003514800070301e110683c00030701d84a8900c880c1242c9034015241e40700015181011560700e0f940001da1070010807086100159801d000c10580c3c000071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 442384937 1250 442383687 442383701
    0x80a030b0607030305090c030c150c120d02181e010e12120d1b0c30030c110313030f050709020307020a1b0e0c130b0c030c061b04030b070909020403060b0301 69
    0x1c60060019422427008540c0740c06042c036821100c4800070170101c82504050121000901c2c4808403655224032407040c0c0c00083d0846a48550903d8605001e80802c0c240f518074152800176103403641d045031820000456409600506058121507810704c820b80b52201000300c030801103442060f068031000162040c0c401c6032981061001a10281440001115080301c0065000d641281c41203560610011a90031600c44000354007c100c141002c000d1101035040d07000c840401000d5880d60b0310b0b050701c07680d03841e5a40540031800c03090150020040000503000c00034844403600ca0402d0303d50030b90781c508400701207800440707a03480985c21964030601003011200300c0552408402072000341d4603003801c010702e0b207940c00282160000140080c010082c180305450200041000b100610341d02e0044119054aa82146040c00c06622807600440d0040450000c07081a80350480c1056080c1450360700ca01d4016840a00802c052003111500071402200790700041c400f9500806000c41c02c4003403002818215149 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 442386187 1250 442384937 442384939
    0x130302010815010507350301080105130804090b040f02070c05120111030a02070303090b01060917011b05030403270f0902120c0c01021309050912030c07080a030b0607030305090c 78
    0x6031402c007040eaa040300554000d40d070080e9000d080398001c1407000401c0e040e050340c080d081c2d00602c0c04605040c4441c80c0154107035880b0500910490f20f0b03150800c42c104101d15002490911b043c00f040c01400500c0e440b41100610003040030a148480f901d2120817a40070a800f43c1d0102c803510b40520403801d0800c0c10b50441030503140204044031286410380000d01010700301f50b00705034000800d00c042c5131090704907007170942c1c2000005520356035405c40075040040030321801c0c0e80440d0520703139103220707080600c154071004610207900c0168080c401d00440c0e290788000c00880521481440090100c42c0a1030642c42203131340c54403d003c0c8942007480040c60f158090740160300b21801045144001007440303010942040784600780342e443c0c614100c01780b4068011100810300e15260300d500003800452540103680142c0224040ea00350460000300440700d0b00c42114030204070182046044002000c080040034035440c146000107044002e03000203100b55000250550020f41c50780240180d605c0b0074850340c8080f1130 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 442387437 1250 442386187 442386211
    0x50f070809060115051210081b010804060f18050123090c0f040e0d05090f0105160f1a090a060c032007060e0304031a0603030304031205040f06021303020108 69
    0x6011810942d07548414090400b20601031100690301c640280d00760342c80d82c3c944008809030b514100002c406103280900c60011184244400c070f00301000ea00800003e0303402c06958001c9256070b5a10780034080c1559041241c151607031914202c0c0c0481d11404540803041c443c600106151240d00b06840614204400c0d1103d80c00c80c0e00b00b07001d0000b2000805035001001039030501c990780300890005004186841d015500d60141c0d603466000a0f5106000740007078031003103800c03103c007441501c011039860141c1e21455400200c1240c80d0008154003140c000d071103902c12011150303441e200803581560b038102070f0b070382d461203034031042c46042004070a0103481103018940c5801c12064000c0d983c0841620b102102041044c41d0028441040c800382d50000d210600d41a41141d60f9a42d503031911020074082040300b094002c0000010802a1401100300e0707000d150903956044018601010100003400b02038000c503014204404c006002900f00d0024000700100c4a040300340f8203241d400050240301004140d81203000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 442388687 1250 442387437 442387441
    0x30703121205060a03021002120a1709030316050d2306010813111306210c061106071110090804080c0105120403050c070b070c140d05071404020f0301030501050f0708 73
    0x4d100c91120f40d04030380c0c044924060341200d181042e0701302040e09030202851180000e000901581000d006111403c0d048603441681d5125002e1580b640020344104100c4090342851207c00c0e07100ba00035040c5c82d0b0390740100048004940c0300c8075602085503801c3d0001e41e01e401e410071030950380040140707922040d003c4481c00010300307642e110300e80e880103004024801c41c800d00ca07021580d07602d40c0c400310207041c0c5a0719440007919148100320500d181100c044079441c1030448040788091081d030801e0070340d140c01d00c0108415240c4840075141c58900c41b240415030322620301842001c000314060786503c5400317002020355590a103043c1a040c140c03804541070500c8401c000050300c1f80d81c8490600d510507054078000341c40d031684036002e6003481c0e081d900100c0c02c41c20125041c814403244950714801c40b003100d000080803950072810702c0307028112000c0150a03504915020050080c41000031014410020001031400d4044000e502254000707030410b0f030389691345808000b20411016200e5801403504d08103030301d140c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 442389937 1250 442388687 442388689
    0x705100c200d0e03010b030a062c031810080c0d0e031605010c02070503030403110d0506040803060a05010905091b1306020c18010b0d09020616060504050c091608060a030203070312120506 82
    0x60003900c0001400c040e039038140b42c00400c2b02003542000b82e22450340c1481301c4c1c2c0c0090b074400703650303400c038407000140d0109100051515161160311002c0590450b00c4080e5170740c1c0c0e00c1c400d004258000e83c91341d11305a9140d070001c141246c13007403004081c180d5613039803440e02100d01030400d40d084910904100342954032619080c0840c0c1d5000040d24222074ac004640c840340c40c0c400021074044c40349540b00400030f1296805100401003100c001e035200ba9019102203800303664400045030140800d100f400c0c4c01c1050540450404030b1034801514600b01906c44040c0b40085904d030411a80250343e21410050300302145140c01450407015550324154030312840d11403941010800042071040c61100100566a1441d890454803224103483d405404052580030040040c18848080c1c04210340498441c05400c00c694a42c1c42e001f00760900030540c0007400400303410200c009540d1480007801c120340c0460861400401664100701d0b03240a5032054115000c1d09450910141c506903920300108005402c1608110700b03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 442391187 1250 442389937 442389943
    0x2030a12020904021908012d06030507200304181104180608031b010e060c0910031104063b060f2101060f02030705100c200d0e03010b03 60
    0x84000450401a40c5805000003d0001c0c49807801100c85c1c01c61546070241060b81080c1c115049501401c00078a20855002d04c0000ca84201080080e10381004507080c40704500c030758002035002229040c03001038017005c8950f82c8000070440d01c0202e010b40c0300040500031b04803120001004c0010b0420103000085151a00000902490280d801c0540c14030b044032000d83e5554211070018046801030304c0c1e889240024085081100c80002c000540c28000c03d40424900005e2081c0305209890009050504032420401043c0d02d40c1ca44008240c0c071000502800140c2c80001c2000788250385840744403800b40c400c1139041000117216402c0e14200030352600b4000711400441c00c2001d0045802a40c0c6e00002d40f11002a8020208001c840202c2840c071034100181080c103d5040c0c03030b90303030302c0340071110368551000c036a240f04d00e0740024850b0b0802140103544c2207040d0810281032a840c108401d868400c0744a442d44242a03110100d03640c1d0004114880c1c1503000342040031004810f0700240601c1100c000405d907 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 442392437 1250 442391187 442391207
    0x61201080615031606050c03070812011a030402030a080912030408010f0b091306050c0d0906090c090204060504030209060a1a191b140c03010e010b03010b0415120812091b0102030a 79
    0x307206c4001503605000b031051040702c000661000c1201c0d2034102c4560851014102400307005da880745041081e449103c130440a03644500d034010003c00111171940d42d029116004800744a810180e000070480c1c59440c10b1010b400074000030b40000541080c175028085c190b42c50a203180380240c0c40b940512808142d9102030580507600001d022030381d6140c4007000c0109100f040f031252101850f01c01c4031820082c2580005009074001c00f0020f0f410703034071100d01400701d204900c59980030034010001080103080100d0681d9201c00000c0c08000c40c140d0300c507503d082c070068620124a2030302c000034020900024601203100c9100c2d0501d4042c0c9000c52000e12120324070803881c40a8032030004a0684e0045031410481c1210203d0050005d2001c4050301414a02034068000d019209508200540c00c0c2070500d881803032001d62181400c1000c0c07615110821107201e99140e0245d5031101c04001d0034400f10000e81c0490302525010005045045488900300350840b90030340c075503046420402244a1869120700000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 442393687 1250 442392437 442392449
    0xa180302060a090f0b0717010b090303090103151d011712030c070507031e050c040203041a100302040207110f01020c06030106140714010c0207060302270612010806150316 75
    0x400f4030007030400c41e030700161a41d0b000300040b110400f040540795001074160b990025002c00a07000381d0321441440d20300d0080082c16501640180a580b41541c482d4000c1d24000d0710610ba4070341019101c10074000e044140307082110b044000e1000401065840d1108020642c80140241c9152501c0300003c064510018048000e40000410418180b200510440004503072190703104c04500e03510031400b4518010040c00b80d5007402030304200c0c0d541741481d0088a00c1150301c1529449030b0007030700e4140510b01b1805001184420107540004c40161101e00c000c0114074081c0044400d488202010001d1401340c00a0b0a41150004d2103c0c49598039100182c2c0d0540d4058141503451424181194800b070003200b50150a0850031303258000b003480306502006c45616143e00341d84203070352583c409405900c10303030b100100e0103d0308807800d180310121001c060a2810004000305e19000b1461103030308188001303800030003950300403c05000464400e02a9800e0280c000c0d000b6144a0400e0b080340d00801d5401d103e41c2e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 442394937 1250 442393687 442393691
    0x30108070302010507050c0d030201050601022b11070807030804050901050409020d2301091a16021b0402040503030d0608010c0c0f140a0b090a0308010e0f13060b04140a180302060a 79
    0x40c003007046c18081c1c1c403001c0c1c07000b60030412001c010303050003400b829043e1500c071b0140c020b220002ca401c2041c080e80310b01c1c3e03911a40c03424040301c080c00011a140b12030341b551003105005002c030100e0340700000c2c8162401140a0b9100545607030038141040743c00101a406240704524040c040d10043e11240611441030350080d035000c0d01e62003009098603480e80b8104441c1c03080d518151030b10f005c00900a201c41d02802080c07031900300c1035031030102d00c80b040c010348007401000d41e005601c9540000c040b0348100d0041180900054141a0380350003191440c2c004110391802c594841d60103110100d42442150740c480350a1a02040c58215a1150347c0c0c05110344034090320faa189050042031085041084401030380e80090303041d00c1c0b4030341104a01d0712120552000c4002410b01000064200e01d0200614010720940c0000e400d40d0300c0d295582d1002108181c2e046801ea07486081001150f56544a0b907622a5603151141c401e601d0610003101c200c800d0030700140d204581134900000032035400251190710000481340 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 442396187 1250 442394937 442394947
    0x20412060c0212040e090105060103050405100b0d0f0803180d0905010e180c0301031e02100806130f0606110a03050f0f1e041508150d080d050106081801020301080703020105 76
    0x10883c00c00700801c1095503200700010f00010641d410702c512910551584000304a00c0d12904011415110151009010f40d40009100c81d0840d41a5106035100700004205414249041d0b50708400d544d81c6100c00c1d030710f902000c402c2084103a040c40803403001c5442e95003e01000070700110301906a107840c0c02610304000220184a250b1384441032007940c40c1013403000c03181c01480c1c50843c02d4001d50007400210780071048100764403205403503501e40c8190b0540c01860110080081d00e0b003114401c80060000da841461102c400003480c50912440c410303201118400704074030741050009083c0000e510b0080031542e20009066010903030000c159055001d90802050362110b000c4000103603030041d80c04001d400313500c502c2100f030360041400c01403003159503041103020540082002607a04c0e00044075005e6104010b600c921a03245007c1240404591140b4005410080c0040395041101c400f42c001c50301140380350081c401500006150303000040079000003540b48d50705198069484d41c0c0030f44070080c180040414 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 442397437 1250 442396187 442396211
    0x1b08010b070606090f0204080d030207021c06090f050303090106050f1f12020d0515011107171f060311060a02030d05040809100c0b06120c060c150103050a03080a02041206 75
    0x703c2c01c01800a40c4091040a040302040b400952291040d204980b04074044d020b00301e0301078020394503110340003404c410244035016182614981081402c8070b10303c0c3e840b043c07034000500080001c400540a032000707640381e2501c0f0200350308542c12904140d05c20315030f8210f00282652140518114640f00701d15a94204500500c01c3d102d0083c1d160820001500206150258001e19800030b40b040480a840b9400411880015a151415840c002440d6044170030103000900801c01c5820944c00d114040b12040501498002d8003030503c0143d10b2022515400c3c03c00c03c0c0b019800a03448007100858249180100c0f410001c0e550784a000000e42c0d040c5d80301d000003400e000d054400d8030311005029000c1c00d544001c0c000f0013000e00d80138041c100c0e411195a4082401818942200107030007c0400c000d180342c4030b0020030045290001c6400724068810303031141c4001d80168501c0300b8000c6101d070004200748922460041d142610042109064601c1480308001510f40102d80952254000b0030000d00c0d421500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 442398687 1250 442397437 442397441
    0x30111180f03070e0702030316030908072d060e01050105011707030b03120a0e030609071d040c08010e030414040903082d011403011808030403050d0b0307060c05011b08010b0706 78
    0x135006000c215240010031403525008402940b00c2d11502c3c030401144e5103101c105404456441c030b005031906a0520203040003404161803170b4210785400891102c00080c8050103401340801c003408850503a25000d4040ea1070380240030b0b07240588000d003070440410090691180600344000c01c0d203020541c9840c0b0b408003a450600117110010720700f50540d9601e00708110050b11216010001a0080c41f9860008507450030100d000303010760b200010f0070803c0f05541c880840465070054810ba648501a03180040c071058244500d0503080700c00c0000c0c40d240ca00d020a8030362402d9451810358001d509003100040007a0340311031060790015000b4619001159501c0100e045031900004440100a50800100c8c0004110604110394034045000340011a0711409c000c03000f50076214001e01000c800c1c000310f40001d00035805441d00718503020000802d02c6411740000c0c94600315074031803404074403101c2d25541800b40c00e0003100f0600d0140c00c2241071682c003002004100d40814071030118200000301d5090200070b407076 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 442399937 1250 442398687 442398689
    0xf0c070c03120e1009061e030e0a0b01290a03050c12180c030f0c040e0f010f060e150d060513060914070e07050405010e040b0d11030111180f0307 64
    0x40040c1c1c411015042c040030300781d00c10ba4000548104903140356041c80b00c1c45096501e082e500f00d551039040070703030400f14000034012a04645400b8561106140341d0f43d242c003049450780d0300b40900500d491a5150045a4047c0c80310032803c9203034102c00030950000c85051100701d4481c40168030b0001039a6413510303055402c0c0d001d84184600000203030303400c2c008080f904d0340003e10000030020540358214801001c2507610401c1c0d240c00585604040003500303151074240e0049103886000c4040d0340c02088500880c0b421607015280d00c800c0c4658030042845461520b113509584000003040f01c100301041d03680090814a00c0004c01448d0a454400003007004118508000384039070b201c4801d0065080c0c40c130303064a0024945110786038034805d10100148521040c14802e00070082612403170300d09030800d801100c0340c01d01e00034078581042c2c40c1c2c07402c2026902c42c1c05c0784802c01401340101c103050440a1341010300f9142001140c245444045c8803c81050301440c420449401048514481c0106007002180c01e000c06 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 442401187 1250 442399937 442399943
    0xc060a09050409060903080702010c090323030c0607120606121a060a050415020601031208041b0806100e06010522080607021605090c07030f1707050a030f050f0c070c03 74
    0x200f0941101300681e0390803d202d25072203511940340c3c507034910b5000c9089500c2280c04500043c84e0480820201e02c841140e01d225019800081d065484820500d078a981d014485021080c2d002e0342c00c100b40294480c8a04014404065050080e40d190a0300140030011002540364295982c0c001d05180d02c40d510f003035004210001d400c1540f119880d03040908036800512684d0420030204c030401c602c07240301243c900d06072070380004285031104001900310f07000600100210342c0070441d11100912003c40d03003405030003000e20400600140c580601703010400e40c119070054038110041001d00c282c0e030b80c0280a03030300c0c0400d80a036203903035101513003003586201001b9038008482c5000b40c000b0f1182290340402c151041050b05031350a0402503440e020b1007000007013104d198400d45018040000001c0c45914641c50b007410901d0440050100d1039052100c50505444600110b80000b80049245405018007030924001d0300007000503181c042c090159507100100f011130308100010350b0a0822158103003500c00b46070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 442402437 1250 442401187 442401191
    0x901090315020406030501052b0f02030115330e0312030903070c080c03100e010219020c0a0812040303180803030a0b04060b030405120a02012a1404080c060a090504 72
    0x11026181c0340294041c1c000c080000b0308040003c00c0c01e04202e00848180c008000b0780d0a002c0030012a200400381c00e10408640d030b40c0c99001c025026039800d000c1c2280051540c948007481502d003074030b2100302c0e17150400c0c00c0b680f40044041d69400c0c03847c051107103100c59009003043c1041c200540c1c0007a0421314000d40b081031182010003800001c0c080000500810742c810a04141c08070b4403828800d61710080a07010545c1980b200701e18481540c000d800a94207000c2140015080c8405240f00318040c0409180c1d030030050340400c0040407981740c05407120b40100800f00c060301c00c8460014000000d4031460102400b480342c001c003140011140d1820030380003495101c0036651281400080440644100e044907482a070070f10502045102c003440c2103d014aa1210040520740d80c8030701c4c181c2d00ca810001c001002e555854004001304485070540c0161412203003001d0604010b4000040c0250814030702170310200005000510501000103980c1e400c0050840e443c60316144659411102800c072900002e030094 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 442403687 1250 442402437 442402463
    0x10e090a0f230318060d0b120d030b04060806010e06010c0b070f20190222020904060f0b0a031509020703050a0e090601090306020d020c0d1d0a051509010903 69
    0x14002e07a8001a00341254000498000c0c0c8400da143d403030191031a92030b04e241c803002e00c4480031314101d0010041340800c01070214889552400207402030340c8508070109a500300284e2580300c1c540c0751007103120390341003110200071607030600680700c0d5595014040d04003a0b415110129441d0382c01928520500b99000c68a04800c1c03401031700c002c0250075030800c0100880e100c031080d90a030403000080b4581c0719082c00c005084588102c10907240b4801c20210a0360460400010b5079540d810f0810001841ca810304000341e629100001400304403585580881854140703072000b400840d00e008100c80f03d54090f0f240108002c940c611118004500c268499810584000303001c2d010540c002002d84010152625162210302c072280a2000304002101c07100d0001d4102c0300305200182107a40a4000583c0800e401800d20710948485841d0500b04901031000c14004c0401a43c02c0032084540b000c405c0003074619a220714903000c04a00c0c0c00108075501014442d010a195801c0e03407054440724010b41d01300803900304103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 442404937 1250 442403687 442403693
    0x309030601081c090e0f04150c0e0f0a0e04021005130323010b0105030a02070311070b091509030c04090f0b0c1b0a050a032f01020a0806040e06010e090a0f 68
    0x81d0090200c0c400002091604901030a0702450710781d401c454006985c0101a9038a90445400d011300030b104445031125a640c001c015071031352090101c00b010320349403c00003d100200f009440c001c1200000d10a01041b001400002c200030400c035000380c1d06031044c08020a40c8a0140c03001c5c0603c00381010902e4040c0000010b00c00c040d023507400040203448540c0002c154a01401e403c0c0e40300c8140c0a8045001000843c210301c1c016401031400900a2604641344801ca180240c04d1501c41d6000301a044d10100e10441c1e14130b020204203903c8001c001c1d480b450803c8560200c0d0b11000345c845d140c0d120702c0d51b440f1000c092003619092800005d074802e4101c012841c100010601c03540155200c0b00d1031080c80d020001300e17080001040410315030444000c11400c82645d0303045801e443c0c0c0100c038510700208210310321061441480e0501d240141c1d030b400542c50709907060004050b0308000744090b100300d0521001c2100040003140c07140c192a0305202c07904103652f0f1061042e10b44036440500500302c1140013004014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 442406187 1250 442404937 442404943
    0x1a01050405060402070b07080c0c1c0e0603040302071e051c050105060f0d080d020f0307020102120a02210601050418060503071401080115120e0303040b010603062303030903060108 79
    0x1a120115000c100d19140c500620049002d540303001810b541020010031417150190000d07517400390907004030500c0c02004030a201e0602c2e140341381e400001c1c5260210103000a41142c06d9000d150000d4400504500d0982c80080d03032150180716020103006611104006402c1640c0c4180c0a4000980ba804000781f80064800c4850340126003958154600400300c0c409107009d031554448003030020105018109035413580f01031680480e140e07a070400da0812401540310001c0c0003443c4100c8040e000181c4a9218540110950781d004114011141c41000900c074104000851148000314408a070091030755684c00603920b500c02c43d0006e00d198503031100880d140482c10f4010809480041c0c081e9100542e440c40ca000c0000816002140030502407801404024680050b0400400710b900d00f09080645440a1760700b00d0b20b0b50050000541c1000080005100798a01f1143c010113081c50100300c0c1c245000c4403220000c0c1301080348450f00301240c14901c12560104180c4080000007030176141c00d541c0d03c907111070b6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 442407437 1250 442406187 442406189
    0x1090305220e1623040e1005030d080406051b0d020d0f0203150301060e06090c070c0506161a040206040614070b0c09030601060815121f050703380d1a01 67
    0x160084c0d81a03095203119415440407a201102d9039804d140c00d1041720307004e28000800440d01c0c01010a40024213617420402180d00c0c80058035504540d0902d0b0826500b580c1c001001000709850b500051003000c031000c6e0440e81d02c010107610041e16501001c1198000d0940c0c902026038642c004000d1180706d1400c0c0c00c200b020341c501200208a110340d248c100b020078400c2143e9869001c9407580c00074110907800300041014912401300c2c12982e60700c5800050b07003a0016101701c80480e548034040c40800044191402440d05060b02c600e1680c5030540c0010000d02c82d60203a40e08212004018a02c49082e2a050320201903100284038170030f19140050303452542004400a10a100e034100000c0c8550080516a003e40703440040000b01c2e18100701070060070101147d82c02c9003882164080d2070b50010f004011103080c2214000411705051040c8020143d0300b00c032002103800d068001500078869076002840100c05060f00758131305440381080c0000c4182c0075103c0d0141000c0c0d00c80d18a501e841d852144854 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 442408687 1250 442407437 442407481
    0x20907050f0c250e04050615060f0d020d0c030905060c0c010b0a120b06150d0b010509040e0a020103061403100e160b04030b0106080903070f050f2d01090305220e 71
    0x10240603510340c04c5008440c01514040c02e25004030001c42c0f042c6805403501c0014400243c0300b2850071a00b010444540c0c0d210200c0004500d50215600641c29014001c08000c41a0391805004000c46a01c0f540c0e220100a044014580c0c40010017007030b00d030000e4002c1d00071410010701c0780711340c1d40e550917004041d808205001c860081d810307400140c4a181260540034940c6108411900303000201d06418001c0000e07044842c18403000303201000b240c0d0f40314010400600f001202401c1c01051910015040c0c0361203030044524012100315111240c1c80014081c80c0a0f2010100400c404511041742c500b010703100c5102c011b40e800007440205410700c031000184101c0f41b0480c20612380c1d0381d0f161011100c0c903005843c655101d4004001e201e0219241c03c040010300d90040054031007440442c1c2c1c126181403002c1080c0c41505200300d09507400034080c44207102e0348405c160000e111040081da002455803059652840d0510b0101e2000c0181c40c40340700051000d03103804e5500d200d9074286011604500b00f1798080c51 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 442409937 1250 442408687 442408753
    0x5061f032f03010825090f020904050c09030106230103020310150908070807031e0309091d0f030c06012d0902091c0206030a020a1e090305100603020907050f0c 70
    0x200c5010f01404450700610345440f4642d500317090040c00b0011f00701d41d00300d800e0326907001d00c1a8a00340c0d070f482c49141e005c1c040d0b00d01d15030b907112180c90506003903071969445035141035070440700800c40c0a0008030704108882d0910b80140d0301c0d038a20f46844054041c64108039801000c040d91183c0c1d030740c2c006409500307465044045511507651200100c1d035450301800014461004400309085800705281c03c507035514800d0619000c1140c5644580e001c481e0046510b080710491407016581610003409030b03010081d00395020354a416030600711103584040c1840782240058800c480700012070904224007000c400b5000b4650400c2c2e607614010f1010750851040d05101e235001d030000070300701d10032500d4400025901800700c2c2d0850342c1d025003540080d00310f110700702d0921070300944032122403000401411000c80e40f6181c0000550842c14101d1030301c4203268071075910340e26014040c000350781d800c1003095001c0d0203072804980d10b50040201030340b540100e8885090314400c080e4030b1941049524400519000d0725090 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 442411187 1250 442409937 442409953
    0xe07080325030509040f140c040f091505121f06030204050f0f01030803090f03040b04030b010b0c120706110705060f070c17070519031205061f032f030108 68
    0x9407120072001c000280412000c00074440142490380200744680b40500000960a10303031000050b00705400c42e001c81014400290a015900240c050140500b08001e01040394001c0300101c00c034105200d003d0030b8440c0c82c2e02022101c41d490b0410030b440000310b482c4682030342d0032a041c030190301808030760008a12881c03c10700050842145016403034840c81c5907605412070703a4615100e1500641c0054a026281d010b400729800616800304010030042140e5080256614030f50300705001d4440b41a0452a00c0310b030104503c40c051500018031500c0c84c9403100c401c0da80c8074680d250040c0200310303002144118200200f9800c09018001c04d15900c07404038040c03101074560320b4040880c2c80e0748000c0310080115134071a0402401141320009401594032840448451001d104c1c203455005084a1040340004c1c0401207040f007590751401600c1d0002c405950028070340390030071211200c0e0301c000d01140c402c060f0345181000f50750004a641d0035609500b00800601300040132820f16069109009400040c03007201d030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 442412437 1250 442411187 442411237
    0x151207060e0901060f0509100e0d21050306030d032309101406100815060c0616180308160204020d0906110703020c01050309100c0c02040c020a020f01120e070803 71
    0x5170103080c0c40960396070318544640c0c24104442c0018080d120390130807581202001703140d2030380c2e4240e104290007515150030f03080881c00d100401d407500b904807004101c02401801203540307000031411400c0800303090105910080703040140154582e070180f10038014010302401740543c03010800e59a00c241c03117201400340701280b490100c035082c0d05451072a00901c1d820025104e0911501c295070704420340b40c0c0900c040e20062000241680c0282000c108550411010300030740c400009a0084441e4240c1010200701a2240d91303071040b00c05500c009001107000044594040040c00c00201155070700400c1151240b00031314142c0020404200e00711881480d0500b40c4c0d54480d035101c2900c2d802c5500d980185800c000c00001140c050b0005803420066100b518200c01386a00d1070300030743c040b114050359035540080d003030700402050300d6054029505540040c401c00c070241c4c0b14103200210800003030070700d5a1444141d06105005051115606019009130403000c983c1003800700003494042c410348c040e1101d02c1d007080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 442413687 1250 442412437 442412447
    0x901050714071e030906170106090303120b03010e032223060705071e050907080a0b06160b0103020123030a0f180c030c0b090108151207060e090106 65
    0x40c9080000c01e0141d061100080751078001030140500c50110380561540e4480354101000c0150350440c04100704d041e0034400b0952003002503150501140711500e242d49842c6002c0c1000b0780a000c080d08000c100c0280c03801b00c81503600462840c40d0054020049101e15802098980e04424220407a0301600289003242d03130701000e00c103810f40f112003c1081c1000e4244065201c03500051140ca90800d409011460104070144034080003441750302c0b0b000b588000c40540c40d020045080c1c118031b1061110030103000c8121b901c010702e20307802a02c1c0b4400140038003401000800a004009216182c1585140103204000c040803004c1d040724803e0720b5400500b0050b1800100d00e6482909480e150a8140000382031492140c01500b18442541000103118640f21b814403049000246d080d01c191100da48100704001c205030030700009142c100320560034001e002c40000c16015016100580741c00092600b94201e0391400b0500c0740003130b4203108640d103896440d4806000b4042400080d4403030f2400500010743d00c1d000d1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 442414937 1250 442413687 442413691
    0x41e1202070f050f10020c060c060109050f0c03060d02060d0c02031b0c060d0f111801080a02090a0e06040f0203281104120507080d120e0a0203071203020f06011805090105 75
    0x4c2500c4290152541031040440c1501c080030110b204810760030155481c2d413170081c010750788900d01800196050009010075944081c0c040d80c80011003400300107400601c001903a0300481c084403400784621050000800d68010f007026110b640d460030496200458002004042107020080700403407170045000c000f61a0780f4108549070300319000b000354098040302644a1407080c1001301000500309102000000980c0040060325054207655103101d0301581c2003131140740e1124088100b03616000043c0c1c0400e407080c0c4184101c80740904800b010030740c190f4840d008110103003030110f021926480c040b0604a90000e60500c0122441201c0ea003070340c04005c4600610401c00c1400305414501460200c2d0003102040d4ad6000f03580a0003440b0010078012418401c1401020950380e070031018009185100084840c0c80703030100101e0788510860001030710089924002c6884d141045810f025080c2000e81c148444180c0c3c040031801003c00106148840780c845082010748040c00308041d0303468200303ca00302d4400b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 442416187 1250 442414937 442414939
    0x3021018171203090a150504110a081b0102100924050c0313050a0c09060911070215130801060e0a0e01020a0909020f0405191d0f06010503041e1202070f05 68
    0x800110b001602814000554118030000201c46042549490707000c03c651144400d00b01464540c402d000c184041c0c000101e4030a03c0499544000710f14000141c3d07a240d420904800b007000c1c8001c0c1d41c003c80da00910044a082c0103001052101580524040700c4030151425203990100701004c00c040101c0740e91290038441d80c00c5d101072030300c1c40d180c0104265503040c8440c8115003510500382c0740c1c070000750052201c000409030a40045041c5080c080c0260644e11400b21030558200c09100c0d00b00903996001448244c580d6200d05c00740d0355550040c03c0840022141c0081082d0740c20050700043c50224026140c2c4101c100c0c09040001541e041019806d0340315908c562000212600341c20b0005a910364020f025003915200c4051070a59038001140c80f05a00b51481070781d84902c031004101c4100640c0004080340c84850081c40507150402c010b010107100580303131504008001c030024040001e030790004891100700185220f00c0102a280240c0035144080c4540c0060207508800101480036082107025518 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 442417437 1250 442416187 442416193
    0x1807080a15090f1505010f050102010207110d020a051e150711010806060c10021b030906070809030705061912270516060f17041505100302101817 64
    0xa40448034809000036400c180d030318841540f004000036004821402d0420101c84000c9a998980411068500840d901c0389055900410014000440b0300600800c4ca150492340800910198008101800c0c8c1d143c01c182d4101e101200c0e4995404c3c02e88403451002401102d8846510140003025001d03400b0b001002460003c070f2034000d000541c0640741c596400107020300b0043c00c1203c10780c05180b8004d60650002031305680043c84040090907142d000c01c450184c0750007546060031200114902e88030f95007020705a10070104a142480d07030203102031802004014181c589031041800c02c100c5031049900b01c5404510084040101001c407401000743e540c000403203482c0c072400d0f400d89a151282591804949034010412a0b0210341456101800500416503403080d50088003100580308680c196103110551009904200c0041c0b6070440014400c10000c0c004a20741d240c140c299180d40c0c00c2900025401020042d00c42901548020514044600001144182d582d650850368420200200741c400a030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 442418687 1250 442417437 442417463
    0x50d110f0f0304141b03060105181605040504140a0e010507080c0702040209180106090605192a030320040302060924070804030308060603070c03180e1807080a 70
    0x10301c140000d194400d00800400c0301269503030852074100804110f1000c40c25400840003241400e00b000001d024080030b8690340865568810002c52a20000705501c040c1c03070754a00f025003080d1180c6e058800910029200307000c4c2107046826450112012100000624035245003403c60020500481e4045e005549400a054a0380041031b11181d00c0703150f0607600180c08006c5076a8a4075140b14403640742d46800b0292120794106078000340305244a0f40200c2c01c208051089205003d8074030030800700c0450a0a051032001281000c450310010001400328040841074850414590140c11072020710a4000c1c528200c00d10046500e42c4601640c007000c2e4004105229441c02410130a60005903a0034900080c6d1260040701140300f419400b103203045401c0724000c2820810150442601034100c001240c0141c154503003001c000b00100301400303000d42000b40c6521a4501c40203003009110107005180195041032525203000300b0700500b0001700c200c4034880c1040001d0548004100000d90304d074440d054004035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 442419937 1250 442418687 442418707
    0x60d0f020f0a030f0f17120609060a0b130f061d06160b0106020c0f0f03101d0f070f080705060304080a0915021c050903100f110703050d110f 62
    0x50710082010310b8001c203202d14003101062209000801051040a02c1c02030000c5903d843d4a5600c0302c102007844100082c00b0740ba1985614405071a8859001e68404841c1d90b1202d0000d90601da5a9104150f4054000344101151901651740c001391412059140c85031550340318212240c0c080404041c0030300380c0c000241c80c440e1a22200a0500340d00c894403030b116020041e10350804024013a806180581d00603c0c0414041c00c1c00a164203d002c811510700c0c924041c550301080d20f03500c21540405040d2781d6026840c3c038014044044032414035034082104d229059481c482c07035951205004801c2d114040c88000180f6910000d888820b841c000340079070f425600c459550640c56000310070844c0034072117519004144180580004888407945500404001220407080c410389124408810208041004100500e4400283ca121402c0e0bd1160008601d64002040801031040ca40d05030005903000941314127140d8010003070580384101020401040350080e1815005105440c1ca044019000b0f128403828 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 442421187 1250 442419937 442419949
    0x605040f062015150f010c0303020d0603120e150337020a05071109040b162717060712090302031b030a11151b12010603050708060d0f02 60
    0x103041d04142c12540344a5501910b50628903001500c40d60014048100100c00b48a21083d8920500c261850190b50f000c1900080c02d0500210001d01455000070f4100c0741e284007540040b0041d03400c00c070300c40c007080501c110080c8409400c070540303071282402c60045100342013003034101c07409200c8048070080d56601002c0802034403001d558101d0911440c1c03501c40555091140001c009801c1903a5406a4400c01c17460141040110880303440d004124020400000030105201250811012402c1d118180e0103018100e900c4211500500401d03002c00b40c0216128080c505102d00351045940103842101c501c100207581e84404450307000018040d284000c050030402d03403007101030f6802407040e03a140c0900268200c060f941c020140c02502e41c00010013221980c1d00002e01042001d50001030208542c411207605600ea2014103007140c041c0d003020401040d40c0298088a2003c00e407801180d13401d694840001d40208411611040401d50940000d061031410884182a0079070040e030180c1d00c0c640c65000c0c409 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 442422437 1250 442421187 442421207
    0x20904020604090c050d230c031801140405010b0907021207032d11010b0904061a10050301060914011d0123091905060a0e040908220605040f06 63
    0x1070001c00401000c11080018000d0002e50303a0036888041d518401c414090044812012034000c855000241c20191003220f00091030300610201982070b00da448200000241081a201c2c00303140b0340c46c0030f020f0801c02d404403855a1007107001d10020080c00901c0001c0c07200005040b1400c0c40141c00901444440c41013840c080c049083c0a85840816521075520407920480303215401e00f0b114125101d444c51071039000201c2549000208001c0c80966590f00200b200d2840c05040104041d48030525002c201c0c3c2500e88222030408001d00741c0000c80034200000c1e29540c02070080c1d100041d00c03e90302040c103000c3c01d0911901040d043e59012070b03045030540d090380398017805480e0604201c510b0902904c9604080425926a50444255991640c00104000e4200d0b02c080a650a40114000c00c004071ba54520035112210345074100f0465004141c00020300902c0170794001840420040782ea820001401d504a13000304001c43c9019900540f10705041d900da0203988100805003c0780c1c14188940392103101c4101d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 442423687 1250 442422437 442422439
    0x91803121509070203070204050a0204080705130b04060f1e05010807050c0a080301091d06010f1502070506070f051011090f1203070b1006090302010509060a0c0f050d02010e0c030a02090402 83
    0x1d40c401e0300541c00249103507400e40715140143e10100354403081d40b5083c0304198101e111440d00318903007803038610035945442280c40340038440c00156034140e82e9440150000c07034442c28024010400d01d0f071140303460041c1407031502916090b152201c0d1080440c1c5402c1d21303841c0c142d820584840744681c2c3d40803000c46159104011251b640d028045c205800a01c104020f1406482007200c08200a901224aa0390b000c04543d610324044d88082e004000540f5008240001e6410300a0307032585101074081c1c01d80c03134045207911641c1c01038030004004c0140080780086200840c0300300190303500c0c003130713168890420340750b4801900d03000c1d1504100460152810300001846403a01910345034080c10200c01981c21a001a001500c44000d01401c000124403100b00590140646c0d0a0078ad50150035a00000d04a001f00d50740907003e0f03600090980016405203181403e242e500006c0782c82507412030318055071103400c1000d461003d0341c00c00c010b290a00901281c0b04500300401740c024104610a0780070001041d80c060016 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 442424937 1250 442423687 442423711
    0xb0d020c0c040501061115010b041214060106020106052719180605010303031b0c03081005030319080c09130c11100c080105041a130f02130509180312 66
    0xd1481da111401810b0080c03290ba241c03644480f10304c0d6100c43c04c00801888820f0f02602290050001d2407814080d02c082ea4500010502c4030081860482c4442c209900303a92a58480c0a0002400c10350540210060383e9094603135441421440e0b07070b119a084074605420580380104800155034105c03003806008441d1480d01c02040e40039008241e41c01c40c4900c0300040c8d90346501c1d20014014107416010b6100d10a00705030103c0880c401e1020000c02191300b00d8001000c1010b03880c08a04052511641d10003e01401030a032035443e0040166102a035010071020001305051000040a03650a41c0503203410b2480a41980d2004081f00c020318000d01c4600307101000e101b01103419000d2000104502e6000030b00d0103600059100700c0c1c0c0d001070034444050303011134461070424411038400c490a403c00780004400f581e0480016020008003405082c0d56010140300e1403010652000c81c2d146c4450031001c503030381600e00e4502600d07400203104000c0440c0120b21a154010800241101d0303d1201c01036019070303c0180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 442426187 1250 442424937 442424953
    0xc02040b061602030601050306070804082206050c0c0301061406070602120c0c0c041e0c0e1e13020703050703140c0102030c040801150f0510050c0f0105070f0503010b0d020c 76
    0x1640940015501945072103100d0900d00440c1010000e15007d444210024400742c94aa9002000b080e4004c1004080c0400071506940c1c00c0b0704403c1d01c41d0302d00041d40c4030301007498540c10000c10503002403034154554401c107031031041241410300c03030304055500314800005150044420f0089a40c4007140c00c46a05a080010180110102c844207000b030481c0ca940c0c540d6080c000c0a8180f03050780703c0340c0d203e114510f0106000608035044003940a044103403000420b04449002d025610141d190699a4000680d841e6004154a4840e803e1580340c404903503541c100389450640e40c0880c002d103400200407440c10401640460302441c2064003403003881c040f085c0780150500e90340c0d0036a00183c8030500c001e200401e041c07140950a001e00302c1702c058603020f4581824600b01c4502d24026481c4541c80c00b9030014000003520741c1c032440490340f000c4174800443c0c4a0244103403015000308801c031030400000b04005a07070103102c0d100d40c00b101c0c12103580e0580c06080c207001110260003944400d140c25454820103203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 442427437 1250 442426187 442426189
    0x604060b0a2a14240f150d030801060201110c1b060403060e06061017010302012f0c01091a0406211e1b02030f0f07020d080c01150e070c02040b 63
    0x41902071051282c0510120400440740c52498602c413400710503581019003108800c84084415041d13030105185800c59102e469074402c1e4010307800410390094100e0f42161a02061540215035a8125880e0b079008010510445440031818041c0e414085d00940080c088001d071a4003104080090500051844d481c2a03900d07507804085855610300b40b41140c03c049d0800c40246000e88100040b4105800c2ca01c000311079414510142c0c00c014080241404200490841056401209040c500c15003140b2a5003956222560302e986107004c80340140003078a143d0010880b80310340e042003611a54611059424503040c02410703a0300403035241c5060820041c100b079503080c43d5134500030400e43d14201150f9030b807407024003192038050707501e0080043c0007101d0400b40485441d90010407601c6000b4110000c6888669450109441340729a540295200103055034a07024840301a000b816454042c4000308006c1540319480c4034a000f1030701c2020000c820203400103240b01e02444118182d144001c00014941c84484 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 442428687 1250 442427437 442427507
    0xa0f0f0203010b030f07030b0f0402030a170d090501060e0c16170721020c04150501030207060f15060314011202060d060e01060f0329131b170604060b0a 67
    0x32010445d81e40400010000e002c41d01415036000b00304601702201c50f14041c5c0210703550340143c07100241151500c80d03d410400c03045c0f8066590704400c01c14184210340e505d0030018003070006406090901c041400c04215404460f41c00c031090f43e4074025501600042c0d42d210b0300200e00c0c0ba100030408101e0100810000076107000b00300700c0c811030380710030460010202d881c0091403c0713500b208032401903140403001c000c103654040c0f0001c1104ca003441e016a07924014a0007001804030445c1d03100c0322904003119105208101e18045c81aa00e440e941000390f40c6000001405011082c40390f00000e0f0302c0e4500b010701500b011401840d5103203c000307001c14042d54440a000d807442090b44980300140d05031501e221030325407502485510107802034508006070100308088004400030041c0702d1054094800d0590289099007040c11500001c10101311087e03164400075041080604103064460030301000200c092401e84201401e88400c40c03111400c0c21200310058902c000c40c181007180d60507007a01000c140c0b800c20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 442429937 1250 442428687 442428703
    0x6050c030103020d23060f090f211c060e070f03020f030a0b01030b0315011505130510020703050102190816080c03061c1110050a051602010302091003050907080a0f0f0203010b03 78
    0x245000c03021900e41110700070300b80351503030b6107109c0c0395001101c14101014401340707440c03080c202ea001c90903500c1010b643d14450a01544104103049410b11a0004800d0b56103981d281c0f24010b07580740c00320003112488044080344502c84850805041c288081406e103445980140540c00060400060b40074282c000203140c0a65101180c29401002c40140448018034440d86020049802d18a00301480b00c0300000883c1602e01505014480c48014664110b1081010300021038011008560780e0000700041c40c00075141c0c80964000c5400300021034003203076459203001c1c1d01d50305603950503a180c1c44100d1009520741c80076203081c0c0c2c014410501d07020020700e84507c504201d8458802035101c100c00c0302c10300454131001c070501028050140095490300303800100b00c49248a40c68202d000e00c40031880103a00030700845070105c1d0494241c4413181c1070750360160300c10350045580c4400c0303c040c2c40c1d03108000e0b0307600d011036030005015860020f401d20004040c07014403403030644020b0001c50a03407a4113010038a0705640c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 442431187 1250 442429937 442429951
    0x8031302091006030608030a05030609061507060c230d092306011802030601080c070c0e07020c030c0406050315130f240b0108130311060106050706050c030103020d2306 74
    0x8180802026405110305e10040400c807020f542041d200003c05421404010b103000d005080c1040099199a43c2c280c1c0c1250500800e103a045d114000c50505400a00170780c500440810301c001c0c0c5a003070782d031022016041c41c0c180c07101031289844640744042c03001d080d035240210359210700300410480860400b103d07541e481c550880280b070369614000e80c58943c000c01358030b104d1900384100144000c41e42d00009503581b0040382d808003582e81c0d040745040c0c00e0340b0300c03d0760005003078800c00710078004003990101d05142c0c985421012160a42e00070410041210301c0751151680c107a0000c12060042d0100c0703641107a00407098100a5502d00440c5c40707003060210410300c04c4a4a180724031134400075180c0e034050b91441081d0744808006148213040003801404024121121014040c0d5035841054031030111200e5502c51f11041c4d64855955003801b42198125210807141c00781014001458a20300c070091700d04030780c1c0040c01540d804042e500c9184003c40300380d003807603002c2e02801007014580604010302802410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 442432437 1250 442431187 442431211
    0x6070b0415200a0806040b0a06301d120307030b1f09290d050901180506071205090d0f02030706060f09140601020a111207081c0c050a0803130209 64
    0x803014030001e042c00c0004145e42d20031840d00c6240407507512007a100c1c01c150303162400c00021b10906d150a4107045100b0303540e102120242e4401c0c80c40403440315084a0f9801c090714031018080c100c0000c0032a2682c441c1006400c0208040c000100520b1098101040d00031010b007600c40c441350b52401003210710720741c043c0583c0425101c050421020000c6202099204100240c81880e1746c07000c11b412030b4a1049401d20380156884001090400c402940608101880d40407030b040c0b01202480c103151540002c50305400070980c100c2c0104007081050203550b118080e800c000e05120f180c068410b030390300d4a0300e800e02c0301144020710481d00000c0c054440c0c0c1026005203075200c8841d03454454245c06884600111200c651700d080b0520070f00b40d80010b845020340c1e82c800784030701c0b01c0d00f0100b02040c440440b00002c00f549109000c40000c0a820204922040062980031003140380b0340c54409841003008054020038075400410b0b46004540309801440d0000010000c0c501c0d01001600080c84642e030a0f5208a0314171 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 442433687 1250 442432437 442432447
    0xf0e0a0803090f0d0803040f030e090906060103050a090b010b031e09010e0106120506061e0406140a0608060114030714040303020c030c1e090a060b2706070b041520 72
    0x4507011924040c00a804c0b2640420715100d6502d040d020700016100900c01c8217850410420103028441080c0d1060014103982000e103000b107901656848141c0d1224003091415005c41c0e0b030348009005240e902034001051801305d0746899032042c543e82c030090031121840260688002c0301a00c601e83d160041c0c0d02e5070000f0500c140c00010250071030310581e00038070b4804a82402040003030300215980d680700008881149401103142040254000c2aa046560291404c2004981c10303689045940085106482088016456001c107480e080415140180865001440480e145c60388200545e481003541c68242e01c50110380a108040750042e400407400358114103203c0056040070803c141007130004550b213030744205000d0710000c0c0500c140c8520601907000c0c040060040e9005c2e030080d000038290300e5941c0350358940e80010442005c1090150605090440c0e803420039620f40501174504d01900440c0000064030b40e952048251094000c0008010f0b4444014540d802001001030030741e0b400b9902c0c81d50b951 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 442434937 1250 442433687 442433689
    0x1501060e01050315060711030d0302070b0f0103020604030b0c160b010302181902070c180506030d020312060d0f0c1502120403050a060b01090e0a0204030209061c030f0e0a080309 78
    0x216a1280a250412605008000404615130200d65840000703071400e9582c2c15081c1400e0b1168118030990035058410b0102d40308186e54580d00503d00640a1214842c0a40300c5028922130b80701e003884080d50011703082c80b080c004110520b80243d04505902c209624101c0c0326803591000305044101564000e981c00d00400c15410b005001324010007200056075038602d0050051251001c5500200046540c0440c60f50100b065030078200000e0501c4007003091000881d50010030291100301d44039806406100310704182c03680000203075010203400c583c170b000d000d42d204020310981c0358405800752121b0f0700d00d82400004c41d8400c01d40c000a400d182d00d2003c400b22210034003a140101d04c9a003111003d0003048204082000814214407040d8450004540201e0718401202c03900c1281c0c114447c0d0600c440d052201c142e00a500a00469200340c44071a01035540504000b00030b480540e0b01c05a070080715000c0e6000a20490407443c1105460404290116002010880c00c070344c0e40d004001140d2001a0150301 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 442436187 1250 442434937 442434947
    0x3091017010b1b0f0d0f05131e0501020609250504090311010b0a120f030302040f0f031203020313060f0204180b03061b04030809030705060d0c0e12210c150106 70
    0xf20a481c04001c1100c0141034600c20703500d0402e88014800c008908074401d4245100c0c0040703450b00540003690319001900c6603040900d1079801480307186080091400011194000300c0d81318820074501c4050421100b6118040100f40b034441c1c00e10005401407000442c140d40d82c0c4c4202d2010b1780c02a17403a40b13042c03d2035416850071100c2400741c5c0d5100740441e0302c04100d000200c0f103201c05500e500c0110f10011380983d20302075001e406140c1242595003d0b520300880c824100d112150100d034014a8000b6050180c104207404900c0181d030902c049081d01c001c0800810030350340101c0c407519041000186042c1d13441e4108402649041d4031a5800c03520f0341d03c801d00c80c0c502080f910b50480101c481100c8100301511000720984558400204114030104490000d42d5047c8001001082c002d0451691002441100c0000300103460081e0041005900320300961304108a0700c0c0e4981081342c00401500c401000c0d488400d8110411402d00700c182000304550b40c04040c01140d01c41130082c4000c2000e941882400780c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 442437437 1250 442436187 442436227
    0x10303021e1f090f05070e0a2003070c050f0106090b031507080601180308070812070c020307140f060c030c07080a0c060f171f050f0303091017010b 65
    0x2002e038000034140201040b02c0700020403500790701c0c1000800103502d140c41c400351140388101a00f54081c0c030030300188440e0900c880301d201c2c0101303e4042006107a003030042c4411140e007a803000313107106090001a0f00540940c114454180c002d40851702d2030003079503c0c2c0a081d5002038010485540d1610100e12050404000d41140f001a20103040c0851524040c02041002c1c000c214904200e0401c0c80c0c4c0c20428030303603014000955040300c00310b0754034032107814084815445486e65034041c1d240c550000712424801c0e1300c2061001d90040c081c1c8141454040c002554035501161a80d00c034004082d806010b990300401080c040c40454003441c0c0301d240000c01641010420740c803040c00c1c0d800031940703100000c2800742e021003991111f0900050002000c40d007269850300e01e1065400356004d42042c000001c20001003860300444449141881a84900500414001405119070150300030f11040300c080c43c10046802c81c54485203006c0c06c4030060b030700821700da800d402c2c2d00110416100241040b40c140b98244001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 442438687 1250 442437437 442437493
    0x10f0b0310180b0c16050c010801060e1f020c04021c051f0504110904020a03090605011205030d0c0516082706030a0906020d0204030b010512010e03040e0a021201030302 74
    0x401e114201c1e000603502941510b0091440d0100c10004510304060000e94150701800c4d508030099101c24608182d56035103060743c89001c50408400020320b240304842d10740c00d03500040d0002c64015212228071521440d2036042c1030a50050030901c020540350383c809890b00860b4901040130a240788000c86044a40141040c5112120020112000c0b41d01843c2801201c1f000c2d076002480380b22000949089001e01d8407040e0b4450300000d070850780c8507455000145030031302170340d03007004107907654019404050400c09004080790000e008066004400d980100c01c8241141491460401c00410364102b09101c2a8110380440010a0005001d6120358603000c9401040c11182d4414130007500040480c00024001405181c85811a0007040069010380c0c2040c046540255100c540b2440d18000168090150300d000720070385111030b202200305008411044a81c40091480c2a0034400e81e00700740700001f4240949503030200104564403510220040c0294003e50103012041d240b1000c1c0c0103d04403c072502 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 442439937 1250 442438687 442438691
    0x19090b03151302040b090a0e1b0711060c030c1b0d0209090109142406100804050c060316021b1507060603140a1a090604080705010905010f0b0310 64
    0x140444048201100c1d0461a410900c403544140000040c40081410304914116800070034001000103019011381344105d4111030f10000e01e0f89500c01e150b0602000c5171b141a12500d014004100000d429000b002ca160141c00c0300040c01e024030380032600c01d50040050500a52002500d45041d000904c030038001c2e0500103040c100c14a603481c002404404120360068420040f410200f0740d070034025407050f103085902020394034103407060394002c43d15010354240d00403604d80c080d20118140c4582d240c040388119802450040002888003040f02c071604001c05c01c0700d40384a20030344682c8503500d1101440c03082d03904482c0043d918210740c6000342441000843c9a90010b200d103880034135030752003000c41240410001440b980758074450130400c0250219034006482c2201d4030035900c14841c070210381e218000b4010089580a03414070040d01d101c60104032544100ca4220001180020300014020400301c0c0c00f540010a105440392640c7c1d00311940070f06110320441c0e503008401c0a6007002d010000c8068450350007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 442441187 1250 442439937 442439939
    0x6090609070e07080a0f09110a0602070b0712090308030901061a0306030d2a05101118240c0606190303050306091e0a060f0504051513020d0c02031909 66
    0x70704410781c0e0190010f4284020719001821800e465030096120f5901b01c00240700303a01c01400c2c03810359a250788107407070300500c00c0030340200c1d2250001509804540c10403424620744a0984c8481d55844c080c11890000c015441c200040426601c40240d40516404000007910320729020121152540304d8002c03264418090080160720382e000b158010122034035061a09007213400340c4e0030324008100280b5058210b40310540740c40504c90001509101e010b141c42080056000f4403483d58024000c50b044a11610060301855000d81042003507903118020b404484041c1c00060098800c240d04404070429640c0d121404004041c0380400b140c2021007420112512003a05580f0001c0051100504039801000401d0115100040320b08004652032188403000c8581e08010a5030406007445100321001d0150612010440c1d160501c1003038002c1c01900c4c0301059940c20401841456039200c28070100301c1e40d0a200300032a04c030030b42c050092000000d034007642ea0b03581302d00001200a07040c0a101380412201c810 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 442442437 1250 442441187 442441199
    0x106081e06010905210706050412060e0309090f090c100210180c060221040b03010504090c150f080a090b040f0c08120c3f1b0609060907 60
    0x4101040c40842000e800c0069031090016101030941e0340c4003079000f0364208200c5c00300c8500800c007014184920030544174519030310f4104031100c0c0581d020384a034a40c0e916060100190540d8410000c0808603400c1c0c07402d2902c0341e80011205041112410385400d0000c041014021081c41610350090003194035103180620000000d544030715122510740d4440c0d503442c461401c160650050303d01d0503032001072500d61076100e100080d1100e1a85654100041c0b0301112001c035a2300e08802c0da01614189180e040c296882c00080102500c0190000d684150a05c00f0108010000d034000c80300014403500c500e1049240540700402d481e000a0000021515144e02d0300000349082c4c00341500582c0000400903070020b43d05060000d09142d03445032001e44100c02c3e0540381b50800c0006405940000401d40b00d885204c017464029079501c11205055200100e0b05942c074050112404503070041d25646031030b090014504010b1641c0e100c0400180702640000b04000c84040100301d036642c8401690060050246841 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 442443687 1250 442442437 442442461
    0x501020d0206010308040b0a020a050115050a0e0103021516021815060c060c0c0f0d02011a0108040b0703050a1e0626030f0901030e06070c03081503120a0504080601031406010608 78
    0x7c000e00000c1000007038401582c1d8400c1001040035900640200003046140036456815110340c49481c4c0610705006000407800c403500a032034102c0750003414492003049162180b95a0b03602000300b101c922980e1000010141e19603185080344840c0c1064a65020b0614a003100c517808002e030502ca00c0b035001081328215202011462030380140210800302d4075130488410f120708007003000911094910610807400200743e41504808000351865444410181c411070044604d450201e8015109400c48404160018402d03030000b41c0c41140c1203400140741e841e207902c1c544103012a00150383c050703403100b8042c4540180c0108110000e845040381d001100817400384581c0303900030503c2c0c0e564044400305085907075034080d07000b003c04e10300c0400030b640c00e81c504880041c00d2142410b01c01e03400150000300003040418003003a0101440b00080090816501069030b42a00758801100001000402e200004000034100031940c0698800c0c081008000211000d4900e0004160700c1101006000320a20085203580 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 442444937 1250 442443687 442443689
    0x430806040b1c050c0612010e01060507030c140f030c0c03060108370b0a0504060f051b07050a0b0c1b0313142b0203060108010c080609041b0306060501020d020601030804 74
    0x2401c2c82c41d200380d119080071800c01d01c912450913001100010186505d19880c001c45041e6105c400174607007181d8031004200c4160140350710040215022002c00c0d000f0032003904101401845407001c0b9411084110401425a00983c00c004e01a034003480482400c2e10f800d000450140c20300c42c00402401c8203035007002000411035034400c04122500f030180405000d050214081c0e9940003504008182080c1500c14024a02250b050311880d184c85885215448203010780c6025149043c0464103600726120b5409171580443c504503000d03c254000c0d580010f00c0d82c5403040c41403540034210358552600c2c0282590400388040405050f41080100c009032406008140d01a1440c500d0018581c0d480080402e003000040214405011038001100140303d580c1229840f07d58401d500b41e41c2181d030799440b00c030700703840ca40518100443c1c241d0340083c049040c41d84009070301a0094082c44030310000100201c0d000311450300152501034540c00300b8891540c0402c00c40000742094801407100d90b00d9a07c030f141031801a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 442446043 1106 442444937 442444969
    0xc080f100b0c2803170408300f07020f06160309051e01020d1a0f01030b1f0507021f0903140307051603111206430806040b 54
    0x41c0312017544c00755900c51003140c2070105122080444042009085c0c604e05005075050303020311413102000c0d000703501c0000228010b0802100090504100081c214010350160f000d2100a0341400d120401035447c034500061300c0740c00b500d4994141f007489005641d9540e0840b204608a92041d8003d1945408ce004100030030400c000b10011000c001706095a8088003407040c0d4089540650071040c0c520400410740b00c105003540c1e05090303a4441000120001510100e88281141040c91f10a2021a02010741542d030500c08a401003c41d001400700401c004100d440914000c0420415101d0b1903501c00c0c103407403a100a900782980018210701c01520400007400300301445e0b00344a0108c01c61810104085e05140da2903040c04180014142d590000060000c5010895031101c100390030718480c0402c1c1c0220b64800000b40c01440200d010f088103228070702d04080301510b65103c1d80c46c070070001c80d = true := by decide +kernel

theorem cover : BRFrame.Cov 442266187 442446043 := by
  have h0 := BRFrame.cov_init 442266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 442266187 ≤ n) (h2 : n < 442446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
