-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3329
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:20:52.404813+00:00
-- url     : https://prove2.me/submissions/79042e41-7fb0-4542-a4eb-f6d46e4f0dca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 598561151 ≤ n < 598741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 598562401 1250 598561151 598561157
    0x1121e03020106080c040b030601062303070201050712020910050f0c07090906060816180e060405060f0114090c1e04091a1512060a0b07150e03120103060c050d0c 71
    0x882c10940d0342c0b81080280d17080300e84550b0600b038900c8015980414000c2c1160719a04048055210141a0900b2500000141092890040204003030f65806400c03035442a9582d40d81c0018407031010b000d51089009104104e908840c2c1d0030135010300a030260005029000038802d070a41050b1703e0380c42e468078220301504114103c43d2100ca18001b001114000c201c05080710601401080302c010000000c2d0003854402e6200c032211024000014070815445903c489500c441901c8581c9000d0801643d6a50155905240001c040c0b000161080303c001d82c40c1791810000340304c0f840a0326110408451904401e01149504180010005e440301c0150014001810180b00110720311120100c04502c4090303501156004244541901c6d41030380e400c50840300b10301040d020001254580d00d0210b01c0001145e00210400e5000055600600c038840c1544d0080394a0203c06000581c00550b616442c0d02440020508480104006100080d00354010750703c550701c6854801e0030001c061408a0a890b0506421008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 598563651 1250 598562401 598562411
    0x80411040216110306070518010e04051f0504060b090105250b01030b01060e01140a030608121308010608120c0f060c04080d0c0816260a111501121e030201 68
    0x20070000c3c0c0322903418041c04402411085c6800381c0301502902c109445200441030002d0300401c207038001c89145260703e001078020001440c1c15900c1d566031180b0380301c2c40000344c101d031400096645040d00601d810754200d0741c011400d101412006440c02d400001c1d45c582030581800314a2500311004481001c2e250055180844551550909a02c0c01d50b040e000300d420882848034a84840e604030b041000300101c03500e01c01c0d940340da60000841c0144070700d420411040c0680305c5580c1c41001a031019101e01061a85602e9145550710f400b9401c035100b80c0704a9403d5000424100000c86095018125582003001640c40900180c21420b04091040701d80b0010201c0200e800e100720070042000c20604621800c042c05036a05507207544020f4015400210403940301e00fa24402004011030032010f00c01c90198000c0101c0c5064107050150790040103104000a42d4203412003100c460001d501d0024040d0030308400c21076420241546105100d2000036540700c222581c1c0d10b44400804a40000c44a01035400050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 598564901 1250 598563651 598563653
    0x50d0602071203150302211f0f0902031b0a0b03070503040b0612071703040902041d070813081b0307060605040b19090b010207051003050108150108030a080411040216 73
    0x1429950038442c0c0b0040610b81800704c1c0c138503160304a505007078079011113188400d55000d01d01c101d5184030400c0d5200b02809a82c49080030f03488800323aa00120b43c0817005c117200101250184d0300032a41c030200041d5042e070150b5a11a40380c0103150011542200c0030f480c0b26022030f10f401c0c2000d065403042e0b840000283d400000c05c014003052006440c2c000780101c46c0100207401034401c10f56640d4881c003541d0120100600d108050050400845005000c051800d640307880e90b81c0100c031030900740700f208251011401c8d00010f107440e20941407644140c44404407075819605644501059405c015410651408480105110b400c1c040010340290781c421071001c10b049003004140801d41d88a000e615000c0d900002d16003034039501c1555818282c0c3c4101d440044d0741003a51004038a000e10551007182c0280003044060700d90f41d415009141625281001c5a566010307080039510001402d1003000d119400c18001800c0081c031905490350003500030030a500c4400c8804000808030380c41000300c00107220075020f80f030f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 598566151 1250 598564901 598564913
    0x3030f0615030f0402040f0b0d1407150206011208040f12021516081602100801060f0e010906030b03070506130801060509061813060507030203010e131119050d060207 73
    0x19801c4012001c201c1c15414107402c50408504081c0000380b02d9500c8400c03500f000a100d40c00a82d88010081034100b010300c0d18100364201c1e4500e50075851150080700000b0941c0300a03032045060030f8642c0e500618560b8648a19807904801180007160011f004110028507116442c1512010f010700840d20400c9000c2841040150359800d81e19030103000c401e200b03000c0c2c91b4034208942d4101c540c2008902e903441d80040802d881540745407200a5014000d02820444103510860741070590700c660300d8100c0708000f50f08040c1c8894003182e448038000f81c0c2d18071060000705c0c483e81150f80068001f0781100c440e1500c41c000100c440e0402c17902491403964550f01084601c909016010003070100703884880642c200300300400e400701c0c402c1d0343c030392400740d848004102800d400210342c85c10190040020040da003080d4000401a41c0700384162541c0002820108110910a031007e00100764060030b0070b00401746e0003084c4003103030b15000c1941d61360041c01680003580d0348039000e0b4072150314814000180d4a00709841c01c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 598567401 1250 598566151 598566169
    0x31b010c030608060105130906060602030901110721080d06060521010f0b07050f0d2d08180a080408010203010504140c3a061404020703020613060e03030f06 69
    0x100105410034004208000002c15132a064034003c0c0c8002542c2c0c0585004000948520b0340020420f41c5014070001e142c55001c0007904049200343e07510040080c01c00201542c944080c0101c1c1d450901c1305000c2c8203481804940c040030940700f44070007400c047c446240c842c201d038002c0e40240003045000901c80d981e244030440054040c0c4110f030b10b520480d4141b02c0680b601c40854042c1413403080d40043c1d038109000c070802410383c07124080c1c03048440f081d2410b60020464078144035180042023440b2000f290350300d20020341403440d038855500d01d41d83d5034070070203540b00e800245180fa0394140078031814600850052001070019000420001d40c0e29454581800121900903812050310f50400c018018000c0b0214201c07841015003504902c2c51641c0c5112008034104040b8004401d04004800e1a01221054200d001100c07000382c4076091300c030103210901060384550400103006070403140004580800c154481d10741e1034020400000e2101400301e84514641c003d4035071044100c0140304000c9185413032640 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 598568651 1250 598567401 598567421
    0x15070e090925060509060d180609021003090b0f04031e020f1b0a0e1b0c0616030b010c020103110415020616020a0309032a12021306080a02010f11031b01 67
    0xe441d012071803c00000c006000d5202d0307040c40340c803000681d60a60910703a0000c0c6011418042825003040c030720b1400000800000b03000300d000703d00910700650303854028455103090b15009040341e00c00b035503800b4142c42288001801203084c03004192052022141d0b03954089148071080d002012a80001000146095000341c108100307002c0080c0b0305401c68407150706d0b42044440c03065a50202d91150301486603640c8000b41e9040c4441404201c80c1d80c0402c001924901503104071140203244500c0741000c4081d9208101d14a0110f071b61190b02100551096115003000459039580a0910b605c1e880b1140c00c0041c900c0c0401c0c0168014020310401036440034092801014a0000b03201100441d43c010b003008103240700150510b4802c03400081401115000404280302d0341440030707901519948000810b42c05080241d000c1c0700000748464513036050b8030482064a011b0b400514030b4080560044408076201081c01081040c0c60003041100c180400c0134110031159104c81e01c266a2520102c0b41c21508841d01d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 598569901 1250 598568651 598568713
    0x105030708070510120515010807020c0901120302011b022505030607030b030102070210030c0f03020f19050f030426030415050a061d100b03040515070e0909 69
    0x2810044038000151032000c451065604c80d0003d010030f0419101001c2400c81c5441c1e450901c800c2085500c00074800034001c00098891681680f50140202e03a2041560340c1c690b0840c0000740180045003090700300550240c0719100100b2040b124480c0320358075030f46103000c0e00d026901c40b03405034280350a5980c0c441844400e00c050b010a0318500030001e50b030b416025000005050f41c0c3c540007440c81d1020740465007800d4014210b000e4510303074601c008000345400a005400200c8a10006660510a000312914681c4030058141803d003001c51340901e003110039141c1c0e42804402c1100806030509400554840c0b4002d000240701a425840b002c118030034a0709510803070701400c00030040042d40541c601500f1685c2840c0010300e950740c40d100803000304003942051030100181120754403085200415035114404d91803442e002c40356951124000c0c0d02041d50000d145800c883c006100e40c00c4000ea82035803101084c90124aa014404081201600103440c0300b541c40d049140030300c1a0030400f0142980c095444a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 598571151 1250 598569901 598569913
    0x8090301180b13030306030203030c060f0a09210c0f110301060905060d1101090503160f050a031e080d09030507030f0503090a0803040609082d0a05070204090501200d05010503 77
    0x142d2411518000104884052030400d0914404e140c402d90000f00034550290480c3d1303481600c1004683c3e00c28046507810a00051200080c00740c000074040d40280d194400c0c1c9a90316000101e402840c0508000e50362420081d541a203480840e034058080c07203040d4099500400c03103412500901d425a0021f0b0040b01c87c143c1088103010700c64441030030718003080f50042d10842d10a10031500403203000200307912103507061065001011038060b840d0703007440031101d0003015125416512001d000352103810b41300288c60380f03080940c1c0c0740d0801d0500304003c4107244940025031800748100e64903421070300703001e8050380000e10104020041540044551130b1610381414424214540418100d40d5800e2061004100c8480803000c9001c010b007507001610403992014034140c0714036404080201d1041280b00c507400300b2a803041040c20031204501152801d100c1c3e6952589080c90341d40900c001b0700f882c0801100e0359988c80c142e8000114003c00c0080300c514031140895650011560000b0a071a0182c012038482d0f0018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 598572401 1250 598571151 598571153
    0x1110f0d0e160506180301110408010e0a030c030f03020904180201080a140105100e03012a11030406030504050c130f0e12070219170d08280b04020d02070809030118 72
    0x242c8000d20444404032522a5100d1031024808420022414020f03095801d104c0542c1c48000f154000d0b00a540001c070080010100f800c1c0000d035151040c0c08060f001c509080c54100210f48220046410100d260401518058040021508444031210f030001c070840001d40040440d80d00100940e00404e42c1c20b000e00c540c80031070f034000703044080601c64644260301d10803075544802d0142500ca90b200000600801ca100100145141c0f201c581c180010100801c103c03080c8925402041d9a05050071940011070900f401c001042e4000d041c00b03402a1814402d5059211844da1800355804a2034002c4038046030621160310b40d407050340c95000d82c2000c140c0000d452082030038842015a0911501211011602d2200035640d013004401500900c2d000807030905501040c1c500007414510082c082c4d030340c240d40da6840403801c944119880b2050741d0064616030407a480190075802c1310f484940018001441c1c000300d00004401ca0b03000030012686004082000b9403586000e2003580b55600340355040c00091801 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 598573651 1250 598572401 598572433
    0x10020307030e010b0109051e0603010b13050303030c07060506120303040614010f21110d0818060301150c0c180f0b030f060403120212010905160f0f03020c01110f0d0e 73
    0x20301496010f01e218822040c4c110510450315a108c0d0000307401d50740d69503195910414150f200346001c10b6007811842c1c00180d2410000200c9100c2d800b49644d05080c5100c0f80e0700d0602904003e130006034080c52410104801103010301c0218041c0c0d22411001414111200e4192103241d41640b001e003c042c06480d040261291f541c02d0503884100e901d601d000f0510b0946442c542400e02c0c41c1d40c03150070040c01064481005640d000504140409000c902c1c03041c01c0c1a400c0080c00e210900824a0720300103489544240d600410440141521480382840d1054503680300081c0202c03803000000f90a81c4560b600c0c40c042c40a445001001c52094001e0045186140c129a940da100584010708101c02c0b2941045120b1b2164140c400f49203441314005500d507510211080075003c1950410b042c910036440307615940d4000d600141404c4040e8440e92501c0110708001e500a4110008020407552101441740a403100320f801407403a41200c3e0480c0341c5030099444504202c86100e410a0041c1d4410703808a460544 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 598574901 1250 598573651 598573667
    0xa1517010e090706030f0609020a2601050607081b061e01090501030c0501050d060b04141201051005041e0509030408150705160620031b1c0506030f10020307030e010b01 74
    0x13086040c040380c0d8035202800800101001d50113800d40791310203e81c0050007076200e5611070011180c1c0900034034140032aa0000c941c180c0a00c9120390185040104c84001008080a44400321100c01800000e140d1040510300f840b030111190030049004082001c04450f6801d046405480401802c000543c11990b0300b80c201c403000d004d0181030080128249510310600d4000c0303000340550300c4a4940711941c4001e40500b0341800c4200611910168500b0301e428501441303020301c44c1d003460342004d03c05898070040c407000380501d40107500400a46402c0c800b0003803860048501511925005550f80d030b00d030440703107820103441d20f100074182350f01c82c02840f44544c0d100056988441c0904800340c80c909151410400a02011034074244080a2401003d0340380c0c0e803400917511590700b12810007509808040540032511032003c070300200c0d401070a1906006115940501d1b84098050100c030340b81c01650000030b01d440346528807c40c0854000041000095041c010b0b0110402401c000f403040481e00d0780068840e02d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 598576151 1250 598574901 598574909
    0x803071a10091e0b10080a0c0302070206031816060c0b0a1b09030c05030732090a020304050c1e0108190204080703020301150303080a0b0a1517010e0907 67
    0x4104035011072003040c6800d001d000140305240c000c110301001002d030199000d590700e000c020014900700d120180c0c1d0a05804480d6101095a07030801c0b241c0e248062180106404001c1742d04141d42445100e00503154100118080e642d910482d450f050151946580b17055010010440307030b94560041000150340101c88255110b44c0b1031610358060b075505403450003c0015030320600b06643c41000e112032480d00200400b058a0191b0030071040161034406141e5590304600c50f048412000150080b04100d00302d10003500c0c1141505030740c3d4003044440010385000c0080e02c140341503aa0006c00e00c4200001004801c001c060169500010312030442502e91007050944a4107040c003404400040380004403444070b4840182c803400454807642c4401030756944690a00003240613603c0c00e10f400300e1018910340c04604817903269440c4001951010318083c05400080c81c07031900445181c03404035060380500519001c03010b032542e5294021a07007202c0700d40175843c10b0748402e151800003c1400b10108001c1042c2c0151 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 598577401 1250 598576151 598576193
    0x2040e040303020d090602041202090703020a050405150d0c020304060908010603020105030a09061d030a021002040b07080a03020409051509070e030d0c110d0302060403200a0b0921090307080307 85
    0x40c0125103c4c1202800e165040204150f01c0080d0101d0b0004a80c40c01c0d14800c0d0003501c1400b5a6554017105504921a003100040400c02c00d003c200502c2ca4010101c0c4060301d00e40c0e50b03480c01d00f14a81c410340140d40703883d800200940c00c0032030180040340c0e03c543d1490003445010024409540313150000b0b8041c0c071019001c04031342a102c0f50f4050a0205a401000301c48649081e0302e44040c800a05007500d940015441d00014000d030b202d5854014614026075003a00d001c2c00f040e9180918a5135910f60a078800031120b024540c09000002d4407800c24800e00348150f0703144040c00a0642540104013032101d0060150341807007002e54100c83c0ca5180000d03020203030141803d24515555843c14085041c052103242c140c1d010500aa6003420594007040c25401507100742c9a18401c030a0511074403e6041d1403a40c002c000f0b41c42003075400c0104824901c0140c1014031304c002e6550400f0400404001208040001c004e071002c0020500c81906080040314010900b88010b50300300b2200b0f82c0c440401030000040d000034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 598578651 1250 598577401 598577407
    0x4050108151c03020124030b010b310f06050304050a0204021606060b09100f0c08251b0f05010503060402030601030b030d0c0501150b0d0e0c0301021303021302040e04030302 76
    0xc0e1981c041c03100109602103850b180401e440d00d4028007900e80383c02d40e2075006148240c00c0c11030504600800c0d041c0d0b680000c0e000c00f26801d2108103200340d0800b40e0100303a40c114111800c1d001d0030030355051915001c0c8030004078404d142069440e20410190364001801c0000400410000c103801044951019604a4000d40d90300300c405c03591041d01c0c0ca0800081e011a1801400080d00301491005000300c07102521201400d04440300c0a85c0c6545540e060000480c0000e0754800015400e44024020b200000d0b4400e01a00710354001c2c0806440d00100c202e602181010101da280780d0080c0c1244018003500c0004c03030361181410b000800501000e0b040030300036900480810041c3c2c0c080e0700040d284000250031500e00360141d40e00182140c0d01c50b88180c50035460a20050112650982e003201a590244400392502601c241c5050040100d00502c0c980c60040071030100e00303950300b030005241c40d211030403869808900710f004201200c0c1c1c5420f860030300103104200c1042500d45070442d45a202d609800d0041e1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 598579901 1250 598578651 598578691
    0x10507050c10020106050303040e1005060a1d0a09090b1e013f03170f0c070209042a140904050a0822090501080d0305070e0d050a0b011409090304050108 67
    0x1005d0000c5411281d818000480c01144202031035440c0c40c410822030088410b07540e17541050100b50301c20100018000784001d070403080d800210391544442d00d18040e2400d00d25562b00d5040f0000c132165510b04880c5190014184440d800d10001c00071141940d044014980b945000e4038071b040e50480450100280c00d03e03192031110191450340c0444050190f1a07c1205407500389402080110101c46040282040201155110340c821245600c91140504a6440d2051070f4081100a40c8000e100710354100130030302507840d0540d23001400d54125030300b1191100e1080c1000b450f5810b6a4000c0c1101c0d00070415541040701243c0002030340d0070344c15000b0300c01c10f503507441803c6000403d0103001c820300d514841d03000b40012204a41d500a60484070608160740000307400d00401c43c2503c5040c0c46c880000760000070701c8410b51504103000300103588690708561b408040ea40d248004000c00342d0002e4060a00100001c0c050b040c02e0000a51040885003d1403802d030030800040d140c401c0c041c00140a0000e41f2241341 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 598581151 1250 598579901 598579903
    0xb0307060c15060f17060103080a08040609022d04091211070801051003060b0108131e0b0a09060c05040e0c030711010911040f06050d06022a1506010507050c1002 71
    0x500c00e4802e00c0038410251640000c6100040c02d2081032a20a01c82c2a5440d8031200415640d040c1e0780d2144a40d854281e200004480320400a0400d0b80c9244d80da0007283c005a0304d03a06030285402080c600c0b65410980d640b16540085088046103005904040c1e952001841d029071403e905e0b81c90741442403038450850074191810040f90005000707580707824184010300003400b4002e012a0310400b8240407050f90f0b000119905201502c4540380c8201800c4c0100000d90a0607441050703d109492001c001d40090326400e03104d500035220041100d644000020900c0224014000c240350b03a400d0207480c10707141000080c40c440008103025095030022000c5840144992003000c010074a000c000c0c450035015050a4595404030340045101d145420000302c1404d480c0d0080a0848a00904040c500c0a0755160803000e075104a40140315800b104c28400c20704001c0d480480c81d0607148100500980040c031103550814070010b091607040c08000e0110724001240068001800c58082c4c80100084c24035510030707 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 598582401 1250 598581151 598581173
    0xa060f061205060a0c0e030307060b040e07060302031008070e0a0207020d0209091b0a060509011101020904050103150513020603041e02091806010909020108010b070816110f040b0307060c 82
    0x940c403440706040c0c10305110000800d0303809184803110401507082c0c040340690b600001e0b001032942541040c00008041006030b4850445010090000705180802c000a64105001c44c0c2094010036070100600c41035141d522621006040e5540040c0545414103118a074007100007400d200b001d40d00055284110f40304c1181d80c440b1a5806841c44446050600d11030b5182c25035000b203e50325495410004401d4a03184104108030f4009448281c9070980600045943c0500b0040300300040d0740800460308140c03128880c0c03038025802442520320304540310030000150348000d812001a5085ca540710000740e55003204507074105501410380668101c10310000c000d20b4030744280195100c0404402c0284d29503411842c020051400000c2d208075a0301e89201804550480c1e41c082d0010b440100184408080f03040200354171400b42ca220781c1480078001e0b240044194021041b544e1041d0030a006401d414281100c0620202c1101c00380509449030002c00c1e5640882d203d20000c00050b010a001070003089410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 598583651 1250 598582401 598582409
    0x307020303160302010b01021c0c0c1a0702030d08041a06120d02330a050903070c0b0a0306121703150406030c051207031a040c081506090907080a060f06 67
    0x756030300c4080c010303040a6003112601c0160055406c05010404545c40441c2c24a40d009071280c0c401510000702c072040341d540922401c11200e00c1c14000b40172501000b034001c145055460202450364665240c0706050a06c1000c83c0c00f041030042490601000600981c0790740421854842000c0190ba02e0000080e10385c007680c120b0b40a2801a03072103090440d40d011480d080c0c600307400413281387c0180c040803c4440c5d0302c00f060140c072107120b001400b061680105820042e002140d48041700e003400711503114241c450718a6800b0383c80000b800144146c003281c040c094240146074a1544035040750454650780c0040880c002c9040403064000001004502e02d0800e12444800c00b41c010841e00d512441c0c040c00c0b20900e40101c5209a04038445082d941100280103c1030720780c0b0416900c20300b50309220f8503250f068040c00884003846106c3e00801c210710108544071601001c42030030091400d0400c24041c03003220103002240c0b00c0c1c01000d002c1c450392000080c40d080c99a0310100c000303070400690244000a00150304 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 598584901 1250 598583651 598583653
    0x23004031b030c080a0b0f0a140c07110f03030d1130090d050a0e010203040e070302030a0e0d020a0308060406090e071406030f0721020406030f0e12040b0c03070203 72
    0x79040918000103203884040d64071407542444000e8445012680c1c5000150000f05000c040340005080000d1041469812403245000880c085c408078520502900340aca451861480c4040f6011091012400c20005e0105040c0da0f8034054828400c0400e469200311a001c2c028a03444952200108070305404845403210303412039070910310710381e40d1054054000c114070b110403401f1140049400c0b00000b1030305048010380794070740710b141000b0b140c010380d0790703c0c001c0d10b42d035065000c2444000380c05030180c080755100385216907005030b613440c004040e0800c032507030411342c00f20b10350101c140b040781c20347c0028895901d15014209a001c50340c0c5e9a0001c4d004e27018a03080402890b003071140c1c1c0170a40310005522029103851b20790300d220004c1c80390103000d4503001c122140003e4440c3c44000c101014082d51928135880d82042a00e119400c5c001c00b0401680e11642c44000040ea40d80e000c5a50101c0500c01c0c029540305c1940070300b989a1180c4140c01c91801b40703000d00c0c003500071300140140c2e540004004a13207006034058 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 598586151 1250 598584901 598584923
    0x70507030305191a011112070b090102040504050a0b01020105090a0c09021308011a090a110d110c060403020609160f0b16050105070909050c0a020a0b18060103051c02300403 76
    0xc076403290f9840b400306080303020810780c480b0002106d1000c101e084644540012a5040010540318000b07042005404400f60b95420440801e96813218041c2c1d40c031072001194003244c0558140002802c451004100e915990071081ea40700c0010b00c400c5001c0d0480d400140c000d6240c0c0138607101c2c49070018032980300c03401c43d602e0301c1031000c5001040041118208411205210341da40d41450610a50307440310960400107a080105980c07441c0e40342e2140c030441c0b18003000036007002080390510b490050180ca0a5001d64441c004200d0b51600410845042601e582d2103440321900e8101c01d00303903040460260420300f1a001c1744451054001064066086411100900c06410b000c0c1028220318554001c175400141003c00041c901600c10b801c844801030540d008010410450300c90b0110000060182400040305080410310340c2010400700d400f85000300003030b00d2100e401c009045045003088088806540008815544a091400724012600710018140c0b10401e220205600301d841503800080c4200030003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 598587401 1250 598586151 598586171
    0x90d0305070314180606060a0906080403141803010c030213090902150d0c090b0901020d030c09051801050301150e010b0c100501080a0201090f050604030206071403190e0907050703030519 82
    0x14080c1d00e8001c400201740d0307485d0749402c424000c0600c80c2c4c0707035070308040381c4484801c1207854071800d01107138805e002e4507003100360282c8426402d00680c822445500c0c4101481c00101d420f16007072249000301080d5003000c40c81d0001004121a01c17100b14401c8900c1290b95030120005d5484504d90500c11480c3d256100b1794650310083c000c0c000300b0085229900240d6651070100300c8540e00030032290300b844141c005004004180e0701c1107014281c106c403200200005440c000556440341e1080594201043d203030140c05604060902d800c54414901040c0c400b03900110800c005040300200d030303040d1110b40103690303603a10180700d03040d01c0c0010107a00f880c1d0040c9000000500c4902c081041511180700b43e8508001c1d030758850264070700d103170705010300c5a1142c01040104014a01170008004041c0b04054034071106580c00303210f40c155002441d00b002c43c8001915a41c44403540125010404081200c040c60b16040c1800c0c020010b000f401001400e140c0c0d00e501281c1000500c072010310780c207e440c0505020030319030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 598588651 1250 598587401 598587421
    0xb1b0f0d060602060103080d020d090204061401180b1204060e0703200a03080a0f021608012a0806010e040f1e0c08010e0406180b04060204050a060503090d0305070314 73
    0x200118041500d49011404600d01e0701c0460340c01e0480741c112a4840c181071042240e10025402540d525022654980c5c4c000c0068071903000d044001c1c001d201d5207143d0203015000240103901d584041c0d0aa20001e0042400741410780d90946805020711500502c0694039450018010540c01510381803521075210000204006000c02001c401301e5000005803014a403400e000364a001400001c0c510344052150340105c0b4400e102e000d04112081c8100c40e4070b001c4044111001441503000040346035142c0100011800e5907650400b481400e00d08410100240051f0092030360402074803450400c1061104071400e0f940d17641000ac003005400c442040342a0a00341050003010b0300005880f41d80707007400005d01c0030f00e0165010398102e03800c5061000c0b5030354541d92010000c00c0c2a66072500000c0c014403180d40401c02d440350540c131486c030580340180e8941c104000c00c200300c60264049400c1010030800c00a00340d4011a03124680145030901007503e44420030140c0c098403c0342021010134076003808004182e02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 598589901 1250 598588651 598588657
    0x42607060e06040c0b0703020c0415050d0b0901050603070e070503040c0302120604020f0a0501270f0605130e070e0120030d090614060303030c0a05120702010f24030b1b0f 75
    0x100c02c800b41e44c034080c0d031540169074034007030010f010340940c02c1780c41d0492080c2426080390034600c03440c0404404c0d8079164000115108003214050b510061514104080c0396030074800c00d45c01c40ca0441c01004100e10341410f9120100000304034400304100480400c0c1003294403c0d424000d164014021046160314004807030366008115001d0f03119410200c00450b060038003031060030544806039620f654409186119205c0642d08001e40006920211000a1040b1a43d010400600025511141d99a2142852131801c060b55000300c0c100070b03020001e21100b80d400c1120b400c83c0503002e003040c01d114150004001e00303e17540c00201070301a010010b0700700c0340c48150764001e012461043c0c204001100341480c910800d02c20464405130190300400200d9880b010b400003520030f2806604d0454a4000001ea804a8619041e104040035079110140d08980d01e00f18080d0b0541d050035005642d9103031103a46030300071002d0401d12002e400904090f011070f4540d4001c2004098400c0111001da41d82d030001c0480e025154 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 598591151 1250 598589901 598589903
    0x20f070203070e060303040902091c050d140a091202030703080a030c11060412180911210601050d0b1801030f0203060106080f041e02031e0114042607060e0604 70
    0x1010b2103402041c18421202240e010310300240c002c50405060050000003540200c10050b40070070343c003136034442108481c99650210361003040030f040d03030802c500000f409003542da034000000408140000703035506e98401100403c0752070b1036014180464460003c03038240750061f000541000400594072021641581080d0501103a41e9520295a00c160280e07580f42c00040e140144049114a1002442442090584c017641c0c0b0f540c1c0b10a4640c1d6480f082c080440304c40c94008901c881c008a401d002803007245401c0c01c00316103401d030500c91a00d00400020305600c2400c80e00d03c2003aa0300c200c0740200342c80d6102c0f030141c4210804102c00d09540c40c1d042c505a000014130040b4441e2140a0000c598640314050481c001d03080d81d8103240058075070795110240d1141c01095145030b04007011204015035002c210b201020403d080c00c4609208014034101c0c00d664844261a0740b01c3c84d000c0501002036899038510110b00349503801014090002a04910703070348910309004d4106030400d80410041c40c00421000e00032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 598592401 1250 598591151 598591153
    0x4063503310b13060903052508030d09060507050a091a04080624010c350304031215030503030c0c03040e0108072c0a1d0f01060e06010810090b0102010f020f070203 72
    0x1c2c95864000715607102650000400942064945903002da411005030b800030300234042041d6416440f0352000340b641d0080d4060075282510b80e44410f0910181d481041d40240b500d15000d0314005800c000608054080d101e20310051031032400c0c540e4183d600e0000d9601424104040d109207041440e40c40c6200d045c03a2100c9050203484203030400c4c1d6903010303050b00b00322581d0001040b076488400c0b0105840039046181e200b0320515500c00b000266030101c00c000c51095200c0d40b1840b1030034051403012001c40d481000c812031141c141a4060001c1200003080d20750000401d451940c2c0c883c6038409407402c5001d01e03072103030319a443d0b41c000100351740c0030104040d070680c1d9041546001114140500c140d40204082000320959400c50101c0d0500c02c2540100d0300d0301c460410024481407404210741c0c5450121081c83c440d90755542000e10134400107085054000809190484983c20280540c2c02c005805116055820b640d480911659034004e4206c618440942c03141103480300840c24045205070321a500491007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 598593651 1250 598592401 598592437
    0xf0e06040506160909051314010213050a0f030b130b04080d0509010b0901050f0301090803191d0d0f0201091b0806091c0e0301060504063503310b 64
    0x180940d0f03524424250210790354121070b140c940481c0500828024080c0300700d4049180c0a000400e003103148103690340701a5400143d5441c51441c042c1030b00d6020350403040c0700e0401b001d0100051031070810782000f641c2e0000c00001c07050b00d0f070320b040c0c6507403002d600301c01007000d40c040040209208200025240c031402c440303400e00050380e418110038200c54144182c1680700485200500a905000111009500c00540000380940c901d403200c003401c1d0001c68074a11038001001c1814009030312402600c00c1110606c0fa940c00710244000440c0d1100301e0402e003503081002c2e024003c12123030b04c01d410140595400044803592140e0724100d1160004140c000c5c1c00703452080b0300201c3c3c1c170000300003441114045004100c00a0003401c0104488000500c62807550541d269000460959a0f512900f40140310380c03400101c40480999a424000e24500d4101780c0c62103855011140c0a5808400c580d503450400341025000324080c50f0b44070500b103a1501250240c1030094000c991105e8410040050318080707807039012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 598594901 1250 598593651 598593661
    0x50615060c1e1207030807080c0c1204050102070909020603070509030a060204080a0209150102060106050c010209120c100c03080406050a0615030518120d1109060708070c05010504270f0e06040506 86
    0x400f0344140d180041c00546200009619584680245500499299241ca00d01400c10103007500c1c01c400310381c82e0741032a080020100311a613010410400100741c40030080c040307041c4a400180071400000c00d00d0092107400102c40300a541e0038491158215407100c0b08545a0340c1b33492105a490341c100760200c0c0141c4540c4042030031220644014000c85105a00403c8182e081440455040d080307015550130030740d020301002134640d4403640030504c89041000103140551901c0e041102c0b0b406402c2c0b41606008500521502007980310040a50183e080355001c02c00f134a400070710000900300741c1c2c000e90b1801c0a1080525045034581c00c005c0c0202c080c2c01c90b4001403400600d0443d01c46400e00b0798080d95040803c041711100d004c54101540c06510304220905000130074002c41c00b076500c072000484040c000002d6800c01c202d10501680060070b428030b0094102030400501686009030001c100c03406d80003031850001c43c9041904a440c00003030051041c80214980c1118981e11407040d942101c0d00d0041c200092 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 598596151 1250 598594901 598594933
    0xc060c0a0512030f0a18030e04020c0717010f1b110718020c07052704110904030503041704260106091802010909021204141603081c0603050615060c1e 66
    0x80e540c061b11034104c1c03640628503507081d41d40c24000d40402c2e0304181c0901c001104078405010340707002418140141c0b401da16049440a00311607040c19020201d5292812285984c0c11140107500074500500703002c0da12007030b0030341c6140c0b40664a41c0444240d40c43d926900c0701c0191990050450800500100c03032003d5150400c1040e03008405480b200403071100600c943c9620803040c03001c2e80050107420b034810004c000c0800b04401502c2220207a01054000091008025800350100000c4904000b501c4c20141001194052104150b021103110042d80807038040c82c1401394007200c0201200d810410141070041c407c100841c1c031001d0305078081111750078001141c42c068021a540407800f8040740a0a41d200c1c0d407207008841c8003241d000510700c140b40100c2c901c20380218040003c0e60140d104940c44840c042d100080d0110b0392550541810704080007000050380014619030040280c200700c45080107a20b01040c2d1500441e00b000680344950107450b031080300c0450f2010503802260098404035102d1000742 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 598597401 1250 598596151 598596161
    0x60a06140109060e1e0901170f060402060d0f2a090522090c0e04030207032a06140d1407020c0d050303061003020d021315020f0c060c0a0512030f0a 65
    0x603c0800c0310b40000018501e030540a500100310b001496036030100c514000708990800c26048500160343c80f042c4020114000c0181c00c80146024004100303078640360380072840c180a0703000e002c4401a180c2e0001d246001d526002054646c010500421042d0000e50f41004c000c20544003500c0030a0700040c02080e070703081c0303540c115440324012200d2540706080105094001e181a840a4444190350350001c0b40d10b402c40800c041c0518000da00030302e0158190300f00302100300320141e00320455004030035444140036603180d26507040f5583c0f801d00f51810080303100842c55a20501c0000d2551500d01401303c1052505152040d005c1c40103a8201d0b1000c10700301040c00800000703010050500ea00500000c0c1440c074201058846c0031001e8070703001d030509603940045016608200ca24580005c0d035a0000d1020150301c010504408503948000c2481c1d8082036004c503281c2020fa0140c40c01064001000c2072a13010400803c945203038030a00701d0f0a01c00f01c481e00c01c4071075002640c0d4200200300030750200d070002085010f2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 598598651 1250 598597401 598597409
    0x3030606031515050f0a05030108010b0a051e030705030a030206090105070e0a09180206030a0c0f050316080c0903160906050409200a03200405090601060e060d0e060a06140109 77
    0x59506a01c0c03c20803501c0c0707502044005071080050400004c68800c0494020300896040c1d521115129418510340d10700350b070405a90140204284001000f0170380d41e4100c82d8107020074241000104141d0031010030b0901246800084e0544a485100410590700103003ea204842100007007015480d01d58040701c403410303001f5009501410340e41003809103801c070f41e0002002d40700c00500c070380503c80e4950215005820440704060001e036100e03000d44d040ca400c540c2551404d602071511a1452601d4580c040d541d11407811200c041289035000980301d580014102c40d10b100c002011a401160902031003c0310b0500c42c0521050541482d6001943e81800c0c0103042d4801e61054070007144800c28010f0300ca166442d4460242d00840c0c7d1080003010403120f0303092440008540741d4000542c02c120b02404103840c000340805110b9444040100a099030009062000038000c4441940c0d1300007801d0b102000d44003030003000c5214003500c41884a210269401801158048010701c08070080400042d952642c003403003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 598599901 1250 598598651 598598681
    0xc0b150f01110106080105011d1e28090602030601110c0108010b09030a0609030305060103200708300103150c0e090703090807050c0108060d050a080f250303060603 72
    0x10300003560203000c0d000850041c1000014840d507541d1049425510283d02c0701c401c10b00a09056030a0506c22a00380e540b151025100c00210750350b510001221800c01001440703070444102d0b001c69248001c50300e00d11080e1182c5414444482d8a003001802540241c50360703400300e000003d00800c10032000c101921800740584171a009a0710300544001d61740d0201104951501408100c580000c40c68400c02018a0081c0e0700041c2c41e02c2d00c0800503080720042d0074040c03000b036182d0205000d009042d4049980c45035000320340540b40d1010071041c1c08114107a4075440700a00ca0b00d2002282c820300c07a00014100da016240c0300c0038644450056004880c40b6034100030014104641d150380c00c0c10802c146030b81207174491070009000e8680d40c80305040c0760012123040740c01c3d410450304000c041d83c0c00580103030856821110214099443d6541581c3c4042004004041c40408100100350825200940d04400039018030301766002c0140611a81c2ca0190400803000700349000008540c1d10f210384200282ca40c2c0c040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 598601151 1250 598599901 598599919
    0x105090a05030a030506040b10020a06111c270b040201080a050f070c020a090c02030301051f02030a0c08043803090a030c0203030f0406020604050106060509010e04020919060c0b15 79
    0x252041340940b000500064102e80c40d000d10100715147e611011413a14030a60251440c038155280c5801540d0000a100304040d00a10400036800d0f24140f9415589010450016401c900214003985d919035140c100c0c4000000d008018060000c00030b4030b0303481a403003660ac103c0030350759008030071080310000d0b0380c0404400d040f0400035072894001e6801d032402500007095052166038460240701958410741000005030004001000a402d1030365003040900c1101c007a0300308010b20309000075501e024418444080040b101203e40c20b200f59181210003403e41615480c0340c441d400b16641c4109460341801031581d00042c890302c1400e614250669006001200c003074001403005480c100e4864550a07016a4980010402c5110480013440104001e0010b50094500c511f0142081400c40c0c4070395004200b405030401100741240c6e030003062121100c604440c0141ca400c40c14012803259001104814800035580901146840d001085044110700c030701640c540c56038070a074000306822a0130740d01540101140d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 598602401 1250 598601151 598601167
    0x9030c07080a1e0629091303211e0c021005090714010e040f06060207121101050d020c010c021e07230612010e010e0f060f06090a05061b0105090a0503 66
    0x440303d008450300404011035584491001d40700c0c0481c1400082c0e84015001c10400c00906050302e000d070307000c41003101e840300503001d60b140a0160040640c44503401603940c422a180041541d106d51300e9294041c004c030780312074108507684004048040d215009482481d00b800c6410a60380a078074895145007014100c2145403000c00300c024084008880e05005e000081e03500c1c2900c540c410f0482184080300c0220b041450414082d040051700c0d001315405558003140c0d903010500103003150065500038605295241e0038407160710000c2c002c00c520208154201110020702660016840c1d507c148005ca2710038040080130861030783c0300c0140c0700700010700c2070751500440d0b02c41d0300191202c020740700a40f03241c0c40d04d984140098000c180903040708d5404206000180440b840884080b43d100e201c050050166040c90340001d00481c40380400b4611a1100299080306034640190700350050070060003043d120305240032500d940c20101140e8400541c030b4040018110440018070300c0241e80c1200165180032a5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 598603651 1250 598602401 598602443
    0x70e0f0a030312091a0601113d14091c0e04020702010507080309101401030317040501060f091d03042102060f030103030507031e0516140609030c07080a 67
    0x5074126083c6040d61000c002c00410141d0384640f04240c240c141d5903103d0310340400050801c0410840c640e00542c0030035017010f5a4030b40080a03145070500001e0020504070b41c640b4204400d84032280c002d40442c14000c104050f0f007088407003e8011400141551800c0b10b56030a40c60142c00e10510030f1000a0440000201c1070500350f00030280240107140040c90030000ea141d40c01c0684c03042d5400c10755507000000c0326512840d14442c0c1400645100910380ba25491030300d00078140c610f540c4001001035a0b01d000715082080952003c00109440d4002000300c1d943d510b510802420701c0880b03088903071403140c1645200503020045038240c56603510b01054881d0300c00e555082082c44184102c1e04010104020780001d02c200010f14029031107551015910740140c54000c0006034203a2103c409030317920600003009241c000c030640b00103803480c00c03030510231400350b080025404590741c10f01c2240340110b109110407130310040028a882108101200c2449580d4083c980d507030200c0c2c1d50b002e00402e058060703402117000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 598604901 1250 598603651 598603667
    0xf110603060307062d080406060909020f0405070314010f06021e120d0f0501180b2d0f0414011a130504180605010603060503010e0613020603060d08040e070e0f0a0303 73
    0x84c0700702903c0c17080c1c40300d61416583c80c0c048075103200c08158440108010801c0340e004070f00252030846010300c41f4131640c0d404503681105040c4180c0c440c0ba160310004881038443d0b4030a440c3d003103620b06050740030f580d9840b442820281c24000c210050241078490100041c0744001c00f907007800c141000302a94001c0d80f0600d07101e504040c0480d1072aa0f00c84007000a0f140d01402964082d00d401d500303000c00005500ca8000445401d80070403406000e1b00079501140440000c0001e146030210850109000c403e00000b6800444024140f580035280490301140c0c1d003a400741c22810703a07000b022042c8100f030a00c0100300030307409010b0346404145510942484103003001c0d04003441134150310000306d54000c025031f01d0300c1c16100242c00010000f03035202005c000c0c03840c0900420000141080250003d400c00c040c07074404003541050080c0c09008000040380e40740e2120b0343c02895841e00b00c0b15203500c41c1e49803520300d1a0302409032454400a04008800c0d20b50303203412101c48640345030041880d200e40d80755540c1540c50f00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 598606151 1250 598604901 598604927
    0x1002060f060405190207030e0406090e100b010507021f0305131e14011404051006030b011406040305120903070f15030914010906061e050105070b09030f070f11060306030706 76
    0x2e191282c581385a482180040e1140611a8072a24010304902c0c00f40070490781c480c0c0c00b82801d141801c98803e4080004108034001d200c100c80041001500440141c525110b01c0344c0094000907040800c44003814140b02c0c2000d0703540b03d40e03028029526200c1409044465139180640001e40e0302e41c020b40701c0401c424840c1d80181c0f09000c00001d007014031200c2821101202d00d81196205554104000c2000c14850645649682c071400c02080742591542c201549050260340c516440503070400e43d10745e40b81001d030380045502008072002164065882c1c200d80d08400d51480c041d01c503040f00828154410401c2605541c03402412201c902442c80042300580890101598201c40790300700414583c6007030048000b0307180518404140389203001d1ba800c001700c0c06100380400c0d491004500344800d85e031242c110346000c0d07001080384540e6220800ca050442c41850707201844410001502c0c01089546003251504602505072401c40409a505010f0a84411140950300d03802400b400d210950140811103808 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 598607401 1250 598606151 598606171
    0x610051e0c0606090a1b140f0c0304030b06090c0d02160c080c0a0b04080703020d0501110d1d3c06010806190c0504180b0a0902091002060f060405 64
    0x3503264a0458852030340000060042608a6402c2121504182e240c142e0840c5041004100e4985403c2c40040301501d2800c18400700055645560744801040d016501c00034150208180c0e07440300d201c0090703a680e11603c0f04650340808180051424504182c2481c070600740000454a41900696280001d41c0f0141100803200d01c0540c804011a0001745018041c02031140103000111562007044004841c40c0d014403981d180800c018881c00602140f040c0031281d043d5548030f1090450305c2e2580c094501880940c0e1405e0020502e4181c0c203142d070300034a90b0189001280d01001d20440a503d0b210555400141301c5841c01c55115068220202071140850080c080c840e811001000d50207400c1c02c9007070707100b410300783d000c43d062001c460010360b18119910450107040040c003442c070740050128000d134441c6d00c1840201c0c0212009801d03290704030680804000300800c041c141c90b01d091400942080c83c0403802040b040c1c2003400c015000003a03480c0100c5954814001036a20482000f0140100603e80340700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 598608651 1250 598607401 598607437
    0x60702190807021906080601020c0f0d0f020d080a0c020f0924060c0f0105040606080d121d01020a030e01181a040c030f08030103030f0903080a2d020c0f09061005 71
    0xc000954104d0405000d60303130b50710031050034060002890b2810a00701580311f0350340c07000c40450982d1004d50200065038440551640c89184e800000e400d01001c0304080c0481c10001105049550302c5031003d03444510895146002103520400d210751218111400d00d0a00c00014144420305511080b21100c0b0344002e00030352802c011101458100386543d1803441d0103a446405003c00c00c0307410b02404002d0040300c4001c1c1031042c2510710083c42a04d48801000b0315a41d503204404c40707901c0c40ca480409160350f81c0025956003014010040081c28030390503c1449510300b804c01c5419003241c0c06844525900580c0fa1892030904c1d00103142c0000c8050401c881e00141c3e0140003000070f15080303510303a00710300940d003598503503140d0b04016048a0080c45c0e6031040000102c02803000895240a564070400d481c64002e0403000c4e000c0c2c0d2501c04650501c1c040718010400c0c119601d2181d40051a502220800e9900480c0346100303c05200417030310f06a41d03141d40414103d1040c5200c0c0e10600240825008044010036 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 598609901 1250 598608651 598608679
    0x2090109050f0a05420f0105040b0a180e0708070f0e1e0a12110d020105030c09040b09010f03060e030307021e030702150703110a020303031f030c090204060206070219080702 76
    0x141001700c04a1640c190340b09803101c000505050702540034185025124104600e48000000340345100d5070241d40c0c608031010a0b12101309129140c0c80d07825034860003040103440d894101000103014100e4070240014441d400003400039100e80d4640c0010510f50302c0384020240d0303038410010b0303c40c00c1007901d18855002c0e2020741c0c81c80c0d071108e903404010195012464200354050502e4070000405800d41406800344150940c01070340e01400312540201c41054880e1a428400000303000303006880761181e07120229a00220300d50300e02d10b2112040ba84600010028007480b0a0300d80c0d00c0c2e010441d101000b44c3c01c1941011184a08140512841c460710405d4a2074881c6030b5002501c45e10510b1005c405101c00410b00e0800c141d009106409501e00003002022001800c1d80025503e10004100300100d025040224000c00e0050b104034000c0c5500182090307405854801c100000e4001d445500e0043c0b0840011500c424008600c4a020a00c0000b1116444110b030b1500b08040c0d0000c0710480e00031410031000c074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 598611151 1250 598609901 598609951
    0x30a08031f06020c150d060f0303140304050312060418080309010f0b090403050307050f07110117130618051207020a050d0c03031409041a040c0311090d170301090902090109050f0a05 80
    0x1001412101da02c0c23524031410340c01c00414a4070f500492465400c010424040030038000410b8540d0302c1000700c25034981755503e902003005082e48411080865a0800b01c00d0100001d1030061440340d02c8082c02040203980c0d00240700305803200c002840d9040b90782003000c50040b911030401980e0003a41410801e2400004903a614036607031203143c0650742c200500c10005150340e80a03020001c1c94140a81c00701041c142076230000014000500300405240d40d481c40d2110000c115101c00e90031039080815555086000400d000c601da01448040b0710944e2660030201d85031405035840303120190008112a80c1c04d040d550203031190b43c00346052018001090114207040c1d44c8a018240c4c00c0c011508403180800d101c04180b00540781516004028981006003d0348019202000d0380c814010482c1d61241049460401a0030b080103820308000c2d15070004008a55101a9080040d5013407080d40c40405036aa101070355030817541c6c00d0300d00a41d100f0f03425000c543e4107030349a0400c40d00010356940c1c1035000c02500c2440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 598612401 1250 598611151 598611161
    0xa0b180a12090306060b040803031314070306140c03190e0c0a2301021b1909060b130503030304120c17030901061802120c030411030a08031f06020c150d 67
    0x100e0002c1c22200c014800c0100030301410008090b89801c84d400e1504004500740c581c04018003440700b030380c00d040448090100856211540f4085982501c000070b0305c034103161003e4000c400d190400884028080b0741d0440e805400c481c450021078640180141d08200903070054080508540010f11641156110680d500542c02005100d980c0c0400203a00300403030450683d40b0f0882c40c4c40d05540002c459410b984002c1480a20484000c44003151042000346003e045c0c8080341d0400110585003140200705490360740d00030f14201c400c400342e000140c0d9450042554920003201e005000b6184100203106860213000f001e030407e031040075019244050030a40340c416400c200e800c125980c0d11050200000d0080a42110342980c00c01c07010361524510b011503c0c84030342c02501d000b88500c1c1c00000074080c002030381da514240d0701004040d01d0844115081c50300d0700c1c0c0c0060740e115010340101c403114005155190a001d003203c0c45500038020103a14001001302400034421104041c000c03c22029403000d2661207a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 598613651 1250 598612401 598612433
    0x6100509042406110a0c120f0c14030c010201060513020a05160f0507080610050d151b09050102030f0a080702030706140f01050105030402130f2307090b0304050601051005190305060405090a0b180a 86
    0xad0b20118082080c00c15240c00d0580c00014156403403d4014082d0b51100340701c1040d048104680540c4c0c0b0083c07040b0032107641c4205561a4041408040524104582d4010390038143d0300503030854075029142c4c041d154507804160f07010092991030700c004104034104175907810710060207800071040382c1c141d4107591429541280780d0410034042881150f0001500a036942000c4d0600307100070b606101c4900204203280c49900084030a0181003400207001c030b4420003c40301c80c254025030038405e15062148040c10500161001c00c12120b507040041035651059090300d103d190018504a42d00c10864806001030400e4921301d80e03910f8460503050302c4000c040034580c5a1759440344a10032907150900e001040080c1d550000e524207013080003800049a000141103055801c100c1d03000003207003d031000a84162141217a00c00e003c21101c0d101c0801190950f00986c89281c0a88080c40282d88001c1001d45a06000704000c182030810f401048400720750120283c0041750400407280200a41d07140c90509410b8020703 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 598614901 1250 598613651 598613669
    0x5070b0f091903020301240603020a0c1419030c060507111b03070b1305030c2d180a0e0c0f1806130203090a170306100509042406110a0c120f0c 63
    0x345513021041c1f0a451038005200a00c1c00f18100f02031050000e009071040c0c50060290300c40036590082d09407081c013540600030100e201c18500d03c2758610340a032000825810542d0340526200c0010391840c050351003170310303010384e01c4002e0020000b00f030040d0319504458540d032580600c40c400000c0750682d500e000900415001c039043d41011403801e002c00d0318000402c02846e02501030580801d180c04800180345034101c400c0c101c8a8242440d42001c1807003501150202805904400140402a000e950200c2924140a42519100070440080c00134451090101e41e411502d0b403040c69406154003420303541c00c00001410044482e841c450340105a800550342e000702a04000c54400801c401c8440e4400c1c1d0031000d03080e036811346c50007000240b030802041c041c24090102c0010702a030f2a030340d20762145800b0079004c142400d443ca802015028942898040c11300412b0703840700d003440030a40c0011045070890f070006a80d06d03010f00300070f0b601e51980c01d1001f08841813400003440300001403c04e950080505480030b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 598616151 1250 598614901 598614941
    0x40c080d032403020607151b030b040e0705030615030f0304090606230417010e06040c05010908160b130e130308061f051c09050a05070b0f091903020301 67
    0x1840d0440c500145611140000700648042005880c3c0e90f040c0d61b540d5401c495815074607109064041d001d400c0c0900403104911007610500c0d21130350564072004814030180d50410802c141c001d0304070754a82d8207000e81da50550103880010924011340e03a00342404a400360a0310903440c06841c812b440c5030015003010040d541c40303900034448164071450700c41d5038002180269404c00c10058824456100d1801a110f1710540390741c0001d2030010075006020010552412610603241170705224074041c000e0300515002582d5032000140c003450000c0c401c8481c6c684550101d4100e0303e480201c800940c0300c0ca1a21a030a0f02c5c40c2000035000c400d44c0929841500301854401002c05c4615004140300c00083c080c0307100702d2154031a11b40080d0000c40c0f00120301500d040056130f440204020000000c0d951000c116900d050038460400c02c900841d0345a4182c1c40b410440c6c40307070b9481318a598068000c800000812000c00e01092501d450520010b040d12900702e0002d8407207a40b25008242904e1110045d4904034240b6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 598617401 1250 598616151 598616171
    0x628031506060f0207030f08090411180f120c100c0c0b090f0604080d230403080706050f06090f0a021b010207110f061605030d0501060f020c0301050f0f040c080d03 72
    0x12030102d4040403c50320107411124110382e150410011a140040c055100100c3c60f510b41e40c8490707011000660201c4070071912000596120034003c036181e030b80103000d500c00b5081d0b00114245007030510003100d18040640310200094041c00f000c0841440200e00300075403c00b0060214200c807800070701a1602222050703032a038204043c005806841c1b44240e00801e01044100482c007804a50760f11f40304104d03e80b625000079400000b00707105c1074443c12000c45000004e400002c200003440202400342c840d0005001035030301d40d0071245100c2421104680c11480c2c2c84e0026000001c0640903642c064151403005042440d030080e501d0045040429034a0b03507a41c000348500900400c1c860f00c44c03503000c0813141a500072540e000462801d0080110070407580c540e6841c480100001401a1032007a5041c40c0300f0881ca41e0b4510008044400261015016001d0390507140c000d42018041d041c440c1c2d000305804042a12088950815808010016107107842d09480104103002c0900074002006025900410b14002e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 598618651 1250 598617401 598617407
    0x1b0c100c200304030b0109020a11030a03020c06060d051c1803060606020c190b0906041203020303010512010b010207061215171006260304030b0705030f070305062803150606 76
    0x7030904035210540c018401000001c9100f40124150780001c5400342c2c0b0740300d280109440c900d40d04180702945010100314103049590560140c407810b50480b08986554462070140051056005d501a0a541100002c00a084000c00000004962600c0c0846074410b04100301c06800039150007c503406a00c5690803c0981e0303042028100c800c2d021281e0101c40c0d40343d005a00c085c4009403159540440e03000c83e044c0042c1da150815a8002d10301e40044113804205490025125030007402410300c141d500306c6c184029000d05101740d840020301a0001d280c8079003410b00c19030366000d083e80c8100c80591200e90035081080b1007178019000b0b2803205140403840c004100b50f80d040100004802400c98a1f01800f00250f1400151410032180700c001020607080624000c14154403d40d08060944000c1d5010701031070690040046108101030000203801d40c41c4c003542101918401da513860b500141c00c042401400d400c120081140303006041d8822805030b543e83d15131141c1204010b1041c500c0c1c2d91103000308041c6030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 598619901 1250 598618651 598618697
    0x30807080603060105040b1201090c06020607210504020d0f050a030327080a0314070e0a120b06041104080706120b0d0503120a1104140103060501081b0c100c 69
    0x55800e0014480c64103a0200343e0700c181c144600e0303110300c2d00d4441820054940c4c2d4803045003e078881c4004c1c4103003601800d040d8175070a21031160707400600ca000000b841040c82030503a50754000c0f0310309041d200c1044e03d005042c041c0601403c181da020044c040c0132070004944144504c3d0342e6100301e000d400104040e01b005001c859140c014400320b03003410a500000e500e8100344050381c4076844210540c403480401000c4005011191040c3d17103071001030050003402c0790402002c0c81e10204c112078281d910b1382c91704075040c02410a8000100b42c808008003241c20b13072030603820611021000d1584103092a541b04441307490003041d0b504c00c07c04550b03035041c07245410340c40d40284907190005559070100c1c011641d484c150340f48100c411004401072081c01195400310290400307640b0070749410840740c43c2d80c0c480303004d50205404813040c680880d1601d14001000d5000d01c84607449080c16081400d0554080e4014005030351025000d04654043e5100700b00d00302d42d207031040d441c60749030607514102e410340c120202c1c0319030503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 598621151 1250 598619901 598619911
    0x607052a010e0601050909030d0e03070f03210c1b11030d0c0b01050402090315070e04060f06020d1e0318021804050607031802010e01020a0b0108011a060705031e040902030f040308 79
    0x1b5113480407c040c40701c00000b11003000d0b10900c0b001481c0c1440000d124118012004000c02030741d5084960360038980c1c012030046112410000400d1100e0f0030302e10040840700c03516521004140c0022010541c1001d56211300c00460081d042003803011400b030b000034289511904008041101d1403130150034407142408c56405000c0580e011450301c07840c000060764600c48616000250f222220000b00d40601c100602c2d586820003a1040c0183d41e19003606213000c0302180201001031080140005140b8031440009240c00101044400c01c0091288200e024001d49841480118110140d040068680e580d00c1031090a00ea040030910382814034203075007000d101500328010941090480c0c050b480400a082c95001d509007041c1090710512401030b82840c503e00c0001c1d02c10420200001032a02064100c0e46283c40c00b40352803800c807621441080814061040b000c0e0943d4418410440001c11002c00b00042200c00c03c40603040c9076403811a80c003a6441160341820403c0081c00344010503402001141d000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 598622401 1250 598621151 598621159
    0x9050f2b021e0f070803090d1101110105010603020405041a0109182310150909180614190903051204111c0c120201050d1d0a0308270607052a010e060105 67
    0x800d502034005140c80c88c8122001e00700c290308400700031440e1f000c0c640c04125064240000d001540e074910b030140080d00248074590140e030420f0000c02c070b1248005603e004890050315812409810000400f4180c1c0c10600c1e0000c01c00da4030180001c030400703012825420400c540b80b10385d80c0307450510320045541c41139a0280c1c08403204c07040d10303881d081d03001101c18090700e4200000052968107000400c00c1a901c082c0003406080c540708000b10382c0399540000300c0c41500302601540d80143c951210200b12024180040c2c0021414080310046001e046641500300b0b0040c1340b0946481d641c00c001400c020414026184180041400401040150b001403030040000c00030400c4036400d00d0f0000b0348076204000a040c422541d4504214404402c1c40313100903001080ca040701c0500b0954134010b814140700b0b1703130241070b40e1901d0b0141d01c07160f45012112504401510b070142605480703102042d10150031401d48894202c040614040f011004e0800f03042c200f21a03180040b44201080c1042c82c108103040c2c01190007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 598623651 1250 598622401 598622407
    0x140102070b0d0207030201020702040f0903090b040b16050a061805060a050c04140a030611130503060105030a141207060507030e010912050705070306090609050f2b021e0f070803 78
    0x1c0c5204041560b241c000000b602596640391403508038024481c6000080d8010316000d09081e2007115a4000340401d4441e03200e1982c10b40d2610692041030243d80300c0c0003900201004010041001c1c00002d42c5584d22410031540fa8481c40c2d80c03079200fa203e20407440d850021114208c130086c807000704400c03a0401120780382080541481811b0041501c01d60061a5403c402c11650650340d03220030f28000300868201401704207445034200061820750000040f80c05101b54450007050790300d404501141295001001003035854016620624103204031140010a4000e01d10802c080400c070780300810703006210b000001031a1909140103803c8403d5800c08030140d80c90300b15032a0015211590100c10520603003001e688a03003540c07800518020607908010021400c040c203003010002c01c0d40292100700c1c41001560100030100300d40c5030707490040d403049286100701c10302c0203a12004219441003800b0745600c141c0300110324201171010700ba0075441055005520501d007072400018180100005004141c02a500e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 598624901 1250 598623651 598623659
    0x31909030209010312023d02030f04170f0406020d0909090308191503050309030106120c030807150c02060615040530160e1302090f0705210114010207 66
    0x80c50b00d805020041000d4501c0f0341c42514140200065040203400305944840425400d940714900180701c00d0703201c03400000e1038070602d07084c005c0c0c000d4901c0303841d22032444640340d03413580c44000c40c980b10300c0301314480d0400811084407400412401007001c1e140301e8006140346903000724010450495580020320161804555000003030384521407d0b00700310650460003000c07001c101100c00509010f0b00c14510300fa40001f000040000201c05002c2145040b4005c0100f1603441d900c00c40ca009a000d0000c1a544e6070320001d10001d00b4030304c0130b480450700036060800e5030b0762003111400849900342100000340e07201c001001003a00c1d10081202402041442c0e00d0304083c0343c03001003500704061014444049450104030100710b8212102074480800c0b0310100c44123422302d00750003031042e0304600441c0403946910000480d80323035040c10080a19a409042007403107a42c1e194980e418400007510800400c58200588002d500c907005044003101c2000d01c03820415450048001010400012840c0c10b64001080401c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 598626151 1250 598624901 598624909
    0x3070f0c272003010906050117070c0b0402040e0a0f0210020726010902040203151203250516030b1009110d0203041a0109060e0609071710030c06050c010b040605030706200102030106020319090302 86
    0x4031480764028014a0ce80c1c075184001740150405182e0b0404030300c2170b00800d10603c01d90b2020740c0c210600030388010101410400d403ca86038820b500494160780701030309900d1507a2000a00d1415050b54040001503008465800507003170382d0040c0c441081c460140b41c40104186401c001e82001070381c4001c000e600d4010040910040041950704c2e80341840714180340130701401020f000e007003c1c505203103000c10030007a21307071411045041c2e06949400a032120000301244000903486400038600300491034078203186036050044082c5d440188201c81c0790800c05c16060241c1d55026030310f0b018010f003c60104441d800c200b9010000a00102458400c0000b90b052100182c2c0119000c503118200c03014241a6903541c0c01c02da402e0352560703400101500b0740359100241a6501c003000d00003401c0d180c4004e0048044450802003a5000c2d4024164907402402081240074004d4039601000348898425403013242c00d1302445400ca0704245c0c89440560030001d880d003201c02100b0020303c0b80031240d0030b24030b201d542150041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 598627401 1250 598626151 598626167
    0xf030b0907020c130e0a060c0f140912010219020f15060f0409020307030f03030c1409090703020310091104090b01080f0408030408070503070f0c27200301090605011707 74
    0x40c0d80200003d500c0031000c43d469402450349040d44170112030740141c0038580781006000844504000400c92a4a03c2045205c0c0042032628140700d614030381480c21047c02c01c80501c10701068050150760070000f0425905074400301c0e201d001420307000344c080c1c1030984030343c0303802c0c05410214101e480c6030440401003207a0310707082e00140741c0b0002d49002410041c0c0d4401320346007003e150000303428a17428401003401c05030b054001d081200c255950700001c5c1c0306281d01d807040310302803511641d40c445640340020710702c10303c65030240d0b500003640640c030300800d5030b10b444170b10840d054181d000948590001d03041c0f21200141c0035820101030b0078a8444420305c1c24011040002101420007804c02034000045001e009002060311082508001621707941d6109140209a031500c07540704840c10410202c001403501c003c08049500c400b2500c4c000c08880c0315045849008020300030b41082c0c0c0c0444900703850010150780000e54081c0020500004400341001c0025000031580801c3e102c42e81848001c0040d040c0d403040e18 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 598628651 1250 598627401 598627423
    0xf0b07060c090e010f050310050103082706070803041b030503070809010315090213060206090c0f150705100b0604050f09340e1905010507050312070f030b090702 71
    0x300041801c184001260b2009103503004501d0502410000300c0e41c051600009800c41d24100c040300c5c450300001403200b0603036200348000780c018002030100264207000c001c201070034105d18045850018285900082090b00401d400340c5203640302200b000308001c41307803419201600c102e03400d1040040c903540d00c440d0741c0c0c401c00c44000c012640200c0d404c220ba9000c0d82100e00c200007c0500d4540b42500c519081000307402580858050b12850400001c0d00780c0003280c500d004405c080007504800d1916001c1c04540500a0f0405030004030984c00a40d40041280207011030a104201811011801200e1001070f07400c4011124401c01040000704020313561000c83d10f181705000c0d03c444a403581c0d040318044030880b8501a4284041c10f01402c184141c0c150507a461210f80700d5101d4a285420140501039440c0c150f40103000a10300010b002d100c2580290040c040492251080340d00d0300e90500001d12100c10180c6100b004130f1052038162140710b0f05401440d540800543d03c2c0221340c034100740029074078415441 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 598629901 1250 598628651 598628663
    0x90e180f010f0513170705070f14032a0f01091a070c0b0a09150e030d0819020906070201050f0d020724091101080702030702030703050703140714040f1404030e0a0f0b07 74
    0x980c0c0760070414203108440043c104a503400000c3c9e50340c0c0111540082140300494801d018078018000020b640c2c484010b181945403c24080d20055035051160041c2540c0d4400d041c0000c92000055180c1020741e84280750104004d841e072a24898502403500c0c0c0070316000603090b01c42c180494250154000030381000c686401d5410590080040c0064420021440017690103014049080240355000007046001d80d504400c0c01d440403007080950412030041c01c14003540708400300801c0001d517110744086c04c490340749000380c0c1d07181103500002070080b40e129850450310340100c04c0c458104894103008400803140400000d200c189559178510800c40040708980d414070a1000206000314170810645203180c0e4040d0894404035101e040265440720b19120854200c400c005848040d5180400c80e0401c42d46080300c5140324004000030000602890030788400c0345aa118403903000010343c0752407640a60f0194071000c0662007002c06000c1c2c180d00030f8010700d212043c54001001101c10307103001c40712810b4103d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 598631151 1250 598629901 598629907
    0x60509190305060907080d020304120206030a0b06040e010f060f08180f01020d020c010510060914180a020703080c180d02030f0601061107050f01090e180f010f051317 73
    0x5080800c41111607000a4030921030074040001901c800a1041c09440300c1c0c2c030407111105103c44080341e491040d07005105550050626440040c02c20300080c50b0440504c1001281f804816400310707100303400591052101c540f007980100400e0080b284000c001c0c00d01460071444e200655000a44002400fa03c0c50001ea1076500d815240c03228180001c0c100c103184503000359030b41d03040400088041d40000340200065443c260105002401922502040302c555468501103a4a003c2802c0d901440d28803030300780c211a030302c00c500b240090318100d01481610301c85030041c0c8549082c240284502001807590301d113150304100e482103101780000e2001015208603821802c0d03083d9440032034248402440486035a110320380020402d650014101c1640700c802e0022100a02c4d640d03400c0004c4103240282d035034081400300c8400d210b0350b0685d526256000c131441c007a03660040c01403600c20b4070b8000503401c680d606941d100c04c03921156456005180c3c122840b070760f031565004840c2d00d0341c02411101490340c4007051000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 598632401 1250 598631151 598631179
    0x3080702060306041b090602060c160b130501020a1d09040503090f0f030303071e03060b030112020d02121e1b06030402010216060e01030e030a140a030e0a140c0901060509 75
    0x1a03040020000d00c5c02c0440b02c41011001c00144c8507844a0081d000540141340c00558080400c1b000c0c0d4523000d01d10500643e98102945403000c400c8000b801980702ca81441c005140440c4e42400100b0035860b076581c6078500c094046120b104404044001039104058070000d0002003000001601c110103401c690344441200c1550024112040850b90a501404040204800c00d0307002040c0148104819000c4c0040d60303030700c0c0350440440d0300c80e000740c2000c06030510052100c050407003030350001c0d81c0c40a01f00c10060b4005800040d02d4803c6645142e110f40e000791720840c0341d106c2c0e0075411626000010003c200750b450144180d01d030148590361050040300d0102c006400d6a200b00714138074091800c4903d01d450380b80c0700c07680140382c000e40b100d046001c039003480d85c0c40001c050b000089643e019416951060300c00801c001c0e4926aa001d005da010406840d441c28001c5c1e51030034064078804a22440300720803510900d4403000e051041184e0a0b0b0701c40e81c1c2400c010008550030100302c3e818508100d23404a521a42 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 598633651 1250 598632401 598632409
    0x9091017030a090923073513032705040911011202040b090d0812070327122001020406080a0e06070c0615031a100f1202040e10050702032203080702060306 68
    0xf01c0b25101d4184403005c0c24a001c002036000c502982194420321f0300c41141d8034041040d0500c41250f81c0100003c1c1314400604001e40c04050154000321030032a1200d80d1a96400080c0a45034a1103050700c005500f0781da0a0195a0005122901448295410360400785020070071400c6024003064a40210342c3c60300400100950310302140c00d0300d10400300b561034034205868001c000b4070140f0001e04281c40c80180310601c5403100d0643c0d00300c3c03940c4100940c2070441e0202007101c420104400b821020160f00d800281c07201d50a0029001a003000e944034180ca1511400300c0007641c0c50400c0c81d4800b604000300b80000359500400c60300388181c100c440451b10f201a040481f688218950014080d0a4070002500c860101001c801d0700600050090401e05615400034103520790151049a0001ea00000e1910050800e500092802020a01500e600180000d10a401d450044030b42c8001a00001840e1010800d840741d84180356070501002500181560344402c1c26215011001e40701d0400840062526a1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 598634901 1250 598633651 598633667
    0x604031b0f15021002070c06031a04020a0c05060610050a052d12060a0f0512031b0d0f0810180b130209150702030309091017030a09092307 61
    0x35030003503100c0a403940c0740e0203000c581070000058401130203110220709901c6154001c3d681302035082000d104074507103001000d0f0018071100e402900440d107828100905030380c0303038409001e030310840b6103e00c800341009142c11030601030300400c40c0d4411910407101d0105260302c00c042e41c04550b02d505120741d81d512120780401080a140803001213403141d42e84e40954640303511024105400b407060b00415591240030400030f0003401400342c2c01040388058000c01c20b51a05640340050742c185801075928212400d179016003019441038440d030459010b41076541031207034004400307030400c440c41c50121039070b0800d14400f480c80002d0744a0f80039200030004285900c0f420941c807810310094010803501249851002c0d83c00a0741208180c51310034000f58201d03514512004048900540d4000e000c0d5282c0321400b001c105828002804605140e2a084000b080c1c19019950a04000320701d40d0095484030710608008102080c0b0303030880b03134400f81000241801942e0403110106141e00907100807009540702201124288 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 598636151 1250 598634901 598634909
    0x206070606140906030d171306060f0e060102030a0e10090b0d090c05030a02030c0d0c050a08060405010c0f050316020c060d0e10051017100203180c0a050604031b 71
    0x41d00e402070006112100c000074041d01c107020b807010f640c1541c49104054854000d019004081045040d040d0342c40103102d12203d50082201c80802c0000c00c2584641c01120b003580c00c0f8002c000171540f0b061002c3c098803410740790700c41c60910045140c1180c0a0f0010000140c0e2074545001d0700605c040c0d980714902505140c2c014111890220b034031108840800350141480b03900c16200005000c902007450b080106041a2250300a8001e100742c04080080c0500c22401640c2501c2c2800b0840000c00c051b81e590304034a00800001000745881d040906001e802c42d140c0a5651007800140c0141c2214540c10a007a2680210313402d229903024180c0810980c01c1c8861051f109a20000005843c054005198858141c40c4403170301c1100d07a2043d19440c0c460864005441c0010582c00003901008001480909031100c0c00c07646065800b2500c1010042090307800c1a210b5220310b40368440f040030070a83c204032005e000c0d017084a69214250bd400045655841980001350a820305031681e4035240b03014445c0d0030010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 598637401 1250 598636151 598636163
    0x30c0509100e090c04151803020603010609030308010b0901080f06040e341410020102120f0103020f2409011e021f0645020d0609050c030f04020607 65
    0x7800305004014054080d040070944100341c40d00100d01c1c0c0d06241410b442c1610319181c60313900100550501a55040c40300000b441c540035101c46c4c0071006842e9403028500805e443e4484200a505616000e009450b051f041400040e03018455042240c1e0300200440c0c0142c03a03180071a10035181c04002c1405005207100b001818851000c840d24460a246a1000158401c4000c26003c00b988041200d0b000310b075106201522682e12034098040c580381c0d1080f035290503503000041c580307107080038131030b43c4d030841190180443c20b241c5004205504082d8013804845a0444071441c440040749004152091415000d02921502181031100382c0d0180c0422918016456442c0030415400c10300255140c01030075401c054041c0ca00119614100707280680000c0d54400300c4100c00e07426802c00288038560018501860038925900140f040f03542c1128100031512000300056551144008008280d8100d9407000c041980f0f854200400361104000b900d4104090009100783c0d03488034000501c06005031040605a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 598638651 1250 598637401 598637419
    0x10c0b010b0d150f0e07050706050702010b01030e0a0213020c0304090e0c040b2704060f0f0b1903080405040c02120d0e1603030f030e031b10051510030c0509 69
    0x40e404041c1c014003030050340c1d41d400f444400e00656140760030212600c00c022000316500d1080c001c181d280c0900c250b0000c0f95103049401e14950761a00402d9900680f95140584d6640c61180e009582c107004003c2054056001001c405d0401e5020a4074181e56441d0810704a5000c200f0080c0f0070801d1007228003c004400c424041c02108a643d1034541034007507101449141782c0500b1080c2c1d810080103504600c47d0544000e1072408200018100c40d1200500031940659a0203040300c2c6000c0600c199a10000c0314100024403807030754000d1102c0e0281c2400300400c0e9070941c22040002620000496091765400d540204048514080580c0f40c41004483d501c102c0c1000304902c036206400b1b600c12580d06010604588854400c4586100048864040940041d00120a1142d418080e070003101741d1880c400100d900d041d084440d0409141c09820072410107401001021101c51078078014290804520441061400c41e628001013913561424068406d05807902816114940114180d410810b009404052 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 598639901 1250 598638651 598638659
    0x111010b060403110906150f09180403020a0614090a02040f0204031a0a1b32031006200d0c0807080f0309010f0902030c040b0303070204020708032d15010c0b01 70
    0x2613412080411502038508240040d11914004603030180e50a4000c1388507203041c5a07900504816406804070642002001006003450740c014030005208900a80c040c10400005140050a9030035841f1001c1400500405008000318003180d00c042d01360303045034000350500003581e024029004507800a011580d00100c40540c00048000884c03182c9810642084817400341d0000c2840640c0c40788200f000030b0002c29203423102030401900203100304030a50a00c04507404c01814269203502c03c80340f040c034280118208014058100303032110490320b58444100300003481c2e0201c140d5142e0740e1281c104104030116007008180100703a4101c0d44540e8224003900c0d51740f4a0304404020981c4251a140704540ca0080c082c00c200100340f180301d20b82680200039081c2524100d017008041d00c6110b4143da0315000404c1801d0041c1d68500c000c191042c4500044c3d62646030001850791086010104c0703c200792083c041c503008108001750030a600030001814a00103a0718000100c0d091490228000d20909400380042 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 598641151 1250 598639901 598639913
    0x51c06020c0a0318120f050120090a08070b030c0304170309070608070203070c1a09040f0c200307080a1202070302010e010c050c0c0904030e0a09090203120304110111010b060403 78
    0xe40454065183c07000c4040c2c0c003040a0050184c1841804070b030b4400c880c840f40001e6404401c502c0350901450012400e2140c3c41b10050b040e411070050f80401500000782e5040c0c070f00382952032000800281c03016109407840d00000348a80c0c07100401980f0b001400200103810480320500c41614214064400741c1c0f0783c40e256210565400d140d015a0012418540000701c0b4107100000321001c140c2d0050b1101c040c2c034a00507040c083d8410f04041e01c0c21003181440060354a032a02c1c401c00440340f00424010a11003640d00001e000007401c2c0108030802d01c1d490089401400c00041103807140da40c04070640d03641d2880390000700c4007800c50301c1b816400c03d130000818209055054001c055030360701d0503001304060070541d401562684035030030400d004c641040000401d40e19184085550140c060304201c54003080440010344500701d90741089078041e554124602c258101005420741541404118a285003016210546181116045141003005500e181c0070001340a401c80752400c000503250030340301d0303460745450 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 598642401 1250 598641151 598641163
    0xa020304051903051c1134060203100e070503040b151503090d0503070e0103090c090516020d0f080f0601020c030601091a0406060801030210030219080f0609040c051c06020c 76
    0x100e00e180c40080038104103501d0034410f014424494110142c60440315002c6070044020582480c900a0b441038034408100100c603007200c0302648502300042c1d40c0c2c904000d080e540554690000400c4d181c020003000035964010701100c0e000384c0c200e8100100d5907200310301a6021101c000210350096040d2140b6103441c2100b00240d402144408241c456110b154082150240411196803000410710307040c4845d554025407264038024000c4580345202c42d16031030721a094038816680c040340002405a000502036041c480304208003500d21b00039694925840009120000181c230107615a00307041e02140e6980e00070045500f4204010f003e032481580d46018000c014104040d0b1020400c031a070301010642c1c0341a01c18503040d189543c548040e0b90342541c00388030402d2494114403045c95401c00201c820040440141429041503694845161410085803850404003a10440c000d0b403144090100003107104642070140c600581e94484203c40d1030340034034407640c419100901350074800102442280700110b1a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 598643651 1250 598642401 598642417
    0x19030903030e0606010f03090303020910020f0709051330050c011a0607030305100f0b0405040b060c070e06211509070812071103100902090114010203030a02030405190305 75
    0x100300d0301401240b40354454804592644c0080d881c11955050603000f9032044070789501030300d401800c1000500100c0e1000f461864550096482004004110f210411102c00a400c03240300501040c240300011560302031103071030b00420014050007500c144207001c4079008502180b0080a001c000d03c07040700a000780e171004120218035420166a603440d00d8049600784c2080c44e01074180381c6084010b480c202c008060151985102164001c2c0000340c2030342003407109002d401d00c9803600e55030b1881e06080204940798050b110340118024007007070950f45008111601203034441241081e055445400183d803820b400310303405082110341405501c608000280403004055020b4451400d41c641c00e205c2541c0d00c0c041d10a0301e4060307201e4040c0e0445401d169002c0c2014612541c003141044000303000003130802d014035141c000c0403595100c0400c1507142c2101c52600402420b0310074405045500d0000b500c0f440028810b002c119000004a020042c3c20080030300842032110140501c0c04091070300a149502c2202 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 598644901 1250 598643651 598643657
    0xf010c1a0f060406030b0610090b07031d1c1101090902040f08010506180403030c0207032a0501051303031d10110d02010213060e030f340f05010804060219030903 71
    0x80d0b450f08103807140e981a29000203c043d0103903145810090084004c10905040104004001614031900b0340509921440703504d48400e80e031820007026001c04a02c0204500c03030860000341c001084050307000010030f540c0100480c0c802d41d14050060702e00407101c4d0302801203588002400500f658898282105442d5400024080e03919510204071400040700d43e1800c3d9031060f1008100080d0003640248241c0405005a911030742c2c0e80d45031050842012101e008070b440700c18cc884050001d10558840243c24242021404c007201201003d52100344c41c000142032140b09c0c2d544608a00c1c0b5040145c00b001d00c018161410101064070080000200e4001d01d00640303c0c00c200400760718010300a440c8028146003603007420a01d40001241d0070414440540e4050103001441c003104c0c0e60030312010f0b0103001950010310003401800d0a41400804211070a40c2c0f8200303016041c0012080c000c481c10864001b440c04d10915215401c05100178841c120b245c180d10303801c08980550f01c0380c042d0421007009020b52 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 598646151 1250 598644901 598644931
    0x8070f051302212a03010611060709170a020a12030801060c050c040203150409030305091005010b0d0c09090e07030308010909020d14030405090108030405040621020f010c1a 76
    0x10042030f805500140c90098402140c0d1101c1c1070108000d03d40e00072001e42407141c0751007140b0540385400702941d014081151001005003c0d0542160043c22403860310300041a0b586401c810052103412a8083c0d40030400b00c030f000000c03c9100401881d24900c0e00188064900c2e40c0d030b461403e00c94289a081100400e40400c00010386034000e00c100343c04140c006014050401c01c0104200003580700402e07102d1529420120b134000d0b07454900c01d12001c0381c0700b030310300281604000d0303000381c03919054035800c1c4034107410f01e00148030080c0a5400d4950340c00c2c207114045000401e50078151000440c6810014400e80740c0b07500c44424020002c2e00b01d0440780a40c4a40500c1d0742c8408000c0187e078031400020750410244007100002440a020603000c00708030a007901c0c10161550000356030000c00782e0202060780d0000c281844649840c1c03068200a0013012030030441c20a900883e030301c035020344c8040030384035090b04003140e03146074019100d10858590104101b051400c42c003003601e60101003620071070940c800364 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 598647401 1250 598646151 598646179
    0x1403091e06010810090303180501050103050c060a0504030b040c0b0712030606050a050304021516080d0c020d02330a0e0709020931050106020615030c0a05120708070f05 74
    0x10980a040e6181c0c2030140010013002c00640010b40001102141015610b8079a010515074180c02c04840c54031070b000200d0107500d503080140c5404101c0c01c4403441202d04002000c12070340c02c0011101102e40c052100505599103081c0904140101d6209030155500001c250007084822403c8101c001c0b9941c40810000342c68410450341030242111000c0800c008002143c0940751404903040c0e41440080014505000325158808070756010000702c0e403160001c101e09030f80000e14051920322031a21320042410084210307000f55140b805c07a0f50302c00f5400780341a520a080000846882c407180407000c030044c540c10403075031100040c28040f100310f425000b11140414801c886000f2200d2500c0700421000003000b8180d6000041c5000003040744110502d01c29a940251541c025a4000c0c80c07030b40c020b0301c80c900d05000c5040703030740040030100c074420f4000c2900c510103039481c040d0782c6050f20000d032a1150041185e00695150101ea600700d010148288a0001020707104500c085c025100e080da1610030010700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 598648651 1250 598647401 598647403
    0x1209081608130e10031e05121809040b16350603010501081e01090f23010b01021002371101020906090630101410050a1403091e 56
    0x8180da800529620154003080400e0322403001b802c200c01c048030001905242d9640b0549480654400300a40390b10109800345416100340300d01c244040700b9503510126152640e00d4002041005040310390102064440342a400d2140e51410306000c11420043d0018600c505096074089804486200804188000030202c0c00c06008080c105c85204004048034191061039800110080540040c65940d50f80c00300c020841000503000c940f40540c100d03810000e0034a144c1d000ea4413860507221503581c1080500502c59030f00042d40c0c040c40f01c0380a001603c421070100b100b12461141400c071010590213900c0349070003420baa900096800566120120740451400350300342030713020b100c46940e80288103000350b00280c105403004003180760705184c4400054206044584603034049600e88004620048100005803a08192031000360181c2c1d404e02030111280c0300003030b1001010742400c1c8200880410010380c564010b030210103590b02015045c3d6100c0c41c1403424a0b44d1003500c40b6200f101403086202101c43c90704 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 598649901 1250 598648651 598648679
    0x8031018090b040209061504030803062106160905041406040c170f04020109080d05090a060c0b060d060605030d020115050d080301121a09030a140901120908160813 72
    0xd40302403600c58655444c0c003007100410000f8030198014000701020006002540010406503100d04060f50300c9091140610107040700c014201c6440c904d110501c40040d210010b400c030b0348840c80118070710500c0000e12007101d0070500b65010715003050402c070710040100e1003145284c2c460001903a0800074030342c0140c4100c0384c0f905141380f05920303182c0800100b01844540c038080c507441030040c1800071803e6030300e08a40d071030000000c0801d8001040460580207624081072110000e0000703187c149541c400c540c88501203040c010709a184900c51142d80041080380d0b542003140104001020740e96107101020f00070303018280c101647c2085020090340413660b1300e000046040c0d4507400008003801d40c0e0038501100c08200002e01d0540d2010384002e100b403c007031004103e1a01c504e0b03201c0041c646a1041400107854032911401485030b0150a2280c000c2e0f6991080c08200840382052003c201c080003030910802900c00c03c80001c1c038a19011081d8000d115041e8010314602070500c410f05081583c85440c007070000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 598651151 1250 598649901 598649903
    0x2c0f01080127020c0a1406070504060905040207030210060b300601110106051005070b07080708070c020a0f0b031f05031b0301150e090706030b060f0f04030803101809 73
    0x80d4061110006608100d035900c40361440c82d40e0014644441800414600911020308071018490300b1400f15501c2400c2c0221030700501c550a00c241450f00345080a0082c01803805071500483d808030f01001030510800120042e40310515040024940381d0039803882a610a0740c00c580059113010b54542c5a2401c00c1d90122a507058401c40340c0c445d1141001103411038000a5005103075900c6807004961555010084044214291103160340e400c564035003c2c1c40c816005280f1014040b900c0d0800103081c0e0080401a4000303000d10300624202500c0c070004000b00020303004010400b400070b80100321816070b80019070003800c2c401e90f200f8010603000c400c04154110380c00340942540003201080c1080325901044500604010008610048150b440a0000c18103601c0f02552000c0001400f0b4840c90520001024001903d82032001a01010100e01588144045c43c84181e1000480c0f00401410f0350555020710350100030299030b4280080c80d03080110160041d8141000c82005100c6030000e107100e500046 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 598652401 1250 598651151 598651169
    0x8190807031a092e0b090f030613080c030f041e0807120204050a0204031a04021905090414150106020318090601120504030509060d06080106140607060b012c0f010801 73
    0x781c0c0e034902083d9842c524240248444103d0180704c85113021904004202a283c05110307641c641d81e82d0020400244a090220340c040e40041007400040003210003240600ca0b08410341603030303c4002c410341525600c102003045030b0403040403a0126110040510940c42c5420200254500c42e886a41c0a51940d000e0304c02c2c00000e8005507120401420603411160780300340c90980040c10a9078940b00c0400c04400001c100c030102e03146604020440c5402c1210240d00080e038002d0046003418800803480e40d14028202074034160042c542e0455104082100c50181145007090b640c080d6900d071400303507903038100d42c20750011105100135540d060304016412506c074036416500c4480b12045410301c08003d00004d0015000c000701000340311540d86590004014071070301d042000410300c0c40c20130000c0c02c42e0810f401407800300014017008203840d40d03410b041c0c0300c1568006a0005013410340314010781da941e0504030840400c295100e850481203002070a000d01c042c0040d00c90003806003440d0011038164000340205585 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 598653651 1250 598652401 598652419
    0x51e0c1306050a1d220b07020d080f451f050c0a030b12121e28170703052a04090c140304080301080d08060a09050408190807031a 57
    0xe1034010b01710044410800c2c44400b60514881e85900c42c2d40b02c0c0441d40003015074464686e81c1c030003035030100329254000d401e0012039142d1305200e141c42064021945c43e04090706095200d2008111070303080c814417131107030204d486050054070001003500c070032403985160900482c0c03803003200004810340203651060014080e12441e01092001c01e83c0142580800707142c02c24229810024008410003500011580c00100252186e000c05006944006004400c02d04018103100c1034082000d02c0050014101e004036403d038030300020300800c446a00701030300340001c3c00c40030009000040340c1560086003e0210240d525a548a2450000f001c3c40c25500322204080c80400023044042070b568003d4000c54018502500d080b01c0f100078a0b81540c100362015101e10200000403c01600704005504040c81c55003040f607080d14200300001d28000d618805d01f095140c4a600040422140000b20380d540c02c05420054001141110000c1044008403180c0c0042464a052480040490a15110800d80c01411114 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 598654901 1250 598653651 598653661
    0xb040b040602072010110a020103021b01060303030504020109140d061a0a0306021b150a02070204290102012708250501090618051e0c1306050a1d 64
    0x811140080003590040d6090108800081d03448960f10700ba070301005901018500c081041003684800d01c4644000c2c17105516824440726404901c0d0804c80d0380909005845291074101d8250604480d400c3c407007594a070080200415426500480c0924000e0341c80281e510b440b0804614030000c5a010a503000107103143c50000910103801040c050704140e40d01000c25444940070844a81c065001101c0c1c4640200f51041503c5492080c0c00344202d0300c1c0d0003480006078007c0f0444051002500348001941c000038102c06540310303504090441c0000e20604000906001c1e00210501102c40d6410700550074903003d03c0407194141e00000191841080e000d031590000e540b032102c0c0b5030191000c0aa1805812010400702400c0c010303002085020f03a0000c01c401140b0320703226003201c03002c01c0e407000e4a02042d10050701060340060b5500702442928511002280d035159803503d02448600e00740d504c003010703202d082c04a02d06500b0020448105891007005183c036018544602103404c0c5103c0c1e240f0076000c0c0052 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 598656151 1250 598654901 598654913
    0x5060406091a0a23090409111e1e0102070e0a0b090c18013905010608030721030f1503020a050612130f150b24030a09081b0c130203040b04 61
    0x41c0040101303803422006901090039224088819200402940c407020300c00d051111046a001c2d41070a000404400400c0026001c0380c407440e0760204a844503d4580456402005075501130040110f00f040f4902d00000424041e1500c1d40078180501c01c4075010841200208040d07601040041c00c55441c4990314000440d0300c03070410b58540b0007500403045006c2c8094400040341444501424180c502040305081250a40d001503224032001e43c001c0200b2004039030707488481c4085070f100010340420007030f42450031030103804607501d09100289040380c03140425208500d5503003141c0c801e070f84d0098240d030b80300200440d82c090051010001c00050000034848041000e288000a00c11f8044d6401500503071903040c2881e060b4407100c54095038800f01c400c680d2070040e090607090882c1c10f04d00e42201041e856110800d02026000140d026103455001c01045081d0742038610008082094401c40c00d414002d50350340300d40d481c41d1130f07000b00e615021100f01c00e50035008a0340304542020481402d47c545680d58 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 598657401 1250 598656151 598656197
    0x180b0c01060f08280b010512031209250e06090606071401050a0516020a23030708030a05010b0415050d0b03060a09110307082505060406091a0a 63
    0x15a94955884001003410030700020801c018040c040000d0a40c650307003500c25241c1c0400e0020724040c0200c60070310700001406040031365040d030314282d501036000c031040c130f00407861030003026041500030100b10100015030358001041c0d02110030740ca640341c0000d101070082c000511014021b15481c04034040005015007000b800180d044138010b080a803a000780c40d241c2c030790b41c010101038907400759440da024840c423450030340a0b00e604280c00065424442c0002400a540e0703000c100402030040e503003488044e0000c0c051080340d40e00c0c0860b59055990710482d600c3c0c0803400d0351044500500403481c000c00800d480e03002205840546003001600501407100c41016a99500906141e80450340ca6030900d50190b1824481140585080c500104840c1c010b0710b8240c290100d02c070310560180d80400c1c01001210341c001400c2c1010600c131060400b520107100c1022000e45080e420240e000031001400080850b48048090100e41d001d46040c003401c00c0e80b81104080348141070f04000001c0d59140d0a103a030011354607070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 598658651 1250 598657401 598657417
    0x51c0216081c0c05060109060906050f1e030c0d030804200a1206020d06090c030b011805010309020d0f030206071202070c03150f1d061003030801061b0b0a0c02010b01180b 75
    0x2002d003c6001c0d560354a454500260072605c6815141d101c1081000504d00131070000d80343c120360303100746260554085456130822180401030451400c00161003078406000340c44d100c00001c0c024581f00700b000e05016012803802c0c1c4007104c8a4150752540d408061140041d450758402c003d000150403031800ca880b0120000041040d6886035080003003200c1300038140702d03c1c001021271410102c0c1d0a0240c000240440706180940c905200b4922519061961a09007160644400742130000f1085c0329400406c02c1d8115070240102040c1c03a07100c0e10300500d9000a0410700c1507803141d4818580d2002030b44440140e0040c03400081401803555014000a81040c840300856074000c6400a41141d481c401803090380c6900441c82110809504030000c04402803042c1d0380d0205405da181202c030b03841d41e038008100040501c951000c200c02d03210b000c0c0365800816440f541c450b410418440c09030900e2503496005280640750a400741d803030702c06109080c0d40586104985084030403080b500300b62401400542c80e50000704 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 598659901 1250 598658651 598658657
    0x1020a020918010501171009260910050c06010b0f0703030c020307240b060301080a02040b0d08210109090c0504051803070f060e07031518051c0216081c 67
    0x184942c0c51000034030400e8001c00515520395007202c070b40780b0058200255043d13040911402c04a042020074101c0c0d0484001c20305020380441c50300ca0b245207240d8180600b03004c1d90750040301c1070301d40760030680d000d8050485091204291080d82e640c2e026402041e1082d2030081700d00503000d1040c0000300740254410380000328940180d900e000000d07a585501c001c941101ca01c1d0b50300d001400103142003034a2103264184c0c0000d0701c41500e503504001c1e14903512015034030024826601ca1005180c1911200d43c6071841c55032046240d901e0344007a041070f01241341149070280500a50800004240180b800344900c40c50300580700010b0103003400c040c4005480010300301e1004402c006208804c400e4100010401d16015007540c045d100d1051400d81e0540c2c240389864600c50f8089481030005c14074443d000d0300304015198000980100c0300c40ea1440495000304050301500800c00c940c3d90349084000442000181582503802c51680d0040c40504901240280075059118a0040004551611640c441403079071382 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 598661151 1250 598659901 598659931
    0x10305040c05031c14040308040e0603030f040909030e011407140f0d0915030b060409020904110c0609012f09130615020d050301030f03080604060b0f2701020a0209 72
    0x42440c05100204c8401d1211264401c0d40c140b90b4400800b0303c040401c48000780c9014656201c0c08054090350149078451040b800c041543c90f0b804008990396201d01090701d54640d542c030300d1460000c1c9829013040d00491200b640c1800c1640c4500405501c60f41c91003140703800c1546940303440e9080c016800d030741b00040c840c40342040340e1940c0422449020380000e564181140f4100309401d81e80107907241c001020301d400c1c105011003a07500c9400350782c140e915441c0016214203c0e00b0002e0702034156080822154100060012013600300480c44902ca03203a100300a002c00e600a0b062446030029501258800c040425140c01030340110900501035900c005000c40300300d0b00c1c20030400c42143c006900450200c068003c2002009405004c0e040f41c0e0682d60404905661561700d810282c4a000d030001410040600c0010311640e48642c040340241c03411200968607044160100801a408442007502c81d50408a500000c0b0750ba10041d081c1c590f80c180d0141045107070075400d000d401e020151904070a11140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 598662401 1250 598661151 598661159
    0xd14070503030c01020a0e060901051b03040f090e0607080912220e0103051912050307050c12040501090f140409031704030f140316050a1b0f02030d0906020c010305040c 74
    0x30000341003e00d044000060342c1d00c0010002402120a0724040c0b802400e041c8007c08042e80c0010036100042c1030440d40c1c09000d001a4007180c01c42c440c941000795401e1840c0f501040e030500c60f0384440b85400d1641c04852007519480d60942d1400811908080f440c2d011040d01d9401126400182143c44a06c442210003441541c0f0f09001c80c034680e070030840c542e92052004005001e002c100640387c55055007030000109140c1d032070b400420341d00c0d00391050501800001061800c7c0c440d1088540c00410030045d240d02184035000c4800a50091161a000a4100b1400b0079030114a2440004031030a80f4007051858002c1020700000d8070000d0825401d02421015100781d61001c00d864034415486030352032140200c06102c000c5c010071440503007908510418010448000b042a44002c0701d6a1141017080d1940101c15084070001d01405105034800c42c3c1b503610f4010000f0003040d40c141c0318400c509490310400204405c40340c0042a12802006034041c2182c1c251b0ba50095000035045802203401c51035254032 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 598663651 1250 598662401 598662403
    0x62d1e0512061510020a061503050307060b01030f14060d06180c0513060302030d0e03010f060816080c13020904020403060c080a1415040509030d2c0307020d14070503 73
    0x820707500415030b900410100051020207041c084007590040301c01d4000190881c400a550f0040030a004100ca41d4400342607038034807006602c1c01c00440d072041c01c49039030784103d251120140c55803480c42d502003030500100d41800a0340f0302811109400100580e11240d0300c88041108007819035a09944050f80c40380610701d601c4003900c1a10045014001c034581951401e8103200207800c0343c04403038003994502030003400140d0740420200119555481d001545110440000b801412035082c070f61050351500000146ca520301083d1441402c680b2000101401d6540e01025180c4203801d04441e44004804461880e500c030b254007508861601400c0141050340b80e0355500110b40545d0300180208611100304100010240225000303007032202084841400c2010410018643c80c070041e900c55902c800c0042c1008508000303070388400c0c2d201041402450051a040e05400c01da1600350000b0160344061900e5002e0000119040326034050a6014203404940322103950902d1005c054280d0300596900107226a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 598664901 1250 598663651 598663669
    0x30e190b0a0801090213030803040317090a14030c060606071109010e04110a05060901050c01022208060a0c0c0305070614040804050a050108151c080409062d1e05 71
    0x40c8640c00360354400e4200c1c400752820314160302603403a890040003551044881460307071030200da901513445600c985641c6820340d040ca05a00456110202c0142006150a000035072090128040c0c0038994a0f2440301445a0b1a8800c51481050550011021950ba07040c00001814480c1c003030701c64481100e1009000800300d201c01ea01c200e20302e00714402070005104d4025502c404c1c09c1c4007120280c6000e4541000f14085000321401c19061100c00f01d0801001c2c2800e40440d07510030a11a44081140c040400e082c07214069405a240c082c0301d820000b44507440c451040c200c100503070381c4500c90228003655003100c240d88a014100e4035161a1440365070280b140203601c1c0c0c0100d11502440f51121700340410b11503680d0b40c1c0e42c1700c0303810080c1032428419030090000030165200001e85090b03080b101c00b00e00c00414401c49000c02407004d480081c00089051859000c0007c1c0d43d01301d2085110f004a045240005a86d040d0341c2000346045000108401204a9141d00c1c100008500c080040d999600000f41c0d442 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 598666151 1250 598664901 598664909
    0x20a0806040302031b010e070b030c0708030a200a140901140c060a0e21250807020418032f0102041e0602031c021e0309010207210c030e19 61
    0x1c0e0021a2100540c80485c061582004e41100208041981103520550b50b40042c412030080e0840040803400380000d0394201d0303a248c1e400168a0f582c90420098450040100030320034540c08007520242e01201d0051000c5400c4071744280d8901d40700301d10034941c848040e4441402c85052280e0130500340d425000d54030141811100240c007901551902ea140d01040c0c40351826100460b07008142d03480c000421440c002c609460040700d02c0c0d5140c980d03a8810b89100402401141e0014002c12510b4040020100040c0030303a40c400d56040c40411808404611014504080200450382000700d00b1b4810110000381e070080e40c07450800032a160f0031162114226849504603800c49280c044182d00100044401c03140100020304c010341c42c000b80c0004400100e040c0607441044981c0024100182c0d14000c20703180800c0000118050b940d01b001c1c09014000d500c07608046a2312a003c80349c0c20b0325220b80c0010607460796825103d0042100050380c08030382c615030000c0c000750b101e14906091030b220092109070308050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 598667401 1250 598666151 598666153
    0x10e0907030b0a0801060b040b0d0f020309030304110a03170703030f151d0903030c0c010204150e0f0306040b0601050724020307080f01060219111207140d1e020a0806040302 76
    0x114181424003e1142d51030300886080c0c1e052013400c000d00442201150304589402d0009601d0b800d03c0703400440500a098101aa201d001000341f0107060000b01c004e5029a00c45d427280e1341180c81174001d107d40c441e42c501c0003922000039200d035801c00000c400011311b5020702c01e150001d500306542490600721a42d1518100b011040c1c64400d00441c05103420f13001d49400d4000b09a005860003c05003640d030f00c00100b07401c40720341d00465070440d208030035010781c2c3c00742c11030002000c500100504000c0c03180c0101c00d0042d04c140c00c180d815030074a003070100e07600780182c0e0803045100040d0394601c019681503104903000ca82c54070008682481c400d60f100b0388002e180341240c002681c0c90030f162000400e001006031031540c0142a4400400049400180300020b0421510710300700c941140c0d050100e07800a020000e96003007890741040b0519150049580c0080e140c00740014442c0c58094814007000d9005580b0042c03035442d08a0044001c0302111081c45069071004100a00300b648841005052a000780c8045001d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 598668651 1250 598667401 598667411
    0x200d0906030f0605091f081510051c0b060616080a0f0810050108100506030403110d020c010c060b030a12020c09070807020a2301020703050d0b0924010e090703 70
    0x5400d505001e5040341100b00242804254280000140402d00107003864003145860b04003a50441c4121600c000201054405d1f12040e4070705146507171000b4000c80e070300c0d035500d00a120301042c9847d001000500c0d800744905040c1c1010055a6051030081e8040c0c00168840d50520006c51400341c55801110807521904080b6103403600f8901c0504400954501c601c14000000104440440707981c04c440b00315a000d2806c00c01640300d00c0208060340d4800e8200c3c03030701701100008210074541c00440300014019464203c0d008030380410004c8cc0c4031740f4103440550000e84008a002c5c04a01070740c01c100c00008000713041e103500c1e40c040c2e52649180d9062407c0f04003da000f0b2036803006a85001e24519070300440c02e040121052170710134402501c2c1d030302c00304000b0152040f51001450116050540c4500035603600001c550303458031303401c016040340c1240503042001802c1000d0070569041c4640710710302405900d80021800c102c060607024001d001003490364100042d04115076110f03550820410b019101a480c0059 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 598669901 1250 598668651 598668659
    0x106060207090f06030302031e040302041410092918130606050f0d060515031e0613021c06090b013201120e100c03020909070905030d200d09 62
    0x400c0e00c5480000b038402614004d41000840e80100c12a07464181c100001da1300d500051041041c03a01544d000070350810326000d1100381c0d50412140b554024144180c07100f40c011750700c00d022800d9884101035043c090900142d0400350380381d17215510b507a00a000b0101400d080340510454170320101204c0d582c6030400546465410300c10301d8824031000d80010744042600e110900082940242c0b0041c00800e51641c0f6000200400143c0308040c00c1c407000107050702e801214001c03064040a4120040864a0141d440850703008440070140141181c3d000d41b40c100c65024455021100c040c2511054404c181c541c1101c900241520400d140600880a2040f00141c018401c0400b449204588002038071914080c640140e80c10903510105404030040c0450300340d0700c2031502030614036450002c007001403c10340e00664240d0560058150200190307009034030356035801012101c116052056030b0b096000205d45d442c4562080c0600c041c18036041d5004030001031110901c42c94180480072074000140c101030f00380 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 598671151 1250 598669901 598669919
    0xc010e01180213050402010503040209090a050109150e0601030c03080717040602010f050708060d02060d06121103151603020307090b1306090f08030313060b13150605390106060207 79
    0x80e1800072070f00c60400c40c07032800b60b0010b0914400030384081d01c0b55060000141d020802041a903800540c001d000348100a094a04640aa0007900785000b546040000b941401c440000700a81280e8208081c00b2501c0d00d1030315002800d900800c0160340710341a594980c049403420070010030080c8002d0b40001403424104940d0004c40300007030b20715410007554030309102e029555070300d05104003601295496516814404a01b000f0421540602c0116103807a515100b030000000c52451789410640640f80c081001c90041100e2800444030f82409a411000b11031000340319501855100c0c0d0380b801c00d07084c0705843c0c1080580540210a04880d0140264024441c8542c4180f41c00c1c010556001c8000d00582083d03410754480c04002c2000b0b510800ca2138590741031202a030001c1c8042036024011404042d130b41e910f00009448142c1a2080d510403507880015850722030812520490200f5100704000110020b407040701e100c200d40303100105244c1c0364080180e540203101d80d01c0141880d03001404136a140100328 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 598672401 1250 598671151 598671169
    0x102071e05100f0e040c02011806051e041e06090f0b09070503060108030a08060a0f3807030305090c04020a03021b03040e010e0c0d020f28140c010e011802 68
    0x500400022143c800003e5030000e03141d8076807600441d40400c40310300c5181c00f2401400c001d086800d02c8194548807000703004e85a884503000d0345283c11519240e401100b1310340130600060718010010301c400956025201001c6206c1001c41e84a050042695101c585595242100a50041c1c6c0d014501c84140810320204228490050506030054030143d0b00d40780c0a69100e0003040c62003428008804001400c51b5288103da2018264402c1d001d01483c2e00c418402d0308060b01c1a5020000155549200748848000d03608529600243c040803450007000d5681100a040042c0c69101284108201c98a5644d6180082d1129203142d940041e210400c00400143c1903040561945060b002000305218403602154a503043d42c458076118029921011400e100038440c40e031080c0c04142c0b002c9014a066540381e002010820a100c0b0500079003c81030300091201c028070813004d80070800e840c4e90f9080a2055102400c010490f001c000034070a50481078942c20741d03400c452120b201d1040c05006508528008445c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 598673651 1250 598672401 598672429
    0x71106030a0c031d030f0a20031e040b2a010f052d0a0e10060626100e09011409150903030903040506070c0b070f03030e0f0a060b0102071e05 62
    0x12031030318030030303071813920354492103441e070814004000000c800c5001c6000d04000382e102804042d1041441030f80c0704d0242e4603030308204a5006456081d0484514030116039054405030703034032a80200e01e490384d41105405584003110305440001080701c4030710300080c000e225803043c04003a000007040500d003001d615402e081c01c00f1400c100014129400b10f00850940da80c007584841c20304000200000b060400500d000c1d1031900746000f490030503a000c02c840360321200d8100ca01d0030710701d0806060f12901b41c04034072100c41141d6560110744103400811045200e040807581202c41c0d58000100b03080715a038080c40100049036038000c0b562020307410300e40c1c00a408400691012502c000b842c1035082904c101a20f91169225282c0302da0304c00702d50300c0f041c00aa40c03038010080184d10361680c4d80305014584035450162100d019800b0903d805034460301c07800c003c15400305803110407000e402d01c03640d1039a030000100304032020241184225140824164031509142540079181c60503101c2251130f007000c000c504a544c1c44 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 598674901 1250 598673651 598673681
    0x31a1503070e06091f0f0e0a051501030902010318230307120806130603060f0609020a05090402130803030103150f0911011b060c0c0213020c12071106030a0c03 70
    0x28208000714070006050380210040b5003074000c50725117185c490103000354036418003c04140c540b0002803656045103000c0c2161610b079400c00726070760b66842820441e00121003541e02e082d1080c041003680d6219922890a203403050500240e03198031104103086111000e41c04030360611086002c0200c500b909920f628a51440600443c03410000343e481040304846e140c44001030106200208840741c0d10184201001e13203103c0741c10405280c0e2810805c020305024010241c140c0c0c50720741e021580002078021a07480020300c0d10740c2c5240000c1c0310b05100081d408000c0c070340c40844242d20041307074411b024001107000714001c480080c0c902503490020811a0545071101010900c6c3c10404c00006d03400c803861260300705003420185000c034160081c0b4008000e034207000030000391401007002501504406e841540354001c0c1c0c1c1c4d0314a00410501042d00f28414a06804840c0e400500780707200c00740c00d040007020502e11071b0022b55500c00840f07000c02c0403608203590428049440745400340d210740d8188904c1e040040600c2c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 598676151 1250 598674901 598674913
    0xd0f050604021e03040812070c0605090604170a030207050304030f021c020a0b070602190815010206040b060603090a0f050a060b0f1503060d02090f010603051b1c06031a1503 76
    0xf464007950300b5400e140d202c5400c100400090203015140003a11760140f208080f412481c80c0000780104a414114000c69510b480d0001103003640f440090001c0c45a68040c0d240d11510001e40030111031a0050a13501d000c15800300300400000c2c1d4180043e100451107024031001504503481008044603600e00c55004210303003040c81da0003680d03580c0c15000480308120003843e521900343c202440607128032010300c842c116403180c58034601c0740c0c42000e09100702c03602c1c03051080f2078a448004980b1050f05440140001c00c0900101d0b00701c3c5001002990024442401c84800342c4a80c1e07150690004031101c240c90702d410142044003031260a009440000104480e031072400220f0702c0000c0c4214640040c00318107405c02000242c0240c5450869150242d0000c061741c010f482c0807807400440200074000c1400080c108004142da41048180f41c00c0b104844010681c106111442d40030080100d6400a44045803114000070109401e0210820141402241c014180c60075890200e0301e000d215100b036000394824 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 598677401 1250 598676151 598676167
    0x1a0a06051825051804060519170312061509031204061206030803130303230114010234170109030311041505030a0603080328230703110d0f05060402 65
    0x4450303000041e181340111003c9100013150041016410040d0040c41e80c41914078000b400c41400411900501980300003206c200c642035850740039180401908101d0304c00811103e2402c010543c40c0c041c00f0100b4541845414800645440e00301c1c07002081c040c0700041c0c10301c420360307110240200e0840034000501c222481c503a9000300500c001022050b141d140c050b41c170030406200741c002042f070004601310707104180a1207807044c200110a110b465a40300e002d002c01c400b0365002280c00c4111316041c0621000d4490412801d0450162515150316170700c1e4468030104484c10441d841c038030300c9110b030701c00041c42000d1440e0141c11191040008070309030790213104c01c00c031071000705408001041051401540f00c1e04c1e042281d00240c00c4030b820003001c0d5100801041005400b6840284640394041000b018a400b0704012008a400c07114480782c540e0b2020601c5140c0020700012250003004034a4001410078040c0d0840310140c2000081500c03d40d21014050b5100c1c0c0103008103038000030120b50440c98103101c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 598678651 1250 598677401 598677407
    0x8030a0c06020d0f0614010801050f0303031602030c01090b04050c0a080712021504080c010912050303040809180405100e0303010806011a130b1b03071a0a06051825 72
    0x880d40000c04294001810005502075900702c4200000391000500ca80c0b034450460100400600f6030f050300150b0b0341c2000045074685049801c000741c00150285203140c440400c250f011064400c03050003584004c00580c41501000d215009010f405074030811280c1c10146001030400829800703851240d400000e040c4506030010466004a400c8448401e003452901e03c081221007061015481141101240015210360003080d01505243c099888101d000e8a60b0b54500b07000d100e07941e02401c3c40d0300902c0054002403942d0000c0110382c0000700003084003109094164180e034030864007103030300c0c4d00051014907100c9100d02843d070b00204050003030740c1150304004055948400500c0340000b031014121210058241100448140041c110346030040192501d0603840315072710001c9401c0b010000d10030381701c7c6159000300648180d90b51045031922210682e0f09296080040602800003c070380d50310380000c80d540c0b504000442c00303000d03c3d020b02061404c0d65188440070f0401d1030400960004000007510154 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 598679901 1250 598678651 598678667
    0xf09010e1c020c0a030b0708090703030905063f0c070b04020d021906020f0c0612040f11041e0b0103050403090308030702070f060e04050a020a1b08070f0b0a050108030a 74
    0x2080c0030750307180c0310012058100c2c9020311400d203098010407400000700038007518201240c40360100c0c0e200c0740c02c0d80e00c420380d8896464841e0711015001414850050000d0300c1e10b500105600e100208a102e10598400c1c019040900c284c01c0301e5040c108100030003105038501d0446168802e04403c100c5042600d5500d40c04801040104002d00c035450012140003103540d100c64560442000941c818100d0740c4408002e5a2042e01c0c082d414540c3c45040103411003454904204c17100c200403044440030715143e41d6940c0c1184800c3c440110744550301d4200401c065100d512400381102d0b659040286c103c2c1c1540707520320450300c00080040c10076040000b0440800c0e000b0050808a0b03511103c02c60341c0b82d590304022414400d65420400109220640010302e542c2d01001c60249050b046404110540300e007810201280b2581003141c4c08202e0384003081c90aa04806c0c40303a42c946001b104900d103800c4d0780b0341d240e21404542d2407003110b182100b80148140d40403244142c2e03004d005481c0044d07240c0035000340c029041d54 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 598681151 1250 598679901 598679923
    0x21206101403120d020c07060f020708010501060509040b01030b0909010c110105070906140c12210f1603060302153004140114090f280807080403080d050f09010e 71
    0x22001403196480b500c598106c91078902281c0c16a00300c1901c403400101040007940c84c0303d0040c0704841c8040340c034210600c41c1314101c6210703803a100e1802c1d10741018800940566001e240c10f140c1c1d51623010540da280e04400f944200d5144000040d1a44000720203490701032081c0e03080710568949020040841c7c2c100301144117540c0181000740d218645000181c10358840c02210310b280c0d00a420315883e0100d00700d030240c074800030090141c00c00c101c480800701890fa44125070000b841d0004d0303804155a02080c1c011111901098a80414010380700e40105003215551a204c07044d018000954480c0788101c0e1030040024520240076403030fa8200ca00c1d14281010015001401d503146103550300214007425441401308648010941d40e581c54503400d50358071a80500c03070344511802454903040d42555a040c44000c3c007d0b141c1000c036045801901e0708901500492400c0319139080400c030100c04111441c0181541610f440d0000c40c981c03424900150100c032010745680701c50303810700b50150200c0e41c011078291805 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 598682401 1250 598681151 598681183
    0x90c21090f080d290a0302060d020c06010b070c06020a2604270c0c05060a0e0328030c0903020108340c120806060d020a0c021206101403 60
    0x141514107100419240c2500010103440001500303081c0240190810002d1007454000907180c0d548a410307905540920030300b000d9000d41d51140500c014038040c0b01924080342252001410a804440660300c1c1031000c0c1c0141610f082d0106040042151040d0080c1c05846544040c24804200b940d40c04d8283d40d503101c183c00840d0640d041355600c0c0003448185d5009100800c10714038500c2c00c210103a8080c04400c0c03c2c01480e030781019070710341c211030156140c02c120381c1d0310500501156880c44800c600805189000e091240010003162010704442030140b4010a1022201416140c6071140175044542c00340e2003500340402c3c80010009130780c02400705513000c004245441005550800620901c1c2c0030310400c2c02d801c07c500b4480c60045a40078001501a030300c600c050269070079030039074280c1d407000d070403100c9a6110f4010040c101ca070090b40d8000e030140001500b4681c8410005600060501e40c3c1407040035810b40c03042040090b0405c11b140b038100105000c600005608603c100441d41741c85d000c0001d1003030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 598683651 1250 598682401 598682411
    0x120c0a0507080a08070e0f0109060809030c15010807060206100b1308030a030f1a150d1803050d0b04060b091c06020f0a1707091202010c0605040c090c21 67
    0x1180c0210200c6958503032020102d07a949003024009002c800c4140c4800c40020a4400008114244143c0841522505031503030b101180c98035908617420440100814907030300042c480b00311810030402c008603084498140d4040a50304020310310307150002991103501158083c81c05c3c403640c00207043c202016030340018981540c91541040e2101900516802010988000100320803016450350041503041d4002c2c1e01440281810307065990030017102d244c42507101e0040d0440c2e45142072101c1c0240754406200c08045445c0c8821801c0c5041075203450015004610002403921032034406201325002510700b280c007001060304200c502502030044000d181c0c00364410340ca204180c106015142100075900c00030070740d41e909440c0207898207608603150b054042030f03080300922041c500d0699040d118000c90341d12012040d1601c0701400342d441d00e001e4140e0500c40c0440203100854018054a0b2240b4007800340c00300c1251604000c8811280407203421000c21040f0070307910ba01043c460340170110070382c00840c010075 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 598684901 1250 598683651 598683667
    0x30717061809030a03110304020a0b07051905031201081906020c011d240118020d0902040c02060f0709030f11011e08041505010b0d050a0e0a0c0e0705120c 68
    0x840555201c50400c2031100041000703003603807000004180001d56a90184070000007244040040e0009440003540800e80071018000039070100e000e0a122406501203510640380c0e00152164040212000d0324030750800202e40740b120303903840a1079004003105001030801c0d03101d135035520491101444004020307a800141c0520b12030002d40119820b990802c0b10311280d481010300c22661201c040c020104492592000406108194121139041324460420a0392518801f08050004c2d44522154010a40d484c5205c00260f103c0c0e21400d5420216600281140d0401d452054081031000b1311000810009030410701c001184920041c02e41ea070702c03e2542c40c0c0c4140c88401a190055844038070842e2500407072094103595032051645000714041c0002c1110a4580c0c2505010f071842402441d000b000d081020000b4503000b0351225520032401a800100f90140c080040d00309400342d01c0540341d20541540900010180072a50394100e000742c03d001c0c3c90315518049a0004101c0100f194440e480082040304d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 598686151 1250 598684901 598684909
    0x30112060902120d020726031804060e01091d070510050d0e030c0307120f050417070e091f1a1c08040b12090703020108060f0f0a06020f1203071706 65
    0x1004008112080d5204100501310096403041d0a116041003228031070010150341e140000400d09100da160042d52400d5008030190a036800d01942041c0c025644010024003641e444c01e4640c00f81026200c04544c440000094000c0940b0b8550f050030b1642050108000136034844c0c030281038000e407038104103441d4185821020001c1c5401e18640c140c5020009800003001004002041e8440c81128a0418000105c1d000c55410007203005200104100700000e000d031080c9460050b4003481c4000c21200c5440c1c40350000c07101d144003504c0074000d40d0310030000152002c070020324061103c20b102200708800d550342c041c0d0f100c9042311044001d0040c65040400151076551031109140d0a0300007641c1c0707503a11b9540c04400c05950085c540030551a003070401081c6000804038042c42101d40503520400540c41e200c0420068592000500303a01009000c607498254580481c080028600c41d00541020321078011420305080703c000140105650400c100100243c101134850340e0a0000310001c805559450081 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 598687401 1250 598686151 598686169
    0x9100b040e03070615090509030301030b090f0a050d1209080d0504081e0301050f03030307021005090115150e0a12030c0201030b091302032103010b1e2706030112060902 74
    0xc442c00300081e40340c240f00080c1c104c1c0201c81400c04d100400725545101680440e0016140324070560410801000403980f100a100c0c0c0004100c400c2d0361070805074460301450205101c00480c2c40780c22810800060039041042d0640840f49103d091141152030795520050748208018200a16500e1001c901441900c038156441c2202c104c4800440003c0480589440e030000d200d510701c100081c4c1c00400b81418088150381c042c98043d0001e0485034400070b41d00016080c001c00a114642da5898508007040d0060315100040144481035450361440080003001181d1100b003030b501079100c899081100c107822414280f011900361030804003105403480101c1c0501038071301642c2d0b4856100d10a1045078204c0403e48440300c0c1c4210210f5804004003500d02c3d80c803050030301d8074600c441424001040703084005001801d113020303001e1000079000e4003c04211407135040701c8d1941c1000c0402c0041c440040c1081490501d401c041110b440e4107540c50841c0d104180d804030318004051b0303a00c40200b6401c41d00c44450b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 598688651 1250 598687401 598687421
    0xc0d06090506071e030b030a060b1f031512080d0e0703080f0909070206090d0818030f040e0105011404090c090b031e0a0504051c05070813081509100b04 67
    0x80d251a410040b00c004c1007441000c02818400900682c410390701c90080c41900744641025010f00034103aa03940342c0c50000d03c040304450ba00090303040c80040d01c464409402e09520f0350300303480024031801e90007010754140225130000c0f8414028142504040794503441621030044840c50301180d52260184414200b1646620040289401040540045100b03074003818040d8810b5545014581e900c0c1802c07651610241c80020f42d80e0040203000c0354030341c4070300a605e500007032a4049080051030284601d155034020052190f0303029010a05006100c0c10417280c03401007409180980b41c0744280c82da81501441a4400c0c92045641c0b030544000703039409011a80b00a14081410649030314243c1d180f00c00200d82807030340d9014500544000307900d8040e00d00c9114040c5400c40000c203410b00ba154021500c10110088600600205101c4da100003104840104145082204120300d46071074084900d140001c000c0700500280400300401001c01c000091000003641100d00114a454000f80400c0041c02903641e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 598689901 1250 598688651 598688653
    0x51002040b3415020906073509060a02031605010923100f0f14070909060e0402091b0316121415132421060b040b09040c05010810080c0d060905 63
    0x502601401140e403810746810300d00c1c640200c0c1c01201100030703100c1c1c8c42e028404840d0740f100901420318142840c0018107400441c03801128901511085030420708410003108039003c6c2c0d150f480d0b0808000845050410803e108107401188411014a540c3c1f1040444081684199218440c07401d1041c59001017040b4024070908001c0110460640e070b03800e40080b41c020001ca1004ca0001401d070506224040440ea8011901c1c6c0341a190350b420400c0e40390014105c0c840d40324800c80740d00b00008603140154002d80d2584200d90041401030b40c060b100700e0700d12445000d000d00e04004881c0e160100445203a0000d000001d410b00348032100000baa44c00481c50411070800d1804600d8076034282240100004200c01050828005543e040c0070404099a00c01c1013010030428411840054499000741c00b114500500102c0c4d50386080000c81d0407040115030546111240640420a55810504942d001270311450125102410b003520070790380c2e0383d00242c410f00030303005515070034180401a840001c082d5030000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 598691151 1250 598689901 598689907
    0x120a091703160c030e13060e070e06190512010b0405131811120d020114010512071203120c0e120c0307060c02031018110603100b07051002040b3415020906 68
    0x49100001f020f4a00035410310403202300201c0c01e928005c50340c1c6607907000000c0003149004102d41d0040c41d400c4030740320403000b030003000d010010844144641c003602a141140c80140c4030b525050400241c3c11203140407001c181d1070840a842403904101c0c1580d01e07503410110315104000408042800d1015400700c4040070302800144581499045d0000030113500000c4d6810340907601d8108010f00c0c00742301c1405280640c071180d0304101d20a001c84c680586c450090400d01c0c80b80503400844002c2e1102d80110000144041100220a290549900e104174010000800c03c513416a07002c2592529103009890600c60005580004c55800704151a5002c800c464244010801d81c0400c086071b008104084410f00e05c400c1e00c1c15014104002601e2048240d1a5020103503031600c800380382c1a900280302903440c1c0c0699034481c0d0410b04140001d1000b4030150000c580e4620a15110541c1e203a200a00c4820003081c180071800002e2481171b40b075480b40d42211109002c50726001c440c4000303100d100c25842d000030004c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 598692401 1250 598691151 598691179
    0x150a0207050a0e0603031b070308210a09050721020307030605090d050304150c110d020c120a05060c13090e031e030f04030e0402120a091703160c030e 66
    0x1040030821204241d80c40010705884a1500011201c00c840b000e40503441803004000c3c14107141d080718081d103021400d8030150390301c3c0c1e01c1d4061141d108581351005210451b803000b100d0b07180c4810752640300d0803221080194400554032a51a05054802c008001d041c01030300318030711600d201c40700f0303d45a4002d040302c1040da0b0701d182c00d202030081221080500e0160410380415107019004891007582e118081030250350700a04820000c00f603130f4441004114000e01c14140340c010401103c01300c0022a0010140c0302940300410500e041850360f812000e41210051400091001801c6908000c25040440c0c86481c000400c040030022603204592641c14840040c0c1c0803800030008040c0042460503902d841c1c215a22540814031058800da5000200000045d0210f0300c074052410810700e009001505e0213003004090100c0343c005843d0744140d165100500d000b00700132220001b403990b00541c00c560862074480080d400541424803450b05124100e0352440805210310300c15240b80c800180f241c0307068a14 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 598693651 1250 598692401 598692403
    0x10509062101140d0b070305040305040302040e011e0234020307152a1103010f0c0315060e090a050a150306051602070f051e090c0c010507090b040e0402150a02 70
    0xc01e120f0500c800071401500280c43c10540700d400344050300104505030503103607107808600a0074020000d0701002000c0c031010005903294040c1a0070108440004103c10520918030001400c2c141020310045104200c041c0d6940480a01d070111060762044054010f107400003115043c4030407010007541406803210109003a0840244a200421155608110f0615170505010407401d0000340c0154480f5890000300054160141e00300c0c60040940080b44058968480f00b055031101d034944408a52900d0610300d24038650923090000300f0030b030726240c13504110384d0011600708030024011614194413940081c4400b503e5030044104101204815070700705543e0b0405600810040c3d448250144c07240c460031944910004020003070311030100032070076043c2c9000104000308803100d049120400101105010560315081c0b894401c1c0101c0f00003951b84c02d4044416821210014484030600c80c8143d4140a11211942902d09030b480050341a2075513100c030300000b04016030150416090410000d040b00c44198 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 598694901 1250 598693651 598693717
    0xe1606020a050c040207021e0d0204020a020c091e0f1003051c0e040501150e0a05030f06010f0801110904111215030111090f19150302030403110c0109030201050906 72
    0x70203842900e104214600030013090303114411000e980310354002c0401d502011040341e901c035840c0004003c18410321b00c1d54081010380e04020f800c070000d60400c0400c65450700300151426070002e40001c000200300b21080d510300c0c203880007400c00c1c601003181600003800002c5440c440400346800c14101c074880c0140a00040c10f8980c2c8903030210005843d41080c0002c1d00741409180c0c1a280c0d2200c003a000010743d0b40e000c0754a4201c42d11400d80c05800b08000003001e803001d00c607010000b11050090200e660504d01108482c0007244d00030003c07603141500b420004045001aa448104121004a908031f40004110014025000401e480341c0f07090742070161400c54414441c01180c0e0540090009064241002071940501045103804c030410380340e001000e240100318003000768079816140000503207030001550340034180003010003c694000180818981c1240e00d001c40004568010895214041d000800700b050911000b4140800841c45a0b469601d40051b140b03981c00040c81c500c041040b200100c8aa00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 598696151 1250 598694901 598694903
    0xe0303160b060a0b130308030703090b0a0506030f0d020a0210140c1c0311030613020412050f1e0d200d0c060c17130201020a0f0503130608010807090e1606020a 70
    0x60f00c0c4030400078101421030142e4007081040104030340c40f10302d5601c1d000c6140c1d10042c1803104040e61039111000088284104a0181d60920030004251801d04141423a0200a03c0c1c3e180c00c9a1007415981c0d000340e80041c00e9281d5030341c15104400f40d403180c0042a100e160040f611002210f0b0003240340302c3c082c00005086000c540d85695110000c0c0314000d415400c071540d415040e44c100d403003040001c445080c00494452580b1002c40010302c3d02da520001200110900070045440ba0840700c0611540314080083d50080c1c207a0010780d400c00c14500c01c91a0b9030b0a40789107850203100c80403103050200d030301039100700c01c440c1d591209481c02040414401001c0c810454000c079600c500c0c105607400394910590601d1401c002103d20300f005901c90b800d0704c0c1c4441241180c12411485070082e004000f480001c001203c072442400215254040c04210380303301035184e0411401c202010004000c9031300300240d00801c881d07000341e000554400b005007081c1048206084607115600c021030003d455940050703011042 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 598697401 1250 598696151 598696159
    0x1e220303030903081f0b03040f17040e01050603010b07020d0212010614040f0c0504061b060f0614030a1119030b0403050307020d050f070b0703230108071d04030e0303160b06 76
    0x3540d441118105c1842c00b10200c0d2a5140703010700611450001c00002c640150041d449034050315015558400082d5110240380c11110340410100302900d0288041409003038221078290440d818540d1500081c0201300380603118903840541030096417580b0b00c070304500320b00802c028444103071036142c800d243d10000000749014900d0b100c480c4446880d18400c0703240c003403442e0791380b14645840e0410880b02d100350f401200116100071212030000035543e200c0d600f0307120668503010400c00d10380192680300030100000c2d039000b908118450b03000958817841810010703000311454a004c44070420301900c220203030f4100401c4104444244014190814042e610078550b983c00c803030a56683e4581110180220740c12101c0c41c28040c0902c0001603000c0030035950080c4a4500002d14905400b01a50b2005549402d61116418400184403400052001601030b0900740060034114161b01040c1d042d440c1c0081014042003040309040c20141e60520448049514440c0d55050380d103c582400c01c0303681000d40d809445 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 598698651 1250 598697401 598697417
    0x1110901140c061503161509080606030601030611040b1204050f15010b1c05070c0302011a0a12060204180f051b070b0703020c0111120703021e220303030903 69
    0x1072540800c11200d00014a03405030903a51902c1d020440100012809141e01d0300600c441464807a4081400030028000703080b5107520030380c5c0c800c00605507507503641260105800203410802d9540b0005022411607611203800110f4803100081c0c024280a1354014070300000300041d80041810448081601441c042c2065854401c900c80119a44200e125101b10340d6007211401000001750003400741860380c40168425208002801d9901c08441c41224800086000c1100640500d603091041c0c2d8140e00d055800c84185000050000d01c0c85c110f03a01c03c2e83d00c40c0361406660401c00001d501070b03800600248040303c20421000080b44c019001c85174508600514150000e4440291041101440740d40051058036040d203a45a16590341d274014086018180c0070008584240400d1107090801e50701060040d80b0f9500300001c00c20701003c0684620b0816005000089114a1217455040720501500003036035112459843d20200703860700b849803d0100c025400010038035405403c038204103442566035400d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 598699901 1250 598698651 598698677
    0xd020a0504052e050c07051c06050703020c0c040f0b150c0d020c0108060906031e030703020c0a0803091e040212160f0206060d03050f040b040503060114010c0206071401110901 77
    0xc83c00705143c0744000c51045068407038000c0c0340144018000d07800e5450964039065101d001042e03440103500c50180f03000340384220034000d100f85441815009210707031030107615000110700e0481d0b5581c13034004001d00c1a03a0303c281c1c1e01500492580290300d00d000c0940a402a41c4d03030082941c0c215046181e00003040d0244000e114503952000c80e00c0c044041c0161600344036900d54009012941400400b1075070540303e120511101035400c3c0e43d0752003084810a00031550380d104c40c0780090a00040c103540502034408002c040c0011180442500c1d2801b00513500d825001101340c4829520707101c451001a003181c070001c1d1040541c1003070000035100c0c0d038203070301409528402c101d412205403000c1209400182c00a0010482519044e00c0d14001280a80742c1242403107031507904007017640c0c496404035143d000000b5040210381401d101d62401041b503c44042c42003515640042c0540d204111f00920802e800204102000721905031403446000703400080142c03445a0300c0600255020010580c04a07100c100072030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 598701151 1250 598699901 598699939
    0x3022203050f07180e010209030109110414060d0605072a0204050f06010804230f07050f0109030f031407050114010e1b1c11070515013303020d020a050405 68
    0x110840d113000d46075550f000e002001050090504411441c2d90795020040c900e501d507002d000e44100180181c1c041c075058041081000101c074001941800c1d9003032420200206503441015a450468000101103480d5554807011107910390003005400c541e403c2540c5042001014083d10070142d84265810049600c4000703400548010448038107002405d00d00014001480a00c0321030558a480301a05400c0e440381120107042ca071040014a1150340041c200300820b19094103141030441c0203090a84050342180c903071a0307014030442000b80074040381000b1041c82480c1c1908642805400c08020030070f100d82903090f4290740c00288504c0800b4044200820f0041c0d10400d08090000c12212509141c4401c407007081c8003084412001d0b200035651528040072035800c3c58020851181704401070060480b0b00c0750101e0032072906821465400740c540400746041c40b03000d507500d00c0803070202c550340042555941d002c80180c481c00110f407541d6800843c2c0c0d9420f40350080b020344207442c021039414100d5102c0041e60 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 598702401 1250 598701151 598701163
    0x2161a09010f0b03061501051608030f060f06161b0602010f0b060c070515042402010501140607110d0203010e0d020f010209100521012c0f0c0a03022203050f 69
    0x194907411800114044150001e82003001000c18104a03051507820b03202d051610309290270170b0715400d90000401011158209506130303c6a403c94022460400c83c00c0459a03030700400300f01500340c022102072241402911000c038240341110180034402281c4812000b406031003403540400305641000072401035842c1c00010364060340000801000001c0c0303080100903540d40e4619034100728600030800407600c4000c0240c8000b44807901c105451840010705002401c50704140d0001c645504941010906136940c0011552040e400001581c61183d0300c0000030307030030004600000d5141d80381206034512280082001690082c060b002d0b00d0a0048100340e4500340d03c1030b10000c1f540024144180440d090180028041e000e200c24400c5040404400320b0042000080c2c001ca0003920704000c03a61140320302540700c2c1504680c580e004950904262400d0740e21014058114012402e02044038140d1620030760544d013000e010380801d031001e62000c0055151b420024002070300c45008407400e008034800c0001d50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 598703651 1250 598702401 598702421
    0x3070c030305090706140a030f0207051e060106080c09040b03011a270103240207080d060b090306180109050312060a0f0806011401030209030d020d1d031002161a09010f 74
    0x2d1001044420407031a405135011900b0482812790b108180f40ca000041e04c0508592031040c030017444070b8900c4900c4201401e242034520a400d500c202c0c018030029070b102844503000480c0079038650310756020400040c0a00041040d29400d586410f03143d21540446005011103400c2c142c40300110724101c50040001d000340901940003400c0c1400c01000015100031141800c0f6050b40c607410300004070701c0c0305a4140d0b80941000c0d61002800300c0e031034001a03840d100b071200900c40310000c1c030302c1d104440e80400d1310380b10010a0b00081c000c002e03450300110720b000c3d0400c445140d40201174960b14103031840b210074400c1042d075505024246290010901885112202003a101004010b0149a10341224450b50300c01328079000b4100741c0c0034496071403952010000303a48406265009060071002401004145420690691030211656040400191004606c040144c0d082c3d01c0c0c0960f13102c03a244c40c5c1130a00540d04500400b0f030460f100089198424000445004001080c004d0000e00c5000c0203440c2950311581e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 598704901 1250 598703651 598703657
    0x150203070f0f03031103040c090501060c03020c010c06110f030f060d0c1403100609050703050603070b0a0302250308070e060a0f1107092f0304112403070c030305090706 74
    0x103125404142d62507240e1903541e20918012401d0207810401c1050740d00b0550701100d19102c10041480b0b01140d501519000d006e15103050800f04942c0d442c001d6880f00800c170701d1070600038074208400c00c0c008140c110744200658440610354840c01d06200c844182d100321601806c02640ba00400c8042c609000140b103c2600148591205801d104e445e64107030340460120340d03140c8290241840d80722640e004910041c000e01100041300c2c5001c3c500a0151040140024800e4004500900882804806850180c8500c1c6001070300c0d031407941e840c0c0c40d080e05402d451920301200460588101a40228010b00c90700c00c1c3d176100f600142c40300381404094080d2820840105000752101d9804600c1a40d00804100c240802c456503660381e103086604644505141201c0c88081c0140c0d81500e40c14002d240300074404028005141d0710f030503100c0100124000003e0b034401c40284800c403100030b51101744071000c1da880a144d80d6890902d020f000c0c020907005da504501080c104400034840d0300d00030601000f100d6550b1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 598706151 1250 598704901 598704923
    0xb0304031205100612050403140f09040903050301090b01020a0203060a2708032a03040609020d021f09052d03100c03140105040504111530010806282415020307 70
    0x410209d003a411005007075140315000c1c00210015a40e40c019548854041d0302d600b40d5950402c00c0200668281c4d040341b82c150b6100c07400c6c210043e10000b030a00d40c010039150002441203001c08880e40020300d400030f441e4424000303207070602c14080300c200214011454240d480c00c82c411480d50b41200d038840c01d400600c1e5071105000003400700b03c40e9000700c07540620003000074441c0303403081d0b001441c03581611614074110764641c07100c1807180341c00c4110742000e004101c030b0598401c200b01101883c0d8008180300104400100c1c0b940d08103a44040106403035400c03007803a081c007040211500003002880e44581d40312861074810000900c0e130505105040c01203400c2060718402150a405112850706210166890100300b005802c40d00714807280951460415040e5000c000e200c0400c06110481d07040e004213966030007490501c03020340b4640751400100c544c080741c901c00c00c2201050520040c540c4100422503400e86082665202c8440c103900c00968980b041c1c0f81c06c141c00003120481c0c0c0c03402411001001070b4444 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 598707401 1250 598706151 598706177
    0x9050709031a0c070b130203010b0f03030403020f0d080315010e0a0302030a110111030c0f0c04060f18021b0102091f09120524070f0f05040b0304031205100612050403 73
    0x320020750050304802c106281038a10f030340300e22005c2401c90344400c01b24010302c83c504c00c40c9000e002e8405201ca04445408101c800200042e84900c0340e840000c2c89002c113940307003070310780e0f19030218000040f50007840d803507124a402c10006882da6507148860740000d0708194145c1c1d607458240e41d9042600c0e00540100507485007507841c1112250b10044417410f00c0310741441e01d081d51030100000c2102007503080240c0658840d0258452a11071840f541521503414900140b01d42d0072440280021a45044071f01d003e4130140c020244002d100c0d083d110032254884005201100c0c8054000303051410040c0c4081030110054000c02603850442ca482000180c44140100030b00c01c2e05121450406000301c0a99000c80c26849400401090508040742c650b01810200206581c2101c13020282202c1410807840380341c0600001441445980100c0f08001404400300e0245445019410024181200200842e0504051145082000d482190700148070700c0c1e511190400d440c080c05005640c151504080c035040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 598708651 1250 598707401 598707443
    0xb090c0a2709150305030c0703110d020d080d090b07090e06120d030e1501030605060a08060126010e2e1802010509030f07061205130f030e010e090a060905070903 71
    0x925840c800603c15900340030020030b10a0005007845124480204010b40c91031520604007181000000c0c850180c00d0504000368690188a07803d0380d41c401d040d2641c03104406041001042c0103603014206a00800030405c00581020725402505c0d0220461246a6142400c100742c1c10f00e004401401c0743c10003100684842c0c020b8000d1004c40e0001406e503030000e1280160001d8204c000d81c815106103031900c00303006850800c0c481c218017030203200026154940c1000c014104a89007208a524000d054200300d04c00d90300298801c141816050041d5042c1300c4a03000001d08100031080d43d003400312826464102404050700c00c1c166000e40c00c0c520000c48180680065602d80c00040049815000c0d071403110010550034070001000c1c199540312428420400002c001c09c4980c01400d81140c4204003c00b03c021850800c040441650725203001c641d904100c1d00100c0b0758100003581c0c41d4000640c4810310586400c540c102d0400d464039160101f20355038a03c882156803081a10019000b07201c6042d002e105241 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 598709901 1250 598708651 598708661
    0x120c05091302060f0a030c05070c06050a0e030102180906030c010e0907300c0e0d02040f02040b04061d100c1412070516080714040f0b090c0a2709 64
    0x1c0030000c198140c400d40d402203410b652000b03800c1c11600c60001441c07241daa402d442908040c40d030728a041c9060910a9880030b54000307090103030320140704001c1032110300c1d5441034440e4494240003a00a41d1601ea04000303144841c69858070241c8507014032000241c40f0300f00003505030f80200e070580d9480c960100c120103215072010050150403c0100a050003803100e01215114030400414181b81118605500440f0044400a0002c001009140300c184201560b8807800c20b0015901102c0005414410010f540c00070f100e9a40902c50504011500140c5070b908030080ca10f403580303030810f034641030071009003084404002902000c000c98240007200011442242501a024108104a400110350703880c007034030b042d00b0580084806520206100d03011003009600c0000506142c4000c4c540c0a05298200c484403168421442c011a520209455008215002084074000c080d00041c4c0701c0c14552203480e030641c031158060020410900504001020600c00c0300400082141c012404034184201400604 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 598711151 1250 598709901 598709911
    0x181505120309041d0a0b011a03010e0712061a0a03050c04120b090f1b01020d02010605010806010e030307060c030504020306070509010206040f0317090618030c07060e010912061401120c0509 83
    0x18600c20503110f0982c800700407a104190251b07240f10029890864908000606842c0791280d5880c00c0c001044018555501940c1004003030600a0102400d50a140010301d9580d01c1640000a1a0070008a400e0601c0c01050b6203075582e0303403d0006550710000f8860501c01c0c1d00c00e50800c004600e0319140400c0403d00255040f500403006d0341c2c1e030000c80d0b2510302d140c6141e2400c400c078a454012800c650540c0c0410168401a81c0e138002400481e140100280c0b50440041c1024144030041460408a0b5010300864410741d6009000b0131451901400c0140100781c210b03800ca00921940010a81070750041c01600c841010590090640d607070b4030381c1c941085030074100d0101d060007000711070700d615089084060340c0724801713240081010340782c8420180340b0720140401d501e80d190010442c00c5402c5001084081c00e85005081c00961078040100481e0904402da1000300b42c42d03400910394007000110340142102c407119050480e01a6200c00b240c2c0203e0905120003010201d9485007080142044407916030f0007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 598712401 1250 598711151 598711181
    0x9060b04030203121b10060512191106041806030215030f0c0714030a08041b030f0b100e0412020615010c060b0103020903121e040302130b0a18150512030904 69
    0xe1600010309a180c8801700c01e41041550700c4010501443c01d02140000270300001c030000700301c012100a106550080000c0c8090329035003520441c1a15500ca80c002ca03001049080d43c010b2844886843e444005d04160004a1050804181c3c076038200031346005490050300302141c1c00c0c01c0d54460311400700701d03944440400c4503034034100034844401d000f007070000e400a034080e40c403503ca46241074500301c07140c000c1c00d954030954000040018070100e12058200340c19203500000078112070b1542d01440001c00301d154040040241820108410000100c0d5182d001003080e4085901c00d44865441048000029a9190010314000e080c240403078500d03001850402010304006140410302c01c08079007861013442c1400881d900001301c0042c0465101b180501042c0400c1c4190700385429940003e400d0032014038030085203921405604c1ca240d80b450940001403440e44c1d01c03042d50b20448906c98015081a07001d8804a60f02d481d0300081600f81450038114007603013880a94a048040703000c000051424400380c1c250 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 598713651 1250 598712401 598712437
    0x1b1112090d0803010b032a0d0203040609171308010501140d0c0504020f0c12160f1a10150c02221509050f01060e010f0c08090310050109060b0403020312 67
    0x106807600000c5010708080d14200c1da9a151031961801c4a003246480e031603000d800b41c042030081c00c0007e000d80f865040140405a582e45503800c240003d8409280080c007a41040c0c101030800c00e0303281c0300601112080e55400700c2d28a560320001f0303081710000d00c19640d0000c1c0c490440340c4545058808101030f01e1140c0c100c20000c613200c601280490300f0000a03e1214030000504104580e020024421041b00c1003c44038940702e46801c14031034411001c0c200030583c040169440040004600c2e4030b4116540e41440c41e40c0500d0720310769480c6071802030300c215001c1810034020089840c1c03283c20818009238029010910f4001c0b10a11003500d01070120342d01e54050703622402c0d00006000d00080b00f0003013284100201d200e04101c03100c007080d07185c181c0c00b0006201c4c0f41d0002c1e124998100308409018011400c0c0200e03404010705010010707200c0c1c428100c5d0b040c06608644041c4070a15801b0906890380c450080000584600c25083c480c440c9000103980b50b805070101180146801004241c098a5040001d81e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 598714901 1250 598713651 598713653
    0x103030807121104060e09221e03020606091311090a02090d0f020306100e0406051008010e07060801080718110408070306141506030a1d030408011b1112090d 69
    0x2c2151143e120110000740300080400c445680056004080d010407201c0c4111418099100c45e00300203405082c000040001d100b00d000d00c048078001c012540c0e126072101c480c8008501d170080d2111022600b03144951400b901040e4102d25545a82c1d28059020118050612401c1c0c1049941c0d4402890040c00c40d03000c109014042c0c485500c146803481c410b01c4c030f01f20000010b2041600b080d9000342100c4c12116039800401001d000c1003040754025030843c1300006e15403681d0b00041ca000110390401c0110303601380a4185402000010500d0413148aa0b0303405d50143d0700c0e081081d498070141c0c82007103600075401030300841c005071030382c414502a284000d1191600d81d07198001070404099074410382d40345640d02100500180c0c0c0c00c1c40c5640c44203520703240741140c0c0b038403100041681c0000b038a011803d558a1030128504610701c50600c508030510400c80e03032a81c0e0b0300d010940c00781c1000005005103c4e0341d03240d60041503000d00b21242584503003101928450f40030012101c490340142c06030310b03070080e20101950 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 598716151 1250 598714901 598714937
    0x80f09030d0c090f060503100312020727050a060612020d09020a080714040209010909050703150f081b060403121e0522080616030915020c060f040b0103030807 70
    0x20302e4820700c0b03031502101180b1346400c54074109400c0c1e001c04c0520400f0410840070300e1f1241c0042003a40e600203001840d541d400311040f0703d000c1d81c0d40c010300c000300410700b41062100c003412016801104410428051503403281000415140303503100380c1000c0303141050070074071401d090b8024000071105c0a00010f8901c095400107805840d80b640880d14036003107020244540304621408401c06103040d1815460461198002803200d2054402d10100c0d540d128045220984a40c200b01d05400321a00c2503002507444a905a6144000f4410a0581d10490712164540d5407109650021100d00034040c90510703145844000101c1c0c0c0b0701c2c04070009c200b204400c0305108418241b07054100c01c0300da0b0741d860315880d040b410b07103040343c4aa0381d4111540103c024200008100000c5076030b80014051481c41c092100303004c05034090034560000404424210050b40f040b1003d5a01406400d000303001140c4240e1148600944a104252400307400220342000500100f40911601074000300c0c185007860302e24003241601 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 598717401 1250 598716151 598716161
    0x1d0a0b0a05011211071208250f0c03170108010e0706020105060f060306150706060312020c090a0e03091c0204111c0203180313260316030e1201020424080f09030d 71
    0x21004079098205000300800b914050585e03186808c480400426030f2480090000415000400200002040b80804142c803130700040c441a0500c80313005c0d0065845100b994060101480f0501320f0713200d1104001000340c030500138180205030181c034001e40c0c3d80720312040c00322513030009042c1604400b8141000680810700c07001006045d01540c00099a2815450500300c40c00881c80f04000319400007800040ba640c0b01501680c100002d132030001032000702100040e095005225102c0d920018440c084000000801c000c442018401c0710304100d00c8a030310402d840c0354010402182103c1c03014820310071034200107034001c9d41c006814090b81064103000c00c5030585594029101100c082c059034004003d0382c082e01042510301042c05405100c428607034a1a99607a0080c1d11000c1000d8044c0400303d000d040c060352010820110142c1804102882600704030302030b5003d84102002c40b81d11010b0401c07040d00d9021805002c01039070ba2903110b25160390303102c0007590401134200780c401d010410000001c1503a504c51 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 598718651 1250 598717401 598717433
    0x36110903031201080615180703110a05040807051002031b0a02041a090906060d02012d09140d0b01091508011d0f0601060207061202041d0a0b0a0501121107 68
    0x385450310341c10130384194205507014040150b0310342072803844c850360390311015039031010385220b8901d007040c0c2d0307542d0f90480281500e0b600c6039104d80000998400c106034490300400603180b01e801120907e665480520051514036006200141c2007403084040e40c209001c40c0e42b0490105408840300740705942c001030304640301840907681d2100c80300c640c3e02050422601240d808811100030740540e15080c1c0c00703d43c44e00d80d0302a001341007150454404588959a0f0404890400640c0c1380c81014003401c4800b5202c81441e0091280e0100c0b200c407203102c24900a02d41c0b0410940c0154044010303480c1030001d0025150044c0040b90450702030300c001c03502c00003d00c5a808907422801556580302d1181020381d003031100c0c4030031071a5141c100d00d00510407160002800d03412115581b50052861800c07541440c004e00850b0000c0b00110f240251712400c540b80286014050501c1c41c3c0100708540c044000c011450545100301800300f0b001c4803d0514080e075540c04103011030905202c0782d03c0c01c5050355401246200000e1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 598719901 1250 598718651 598718677
    0xd320303100e0a0c09090b06070605040308041e050a06110d0903030c0914030a0308040314030108010506011116150306180203071707020a0f060e0a0c3611090303 71
    0x10400140b842c0422034010002c0ca0301000070100c1000300900320640d9024292585468440030b190985424003111049a000b010800042c180380c60020324024040d2020384407000348030030703000c0c00709080c505940909500000a088011b2503544100160401e0304d42c4000912007407290a041e000300d030240d024128840d5030005411840030801070050041c1e90030003030510300481980e103019240000c3c49800d4942504010b031803076451740b4048400021011383c0c00c40b03c580104c00001c900e00150451030040100341c86401281070702c0b480166070f66804c950b881c600c124860404121110018001d0900b000c4075190128010382c030350130200810442203000500840e400401c000ca8240d000459840c12b0120300702c010314500701054000d6803a001c00c6030141c104070b02501038504012840d0700501d8120341d43d07010349085942505080c1c8500d8418400c404462a85072a03c05031408190305450b45948a02104c4500500072000341d001040e81041d60413101d0300030070000d103555400700040c02c58004441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 598721151 1250 598719901 598719931
    0x504022704030c1e0c0806070e060702060304050703080c0d170408120403020c10080a0b15030f0a02040e010e070f050301051014040305010608030304060b0f010e04020306030c06040b13050d320303 86
    0x1b007140e880c2c90320040001042044c420305101640d45c580c01256260b540440320151079884500345507042000316480100b011038002888002c1c0381d004203006440d034140e81c4661180c0d007042b641201c4012800c4030000c1c184001008040130074045484c90641207070003481104c01d00e07182800418004c9a08240e20700c040303a001010004459007030701414442d00c2c0d05031a120340605148040010500010700b15407082e2202c40001100852a0350658008041c04402602d0035603440000380400001955150000381c0800d034030404186c01101120704030349000e06002d100f0661101d00319900b020f4108102c480000400000000c5502409040003410032800034580e00e04040c5416030460700c030705104a000b007010303020358041aa0041c190b07840407034050343c0150341d03582d4440c00681010b042c6ca01d000d40c881004240801c1d503003201000303040030780a1400303030b290700948400070014601c240c20002050b02c4030301d6980c1c1180480c0b40250f1010701d0030001e100e0200440c240c0645095400441320002c0300f400308 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 598722401 1250 598721151 598721159
    0x5191d0105090705010207060503070c080a050d1401150309060e030a020105010509010816050108180105010324050603030405040b180c0a200706050f0d0f0504022704030c1e0c 77
    0x303104282d048524030000700200e40c6000c001035200e69a52184100b800030120001c1c001c1c0b4020010004290fa000001c107641d40c00c01d40b006050340e04800140100c480c070f03103a807001e03c0c0f50021140c68180d901a01202803403020201c0110050b00c24480201c0b4526240e8800410340001000a40250b0400e0340000c81e07198100800e0110f4100164081c80e03e66000d41c4514081075542741544060b58000e280140087c2d6805041d118a100e2004400da400d41ca00381c00002801048110018480e40100c204464240145180b000340d500035520f49500da0808c02080041d40b602c1d40c81041060700c043c080c1c4803419500701a404541008031200c0740040c0d0001400c581440c0d0120703403d10b0000b956410000c03400416906030b0381e030f107030107005942c180000018007028001e018002d55515042c0b1080600110490f4034124001c1e102c01e4404902400400e410080d4002d50050040a20b405046425034141e0f6192821a141007a010701950302d4110702c84c2c02102090402c0f0040502801a04000c070900d1030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 598723651 1250 598722401 598722403
    0x603010801060e0601080c180f0603070305090d020d02071203030902151c0212130204291e0607060504060615110c040e07091e02270a0609030605191d 66
    0x404c4035041140c6441040001d11a61050310415410f44102054003008107001c030f4040740b0903900c000c2c3d20440100410006641c140c0166100c0c5420005560950411640c2640e44040e0105850090f03003000400340b103040300c9108204d00c041d000f4a0b003c0f13280c00300d9402040c10b42052110a011941000034007019603221700c1074031401c0518a500c01c61a1040c0034205051140028041c25521000ba000b80c0e0250355a0b60480d541208a040040348254100c0c0b080410000b00310510b2405070000381440d030000021034040c1c500000c0040c1105252100d103584078070013800c4c018011160243d407407130007280f282200e05440c84040c000c1e0326011009503c1f0317281c8070700d04120211880c4c8a141880019131488001141131002c0341c1209401064141c90700c00a1030001c0403034903c041c1043d2000c10880310010354032401040c501e009010310400302280400f4414000800c0c050301001c184003110400000702c041d800164815040495102d260044c400d02e1000d8814040c0e40d011690b0701002c041c0380b4550 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 598724901 1250 598723651 598723679
    0xb040b0415080c0403110d020301020a0309020918060c0c0f07030c090e01051018090b0c0306180601020a020609011209142a010809070e0408040306110901020c04020a02030702060301080106 83
    0x201c90506002c2072070001d407240d48500c640d000003040c001148a43c161a6160012038020180e4024025505d800442000030010b20580209a103d80d41c10000f041900c00d0481c0c11011900d144400b03080b030b81c0e8444860f80003647c041040c202d400c3c412504e04001a01061000030040c5108a4244019a01d05803140c010780d40b0b1103949811907494002070002c41d000701181c0748111303904844518003030b013044074020008024070080589944030440800181c08200c1c0d0045100c0c900864103100480580388039960058001c4400d9409070348214000c401605e070100103440840c20500d8000c0c01520144404d90554144c4001107a100b80c00742840060403000b407181c070a844505d503400011901c42903500c02841760b41104914184401d11000c00c150034014005c0700d000e0920340320321502c14102442c00c1c41f40b0394014407050b036840346007166029403048441e046610441d016401020307828100340400009500c10255001035201c104600d40058036488050740c000d000362000010654600143c0b009009 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 598726151 1250 598724901 598724939
    0xa0303150e270c010c170f03100503150702150613020d0e010f020a081b0f220f060e2b050c030606010306030f080c15130201180524040b040b04 63
    0x1030001c140b4074000d42d9111024151840d00440c6807615000c0081c6a006e140c81080f9070017000006c0001000004010300780307900215401603080300d4025011014041002c1010391b0340c1401170b08074100082d240340c007107491507130080d6009200000300d136546400e48049900201050803944d80701c034010003212100b80710301d000041a4600030740c50649040001410440000e01c08030b0703a000103680300c1d0314245400c2c0c10b44600c2900c800b40c080d562601d1078031011074260861036070b81c610502c800d00800c0344c2c0401d1031803e08a900740d45a004c044002d0500300400001e101c3c445440303083c08801002110040103141811050103503010b088140d07094414113090000041445046c503041110400004204000441c540307908482a01c0d02c40010140305800c1a421b091244864032004040c04410000d005008640034800d80ba00e00c0350102c90800c40da108503151184681c06446120b420070341001c1d1468010f6400c00039800e203450036031580c07405409600903030458808607001007000d024055000d01104004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 598727401 1250 598726151 598726153
    0x60403020705220e03120c04170c0109030f050f161a0f0702101e080a0e01060b0906070203120c070602100b150724050703060b03090a0303150e27 64
    0x24400c482e6281d2110759180d00403000766a0b880740c41c0414070038006c1c0e0301d180d03002c20401881400c1c00640703e412908a80161001c001d07014a0405207031030001241035072002c0684840701d0795855030302c4030050880000000c3c0e40e517020307d4900c42c840031000c1c081540e0072000c440103481024200003a119100811102d82c903582d2008105c00754610000000380c440c074950488008411130aa42c2c0c0c101c4a0407030f4004608201820240036420254100c3c074403610480e00440300700a01c005110140f420380d1100d100e00c1c03152010800c081c007070343c0c20000d000b81061070010b0100c40b0801c0c0341030ba20503250f52000da0b00703080a80180f08248501c5505000c420b245062514080c41100b4a0b030001480b00340d12070f841540d46600010300b1000704500081c141d03001d503100700e43e004100040c00000501170075044030508006442c0c41d00c0880c0042140040c0d80c080c02900000b0035401170346036003d81c01056011041e01445894940014042a04003c02441b0700810b0b08007005980ca10328410030f10076126010a005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 598728651 1250 598727401 598727419
    0x3031d0406051809070e070e100c0b060f030c060d05041209141e040c020d081f050d2d0611041d0a06080106060201091104060308042d08060403020705 66
    0x1583e580e0706208059414881240911900d401103150b10b480d44551016007a04481001c000f1040c1c1c0207051b002407840140c482103200c41805c60101d840000c1c00c50005c210b80703290300109000c0e04103c0807032030169034054200d40182042c0c40002d00240c010346d003000c3c1e100e516902040100f100d200c03001014070481d81009003030f041c00c1c9110000c210b0340ca4102036008200e20903d044402c0582c940d0384240500281080014403002c40b0020344911062100d60042924100860340050903c0d004200740350341150103a10940c104800c01045810b517840031755a9241240140d16094a0344c4030004404006d01c80901c0c81c0402032402c3c606079036200e01c04041c2c98005000400c25810300c13901c40c4454000c5448248196070313031500e03600010042a00008000d601c1d00c07c010420503015800308001d40d00481030b04800d030301d142c410002601ca40f800b0017000d403141070004010200c00092000813040c0c5249203e04882110a840004030000b9400000e40d5481081840b00f455010b10200c40580ba06a0308001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 598729901 1250 598728651 598728659
    0x60a0e01020702061c1b050304060518100b030708070e09010c0e0f10021606110c0f060406050706060513020301060f0f051b1608030405011202040503070e1f03031d0406 74
    0x800e81c010341c03c6240000032440c003012a02145d561200c0180d50700405400000e424044005003941c104403002c6550b070b8075280208180340161341e07209000f0110480200b804840014420001d040c0400480350140718104001c9a510703000c0c029003000d044024451502c528004031000d0940b107003403007110180181030503429007e0300c5d40e0000402500060b138004107501c140070022403500c2598005001c080c40d03a40c4000c00c480c1c0e40080b01d01e03c015644d41c105c600c180c0c41801002200c90754040740ca94040004c00081040600810140a02e54010302002840c10b648001140940e80c003104140640c80d03000006000c03498000103445207103100c03843c04000b402c1902801070030b18400c050855039031240c214204041460204007081101c0940500350712819a1007200903500c0d041405032a0105003d042c002002e21003500c282c84c102c5030000e000b8000a440c1801d6000340110240c842d00c100b00410400c0350040040c030700c0c0c00380214460368403250404040303010040c1c50030703881400343d02c51401e00b01301300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 598731151 1250 598729901 598729909
    0x61c0e010c200d08250807090617040b190603261c0f09021504150824041107030801030606051903080a0e090711120307021c140705060a0e01020702 65
    0xc02421402d0030302c1c00c0c058480b1184102d14454007103540500c0d5405c0480c59401541c8095514040c2c061038641102441e140e210030740d0440001041d0070092450400000c001c039140c0402c15030460101c810400d03520031849404030660361150010360b00702d0b2200201c4102e1900c1c16800340000e0341044180c500348100f00c4991400710844200d082400c549411984107440040da0060f115180d000f4901e1240908205003c0c042c1d801c24402e00503000810041203a40902035140c035849210b901c140d00c14520694500d09023200ca50410850308a50b546400e11056105c0c0001080d0b41030003038640020715851407504006844082e086580a003011078005028203041030104015a68403000c1d040d1035030b114500c101c2d80e4008884603654003502400610081c01d40011620711032084000c03d0790f84240c04120a0281c500c400d89079400107034070000c0100c1201030f151f0942c200e40f0310301780f800ca06030b00007902c0c000c174481d0403020017990036070420b0050200007401032103806040c0d23403094000c0d030901050750005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 598732401 1250 598731151 598731163
    0xf0c21041a010510110c0604170f1207060c0c151416021209280905060d08090910030804090b0102240c031812030f091605061c0e010c20 60
    0x89040c400080c1200403404c0c81402030600c494406400350351203035516242c8850440322031150ba101d50042038032b00014180042001e207601c0c00403014a91908090b544c50100520095440404019107412030400145e0030300641d41080000110102e40c11802c0b01b950440c5d50800b60005c0c0c50008000c07500c0c3d400603008154945021960001ca9443d54130240100e900c4ca9500743c900400c0c2003445508001c0c0492048203142070f5000894108007a43d00e1310144400e000080001408004c014006038030149001002560b2101c40ca95110482580e0f0b551881d5054206804c1200519141d10480300710303581c100303c4407403031102d95001d2448842c201c2c190821801e4010740048001d04000000501880d4018107490300541c0d044200c4075511000b4013804555001a0381c003683c03c000003004604580e40009010910000c040b44030380c20185050308001070399000840090308201c0141401d94213407480d105107090809100d001140540904a00512503e440554003c0f00c20031448284800240050b403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 598733651 1250 598732401 598732429
    0x922151d0c030d050f040521060c0f0d0c050d09080a1106100603050709080316021503060f010e0d06050a1505190e0a241a0c060f0c21041a0105 63
    0x4036545c1e441c410100c400c11481075810240d0054a449002110050450418404e5080402c00d644440c1c0340c482180324148190954211001c3c000c1c00103600c82c2c541c07640294030010031400c03d24074000c2c040c1840000e0f2905d403070003901c40c1640410a03000040d0848054500760440d000135290602d809000f09850040d103000c0e0808040d07496001828083c02030f1428406024150b049070748030788041172038070242070b02d02c8000c070700446c000c00c0044141009941035034040d9000400303071280428448011110108501c4c441c030ba120340c032030151801080042c032a040c01041c8076880400c1c00c203440d10000503401300546c0828000c20030031040c08201c1608407108402d54501d0481880e45440d0700d06890041d01c1c0701c4107180c81c50501540c002d076042100d05030000460701800d01008141040311503016560007500c0c08610107070001800180a0100f00c41c4060784103c600040c0340c14117a9204504010204507610340a8854100082c44184400d0304c4000c0301d008810300100e07030550304200108400140b0703004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 598734901 1250 598733651 598733657
    0x307060b01090305070f080106090903021c02010b04020c031308030c0a120207090212151005070807150606051206030106031e02012115080102090922151d0c030d 71
    0x10080c0800d0380304200d10720040d41c2090803500385580701c0e82107506003486032240300a00e40c0b03401000500d0500d0703400b43d050029050f070040e0030088200800355a07106035600596086540e24000000b031a03450784080d10018109100840d100d40320800125130842c0325800c401d0160b40280460301180e6000110021220351001031a00600ca5107002a4035100d00da4011070407550005c1101d0725003002e801d00441c401ca224103010924100e411040c0a00014000c07007000008500b0041030012652813402844c07424810089201e5000140d4186012199240c01c020006400011441044509280800e4000104a0082100702e155558404034201f50070b26601001c4400601e01065a0049422600c10703036070110403030101100414010014400d403c1005200da40100c8041a0000c052007513a40008006e00a2050b903102d0701c281c0340140449000540c0c180c0704204181e00014100407000485a00c8040c0c0820111344015424a0505429008491542c0606d050f5401564001000c00180065003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 598736151 1250 598734901 598734911
    0x1b040b041a10020c04050a0903030507081b0c0c0409060b2b020112090b070906021608030a1b0c030803041a0712020904020403020d050c010306060f1d010908010c030e01050a0905030706 81
    0x1c0026803d00b44c50168695002e0f1501d0304002ca00c40e5a60010400031380320345d404014a517954541a960750b90b05039540c40280d102200610f40075070004000b0403064554804480c1740b407100c0740014069a00769181140c01c82c0d00c41c003065415060680d0b07191310840310100c0300103090312100340400241c014480e01034100300d203085d55200d0502c0f565000c21545a0440135260207803404003806849236625120781c00051180b0802d9600c0583d281c400c00003a40c240d10702451038090420f40c125000801707400b0022014130b003e46580700147d842c1980360000c5106000c200e1b04d07807405040452500710b4200c03030000b0310801c2c40104504c042e400b242524451041880c01030710380c6144c401043c002c0c0101d400003900500008044410701400180740325651400342d0b41407210a8517017800315003140c6030340d210b100400c3c10b1740078114107401840030403402d000061400c030404030354652640b801e450b061503610f4042075456404811169003802131940c030804000040c804140c0e255030380c540d00c0c0316404001d003069650b5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 598737401 1250 598736151 598736179
    0x9080d050a051204060b0a0816091d061e070c08070209180106170f01091a042415140a05060f0f0705100515090103080307111b040b041a 60
    0x401c281d07201082c02000306083c515040c5000002026400f5010f8070810002c003002448200c001054103140101500d1240d40900e440761075005032607030741540030300403042c90305e0000e50310402c02010f84101071100b8056401d16054424030500d4030040c1c042c00070820403d000a0206814404030f0303403050b5042d250240c042d0b807035406152211345031442e0250f8950030500c00203142d10300310050442c41110501078642c542414003040b4200c51b2440c2c8000e040060784203030101c81d20002d464050340603000b80142c8400c1000070b1160b0018840e803008080990b60b0744d03c403c000c0052031484405c00f4200030341000e03840c244110300081c240301e814450507118000015000d02034241d848140c0c1c54000d03144074100c0e16a1442e1402a4450158041c01c203002c40c0f8001c001546441e81090300300183c04090040c03101079085850361205070340003c001005100351014500030342d400400c120030803e000354920048a01040c1c04000c150f40300724110340e01c6541401c080e03000700c11b2078001c00f100880003222818003031204 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 598738651 1250 598737401 598737407
    0x90e071509270f0e01020d050109020301050913140105010608160906080a1a0d0305030106080a0c0e0f010e09041214030c090409030c081c0509011a10030603050f0f010c09080d050a 79
    0xa400102010f6608122000c40e0000303054000d4109119a0702090050b070f030300c0d60a524200d0000740704041d4840344c06030104201c01404030b0100f5460303005d8030311500e40001c6d0144250a5179020b81c4000005003403642004a01c480603c6c4000d400c2d03a540c0b80816440b40740150081180c0006490340e2070040e50b46030f13484451400d4070041c04e0f038018082e00d0b2600003075443c20007804070b0700240305007004030f0241c9000a415034190b1060000160098a660080d4000b020078840c1c0c0c0301a83c4406810b10088100c14052580ca0b01075180c4070300d00c5031603101c0740320110b02c600407c265903031015448101014400d002c20001d40f207041e43d400c5441510009841e140b076003404c50341c0381c4084601802000000494450212814416100e900200c4609022076105ea800450803582d4080364a50030070302420950309585410a003200b0740d0110b40c074010500c10780b2916858100703c502c000741c6a00d41d00c20040840c0242080c01192600070581c1480d00c40c5c0e614100110340c1791500b5000200130054000703410100380c4c0c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 598739901 1250 598738651 598738661
    0x2011205131e020d060f060f0b040603020a050405300d02060c090402040308130906051f181d1503010606050a03090611030403020a0b010b03060d140106090e07150927 73
    0x240003003c4c3d1500045605050b0f005201880e4608941d034100300012415058114841c000c41c0d4154160a142030324016003180203400c011401b030b0412100f08030000d1542e5071006000b040403040c044500907a0400c0c61004400145100030356102d40111140d10000c1e6000719030503501240c909007540c1d90742c0102c1d0001c1c0081c401d541004040345004500c0c41d4500105402c60fa05031948684100050707134481c41048854281d01e5040b5400e548400c1e106a09284181140d03502c8420b400c40c44081c054035022102001700b0421800301d134142c0c5900801041502c07038031160070504000e6008001150520314000e2035441103c100384145034403424100c0403c070b85a4005114186101c240316128202460000e4039040418010307203a0380b80d52000454200744210450b400781c400200000a00149540d074406201503042007007059540c2c9080014840d0700701d0040b03400040320300c006050442d0030200c800700048001e001c04410004509010b0050392404841800f07000c0b106456a5495150001d600010344 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 598741007 1106 598739901 598739903
    0x402060d0212152d0a05130209011805090f070e1008250206011e050a090203090f010204030807030509120f012712053402011205131e 59
    0x110300d01c121800c8480c01420742403d170b65442c800158074081160252000d80c1d00040c00f96099a40300c0e041050310100f084c5201d8940b410400440e4003007000800701e907507a030404030210f00164024401c1182080c801804144103018041000705a404191040c950054440032245200b402d2802c0c0384509044030380c01804d9580ca41200701e080b0800d00010a0602141104d0110302e03902c0740000079001e060251005a41d900b01000c0721842d10701d140c0f0824115910520040c030001d445502191a40c9416180a0340c07103510b510000fa010322036180d002d2140788205d0304040c81044041d00422103034200c4000c01e00710100340142d41c4c1104c2c071349042d008007d000d0f000c11603490780e8080c0d03016000310b00c41c42401c104689040503034003210b103001144500740c0040e4251000210340c1c1c06041d1820418a045040c40a810a4441b4508030103002c1002400c0f8803007a21120b800e0380d40d4040741a43e007 = true := by decide +kernel

theorem cover : BRFrame.Cov 598561151 598741007 := by
  have h0 := BRFrame.cov_init 598561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 598561151 ≤ n) (h2 : n < 598741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
