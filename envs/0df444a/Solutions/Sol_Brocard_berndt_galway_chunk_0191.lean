-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0191
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:21:08.178104+00:00
-- url     : https://prove2.me/submissions/264a2eea-1e20-4ab2-b777-7023d7fdeb1a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 34172667 ≤ n < 34352523 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 34173917 1250 34172667 34172681
    0x804060f05120a0c09080a0f0b09030703080a0203060a03021906081003030f08040303060e1003020306150d0b040206070206030705180406141e0613030203010f020a1b210c020301 78
    0x10060708025040b500c081c0c010b560303030700040c0e40e002c0000d08084008042e20807065680060100d48901c03d002c100700208001d50b0035605d8462a0034281589416000303907900c0c0528234000340030030913a40001c0c5544107680e0165900420051201e5201580c03030b004280ca04d10b030000503058035210042c040c400140c0054845800210a00c811850030780b840d100149050120390b00102003124140110381418441c0d0495809020420b003901010b0904005401c00c40115201c224041d0003600002080d0000b0318845c03d41c016000b03061101303107000700d40c0d55400c44080107200300da011001380300050150721010040c41c0f184095499017a620b01c06d4036034600080c0f03019032005209a042c01820301000c0d120f0070303d10410150550b03030b0080d10490b031104569030000b42d01503503070803850102c0c5540c0401031070009101142e0080e40200445504820400c0991003013000361001300c1d840e581c805104223055041a980280a000411140210040031407216401c0e4010707000050071100344178065240030f100d014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 34175167 1250 34173917 34173947
    0x60601020d02060c07110a060c0203010c0306143604050c030d120515130906050a020906161a0708070806180a0905030403060c05070c0b0301050a03020d030e0904080406 74
    0x1440c000ca80c1c500942da0080140246800000801d0301c00410510380c00c2180c3e0b00000030100760390144c440800130480d1551800030b0b0b10960920404ea0b80140c000d10640c004e94030348a010705d4102801c071061081e07142c00c031501b882329001480a900c2d0a901c56410341d040c072100800840300076042c0742c00c00038074214100f9050740c032907040701900a89154010448140e0384a80304404503140e500d8510081d441d408003140700b80c10000040e901e08280103568809034045100380410062a16003014601c01c0f406100c02441c5c10030810800011015240c0c030703c003d01c56105101811049000d01032100a500c000e0340c0001c045000041448259030b00150305a50183c403ea030210070a94600c80880d4031440040e00080342296517206000500605004031005160007807014807500c1c1c1c4540700144503901440003035458444120012680640d000101e90490710001c0010442d14110740030001c4000c8116030403000e00140841c0041180c48a4510764810750003151442e803103610307112000c0d01c402004c8681c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 34176417 1250 34175167 34175173
    0x3060605030f0f03030a0b030c0a03080d1401210203071a120105010c020108070305090a05030403051606020a050624040c020105010302040b0109050306010e13080c03131d130c0906080105060306060102 88
    0x160f0356400002d0383c0e0b10802c1c21002003001400c0c2000700e4284000401450b403c1a5403407030200034450700500821004422030300400215490000d00030841c0000c0c020814011403552034503104024109800c01960300080a8411082d41d0b58041024080c070012060101c800100b076001000a42c00ca6190040c2000c0c01d141b450b5040550008014801c000d00240c24542c0d14004500941d1042000d070280550001c1180d99498030703800c0c502d075112101440b1980c014105d49000c10031500c040390b0210520b501000614150b15083d410490384002c0600d01d003121601400300204130380e6640105035001c65590000541035055006100a68014000140c1480b152020401c0307561800110302d130448010050400c442d45902281b5030007004880341c041c00801006c600c500900102000809101c403120100e4108540d0714400150fa4401425400c448c40c0207000000311280d082900e00704015116214881116484654500450b0a0f0b50000b0329969552000c100c803d050401403190800700074001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 34177667 1250 34176417 34176433
    0x90103021804080412030201020904050105120a03050d020913050a0b1207030602070807050d08090c0d080d0f0f0501060504090612050601030221010903050a032004120201021603060605030f 83
    0x220708008030000c00016400040c030005001e00c10314900303071400340c00c030380202103000d26580c14000d0103500b1801c8000e00c01c92400c00009800d16011110666409114001d00701c1001980c40c107076282c4d0880309046550540030407840e4026034a0300070f0700b01401c8006500141c40e0502d41c405400304c03104804440e0043c2c00030400b080b2001d400080d9081242d511050140e6501032500d0b00140502030300340024034911138dc071813074070246030880c8035940318100050445010300056801c001807054080f20140080b0810070600302c08403115002002c203403444281c042942107681d090042200c600740e201c0c000140010038140200036003801080c1c001d16204500032459117444c0c6540f602e0754410700c0020721610014840107100e05040c00d8107110310b1020350003004011003604000c1d00640c420329613440002d180000100c2b04d2042c42070851500500541c3c480c1c200b90030103408064400300403000307038150310a114440311180380c0e880300780000d144204030100c0e0707891400061500d4401a00130502c1a9000002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 34178917 1250 34177667 34177669
    0x10b1c05070e060901021002032526060d0b0a0c030b03010905030d02070f080705030a032703120212010902040914090a020d020f0909010c0f030b1807050f0c0c09010509010302 77
    0x14140b82501c41112a681d44941041c0140d14040c2c014645140395030001c810801032221303c1c00b03400385426000783c80c1000d03c0c007a2a000c5034194072300d01c2c0490310001051b100e0404c001044030f242d07074868809884a90032071015110702c000100c00b100e0380528691035031540300795a90301d0301450a9103c002d40090125140f1950303099124001c48800500281d03003c6502814485d046410071019034110004c40c0d07072101c09080054403076100005000102c0d0409900800c050751401070004070202102440803140a5507904454051800c10079545417502031048084660410364003900820441d200140d40341e160440120948012141c0c1f116005d9071582008041c8070007280e0f00c4042503040781d02c40205c8440d0310002d001c0201c090500f640000340d1a00f0003861382d605611075985808130b03446e504840092418110b056a00c0703480740c1138000c42050f0f00a1085441c2c0e400c02c6801143d44c0c141242002107200001401d50042c0d45030032001e03880140c2c602c88a0600e41e0426003d0042031b58100c040e90b045030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 34180167 1250 34178917 34178927
    0x3090a031506030206040806090d080112060b0f0406091e0203010608070e130204030b0a0b03190204020c010603050a0b04141b0f0a0801050a241a0c01090209010b1c0507 74
    0x8400502807866003040300345a4259580100003865004003029102c9880340c8180d80e40e5402103540c0382e01407040a0451180601a1440d00d049450540a1074182002d070703950113014100520440350400d5896002c034040703a49901440e0301404070003500080e200e103100c200f0303801c1032041282400c0c25481000107004161748500620b6028136142000c00d460741d40c40c80070890000c440c0020000031417010030003100300303c022083c45010b400c2e05002444180042001c2507164542541d00303181e16210700c41120010700700340d009408210620400051056035035110141031140900f012100340c28130400700420045041c02290414a0180c0200607440ca0503580348082070203045180d01c1001001c518001c0366544920080c058502c2b84000d010f42d040003640c0c1400790004101589078140e45124030303881d50312000c0412003200c420507000301608010100980c4280c2c4140280081c0d5500c1daa804070168031000c901600802d4031006042c0d4958407540302d400c1241025406110050400f03041c04130b1551302c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 34181417 1250 34180167 34180169
    0x150b0f0a020601052e0908060f07020c12072304020403030c0b0a0605010813052e0c020606060403110a0906150306080616200f01020c06100f1202010e0301050901050402030f03090a 79
    0xa5243c900100684d503a0581b01000c072a801620503108070380030405901607203407a0382d01070380d000d800729403250283e80d08224841c4440e2810005642c03051104001e2065a01d21805001c07540c0303600080d60701c0c0c0503000b0905a9001d50419008201d11103000340c1042a00201e283e40f101d01000100b25440c10000000d042c1d00c0040e01011041c1110340400301401010321110034100c04040303030103c040300782c40004a110402c006081c03868500d802c551204550012a1140c8113110050141c0c0c501800d50380c40003d540c000310b41064110041c03602c0807422080a100e00005840d03501000ca5003a51113a40040c29540d4503080121590031000620021039501c0000c0001000e4500700443c0b21113880018010b60302d6102214441c80c0710f40a0740001c200010b5000344940d44e1244d082d188650b80785035007031200c04a140b1901812818240e1b0070407034100c240413020070040c414500000c1c1086041d000074203407035096071050300301e9555009001c21071504001144485011401850800f02d51308000b441682c11 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 34182667 1250 34181417 34181479
    0x12102060d0f0c03050115050c120307020c0d0f0b16020307060c030b0d0309080f06010b0d090303112206030b030a021215010f06080a020f0409150b0f0a02060105 71
    0x1044448081401e6041030465101c070103030421840ba07030044001c0203014203114001c01d140000507006c081c10b210380100e40200028100130500b160425890300d0013944010146411070040e040300424035610214413255850048410340c1d203a0101d81002000701030098929180c1c8140d80034032030300d4542c010060321072a40d0000c0001a9004121100340c1c0a400d8440082e944180c1020f403800c02c2580107203200003624141e80c1103800f003c01001d0030542c0d0f60b00c2030060340c0480c0e03418010400200481d42018040520900c0d0105041c4d42c00401d10071150442c803418600003180c5121a52080040c03009280101024034042c02542e401c0f10220b81c464005030700c068043c0031340c0604c007400e50b041040702c1110030100e80c04540556030340b9480300c1311540c03c500074200020403000c0807881c2c02c00d060081c1e80c6003c104940a40c42c141c9000d9518009141184c41c90710110140c2030000341e00d0304910080e203982a81200915900d40413030300000d050030016000326201d41000c402a00070100000040c100001c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 34183917 1250 34182667 34182679
    0x16020f040b09070c0b0c0405010c12021002040f05100206011a070c050d030c02030d0e06030105010c1a09030901092102060901050f1611010c0308070806060c030d02030103020306012102 81
    0x100208000d4900c00a02a402c40d00050a1000310740c0d0180d001e1044034052034025507192a00302c040e04951007a84180390000d84215000404946030301c0e4030204105450049410101030701c0c0f240000c0e0b030002d600c40c105054180380104020300b0b2802c4c40040c038a1407440500690b6050120740e8082050f0455a4031855101250550030840b60f01c0c0e840c006803d004040d4440d40b0a42d02e00244419440f001c103d001c2e010314001c9491141c020799098400c103000034101c0d0304503800e007401140c21502600051390300122140c0e60b5040c40803044003c034003898015000d1a170328140b1100240c6003622690041500d524400152144c4841d10a103c0c46007a5040324403943e83c901c1500100ca1b680900c4002104a4000003242d0001000c1000786068140c800c2c2c1819508103220b070700545d5180c64008000c1d012401180010301d5043c031421080e03030700c000018801070134080c4003005545550802c02e01040941c0d4000018000d520b01045114010400160420004440c400c0d610700c03000403507100240221 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 34185167 1250 34183917 34183939
    0x60703020c07030203100501030c05060f03010626040c05030105180a0602090103020903060c0408060a0204080a0b0a060b04031a010b0a1407080d0f020d06060806010906140c0303090f070501051602 86
    0x1090002c42d000f9a001811aa0040010030014004010070b1104403804040c2180c000340c4c60070a0401e407035207563748160703040c00c50f840c01c1003e0b01c070314800c40074240c00356002c0100708981aa0300615180260302907a03185091a0810051500719480941280c0701d00e08603203c0e0200c4040b000038034482c071a602410143c3c5a0351090010780107070152004a030342c14010b05081006500e840c0000e0021140c003d0200c403030765220058594224401c1d8042c0e0600c3d81c00821241c0e0200b07a004010507004000310b000060055a50900e006058000360012118461000314102100030350407106805451520001840c1070a02d02014100310300304546a0100d20003c0750340c0e014407109000f81c4040410340c1605004609070810010020342c01103140344c40e524988403010035410f204069840c0700c0e11041e184c0a0a0f1070038000280c0b51034004e04050001540200202c0c0d0780e440c000d1000d94003461141d4018680300d4986504a410640c0741e4201c5810040140039540b11522110010b440091701034030115000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 34186417 1250 34185167 34185187
    0x510050142021606050a050f0c100f0f060e0108072705041101030c0903080d110c031614060601020303190e0a0c090b0603060d02010509011205011d06060a0206070302 73
    0x103030214a00d09a036000501c0c03007140c9264000c521040441c030481400544551240000e58060003140c410340006031044c0414170201501c0c10003413480d02e01c1c2000b00c0e50000c080c03c290b4810303221300c850b0310b032492034803542c8072070254025029810140c84204c0c11085298180b01c10244d607403145104120b9140304c22000c890700442d10391402c00e901c80440b60240090301c2c180c10510091081440e00c01c1c0001c1c44e107442d001003584252283c20a40c1e5110100030300d44128800001d0113060b00042c620440309080186d895210820030080000c1041c00321045041c1c00c0a05040543d10b110301802407080e04400300f044400da030b02008032544042020030011112014150b00710040c1019089482d01d4031550030310a06002c000b034150310403140403580507c40800c580b410300020f400709807101500712200003041c1005600038006400d0110040c90044d69a920010701c101c20b81e00300307a0180404003c1c5440b111212aa02da20007507024800780d03000c42c907251030180c00a50300c0c50010718034400c16134045111008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 34187667 1250 34186417 34186499
    0x9030d03050711011416051207110f030301090e01060b04031e0f050d08100f03050c060a02030702150703120e03071704050d0b060f040b0325030c06080405100501 71
    0x1407800120000c110700348440c1000280c85c50190f40c0c541d10b0300e641e4409403140c14403035003c030b400044002c440c1020740d4490103029102414018103c201078001c0003403804035000100041d5000700450b01000c900c5074040f180040c21101d039900001d0040c98100818070108241002c0c0342c46410341459007610010450801d0408910484001000c40c003510700c0b034405803644980b83c10301a8584c01020a0013554074049501a00828407000740542c103d0b02e10402a0b14044020301446403550055a02c0e00d54a83d0000350888012080100c84000204171041407690100303000c1400e20380d042003085062007150b012070f981d004041c0e0040c5010328006290280800c17100640c0d00820b005094100d50710103524100f00034000464845010b1250404c5407271040c5000d014210394424060041c1035050f2070100b03032900340d04c080b00e207203907030650010000000114038244100051544e0f075981c0b0041c1c2044d1400306c3c1401214210801d001d402e0000600466140c4080d48016001515002481c02801942d00c10303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 34188917 1250 34187667 34187687
    0xf020903031b03130e040c0806222d050d030b0618040b041a0f0f06040605030c040305120a1701051c030c0c0905011701020c0d05030402030a0b040606140609030d030507 74
    0x11312100b000c800144569550404601841c441c02e003d600894031501900d81d81c40f801c84011000b000280c070b4040010040c1b40b01d402065014914100690071450364004808511f10321244030010547c21103c140031080c0a88841ca4000349018444401c56100054840c0621140061603083d03491440801c0d581742d60007415803280281040c440d90f445402c0e444002c21a0422040c01049e0004001c8070a15290044003103008000b003149040500f45a82100c86801c02000940c18190411012000c258100428480b0500807200e0b5036032281c7e0284018200050f191442e000010300c8401070250742e4503207181810505420446850244080c1001c46440e50f0034440030b010510482004501c0704091382010341661700400641c40724020001d1090300302c1c45000c84a580710340100d240050441d22803002150004d00040485900240307907240d000c40140d094604659560b130302c3c1003c10034007946410180424104441040c184504000880d0300e40362105910010913035901e000030800c0e4040c0c3c0e03d000e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 34190167 1250 34188917 34188937
    0x30c0608090d090303030b040f0c0e190e0a0203060114070507090b0405040201021b0102010f02030f01060207080303040846020d030903020a0b10080d0c05100207051c090b13090f020903031b03 84
    0x1021b40f0090440260bc161240501c00b40906401c08500c1c840d4150707031400342c04a03031007445003c0c0f0276912844810000d400c003030b00403810031180303d019161070340903500940000741c025405001c00502e00b0f144400ec940840c200d19002c0d6003000704020143c7c2c1c02084e02c2d0444400c0300c900e03200309112440104c5c0104105182161428408030500480b002c50158250603a01d498003103030803040e20f03040741a0792800101c170001c000b000700300150380d44c03083d03805c03110002c80c00000c1e8043c2c0601b00414112030700d40740302921016051212104000d640e5810050210404c40c070303040802c07083d811a14000d44544807a01c000d0700074040180411035030030401c035001c001400203e041e5140b1900c41e28004240d60b20301e42c8161024828003210882c1200309108513045207a01c00b000303080c6500c80c0584c03401c1c041001555241440750640001030786080c024018440109401e841c44040350904584500301c0f1848c2121201582c8148009046620000200c919031103105d0b8208040801840200b03185114000f190 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 34191417 1250 34190167 34190171
    0x2010204051306050906010201050415020f0d0f0b01082d150a03050d090504021303030e031e07080f0703032304050a060905130e120705070906030c0608090d090303030b040f 76
    0x42c1c1420066444241680c00460b8201035a480d40c2e4012801d07540c00751005041072840904007085d544540c0c1c02405100c000140060522503400c0014080701c2c20510410704403510307111801b805603840210f143d84541c0105486408040a41d020a8000c500040c0c10b1010000702011581569031684485888100100142c603050b4132440c0c070644840c000d90240c07010402d501804112072801d4004d4801c40788140180e10103891968508966060b08a00303031a80500410904001d000f6103040b0340b8100c009518000c1101c145841382c40f600e000c520107908042904050001d10000c0d9229800d900845515803c804648200807d0003456105552060b40c2c48180c3c51800948241c0008400e0212223048034852100426120b11074140d17161481c460f245c1d5000014006c801003800009001180e0203a0201c492550f20303800c20500312002074209890040c0d691900300400c40e8014200b0768070021040c00380440c4800aa8044d20b00c0341d41d03001c01001d144e01c070b01d51802c80380c94540c000c1d1200d440300002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 34192667 1250 34191417 34191439
    0x31707020304060206010609030807020906040207020a03110f060909130302030d0609050f01150c020103050a0e010f02071e0c05090c0706150303180b0301030b0603010e070305010c09060c03020d0c030201020405 92
    0x2070341c0d0b40d10500c0b4607000750040e200000f64070740c0501840c03812281c020503405c0c607040302a400c2106030344004240662040e4280a1540542c55030040310007d188a400407803e4248901d04200d09e10400c0400184240b2040000b0314003901d44e1002d090f007166070843c40003010080385c0b0f4281d0450080082c0c03110418a01540001c1000d480d4101500521484a01020341d903242c441548411403002c01d15004200420b5042d801075209034040c0741d00c080034030310000e14002024001802e540020714007a60164020074000144081e04624482e090051279000780b40e4405951501280107140c81070301d2288017005c0000310904144811030f40401d034064410000420040e26a840c0740c02140001d80010301480c4c1226002c5240e8160081a00d004e403403c103003980e10396581d8096440340148010f0b059500e411a06c03119600400c0716101462062002290b0741c201c0e00030050225145078403800800c80754042e040007194001c185c90403400b0b00391625481031042400c0590285c4031b130b940910340018001030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 34193917 1250 34192667 34192681
    0xa020307030906090b030f070201020c010207080301080c0108040c090b04090c1e0608010807050405060402040b0307080f1501090b09010e030607050c1c05040b1b0106060509040c0c1502070317 84
    0x1050310358440c1c0c03a50404192544411640c054542c064004601400c0002ca000540221130707a070361025241c0f0015103001207a542403030a9820141046401800100c0140195041445410458a0b00f0700c0c140f661407800e42c071a0440140e040c45407003c03290f0f441510444584941c1c10075030311950462150003031244d442c2c0d5030031464140d0181d170405a40c95000c021640e07600c221811030403103c00c50020b01286050404100003458064805a4416800c2000142a0420070081e44c030a01040e10703051343d585481d8091b107051400040c1a031408220445118120303a0304140b4000039140c0350485103466082d00d80c0140c60908000910316403500c5540200a001d40d48040140034110200058800300301c00982035000322221405032402148040c04140300c2ea8140001a0410603c030006048040c2204c1d002282142c3c0190031100c0014000035802d501400c250080d41201d40c2d86141c206240b200503128015805068542484010340018158081c548100b030300c0b4504184c0701026a4080c10091 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 34195167 1250 34193917 34193923
    0x6040f030210030504020306060f0102160303030c09060c0309180f0e07150206090a0305090312040602010c17061e060f04090903020601051c12110a05070315060b090d020d080a02 78
    0x1200c128403030200c10b00021000781c8607001d0140510307070240c003e0819490300c508104410088600f101d04507c1504c40362110340041d1403401c00118040e40b0001003102600b00001d1140005400c54028800c5c40c0071014000380d445401c008c2220300e08200800d540c5040c0c5110009043c40d09000f11600d424141d5103060418045805000c50b01d000b143c1b400c1c0022018001e0b40c0340c14048440d840c145d08421160008240203070010061444000d0a45a02e10141c030554000da40190f003010ac0103030f540d0996880b10130b420500d040408908103d01003000d160203000210350b580301540c0908600c0c41004414000d845410548203010098002e20392104e4554006138010040740d5820350040c03007940000642030038050f02c444000b07140040168600145a201e030f0000f4241025a01c0070801030100c502c601403024007d41ea01c1510450140000c5844d504118140e0940481211040ba00d001c0701005030030f00d030b041111500340050b0b800d40310000340d50002170904403100401030300c10000081c1d180c071015804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 34196417 1250 34195167 34195169
    0x90902120108012009040c02010207050f06060f06030412030914070e04020a0e310209010602100e0c030712050a0602120a060801020306090414010b03071e0503030f120703020906040f 80
    0x494000c0091940c401601c0e4000713440200072008204080008003260304007500700045c210b5280c00054a0203183d81d0329240341003031200c0002d05641018007403003c0c40c600454510f0591804664442c11428583c0341e03203403146000c40002c4180341d5504040c500300104c180720b01008210010a0302e034529991040c1d034210340c0d000c42d0202c0c444c02c9014000308900c0341408030240202d8020843c00000e5251411903108507178100c4070105440307040500d540040e070b528500386010384403580c080e01c0341408512a11050324290317080320350b90780c000d020282c0040c2c07000a42c0200712000700764441e113070300324034103000742000380c9020044d001c5400000c0d41005d90111075802c6010316041c07201008259543d444003802c030b010949030340354400c002201180102d40f50044420344010400c00000d603500c000c10000b45040c005d0b5100103003000281e201d107000444101401030080c002600514681810880302c004c03903201d01802651200d2126010800315407199055404082000c1c0880d640c0b15140d841d4413540c040760b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 34197667 1250 34196417 34196429
    0x90f061501021c020303040b0c041206060e06100807050a09180b10020601030203060103061a03100e07090b0303030402061c150510020c09010302092208090a0b070506010b0306010909021201 83
    0x1601c04041000d0141102c0c104081059130702444c1951155500e5401031040a0321a0a204c4400d00010402440d40040070b40c40a10440000401e00d00e00b0801d045860001001d6910031710348010b50081c616000080e044d40f00885140c419070b9400441ca09807015030041d00210003020005414104940456100c50f00c0c2030301c121104001d1142a000407a55007030240002034042d00f000c00104009003254100012018407a9003c19031130076600301107403900100c01003442e01651541000f402d507210901000c3c018000d1b9000c1800812050b40201c0d030f5034400a4070080c0103a00000c2d00d0001d1440a803030b03200070f000071a01d007031008104040180c40078000c18060f0034070a0f000c542604c00ca01c3e00003d0811210074000c3c000c0c0d00180e107181c0030800f403e000200300c8016140756603e548400141e50031103505c203c3c8100c141a450b400c0b010184405091290840c00206508004000108100042c200c0c1101c82d800403541e603a560b0080102c0d846c17450755101c086003c0c0040f8a8500ca8030804e0070043c142c0d42 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 34198917 1250 34197667 34197673
    0x150a05030a0605121c17040507031106031b031312021006091802120313030b040510020a0e12012012010803030103051b041104121103030301050a06030e12070b09070509040305040e090f06150102 85
    0xc02c0800f0000d182c4813b84041d1070081c0741e0a40d0107005c1c4020303400b441c0e00004900c0101241500e80d03c075a0910100100101e0050708145c00640c0041164801d2101801e03400208004503c420440c81400715040f0300040d11030800c40e149818081c3c810400c4a5800c0548040c80f0101503aa10f0000603018054800703d60b11b01490102040300715040c4243d41c0d200c44c065503071507202010f03081401590309151982a07050354a402049071b01c40340c3c09840562041d02540b20b69610414114149851742c0e040c0c001c043ca6400c00c000401c0803400005152004c402d415613a24420040000041c0050500d1149400340d0800850000380e4414500c04c1881100e00800e080c0c81c405134000101500c0384000d01825900109845040c06603500c60740c0656501710300d6204030791000c1c1c152041e001080d00805011588403503100e0410104a0042c045140203000648002c440c604165801074054000d43c0902e00c9074140d104c0c0011800002003040c1000c100012041c0e510034140002e00c4400c0c0c070344c01d85e221400340c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 34200167 1250 34198917 34198943
    0x6090d020307061d0d020d110409060501080a03020c03030f0406120204090603030509100201111c020d050112030908061003060f02070b161403060603070e150a05030a0605121c1704050703 82
    0x1c02c002e170780c00305020b600404842c01d103c241d40d61252480c0f000209641c00a913208032060020303c0ea80700c1c980c082d140c1000200072141403883c0091074007150180c954000d41040c00b83c60a100d0440055406440d003604001011135a003210510090060394000f0030b055041110000c28160004d000b060124000d075510b61080d240301000342e01340e4050203880c010794103007040071070071078460343d0250031401ca038020000d4030f0300c41070f15148000d8034401c0c1c00c1911004100d50080c0101074104a28000408100024001302c0c5012041c0c40171070480d0344009030125031181d8100c460702c00503504640d422a07001110500034182007900c20503440c641d06140010602000790b01004c00e49250a036440340304000c010515550324000100c2c0e10403004e140c556000450362040700408281200600787c1a07809964881c0c0303928068180b50161342041d48141e01841040303010329042c2601107581d1034240c422001102c000c0003149421250343d0b0b006901040e100250f501403100b0000040340c00012603003d17858014043c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 34201417 1250 34200167 34200169
    0xa050c0d2318120a170301060305090708030304061112040b0103150207020f060d1503120e0f0105090f0f040e0109060c050918060d0819020d1103040506090d020307061d 74
    0xd4401c074540403042041c0000307164824985203d07030740e0706036941c1d00680d541e00719550740740300b50040b4042102c8640707480070006001c060b13070510070a540126014002c106203440c0a0b001034407880080c20162280d0346403440e695032f0400c14800c4030007a94070f040c4a442c0c0c0b817400f070410620084003030004a90280c01040c1800c103800c1140292410340da00140540e2034825242e0402156a00c07540f504c0d40555141c0c407400417426961109440194000d907101d0000c150341c02c10080060020b58581031042c0c100441d00582a40e000c000d460034001c003540da0414444070b16002410300d4141c42d00d115401810700d040e9070054081074000c81030161040304148560200384c3e600b990303e4094001c04075004203030b081211082d042c4001915810110140c0026a000300d03e80f03074151036620940c12800d00102680220008560400085400d00c0d800d19107c400d0300c03480083c0c07076280d00c070b01d02c03070700d486680b01003400c0069580308210701090540c020116000c1a03035590026000e82e4401c0c040864082510f0a24159 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 34202667 1250 34201417 34201487
    0x31902030c0a030b1f0f180e0a0c0306080607030f060b1602060a0c0203011505100f090b090102010b1306030b0709050a05010507050102160308061201090b0c0a050c0d 73
    0x8161450200e8101542180c080b0000c008110f41158005211210710b2080c66903444500150705e180c1d6512040c0345000100600300004022042c041c008845004024141d200b40d86c6940006026a001c1005402c00c82d0413005408503401151903401241d040c00390751030305130344080000c59243c00c017400601d9071100504818081c0c5580003034107541258801c001864400014110200306050150314440c847c0c0200f8215803002c04511a00340008100388004d2914026043ca2000e15291014400e010800003c00b40d010304e1103500752030540411030292030382c001e40002c88003140c09090b05030940c03242c0500368081c283c00d10060fa40c101200c40406e03a5148520040d000b0750f0809010061101e140c1001111158811042900c0300e5500b40640d801404484a20aa40d203001c0c0c0e41388440f40c2885401c00c4500c1d140c0c00080252603140c002d1200010307102c51090b81e403240061a0407520b03a11800c405943c03070b1003442074060041c022040c101000035008110300e0400e0030340724420000743c1c62139200042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 34203917 1250 34202667 34202671
    0xb04080303060111070305010203070507021c051005061c050106031218061404051c05010501060c0b0f13050f03120604060302010c0609020a0f0b0c0c03011401030b07050f0a020303190203 82
    0x2680003000001c000b0f5026041201d07600c04100200c1d41299a203031906400c9030800e50320440002e0000800406510300400b41d82e00106c06564020a004601d1350741075a100710740485c03041241c0d1190000f81099030346000000320020355001c1440c590001c2c0c0b50442c0207104a001c11500a60b61203804000980701d02007000014000303907900e040301d5081c400b00361f131b440030b840c1d04050800e4400c000200d41ca440342494038084410b0915a023420100e01e1030f025094550581001c0c003003107020420032001c60b00300c00605800510911001260352980c2150150000d24180007a01034070030941258070f0400004002c0c5500a048998852152100c40820090701c0040c0302c0607001038103440b1040080741c5103a100400b154802084203003495510b041d50f90030070050764001742040402184005d0100401d101d8962006000ca00802816080d4140d0004440301800094403056070200001c44c030754040c10031151100c901c00c3c0340c280c842c07100c120001d40d2a071007201c80030407c2c520f43d0b080b424100c4090007034038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 34205167 1250 34203917 34203929
    0x1e030302070b10050d031d0a1502013b100e070e06060703080103031206050a090b0102190b070f1106040b0402010f02010e1902030705040f0203040218010b030609040204020d060b030108070b04 84
    0x8150396a003070306c0459682200205c0b081542c00d900700700807410340e03c0d0120308004201080640c00d61a400c82c00203030031150b40b48401004c132050708048d8100d280015644219031240c000d0b8401c5d4042a040d0428034041905c0b1503c0d0f03610b07290500204440000003040012030f182c0c0005850b441e0713216000c2c80392a0242e10f9008010900540041c40024010a207143c41e94248460000c1c11f941d484002901d49402c6134010f800c000da4441281d1100e59050003c0f80c200c490046020245041da640c2d05007010400420801c10006c9201042030000e1040c80700c1101510401c00701c4005080506004030140419903003203021505d14241d40380c1c05401806080d4003039541401070540602d500c50300c50f07804001000100e0389070003a0940440d0955491041403008202c4407c0140c80b40750501c140310001100d03466060595030741100400a42031100300700da5020310300713640c4004580c4075031000c98082e010703001300316045c00d0402101180c15010b18018504803100c4508035108241c1e9411004254460750041e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 34206417 1250 34205167 34205179
    0x1407090605090103050402031504030305070306060c020303070807020303040b0408010213061707181d0a050c070b04030c0816030e0405060a120f02031606050901090b090d06091e030302070b1005 85
    0x1e55030b00d60080d8000c03036003d8006001d07901c64011380c01da0045010011102280460382c1c6506000145515204000c040c0181c3d0034000850040c0d900000ea69024400c40100042c100181c8441103480034400c1d10300a0001011003622951140a40350217500030203094182c03440c0359500003401500c2600c194050003801c1610400b00e0f2038a030411584810001c0c0302c000c1c4011011f200252240140189895074a0381100102150610b240d101040c0c0d140030301b405624101c18404070380810302c0000724641084d418140100d1440251a02039400d0003520b21400c084081300a0660900d82c101d11501c8071010201c84c10041c035500d0b9804c00c18060b409000d00002c41090715091000280c440300b5020425000600301c41e80c1c0d024480c2d001040d20704035000207000410218101e281541c00080c01406040000e595034180511400030600c1c000403030101030060340d11002e0302d50a1100c400e601c0709071300e103c000c0915082c900e5400e01034080c0d804910300700d540700170a200290003003802300400b030180c0302d0040038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 34207667 1250 34206417 34206427
    0x8060c04061b050c03032d0a140c01060f03050d08060103110403020d020f0306071d0409030516060609020c0a150e0c12011503150e12091201020d06091407090605 71
    0x201e80030b45607034072012981c034802c42508185503a410005000d414403c0c0a0020000c0c0d00e41c450000a4070384182000328070f2906100000d481a04403240d00924220011519200e00d01c00d0303141c5000d40441d03400b218405100c0c0740c01106104020400c82400741d4603480c0c0494a031991401181200c81841d10315000400c240014030041c41e120600540d094001004007090002000c00a42421026120708010410081e8511460202c140d41800007643c119010042c9050913200179206100d0b404d50356410170110f50285040141951041000e00a0703100115210528100d500341c0d40c42c0e0310300041d9444828540001c035290101d000f02403074100e1350800340421840c0503040c00b2800d207046800d08015501c540741c00041c000103018280095006000e02c460090343d540e00d03502114180800d080315900901029011044408102d41940900f5039800b808010b481032907500a014900100030038504001c000690b61220340c20420f0b000e1940c241c4c0e80c07159260083e041e52484510b1190001050003880 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 34208917 1250 34207667 34207697
    0x6090103020112020a0311030f040302070803070305040e07050d06030302060a0608010204030f020904030507060509060414030c15062b020f030312040305030c0d0504120e0d05030301030f060209060c030408060c0406 94
    0x245c100512541000304408a210310740040c560170494004403100c0a003800c02040c0740d41005440d00409400300610704c2e115a64a0080041c8164050440c00300c01d2000810a554441d00881d20209807200041000a03203901d070080d100c890540340314090504205002c03510440600c01c5a00311782c3d010341c00820f8000182c0c203208411030000e105605202040c803440002c200940070f140d200e80d1b1200301038070722482c00b4640100300e1842130051032000d900078400405030090000300d4030920641844821040c4d690700002076154000e29544034014130603d800d481300c0c0c00000c3c103010040f900c00c9516000c0c48120100f0305550740103209848201c50030640100f00407034040d000442d00203501200c01c900d02001c3c01c2041c01a00c0c8207450407507849490641c0e4800556201100d64601c24089650b074911544588890b9039a01060102074090281c180c26482003201a80c1299208403000e0215a12110b03d8034050781c4a80007445201c002e8011100004c45c0800030808440c16035080380c5030b41c608208604 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 34210167 1250 34208917 34208921
    0x5010602070609090b0102010608100603030f080903030a1a06070506100b0f030106050901050f0708130807120602130518100803030601080103060e0c0303030a06051f02031603020c19090506090103020112 89
    0x5c1c16241955a42c000114080d4824844400414920940882c54510314a0b00401e5840811308010800c2807c90911151410101c21250400c1c1c0440700455180c10049010b862480c3c40420503a000303000040010030020003003007561103081142040216140c5d550342020303c81c49804003010100382c0410041c0b02081c000d2019011181c010b04d45541014408203030810a644018400e98000c60b0118a080102090b5181017020308051805014503514008001120848a100003043c26401069040100051031407443c000e00c00189030349a16900200301e0132018070151499071034080420400b064460000040724014403040e55102c4050f1f2854449400a20a0f1442c031450b0f40140c0c0c0c840c808583e010000307540601103074a07001400c40e10345410026402c001c059855001104d98242d550100c0c0c0110a56205402248441080300194074080b824003403d204034a0703100c104007130000c038034038001d41c0000103a9400190422280e12441c08020a5003003d10000f40000c84071001e03007071132030110303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 34211417 1250 34210167 34210181
    0x20109050906060405280303031a15030105060d090605070807021902031e1005150a0806010b2a010203040305130e04170d0204080303180105130f0b06060903060f0a0501060207060909 80
    0x810010300f071002d0101c040706002c900c541d1043c1d00080e22b82c2c507501c41100c03054040c4550b200044691030f02800030300342c40085a000510465208140103d20010b004403d9004481d00d144d209ca0200194548510050001036058075404014810401c050716013084246401407055001001030a886200c0e4842075049240c1c4c041c0024540a01c0d0b0003000c0c00c2c44540640d9001c0c0c691101500120419002400101410380e84002030551014004000004000e002c40707500507081c41c1300c1d2100d40d50f1240c081074209100c4802c04191740c400410402032650240280000700051018024000e42e9098659090039064401030040301c0d808090003ea403020200400c0c10b0310200c0c43c09030034241d079940c25504540040b904140007041400d000c098000003845610341c08030350320440c2800303810a0348508980071217500340204a0706199000c50071950f2104181e4412000050455000313241100c141490310702c060390b40602c42814000085441c50000c14400c0c25500300380e5401d10303030308c0c6804c2c9448090868 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 34212667 1250 34211417 34211449
    0x70b060909030f1c05071710030308010e04020102010905030301031109010f03020108060f0a050d03050306102f030403060c0c0212010b01050904020711060714060604020415030c03150f03020109050906060405 91
    0x142484c07400071000c03507014480c41191581c07590074038842c040444080c155002442040c000f1800c4105000103900b016600c0d05580fa1040441d02550700c9200503801000e24140181081c070002c400001009180403010012404c02e51302860140d9803003000b80c030880350500009020800303200000d0350605044200c03003c3c00d03000610842c1d66950f120040313040c1e101a5401540010000400c220b014100544401c142c0d511500c3e0002056441c05c003034410300b0003224104040402c1004200d45244001c10554001c1c607040309042240c0c00030703160050b0440b05072500490040e0340e5040c84a68903030040c0304180c040c00d01a140c0614004580003084000c0d0f20034401200c50391a4441681e000d516150040c041482c403802400c171a540102c2429883c2104c01008070344101e00401c014042040815681c4100018a040c0403640405c60b210540c05403540c080c4c0c0d80040709011900040c000c400d03820120441e8000c1e242d5a001c56111028003a00400843c3d8840d0044070400c001c00036800c01c6040102c2400c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 34213917 1250 34212667 34212697
    0x40605040606030206030c090120060103030f02071d09010b010f081906090212190905100207080903060c0918010e0c0702030a0b0a06030b010806090a1112030708070b060909030f 78
    0xf490754005100f03500b0582d2042c00005002c80d51a401d96003140e4070345600e1030002241344e84040565007055035071505000090402c00c00090100f0b9142c002c100380c07005007070b1140da82d484282c0c820b0342ea40040703041210417000546c00c0080301072682d401001c00a001c81210781d00e1400558900300303100c1420300200d100c000c1d1999603841c00a06187c95102800301c075841400180c005082070342c200798502d05d807062219079191600d00c0f10800940c0000311f490b03030b2194144004d611054107041c02c007620300840c0d04c1290940168000c00040469200040c03400c0c4108442c071039082e01d40b69104084034072090260800d0b82e019000890000440d04004c1d1620038402011690140c04a03501c0009814041c0c520110050300c9050034410006c41c041c0c00c0d40980100c4005148070b1500c3c0790b2995440b005d04d00c0180c4219030341c80031140240c80b020850171a40003400101c0b0303526221480d042c2e01e00d60040c0420b444d00010300000c94058076180d126940603a4005000b50308203042c032070100149a000c00300380342500c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 34215167 1250 34213917 34213919
    0x9170c070e0c0c01060915050306010e04030c0317070206010f170a0809040603050a08030a05130206120601030608030a0224010f03120921050d050a17130b040506010603060503070e040605040606 85
    0x2103c240641009410b886001040501c070705044415141c141e03410080c070980115006005c87c403d0b03884519070040c1c05260035000c906442c03e096840101c001c00c2d19400603802c40070001465000200795040f00c1000f036400710070669410700d00650229043d06400b01c0d800480b12040865110005800c8900c0028000242d8a941c0e90b0341914003240e107a0103c1c2c0d108004403c1080f11003503882000d070310149140d0080d1008440c1c0d800910203200b0111044880a400008112030ba44281d01c4003001d00628030451380e0b20303c0406c101940d9005800d042c91100314861060100365004030701707000c1c12242e0007000d02501c40d0842c0d8840002d501010700c81810800c2050b000100d80c89005184030345940b03094101a085d2450341400c40c18003042d0800f02003800000c0009500c0c0561105450209140e081d99584140d180c05d269910241c3d0204006018204004144000c4c80b5000c6445812a6103d40b400c00c14982d83d501415202e04c07c61041c5a8101c0500001a012a07903035000310b0f5009209000c009202d07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 34216417 1250 34215167 34215187
    0xa0218150f160302070602010c09050103092102030903010e0a0c062102040b09030c19090b0d060e070503060108060c07061d0d02030306011b11010327030309170c070e0c 74
    0x30b5044101501614500002d80909241d0140000006426a88024032104207040300c054135808041c842c150402d0b50310207000007408103001ca40c00c4013000245891080c044d94505c020369a4000e80c4201d4880d500c0c001b800803181c10b0000d0380d507a200f944143c0102c5020f10741a016981c01d410071031000d8a04003120b0301d000c2010400d20080001c0e0201d4000780c0e0300e600e491801c1c98600700303405010078010603036407042c0d9a0312600e0658201c21103240e40804030b91486c50350041200405683c1d0001e00311801d002d0420096040400c42d0001d5450580071034809030b07a00d94415642d85400d55030b41400c0344003005554007044191308091300c500d80560302240c00e03e99010100b807424198000d0900140c0010040c800d80d9a404540c640074108011040c0305a900d00782c80305107240e442100c00a040c150344842440c10414905452862070f1445280703400c0c02240d40c1009809410541012070384440460301800303100f103011003510800c143d100c004242039410681c206201e4000941840c400ea001070062800c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 34217667 1250 34216417 34216447
    0x60105011b05060f0103030f030b0d02130b181e1303050d0e06100801060501050a0203250213020403030206180615060405040e0114010501020c220b0a030f0302060a021815 75
    0x11380004012039959859802d0040040103200c62a008150501c0450700c250384d00c400c0c4420b8440d070110b80c42c1c0c51948d00111203c00410b12880d00e103400c50003488042e41048540c282c001d100c1d50054104840004c290f032101101418100c0c1d46120308015a41c444011a1190340908180c107030301880010000a11041075281840803900c91403080030244003030000d40d00070300404c0e008040a08090741840c40d0501c0c065140d0055422074044100201c416401e0341c403000031a40e0b40d558001c0d0290721440c0d00c0701c071228082d43c020301055001d480740340301103035400040c1c4402032149d010010180c5019202c014481d80658803450f503031644600d007800040340558851145094900441300001054207503041d82280c4c0d05816400f0034199080308500000e1174445c0391040400700495024054210000c1c485ca0b00100140c50304c454010300c044601004020014002150550080d02207560b950b070f40c0c1c0c40300c50aa00c9104084613005440344404016410a901c1140512500001d0030b03042c81050701641403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 34218917 1250 34217667 34217671
    0x40207080705010e0c0109060e090c040b131e03020117090705060319140103170c070f03030503010602011a060405060703030902090906060a0e090303240904060605150705060105011b0506 82
    0x41e142d40d100003404c0f10550400070790807910000e08005580b00e142801c0a007010205520303041c000d00882000500c403504a03030480e070280241c1020544c441810b0601c010703003c1014011400c844100c0c02403c01150541180c007000c5942c141e644610441100201d060900030142441e11940304061010440780c0d0f40718091031240901c400c096103c0750062070340300c0944049652078120101e004e001400410a0901712841c4450343c2c09010f9a201d2090864a01c1c107981e0794820040351500c510040101a8000300450480f0800d900902c1a0221000c10700c8803040c042d031010b64051000c00040085050003070181c0502d5020b8100042c0c52003560f00840d0102c041214502c0340c98025804015061500d546200040e004500074900285804c0b41482d40d64400a001254030500b0042081107014500c80044040d400c041d21880356820986401c901074061802140d100d440d61100c032a000c07406010039200e00b0768210b802485c8036443c1400544081b8040d085030a4014a1100d00700b0104c1c40401c0094 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 34220167 1250 34218917 34218923
    0x7020c10050a031509052d0a020a09030b010902041505090a0311030120070201030c020d0801030204050411040f0b090901020703090306050c2104120504030f020910090608011b030606050d0b0402070807 88
    0x4a1b0919001440200981d9080c4054800106205201054854001381c0d11781c07240d5201ca006a80741ba4070501900c0004150384000c05d50745503103001244a0700580c014104490b25010400c1111401c460300b035886010f94016240c00008190b010408211002a20b6003080d8010f0000180c01440501011083d110315541d0088060001108021560726110307041c0076611610180484103048000288006018070019100d6500d0340f0205040c030088401113101a0300080c420800007a00310004030141c410b0280c0d85100c0d2012800081c07080c98107000b03c0e005d80f80d15988951600d411507036820700624000e0f11410505505104c0a485410120308940802041540030755480c030b807616044980c0c1c0c030095100410804140010400200300b90301c1040302540c100d48421090b42c8200414490001680c4000082c600b401000120329506511250100315081880b900641003440180c09170350380c61140c68001030003007042d08541d1711710b80d010034000c0070000c201500e0110f07241c84040e41d5400075402030b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 34221417 1250 34220167 34220171
    0x7030606081006030b01151218050d050a0c0308100503030f030a0b040207020604090e010e010516080105030109080301060c03210c170103110d0302150115020607020c10050a031509 79
    0x510000030200454000c002e11407505000307082c00c554404580300d106105106c1000314041030195941d010b260455548890740703204100c901c60f42100d105801100c448103031400c1c0581040c0c012100c0c0728004549240d259600c40c45242d0f20541e500310b07a4401d0081c03046001100c1117001158940d82400100411041102102e4490604011800484250700c0349540318920400100340140c0764202030b20101d5030440400030314035008000240c007500c01e00c038003042254600030400c000d00921604640844503a65510030700c90b80c8503c241401c0301d20381c0902514020050004010540c424201c8901c19446403600b00c500301410039a0210b454a4040244100c0e44c90b5018000400d038803040808000b1017101d8814415403450f1140150501c000c661107010341955003041003418020010341409602d030007240b101d25a0358a01080ba40f842d08d018038401809aa8082002144002002201c1541c010312032400c8081000040d901a4071104450003410b84400b11b0000718002411000000d11740c01c0e41c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 34222667 1250 34221417 34221419
    0x1505010e090a03020a020f041404051b010203090916020a0804030303021206191809020904060605030c060309071e0801020307180f0806150d1403090108010603060303021f0e07030606 80
    0x9050340c0200041c00300900d0380c084a03505010aa002a10b00001d80c1c041e106440c0c2941d006001c18080e1288101c1c203130032408a801400308000c030001c0c0094007210300e25203030f040380c0c0012001240ca034412201c0c2c0540c0006444007041c3c1d60340416400715846d4a03503004031401701c8003940d2600040c0e0019801513011035070100d688090140d07584130b010752000c4100d604012040700200298248d207400d00a08100050340c401c0c0c403d1924883d4000e440e000d8000b410500545080d107000000f4084030b0195078028050035040108030704145060324040d40750100680b000504208a045c05805c00d5130001604804c50400018140401c0c4025405400c040e9109403024041e00413030340058881e80e01114100540750030410800d040810041d8000300501c1c2e000b0040d10001001602038802e400c4090070b848940c1010004140c80000102102c88003a21050b501da0303602c0c0415811140c09100c0940980c000c090101456a0300070852406244080341c0003c0c01494020100d1405a5076001200c4565941e00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 34223917 1250 34222667 34222679
    0xd11060105010926070b040f030c050603090316050a0c030f0c0f060906050d060b120403030506030606210a1b0617150d03020c0d060204140315070c050a150501 70
    0x81114090042030800c50009440d01e40040315080d10340407100028600304a064410602c00e101e200024400c10010319112074841d036280c05c002186201c2240c99101031100000d007401c0c48000e0b82c4c4903001c40c60255044c808030000b118081004204200c8441c02815140f40015400103070201c05940903004164000c81140340c60900040c1c2900658007640e8a0201042030070381c00700004050701c50901e00191240401c11250300900b0740ca030000311220794081586c9100a00600d06c4900c6540280d43c14801c0d902c549090507221007060303c1a940119142d04003541e604c40900d241d02401c5500c030204c4010b1011a00c8101c0d40072840d00508c40d80c840d4402080012582c4050680802103003100308042608000441e0301821840317410650003041c0d5404032405143c0248600740740c01c200500070f0035000c0031925065009503c1400303034020140d450341401a650800298500350340c0c100d550041c0d180d8079030030015118131402d030350201c1d01c41c0324070111200010505101c11180c00314025010500b0b505001c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 34225167 1250 34223917 34223923
    0x605010314010b011103160804030b0406051b0a050a031d010507020d120e1c05041d01090e0105090d0302090a09020f0307080106020d02030d0507030608011d0609030f091002010207050d11 82
    0x183c1181040341240800707840070360100c201c1d45048212038030580c1290092424110901070303980003900100c80c150402013030102c550041351143c0d8a403455402201140d4203041c0e030502400c2d4040e4001541840b146030030038001e0380300210007403243c105026202c03002d0b0003c6094690403102840142c1186480b11030301c50700701074001441c64503030720140020080540e000d0b0362614240144104001d900c1c440005030b500030303c22039020b00081e0343c040103104100c00c0d061003811400c0c03142c51001490101601d030140c1040c4643c9000f918104081c01c3c50792080d01e0110040c2d08800301142d40030300d01e100700240142803840146221000400d10710349a2411210181c107002c4140d1050096420909000304007d9001c021140d41100b09200040c058903005800c0f0700600d8250000300d2950b1130b10181d4301104410019007001c00aa400403150a545c41b01405031b01d0303009508411906540c180003004151400006801c80403000340700041c10f0410317644900349890708080910300480d5550341c80c03080500e024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 34226417 1250 34225167 34225181
    0xd0c03030b01050c03030609041a040c0305151e281d0d0804060c0207090c05190e03070303140f0406050d05010f0b030c03060a051003020a08010e0103020d120c060501031401 76
    0x242440ba080904e02e80e0440c5d124032005003158410401c00000404211511740320000c0c404264a03605001d00c1c1c00d14002d8202405808151f40d1031140c40c0a81703d14801ca49541407158a84100000c0d2404c00e004a5040c0c10070003801c44a200c5000c00005010419404840300080300c840c4000714031100c1441c481c900c0c802142000c42c115800a040c4038268a03000718607a60060b030303c80800110f17960f000ca0200d05160580d0011200e01d4144030b0358010349948240680b200d14000002d0058400d14944140e40d40490448002c5e0141c00901c0c0400119001300c003000c241500c0394007003a14140754181c1e8403451b544541c01800104802040c04404000c01c1d01c0303007601411202c001c0d0500681801a512218000200080d0740c4030000000601140c41d040ca80300d000b170101505000100e114580060069005144041d002480c10400011002c285410f818102c940142c2141541445520341d80d60f00070002d00c81d00b0911001c2c0c403404001600d60300c99140218041e946000c00c441d6049030150a650704 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 34227667 1250 34226417 34226419
    0x12050c031c180308041a070803190b0306010510050c0708070e0414030c060c070807050d03050901181a0403021509010f05070513170a020d0f02030106050604061e0306080d0c03030b 79
    0x10b12900340300040c03d11080301d040d2003881d0070301c40e043c000e800d140410034071402e20b0017020307840040140148091910083c00c03040c08100001d100040484d014144c0c0c1c3d4809100303161f40074007440c6140320720034001c400419900a0312802d550046480300380181ca06400c6078046058601c0c1c1e10104810700c40c011400c1c5500e0f06d0500042c503d000103030038601360354900203442c020600340d0000d101d4042068860889a14130391007402d80f0300c222030301c52018000305800c0b030b103109095007018100c03032900c0d122100004110b50f002d080e005d00892003445810b2105001132045041d4403400d0041101040400000c905c01e200c0100041911780c200c28003402512000b0f0281000e0107000c2c484289050040314024041c5e65002a00801e5960440401403a000318403601070340040c8020b202c5010302c00e0000c0700180d403d000307600900c510380d550010b1000602c12807141500061098050f01806404119100b2524060b49400303d0029100c050b20fa0400780b900f00307642d000c5010000410300300b5030580100c0082d004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 34228917 1250 34227667 34227707
    0x60806090708030a1d0406080f0604031e0914010e09040b071d060a030e03160f14030901080c0c010b090c030403080106050a050a05070515010e090601080a030912050c031c 75
    0x614201c014090303401c4900d00c00741003a51890714140540382c6d40e0094004042c140102c0d038070031100726622911401c090f80e05900259400f98031000500307240f00c1c0e000e075010566850280e124030b0316081c1510072046096550400010600004150751940c4070180180e02900b8880110b0518000c09007843c060070f1408620035188401000c0207030788000a49242c401e19050102d44070480303a1003c1d05520940c400b105001c145150b05806009034164504041c5124101d202c8281c0355070b0b05143e03904c0c01102e060746e0024031240c000a44082c581c4000d010303041d070060000306921002d840010000f4000b1580451aa8404010041451b0740001142c0c010002c90074060714041400c0002802072096080d5081400000511601004820840d03007000c40507038294030209503181c00505880540540c0c81c05018414100080380048010505004180c2e00d0784410a04916010412041400340001038505005440011714282c07001d01076601c0c0500e5820b220301d84003282d50006000400c540c03204880c50a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 34230167 1250 34228917 34228927
    0x71d09040c060e0d0c06090602070f0e04080c0703020306040b0403020d0e010905062101120b15010507022209030201050711071206020f040810051603050f0106030507050d06080609070803 82
    0x16075040c01c4a09481c0c892600001c581e8011001c58034440307000c980188104803500d800905142d004050074181d8070a82d007174850702a030311008000c0692032401541c1020040c01c02050004440c0c000800d05920341c801a0764015a03660002410040201c4003501c06540d00d1040004141c2e0512080c08000312600740b02818412680000b01440068050b16000d0400090440030009400014009035801c030030180c0c0307030741d0703111105400000100201103d41c061040c0c08954210111410100c005030103a4881e41082020380030040541a8078a010742c0c010311085401d5044e02c600e0240c0e40c02140250000300302070416000043c8a008160300586490308600814000300075420500701926030041805600c2d524441000d01507403080da03201e01c2d00b80c460303070080f90340107607c0d90011407207400c01c8449070320650a100e005605a03a030456a01c0101d4601c01c00500c40325010360311481c1c100d41c2c1c0d840c082c0d041c503258082030821280d550b00b1803101d1358040e01c01c00980d480c0420072200074007201c502540c10a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 34231417 1250 34230167 34230173
    0x21c0c0c0b0702010204170304030203011d0604021507060c090503061006050706090201090b0703090602070608091c03060f0b0706050c07021e0f06030403110d050406021203041109071d0904 83
    0x25500c45103004009070361500209602034401d4040c1c8018200026958a0b418000002103940c6e5101d40302c04c030701950030107260044502c01c0c1d00401c0c482e103007001c02600703c5940360350070040e4004080d04145c80d0040c0034000c050101d0307000e01c6581c8001600da2101d80c1c0365400c0030201440e24400422022003c2c013120410b0060903802019150019480035020503142c22610045e20319905c15041034404880114507030052540c495806400c481c4030342c09030303410281c82d10401ca81003803003180c110f4081d92003800402d2080401c1651401561401e00d00050015115034031028148016404001d40300000f01d050024000c031880340d25040003460452620b41a880e90216200348191802d805c0129041c0620028580382c0c0da49900d881800142450382e20b1400d0b02c0c000d03000e2061041040107900c1801c4010259a008204803015140c10b1303002820501840340040815138001131040301d5a00b40c1c901d01100c640c41c0d110b4041d001d444180c8032010144078161000480d40c035100141761103652074000348404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 34232667 1250 34231417 34231427
    0x603011103090712020a050d0b0a05010f0506030103030c05070f08030c010506040204051f0c120519020d1e0e0d080306100507020f040e0a050a0c0519030b010909020111010203010603021c0c 83
    0x21500f15058211030346640c0d000180d1b00d090f075544443d8000c4502818001041100b5402c0351003100e01031410040790b601c0714940300f0901d8140c040c443d00700f00c04000500100b030041108042c1c03e48240d003101c04c07140e2100d41c122052090365120040a038404140d408411600303000d1590302503425542181400d140c03200041000d40000203120031480e10520000101e84078940121a031900a41e002d070304007414040003001c6600041c040c0d0f01070080308150014181c80406c0c2d03140360406955a4440c0c521240a44a402a8140300c0900900c03503640041000d58955840300c1008074029501e1603102c0c07070316030203000208520582d05000c203c002c10980b401642d485203404121f00c8203030703400513580e100c0c421003d107008400038000c3c181e4420780440300108003417190070780c0944009549070514061a0780442d40313984079901000b000c0802501c010701900d40c081d40450b84140c01454a5020159051005403c9134000e0b000b80c40004d800060744800c940c3e010348100d4281015400401800c5050326000305 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 34233917 1250 34232667 34232669
    0x60305031b0f0a060e0a080f070204060e040312050603011d0a14160b0307051b060a0b0409030c17040b030a0209041104030b07230406080f060d051c0909050f06030111030907 76
    0x82e0340da0b5208042171400c00300800710350030740c0c40b404061303070340c1d454201e2190b0341d8020311702c01c038802c0d800d110b00404c41d889052060b50003258152a80602100000404000380c5001400380750190760712071000501801300c000c41c04005038490050900c45c1818104400d2044c90702010280c5640140a40018081001c0060086032814412552291600c80c400c482c2d84c8a019519860f0b85203171521410107070b07408070f1603a0040b450508100503982d81002444141c46007100040c0c08150b0b1900e150002c60122044030007054586c80116140584440160246400544000036804e5000c1805a10f03400c1902c01c510504071091078003410030b0324640c1e8050501e0b5004000398200010755042140402188400c3c81442c04104110ba2301c0303035140e080c02481d00b141111480442070307107200800c0450a2000c8494600c64001d030150440060802c541f4000e20340f100c85803000c202d0b0135080060b1a50843c4200350040500441c5102c1780c1c03e0540405087d075001d112122000c8000b00140301c2c1d60700c8000744c1c4034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 34235167 1250 34233917 34233923
    0x90b04090908090a1e0e0c120a0906021b010c0503010b03010b2208150a062402030f12010305060601080f01050f1201060905011a0a170910060305031b0f0a 68
    0x114481c00301e4546200c090140340f40281c0c002c4201100400c1440c402d10a040071244030308902c2003100e5440340e101e55074200c29540c00d94807120411450805c1c5102a0001e81c0c03000030a42c02068a007441e54400c0c2c120381c416528602d004103484040202a02c0a01409200303445914005086504040002c5a20710043c4104400001c0018011042481d280b15513404041450101100e0301d544d0300d003164403000e041e84650941c0b00d44000280fa056100e1185005803844619809075001d080d951211091000704501015848140140710146224400500d00d44404c3c2641540307075455490030078580000030300214140051001040f0803100340b010000e04460302110b0707840f0042d014a011400c00080104501041d501348000800c5194907500100d0480d0311484d00c8400110038040b003a140b40c00707a4120240041c05000101000640b03503035956401054a8059508c02c400b52501340c411100707203500c00c5850360404914600c1d00010f95030420700680400e4003805094001c1c0d0301203919101010002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 34236417 1250 34235167 34235171
    0x41407060815060a1110020c0c011d0409020307030f050129010e0913050102030c03090d05070506010506031e07020106090b01030603260f0c0619090f06050a0b0a090b0f01090b0409 79
    0x140401340e01c00c0d15194140d4400800740e031503261140c0c03850b0010394080e2071841000e11031900043c4465100724400c00a040c180300e001c0d807442c440303402007001030b00501c10166418401da0070044045104175200015052041c0000200d100300c000031815a40304012000c00700030f10740708200d903980e43c0000b441695804200d94006003952001c00190320740445000140c036a6102008100d4460a48002180140e20704011107681f1002100e040b2905e20409000400980118004004034182400a0b68205450404600000c0403000e8044004141118860010f0303445000030001e0076128031a01c03001d10020b2070113100303c900b1034481c0c03100541c01200200340c080d00d040510481e211904140c42200e80050090381d0f8481200002654401d07041d9000c0c01180040c44865035424854440c0c0700e6610303408048403d5600c001e807181d400509004010080c2c1310f0701c412846055039078060344140507241d280700001d04020240244030404540c05002c0d4140640c8280c20320845500724103807401c41d4485140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 34237667 1250 34236417 34236427
    0x306100b0702090402130c080a060b0a120f02070609030201020a08010f0f0b030a090501020a0f0f0306180c020a050610030b0901091106130f0e01030201080702120301060509060c0604140706081506 86
    0x42505400440f1101b4001803030240d081d1051740e8085d00d41d41c003c000000d01072007002d44071012210280f0558108501060ba071002403d11480075801000411074004801818004903413100c0042c0c81070048210700603580080e0905030140c01c280c18601508550b0500c008040c10001007031214482da0295070f4240e500400000d41c20a0300c0e402c00400c0030f034428000d5403240101003014069000c0d8100f5100403a141c16142c0d08901d01c070780700c0c00049400d201401598014150000001045001001c00842c055842c080c4042801000014042d4589441d040f141070301e182415080b0f00005465900c103641010902c070042001c0700b006621440c011180725990300131040090384018560341c454003030700c1e0240900080c041e6152400c603040740d0003a280c2e00307030035965040100e0320f44891a0300c84032000020700050113850302c40d00141075002c6015246501c2c01c82181101480c03d04116821180b1007000440200005000c0c0258401496941881210f41c107040e084803807256840d4115030b0044401040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 34238917 1250 34237667 34237669
    0xd020406090f0207021008040503031302030f060708090c0105070c140d0b040c170313060f0909050c070302010b010819090c150c060605030c010e040e0c060d09020306100b0702090402 80
    0x1000c60020852080100004225a540280a074110303400c180c0c402c541c03001500344642d000c4d04036140b199511501951855a5407604441201c0c818801070b80c152040942c1c29034010070802c00103004041940b1081c0c0107141c40c0c90642e103450300c003241043c1040b805108880c002184609002c0c2517581c02039440c40b118102101140740141d01c06400352041d180c45051005001103e408078003501e00d1580805003a074940d441859480c40b800c0181d4113070f5000f150041006901c15002c0403103400c403600c1c0485000e582e61030308030190381043d41c0112140c8000070f40300c420550244908110004282086441e62902050050601c00e07071528494071162290020000c000c2c40701134030b070094000c0351540e6495000002c00141014101401105e034245817100100b5a03142c001004c0b142024140c1d50101c4d405001c00510000d0941c01d2500100da104040e0085016907640d800383c00101c80b242d50018503140a8010580703070480c06480708008107034500c014003403d9104411241015011750300002291602c1c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 34240167 1250 34238917 34238921
    0x5090a17012007020901051804030c0305130e01050901050a030302070b03040204090c0b120c030105060a0c02030a0501050712060614040902070c0e0703020915040503030a0c0606050a1502010c02010902010e0d0204 93
    0x40d110002c9072440100c2051600e25003005061007a000361007506407a0380312402d02400342c040600070100b8110708000600002d20607079060808034442d150513405c0c4100181e00211542c03294014400303485e02070005001905014114074018102111105101850f544010b52078440e80d002d44900b030000080000c0039520303250041410700c0d51086102040329559410141e160300300d000d00b240c00c1941840032506206044d010fa13030683d0001080c05107413071701001d0252603040f90074070102e07018001d0345014400b165003881050310506031340d150722590118031100391086490b02c0c0c0001040c807644110807814840320390b060f141540e40f00c460060f50b54950342000003500072140d1090f41040c2c030304000c110030213615801509403000203a40d40c08003c2201c0381075030440e0090303004954240e80140001c1c4822441001c880d0040e130302030301000440c240c880020a1204116400c04a9000c030b00c003020b0401c80d682403189082450f102d1008110b03038512a4002020455111074151107039101406800545d540c139 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 34241417 1250 34240167 34240181
    0x9090f09070510050a03050a0603050c19080307081207020303041208040f05070906090f020403020f010507080c030a0201020a0f0305090a020613080f150c03100306090624090c05090a1701 82
    0x20104801610f246500034860ba225112000c00203092102040c901a054081c41c015030790b04c0b8000e440390990300c0080c441c55050301d410700c3c12020141c040028220348107000400c0054000c44146a441089110502007090003501c4202154800c00400000c00c40d5442e0b82da80020003440c00c0602c645583c2050000145003140c090114020348600045005844d403012045941e04e140034401e003052172007a0300490150344000b0350803408100c10a2110b62082009210706c512404502d420840001c80d0300d8a55013002c0342c02d01c0517030350001e8841441e035002400450011803a103424003035032802c400c4003901c88604007002400b8000100f00d0400c10700c0680d51010203024410300b2651074203c00101c0c543c6e90074130390000329442156400403a0b5140700e4141100d1080940c244038805407465039640d0710050012020990b01180e9803a1400d0a401028480005c0c100b80c250f0801c011505041403030303080350802000c95082c004100308104075502e4000805044a010080083d01c0d00700980c64180506a0b03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 34242667 1250 34241417 34241419
    0x30f0a0207050f0a0506060102011109060c030f04031203050a1e0e100c0507170c0a0f020409120c020a0e011d090109050a0c1802040b04031104090818031209090f090705 74
    0x50034070f00790002c03000051004800b030250003140d000d901c0d52001a422130700a4102444114400c009610780c50402e4030042c42209100c0e401c881c64100b405401070303044d8120b604111405480c034240084d016525000e120b030080368901e000c02c041390303150304807110740620b4640900e0015151141e52401c030b0818487e2070420411084180b007603d440c20002003407580090030440d90341030502340314003666000009442c4403210490051001410548038007008445980c030481e0302c103844101d1030000514000aa504444180e110425001ba0b1441003001200042c2c00141001e06880010062145d80d015031111030b02441c0001c0a26403035551a40d07014100404000e803a40c41071050105c104040d505440040f1216508111843d185010014059104902c15502c00000501080c408181005a4181000802000054044045d5480540c241c1008000b61150100300b4003103660341c10203000d2a190720340000410340c9810004800181c071550041c20040d40c61000c0b200060200c08108100000f03004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 34243917 1250 34242667 34242673
    0xc0a05072603090708060903040e0f18030a03020703020d0f02030328020f13090b010e01050c1f0204081203010f030807050709050906150d0b041104150e070314040503030f0a020705 79
    0x83d08034406595a00350344114903940c800c0c03600203504118040705440954200725025009501c40c00030141c100039020781241000f4150105126031007004000900701c100d882d40b8050b0b01c42d0010705020781001819540403082c00806801d200d10283d02004903a03100040107140c3d07240c3d002840c030a55842540c0303055014450310000d0400ea450002e0f1700540360342c0500906440f103d0389ca990040027601c500a10290110310000c0c0d1405441d030290014107161a089230841d0f40f4049010300380740c0c400e0b0041803000c4209500003020300c031400d000c0c49500351403514594840d01d59403410069030030701e4005220140011202082d504200031007481824028410248203200b10304010407000e8482905072003901c10f0401903080d0460506005261341d808540056840c8070659680c0c440d8050359541400042d440ba079580f0f0710383e14002c01404a400074010808940649203001c0c500a4200c070901080b135252840401c1c05c120006e100002100d6100402c0c8143d00055201c1c1c041c1c44002c0e016411004080340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 34245167 1250 34243917 34243921
    0x20607120b180114060f030106030203040812100801060807060c12020f03030403030f0b010c020d0209070311070501020c010608060103020d030c08090d05010b040615170c0d110a02060c0a05072603 86
    0x1c0d2000080c03d041e512846940260b89980300c0070400c4510a4010310304980405100411400303001c1d601559003d070103a6a07140c5050200010300740118021942d04900c924002424845090240b1840e070141c501740c2c1c02060542c0c2851405010324000c010000e1403292a440c9003010180b0078004814000c07030440480b5101c1c200b6180c0500a4855a41d010000f245418145041356114244211500f42c000c0e140c850b2800c00781e024041c070f81c2d07002406002415102c0159040c1c89001800419045000303500060700c40c4010b9150600b500d015602ca45110382c402e03401800969100d08844034400d074035040421a415803490040c0032070103100b41203980001d150a0302000c0c080c2c107402008000d0012101040349179280c140103103029180c8800400050388562078984199074a43c015a0019160b5954505142032868286d0640b0300070002c4804e4450080703003012155404100702078200b100010b40c10b050122030300b80140680a400e0014004445203001d041d040c103203d0717522190010411012a680b4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 34246417 1250 34245167 34245199
    0xc0918011b030b030c01090b03090708030a02030d06080f031b0c130207031107180911040216050d080705030f061314070207050f06030f041707060b150307020607120b 73
    0x2030408101c0e540402d040c5048504185004203003611980016103c0342507450a1071190001904000c0840009100c6c0d07402c00300316107a0810240c450010258000c41e601c000d581c124030166030103a40805003d40c080c01a105480c9408010349241d407240c0c0312a02c00ca220080205440e00384159401904a010f08245402050040d0002c0500031b0103600c6421700300c2c0d07681c0101c9075100303a603110300182ca5544c105200c090304060341000841d40e0061880301d602008440000e01240c1c00002ca0910036010001f070384007002000c1c03050308403035125401c00700628500355602800301d100c000c0c00c0480d030240d220001040c60341c494550055001582d9420000d1252071301d0f01c0d00d200c100a8030460050b208401000440c0d241903a501881e10324042c14813070540d00c40c26100040c0380d001810850305d440c8001d500e40c1a14003034902910501e0f00410010454444400521094851810700110110020030403c06610b400143c01900503000e0314051405407400c640e00402001c2000010380d104030081d03154008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 34247667 1250 34246417 34246451
    0x1118130c020c090c16060b040908160c06050a080402040c090b07060e0c0a03080702060313080d050f0f071b0c09090803090105010609061d010c02060c0105040b180c091801 75
    0x82c802c241c0c0d0201041c0c484d10700b9014903005140f401446110240b60324400600150014048180c0c0a4408a0144e40c0ca0345c80100c940c00c681c8085018101004e03614080c0205003c02c04001c5c82142049840c04c003001c00c0c020503a00000348080d002c0c40c0c45140701c6180702d106a041c05d0061181080941c4c89103d11303d4400081c10f180900700009210b0b44450722807525020609100716680032424030701e091059401c0c000c081d0002407100507290f00010150b004512035400a2a20460a40c80001c01d0710f003030100301000340d00103032240b1038008a40040102060300601c01c585503059203903040340c24680c640340952140c800d035048049e8090406040c4e82c100724600b0091805101c8003c02408a43e8a44104035200201c522401001a42c81000c044441d000c40c00030191260043c50114280000340d000306941c0e920281c00c0f8002a076548042000f07008094038126080500a00c0d1482840003102020b640d45031090b0100e8420b01c0c9540100c0e1041950000c1c54900646000080c04038914014482007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 34248917 1250 34247667 34247683
    0x10305100e1b03190e070b0706150f0303090e01060201050f010504050402040b1c0606080a24150b0304061d070b0c0c030a030206040b010f15030f0e0f0610091118130c02 74
    0x108007410443e00340070300340b17012030a10241c680340c0030660f090107400c1d280c0002816042032500c00e5802c01001c04150100510501e9010b07500075103e0649440c038000d151102201c050b0f21400c00c40e4542014000401d4030f2096003811214220b030081250748550000800511800b15a00e9020004c9480000038004d8200c0d06148540100c808021090307a40451503155040013100420341d0400541110140324030040c0080a070408100000354840c3d001d848408901c0075800180c00114084108000c0040341c0c0205510300d0340350503412140504942d90159548201c1c01913501e20340f0045101c03001d0420401c20000400030003011110840c00743d040c00f9440711000e907800d540000e604400802c400300041d080c101111700d40340750000c0d01200c0c03901c11001448082d01c1e05049980b10b0800c520150380402c00e9605007031080016143e2030604141c038248000013584640c0c1c01a050810b00380d4035196500c01d803511140c1c42d01241202608850004000002403c1c070501450301c1d00e02120005580020000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 34250167 1250 34248917 34248961
    0x2010e04233907031106070216080c010f0807022505040b0105030c0706050c0d0203040506150123070215040b030901050a05091b0301020d020f07020a05010305100e1b03 74
    0x1c502040c941c0e00601c54886844a01014280b0b1400c51181c001c0c1c1810003000241d010746444803064510541042c1011700982d08000140d0050034104a40441301d141007005100c1d0300f006000da5120140040c110074192007940c0180141a0005510113000307001900c41030040e00c003812410200040c480c16029407900501d409285021a0300d82c265001d4821a030190403c201b40c5400c0c50800e54071032000c0c0c100207019a03141e4600b40310202e410034aa0028500442c4900082c0140d0721702052124a402000310303226041003848a003c407105d10407000c06204081c000c42c55942e40740ca40e030000c40c00e080300404807682c1c042030020780059245803080181d40501e0030f100082c820354451141d80010b56000b5909071030701d0f8002e85800100c00c00714400d04006000040c00140c1410555006841243c000e202c543c80e80c090001104004c61034003201d0503015140074203040006040100c83c00d40f1b5904c16000e04030181071280080342511811a0188440300d04040e45550360b49000d80001e040313071164a141d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 34251417 1250 34250167 34250191
    0x1080f180106031a09010606140c0c1002030307110c0604030b09030910020a0302070603060b03060108090a1e1a010b03010501110a121205060a08030a030c09030b100602100608070302010e0423 84
    0x5c034040c0785040c01010100c0394199240600500042c2c40c50850380e002c411142071610a48007070a10a03120803080d0ba0724440c45030051034681c904028081d2440107401030345d2070a900b0031088405560381e01001d075003c0d00d400c00240076071595071707114443c60340c4980440300b41c0c4285055501c02c016030340064205111486907094840342690380d001502550524052081c0d14441400001c0303565100d14030382640466010100c8401421580340c004410001c0441c0c0c130500c00c0d0003c3c0503800c0c01000900203000c2c1035101c200805541c54284c2041c014001030040754100814164640d4403008100900300c1e840b030700b161900c0050b0000c04070280c008001c24452483c12420700e000112035203056607003201203c044c1d1014615111031103904400514540304154284816041e000c00800c0d207400e0b245100300b21200b0752786076180c1400800384c500140307100854219070900005100714040480c00708100c3c0c0d42070030040f50103060380d4001006480d807008050300c40f031038402d40c03e60b805103c02c0c5518040c5241d9104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 34252667 1250 34251417 34251421
    0x10110705060c1c02010e070e0a0f0f0e011a030712020114030114040b0316090b01230a031404030c030c03110607020a0311030a140c010e071404060504090201080f180106031a 76
    0x10580c00c0c0c41d031b00e04416481d500150700812070003045090190b40081c00305000110f81c105801c006045869003200c036000182d885e501c46103c04000d03c035034480884000d0b502c1000175005030000f903480d0b403180100c80421104038818411640140c1c6001003111420401035269078680c00e0079203040521088291145003060441c464500300403805031b02c070004070a0784058540c01d10303541001800f01500220b04000d40440c00c0414000e40680e9901d0421140304500ea4690b04a4401029036020701c450b40c404c601000c050200280c1c001d0502400319515040c41c001004c00390905070380b8908600302c54840c0d802420100404954081164801075100b0340700c40c0a13596155000315524050034100c0c0b8081003500c6485c1145044aa02400d004020100081035005240c0201810f001c0c080e807040c480b101840000748203500d403d00801c07000d014160740c10031040c032444d000204400e2001e0b0010321540341c801e0100708820954400003442e012140002d00a245c1d0340d2034000d100e101ea078141220041c0c40303000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 34253917 1250 34252667 34252723
    0x7030f090e0f04031d040e01090510050c07060b0118170d0201020406020c04050c04030602040b0414040216020609010306050312040302090f0609180c04050106050d050a0b10110705060c 81
    0x1c0600e00410814080c1c200b40d5543e07544c2500c00c055104548942c4140c031003d28012a40c45000309101c1c1d401000011485c035885183c140d2502d1034800d401085c8074144010460840d072120140c500c074680000340070031403c84100c0141c0302c0c1d08404541c1040c0103400c80000c82d80b5501c51810301c400f522228200c44041c004e19a040f4200d0103103004440050304455480f103624030b0f05810094220305648a402d141507566a40d403000c90b07006034401c0b100d0f5a8003140400c000f2540710715180c8810b1043d50290300c0c05041980500c258115520020311962020a01c6201b80e403081e07000308003515015080301c101800030a42404690041d1004904c01c0c0d2076900021920031100405c1d81c01894050a44510358607003c02500110604001095452264244c2c18805a80b40d014103402005241c4815995607402100b10382500c000030045031025003428100c03070300340c1c44102445032480510300e441d036959110801c8590402c5c0055006c01e510070004103554502e2030000c101409024207a510b40c03002040307404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 34255167 1250 34253917 34253939
    0x903030105151617031518011e350111120c070c0305060114030102040f0506070510060f0906090207050703060e030708040305060610090f0312090803071a01060c02090604020a0e0607030f09 83
    0x3c071805000040720004005403040c40c42e403829064a010101601161203e429661a422225020004c4880c0031002030354650b488552b007031044100e00090100f0841084030050768410714681c0d994184180340001c0c030082450043d109182c1d1b01401c807070b00c00e42d500d05240b50303130b00b100303004d901111104030049006614051081364226219001041c0074a03103000c0c104440b903088440709840c540180d03026048200071a10440e805820031440e04102242000b0480c7c0455069401101c1e555204100b640045100018017004503a4443d80220b0380c049003403605070840c020b5513401003011001141c00b008110300410803e00c00c0b81c0545052508e607501c00000c83e001d120340d114000040c0345103802400890b07410400000203040c0760400c003980039601c40802d4034580c0000c50581d0301580007040c004421415003c4540107051030f03e4454804505030300003e008040190100c0d100315800181c1003407050140c1060a20844000c00d556140c04840c280030313210390200c01c942c0703000420745100801d41ca034400b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 34256417 1250 34255167 34255189
    0x3060605120402040c0201020f070609030e010306030515041103010603030201020d0b0402090d080a0516030e01120203060604090915020a0c0c080111090f0f03061e09030301051516170315 82
    0xc90310181c542c0d00c4a07001d010081070600101030455400304001410b00b900782d03004016491040c10006081d2070981801058440d41e150f4060425003008400c00208000180203150543d50714400200303500c0d40d18152090a0301e50f19200d405500b05580001071580650150001d50019007083c0811038440302004204d2058006082c1c3c03010800e60a140031481900c041c0083c0000c80c1000352a00c060217400e000e035461181412400201c80a03140069541d000c04d281e0488421450250b0550501c480054914040c502600303e2281e0b0300c00d4940c003400160380711504000f0711140115030f54803a0070801840702e0010701060382c911180b05000100d14005104a801394000b01b603520b41440100b5081100503015003446030751115154074a8007043d6020310590b0301030322800303600c00e20302c1d9180d039549001d00d400107000311981c2d08180b0040250b5150085c02d0342c0b15003444245c41d17590b032810703a05d4401a2181c03900090320b0a4000d8204120b0000321b6001580280c00800540d1401c003c0780c030400001c00704c9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 34257667 1250 34256417 34256437
    0xd23061b0f030403030204091a190302031e01060f0905060a0b03010e0c071401050a050603010609060302031509030f0a0f090e070c021002070b0d0204060807020a0506011a04090e01060603060605 85
    0x3000081c8030203450102468125100e40380c09407400e030ba12400e000507680c000701807a001d404030010035010341c5029001c00d151801d05148160440c0d1860300020b403030f0181000c00315040d2100403000850300c0429807101c0c010380020070010056030344610b00c034801404101c880b2070290642c07640216603008a002600d0480d008401c2d1020103540d0b404600c1820382240104a40d2902c030f40c0c864212002c2c00380641d5214004003030001582d483d10908160030340300140d10031344550346441700c24070250f20f001c0703146c0302c882c1c0ca0060b8804064850003560340c6144241603280c0c84805021030202125076005410860a074426655803076699215814501c1000c4140c41000c003141030484908014240704040c0c001000e254010b0300c0304a0350f1080b0680240d440f584296801b1a07000405214041d00701c1d40171a0443d115100802030700c5d0256689036075880046c041d8480360b8000c0544503155000789000c850207040034800a20500016a9550780640b00c540504e10100782044030114140d44a40213440b05814 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 34258917 1250 34257667 34257721
    0x18030f071d0415110f070605040308010b0f0304020f01020c0a080a1a090c0f011b0b0604050a06060f05030a0b060a050a02010b010e030a03030b04090b0405070303020f0105061008060d2306 82
    0x812107a03e0001801c101042d6100c0c1001400750302443c2c031090010349011800b603280819289050314008089401c16040b01c110610b0602c64146058118070aa070750040c0e0549001b445105c41c480141d00d044201143c860388025640320120340e91001090341c41d00180710309441c0d410781000d8210424003040c01c4a101007241e002100b000c4e0203190805048288500606012019800941d202c80f00345048075030a0b92095100020f005981c1000c0c4030321a441f010858042242500b061401000d03560f0b00c500303c0f000c002002c07002c00d2810526621004840b80000c02d140e40ea4a02e07040090000e4106482c2c01c000341d40b9080c0d0202c503030b50140040141012008010b480480da440d98160001d10014040d5900240c2e50781c607117000509980d503da07008a0003070b801000402d1a51078000e10300984d48802c81c00b00d90424080c450181c80e8031a2885c4040300c41d091031800b95030360102007081480071510181480018542c4036910801108400417001c01040c00d850007943c60b0341070f441548000c900071100000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 34260167 1250 34258917 34258943
    0xc0b0f0a0e0d021c02120706051803010209010806090a0e0a11090603060108060a020d06050909011506030c0c1e1a1815010605130b040e06010306090509100218030f071d04 75
    0x8110013034010644010304945194a89a64040c645015500550045240029142003081200715804480081107000f5880c10a150000070070559003e49040c0c003410a560128041072400d03003104288404402c2250000348850400c0c1c664508481c1e021030040f00040e020803260704010528038162400345005114a4603124189002544030007180281c0380d03521800850250764070002e00d070091106c000007040c00f100080c50b240103186590b100400b4107107440001e0303403052340041e50503a00542104207520b2010302260b01c180000c404410007001480e0a134210740c0c41040c0c00c0c80040c0900700a001514a0301713482284940d0700d0111200c65501c150081d001004a184a04010480d01007602c81d04007401c0d60701c0c07200b5400c50308141c0004250109040c00c00c0300650745446108010704442c0707014015414a0040e194482e03c1000d8200d0045400194401c00c00c4c2c40900c508000c0300000d02291542c0b14080710864a5214900034884001030b00050b107802c00890385485402507070481000b104d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 34261417 1250 34260167 34260199
    0x70813051b0103020d060305030d05010609150c060b060307080a050c0a020303040803090f060405031c0228030204050a030609020406080a0305030106180e0405160b0c0d030203040c0b0f0a0e0d02 85
    0x320038040c01c0d4109a001c00140301d00040500909009500c074000079511403881d502c090040d0b50f8160001c0040082085041112045031582107500107500d04006d03e004416007000000303490800d0030310742c01610001c240710400341d110030790510036003501c0c2d010482c40d2541030b88404503119000b040c20042e4030500200b004a0b40707041c01540c10901e10001c69010b0f0926100300f42c00c18904840c00d907100d0b0800b040002e00700030104079405801c56649800c528182a420582000e0804144010364100d404078031418070300e000780c4c125400380100404030401c00e950fa1800e4005409800c80881c003a60030101e00041003080083d60b002c0050385520b455013542e00b00341d82125000a00c4201d0440440c8050300000d500d81283c6101d8041e50060001d171041070300d600da49a042d04800d601040f55020100604540d100001c00e0006440d021803401503038030b84603801c10354a00160f640000051140024410740800c030304100402002e04992615000f09050360100603502003000740107500310741291010000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 34262667 1250 34261417 34261453
    0x20f03070201050d020d060b0705010612021807120e0c040b040b0603040b0703020405060a03020415020a0302030a050a050c1219030203060a120609060e160515121803030f07081305 79
    0x614100d513107005051805072403004040c1c40c4e460340140d00c01c0704000390740c000340b1a0a0141e90042e01c0302c0d034582012a8403690128140c11009a0100c0101c5888004503820754400c4180d000603541262041c803010b00f40a86680d100d440700e1a01c00d00c680c2c581903000d12281401c3c0240048c00340d0080c0b1950551351103854030142410000e00d01d00c1050303801c010115450361030314013030300b06814030350380060b2554141002c1210302e0032007a03483c00035075000031480c031300080c2c0c00130807240040c0e4a843e02c2038a6101c0c500c03041d10b542c003071300b00f58003903602401d204003d054144c1006002c162280c0f9a42c000c001c44196015002c03803105450840d004182a40f09100c0c8030625449155010300c43c1030001360200c0076403101412100400d000109942082500b40300c000c05645240c07010707140c12201040030082d1804000c10610a40c48400070050840000442c0d40300904000d03080d041078102a02d5907850002e000201d203040c126080c1c808201c142021400e46050041c0ea0140254000001c04101503a0112410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 34263917 1250 34262667 34262677
    0xc1b02040b0310050a0207020a08030306030607031805060c0c0c090c04061d04050a050105090a1e050403020703050604030e040f060e04060b04020408030a020c36060103110318010b01020f0307020105 87
    0x9094460f200781020000c0345482158869080d02034016104c841c00c2c4100030342891658421101c3c3e030300500c244903003a5400f00740710703070082c2150078005481c0b4040102c6c82421001c43c2e07800b40c039074000c01c0b007013111180c200001010145110816030304650401c1e0100b00d0082001c1e0380e1544060f00c00c2c0700500c082d034002d445583c0b258020020403080c6400310030025040c0c41c03088420b01d100c43d07103500041145081c600307201d81d04140c2141040c000c01030141228000500b60040c9480500d0300d03180441c080c54001d0010360003850708030040d2039007460309040140c4411540da600c1c5000c0c0303250040c4000003071168418074042d80c8044049090310b445545038940904050b0301c0072a44140e003040300260380401000180561b0700706401400c01802c4c044104001c1400384840d6000000f01103428407030907040241c5400c51142e98070a1004c40740c950100480c000c0c9640400a06004000418001c40500c5007a1146090340c80000030b00c042e2440c030004a0711754a0ba5005c0d000e10b580144a004015805400030340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 34265167 1250 34263917 34263919
    0xa0e01020d09030f09051c081303140303041703010302010906050901110d02010b04061202031c030902030106090b0306100f050607020607050105280c080c0309010b03120903010c1b02040b 82
    0x250400e400c0e500c03080100c4a030b0540480106040d5100d401036940c0000c07211005010031900c10126021410405400c0e6003180310060403040f0014050f44030b460200e04803805140c101201c0340780696000c03442c039a20384c0305440c241c410004450060160502c528220ba05883c2d042e540c40340640c0c50004152015008140000d040c008410808403503507501300b004441035103056001050704610304003071200f02c442c00d40142c0a04c2000c2c034080e5000d40c0340010303941c00410140c1081e06840b0405c0e04100c0041c01003c1c0020741c554204180001c955440e0b8018003810780b02102a07a009898039500c5c89070148051203569450364481c041000a032801c1c02c05000b045002908070780c981142071341d07410b00b101c01c01c581c0e0180c15240084420503011041c01803000700144804208441c01c074001d000350180303d0007000720600150000014401c2c1e0000e4004642010001e42201d0b4001004461303400745801a2880341e01039880c5c0400e4401c1d46114094806003c1488070003140011141c0c0c0a102c06004540105 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 34266417 1250 34265167 34265171
    0xd020603150d0b07031a0d0b0c0f0705011a060c0705040506010c0b0901020301090605061806070c03021c030807030c09050d03020319020303090c010806060d09021306031b0807030302060a0e01 84
    0x9040d0644840b0100c1d4a00340c496504812646840c000140c12107510016000004003c1660000c41d6140c5050070403c10380c001030416a551740300c0d620191107128540c151044150042426010804150807a00d0000c604007075030384034a0040380a105890107000001015035105000400103030601360b001c1c580049041c90004a8140c1030388505030303020010f4a000d025030707600000402c6514028419100584070441d82a072511a601d40c68030b04001c8045079440c40341e000080c0c3d036030400c0380d80700b074800c02943e0107803c02520344c44c009205205c00c5112641500070400f8200000e0700c5904c00c2c4506801c1c001c2a44800c1d40e140e0409082c08445044039101710103500c000c0064010300b00f42c1e103040c40c00d40c503d2039000f103582c1d2401070072042c144003d042e010780c14810800c0c244001c80c0c2c0c80000344c0701c003042e50b80320005964201e40000340d00200321046035100e00d481d100000c0140b06201c00d012070102c81c241841141c1903076a0b400c1d40e03038a420612010300142c200700301040c184010b64008610b001c05007000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 34267667 1250 34266417 34266451
    0x1209080c030703021e0d0507110f1503071d0a0909060b030f07031401020403110904050703061a1903020f0607050a0c06110f011b050a030e03030114030613020d020603 73
    0x11880c40c0e020080c20f40c0036a00070201440b9044800300c09004641d8014054180a140c4040161035030144080040c51203404140e0b005450301d1b20803144001003402826100c01d00d4110030214950748c01519407500044845450f003600340c0c8240401c0301c99600280107402c2a500e0400490f00514042e0001c072252901c4a4010100760ba041040c001d48012510240075150b1071460545405c0925002100080c1d0040c1300401c08186480c10030902540250751200e0b45690740d00e000360500c00181c0009210600c1c141c0c0001d414046000b1001000800b41d454142114885081d0441401e107448025400f00030740880c1c0000741042c50140072414860310440301511266030b00d0503600b08240d00008006000b81e4031100c07044104004448514103110020031040400c05041c1d41c200c4841c14401091000020705501980e10135801408410301034420350791296140d041303840041c900307403080d40d20a204600c0030440c075035020a803d00140f5802010315022a9407982840580e0304028203001c000341c040b5036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 34268917 1250 34267667 34267687
    0x90b0c0c06040306060503060a0b360406020a020d031e09140607050306040f0212070e030703080414150c03030f13050105070f080a090c030b100803040303020304050102070b0307120908 81
    0xc003500c007544c802c1501140136030800d41454581000200110074150904201410584802d400030700b074a0b0060104d000c01c10f010f011281380000340b601128004c2490f8404010a01403154003400c5414559801d0303400c60b40305014101c080c0d5440c80b200342c0218143d980107081000320365112a102902c100c0310003c0345140000c046007401030440311240403440c00420014945058482c00070740c682d45034801c40c00c3c0340c00715030a030626000c01001001400301418002e50560340c2041408019640400d015564a0b201c10007454101450a1858043c3c2c01c2c3c2402020300355151003d580c650841d00c0c00460542c0e81389409a00d00c0c02000d0701d0465803032a800b0034040454402c0c00b8003032040c1000d485038283c0540180c40101102402865608640d28100749000000c01e007594130022240c2100c0a0211500c8402e0f00898146544c0c1c000051480001000401c1503004006801140e1090702900d801d40da0324040041342c1d110440d04207000451075051f680e003118103030b44142c0200e07000c0c1da2030a040c0b0490207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 34270167 1250 34268917 34268929
    0x206060303040f150309020a090c02060f13020f040b100306080c0307060f0e010306050616110909120c1507020d1101060b04032003010f1505030f0d051809010306090b0604050601090b0c0c 82
    0x2d08109c0c90540c0325800202d14640400400750494a0150703200070380d290000c0414507461601500903c610082c080d4540680d40d40d401200c3c504d10b0040c038030508628100302c01360060006101c0d820301c1d4029003141c00403c3c50701248132000c0b1121074462040c4801d11440071501111078890a80c1810380d41c2002180d5915520050030941c51901941c80ca443ca890410b000000c0341e4184a0744030f0001013003004128200822803a0803110300c50059500c940e189204c09080c40b0490b006015145411002c01030b9040d400110007020959546504144442d04260300c5d00740c8000780100e100310b600401040000500c0b040c040045090007d0070340d45150380030f200090075554030304400c08481341c880c00e0380c6442c0404200c0d020002c0204400030300c50383c50800106500d86c840c0a042c0b0040c89808900030060002419500c0a000c038014540041c0d5038682c906100108801c103815038410013030100207039a40c10030f07210350360269030141c4030440c0031440c001d48121154804d1000c00900e0190001035503440d1249 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 34271417 1250 34270167 34270169
    0xd02040e0a0e0703020102030a0309060e0616110a0506041202010207050106080d17130201180918030329100e0301151d0c070213090506160206060303040f150309020a 73
    0x40c280c525260402650309001d440d020142c65481c0e801c141410401031307800004803820790b003c1b03040100303801405080c0000284031250008005000b208200420102c01a0243c900a00691141c055500980091a40d90f04404034000c24a5010002260118a500c00070402228031440050325261240c0d0f02d40d825a8035a6010303000c15406090030103002c90300460501c078500c42c2400403400382c3c6040d06201c480040c1c50346019041c0070400c035040c40341c11140c1101501500d10f43e4818841101912010004410300c0304040e00064a4500e11100c00c0d0910500050118101100348280054100401c4000300c0291500d200b44400c011004656403000c0c056600b411a034000420026441d102042582d04106818004080b44180030006d08040020544010940569910030390001a81410006080e406c00c003030040d100f032808000c609103402134544a180480c1d400c0d5101910351a040c1592030086000d00c908034199681e0170300204c4003104041c01032079010718010400c1c0300c441e008282241c400f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 34272667 1250 34271417 34271429
    0x40206180d06050f070f02060c0d02040f030503040612060b0d0c050412050708060a0c0203030a0e0a0b04080c0706030605060703030b0f0a0303111204060e010c0507030213020a020708030306010c0b0403050d0204 92
    0xc0700100429000342e078141d6540030380c5e80e09107032426280302c8100a4036100d0007800c0c0c0b04200b20100f40c03154803040c20740c19680a020185030784204280c803414040c1ea69017081c400d40e80003c03851014449040583d004e207408591501100b5030800e100c40e03100348050001c1503179420412005202c005800d0b41d10040140c87c19000740090702c003003410324420780e042940050444804078140640003954942c00412a58440b04075180000ca905030740f0102424181e0480c006045a4031310401d010911a40720005c081540440d4126001c540e9200000d405484a902c105035009600303100c5940803074025000045c0003c40205208101242c0710000346a010040c0c0059000070030b00c0380e06803090601007000301c43d402c00541c030f0981018074181d0010404c0c41c054421504111940580108011042190b180510341c014581134403d2101d00c0403200039004041c000c0018840d4a900040d040808800c8a00a68040c1e50751580000551150344029001600807410404c0c10030040c10000502e1005e003016000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 34273917 1250 34272667 34272671
    0x20c0a0302102f150105030604080714030307030b1806010e0d08070c030b06120c03071a1605101518020715020703050301060806061207030c0e0a08060405150f040206180d06 76
    0x1440c2c0c240140340001203480181c241300e604005000590f000200260311980c4180b066665410038a0403086600d2071103003e4080748000b00c1400307034403505034020023a008016902014184002421158441030907615140896029216031400b030504168800115009080e800d00e00354a82d500d20f11007511550090300d5842506082c4001407400d141c2424502d61000c00624203607080d100081e4480c2c0345845030100c0b9802420710321201000920540b01103c14521000680c1034450803c0c94450510003103000b0018030385401c0051040c20003028109450301c1c01c05405155078002030b400000d60000d002950343d0036a10070f0b484191a0140002d1108901c284c1e030b8603869514012001d010010058051440341805100400141c00e003a0030003607012150b454049036000351120142c1d586014036001d1030b08280d41c4400410f91603400900203006521403c12100000004605080030031400c1d0750b040c682d00440e20225025107448070141c00404181840d01c441905032900065031801041002c460407a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 34275167 1250 34273917 34273997
    0x6050309070806090d030e0303090303150a03061805010f061a0703090f060e0907030606020604030807030b030f03030f01051009140109090e0109050c030607020c1e0409030908010c020c0a030210 85
    0xf0340d04d8001c410b0340c087d007840110700350701b8407002e110b03184c0c000200b5681030841883c009a2885c0e03100d98007100115080034080080040c849030a02254804400c10380300c075030a1001510350080c1c54172a8400b101c450700c90307400078020f00d000c44140a03449540c040d420064490310100d0841b08080c803c500526264544c18060306050003800314488000301040145840c04c0401c00c03d6580100c1c1039544198585003040103a03549040c1070b00140100c1c2519601485003110550a181c800002107000f6090540254601ea0365801044011500948144000360f6031040400140d050050b1045000c4d01c141011050700785c07610020411a800015940ca80740e450b1700851081c40320910501c00340701c2007600075008600e407000d0301a603a4030046071014051400d210304508501d05580ca0ba40340428000c0060091021a081c01000c480041c0900c99455281a02212503a07000142c1c0e83c200d0040a00380303540983c61502007200450300a0755020034414424a094031100070b100350f2164452a0071b0308c42500d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 34276417 1250 34275167 34275193
    0x70813080a0512040303090306052809030e030106050303041a040e07050a0e0d0809060d0e0d03020a080f010807090209041d01060807060903020a031e0b070207180212010605030907080609 82
    0x10f9802da072032040b10400300014000301e58040c4d140416a07811040c0420580c40301003c1403a590100d14800002264004500001c0403245e009091400c0c002c1e510000d0b0300b01e2101c2054225452403160543c540e00c20082040401d02d50040c1401c200282d00d0928101591041c0101600b0307011603203400000c800103809a0015080402c60070320910076038080c051049642d80325209441090145440b500d408242c0305c030415500c1c0c10002b4071214680954958202d0f01d0f10140c00703908029214808121010009a000c3e40030724001c1d4100e48212000b4502ca91070180b41000170342c05030901c540c02c07540300c0100c0c01c210302148005000f100c000500000380c462401c48040d0404405410450800030a00020000750341d415082600751f0350408101c20440e260003000740003010f541d4100805d0844000b04002840b41c012800c0803c44548a0880c12441442e107008012445040d0b403c0d000c100b0340800520199100b0300103107a00880c0304c000c588016880d000038a24050040b01d00d4a00e60748004402091 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 34277667 1250 34276417 34276423
    0x140d05060c071712010611010906061202090108030a0c060903140a021b030a020d2d0b01060905010503070f0806030c040f06080106080304050307090c03020f0406050304060b03061506070813080a05 86
    0x10043c45a54a50800c0c41c204480b24002070184a29002c10125829000f003006080d03020f88102030740036504203c40b55a500041c04154507142c1700b03a20038241c0c00c00025103c0000700490309401d08503540c0d000312001d03681c1c440c00200003108040c1c01304560791014000d2581014000e00440c02c06400805406084d074403440032183d1072000e0a4065089156070704016101c01c2c2c1c1410004d54840b10f40c401001e5040403481c460050313005a100442d0402c0307000e40c00c0c05420aa07260690703980d556081a403540783c20055940d807005480180001c1d81018503240708038440c01041e80c01400003029a000c6103000c000060550b0040941d00708000d658000801ca801800d2145900030018400503500302450140001c4d2103040c02d2007a02116074407041c0300c04520340b0039411140b90750b2200065603106c9469441c018160b40003194112038852618a00306180d1500280891103203000d4850f10808030702e0380e4180180d0390840c0400311013042040c0700c0000112440e034182c1005d00041d070014810a881c5050840ca = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 34278917 1250 34277667 34277693
    0x8090106090203070512160509010c1b1e0801150506070c03060509031809101509030204140108010c0c080d021b07080a0309060503040506070e0112060b0d1d07140d05060c07 76
    0xc03070110a15505d03100c7e50403506580e80c600c0c09003800c4906c3c0d4464182004282e1400c402c441c4491125000800d43c089082280d03012810060b416402c10382e1625595804c03140324200c3c820602c0c401903402c00051600900070034450f440b980c2180395842c0d40740d9410090365810750383c201485d0408600383c82c6001d08171004817082c82084401c10914144032040307004d840c245020b007042d007a0030380ea400e159441c0152502c2005680c0900308109e0f1542d007003080341c2d000800b03014942c140d50a11000114242c4a1025424440c0d004000366180240008484001350300c990307200c04106070b4052911041c188103012002c028030103070700503043d40c0d103803442c00600801c0260000b42c1032090910501c000b00b100052410380c821000d042120001980b440140c405141c110031581c803260600c4000b0411014044c041c11f124a440d00703044c4428801c1c00820032014042029001d01940801c9041040803080c0c110003480c0703000541450140d034066210242842c404454010003c107000440740100090800c0c2c1403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 34280167 1250 34278917 34278931
    0xc020a020301090830060906010908150a0506030102130e060d061109011704080412020f04020a0e01030b030714100c05100c080604060e040f05010615090503070f03020306010608090106090203070512 87
    0xc51780d45c5900c003124000b440644003d0182c07445d80c00150099010f522250080c050070003c442d06500f0075800014074000849868540d1030602d404103440f030134140244c6d00d400d81c041400180880c1080719120070300c14000c0040754082020240e281c0425200c2c1716014800400702001039407001d00a00240c00c1104110760320076241c03502801c200c00b00d0011000c0d2801d84040c0c500c040c182902c140009181d13501640240c9510500c00540c04000540020342c641c5011401c1e01c0c140311611406e401c044d25040b09100b0200c03440281c00045c0038074034000e10403810080c4241040e010843e102d484891030f128060175440e80507955140e4098510b60031002e4030782d21001c1114144200e43c1451181205202d0107400101180404103040701005029000380001c1e01a240c0b41c441140000a00100700d10310522400d4064040d03010046004041941c0200550340c015000304000d920b000700403100075500402541480d540d0b02004a04812140000c6008268030794455440d108031900410072003030054400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 34281417 1250 34280167 34280227
    0xc052508010c020a0c12080f0d1b0801050a03030e0d060908040603050a060b0406030c0c02030f010603030905030a030e0120010903052502010e0609180f09060108030306090402040c020a0203010908 86
    0xc0d00001d08520401c0058076041c1910301b0444102d460710740d07210b029144807020310721404100c40c00c200700540c2c40030000032105482880c113401850b5013507a003001e081c06502e410841402003800840e0240e00d600c2c00015000d451a43c844409031280811101c698400321183c00c070019040000941c90f006058011544903c02c010031441c100616003940302d1841850241b5441d102c400700031740e00901c42d114210380c019042d00c403540e1a040c05107009202c2d07404200e01203202502c4c0440c646c200013030040c1c09154141c0700c1c4004c25841400544803110141002000e200c0d1000711005541c50a00482004034440c1d102c05c2c3e00c074258414403520081c0011001403d044103e00c4240c00750703a003d280080040390665849030380c1c450301c1e00480c1c0100c4000c5129490000440c0038010b01201003010184280c550405850050f40c036092a5600e074442560941c1e40100c1e1480844d0161a142d8800c03031714002e050040765002e1a50340d0110b403e5440c46c0c603056981d80004681c10501c03003d0502c4440e085d925203440703 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 34282667 1250 34281417 34281433
    0x310060302030c1e1c020c0f03030903070212120409140a020a080f060a030203011b020d0f020607080c040e1003020102011a090a0e0f030705010218120309010c052508010c02 76
    0x21141080c011244c020f0169140e4084c514009600c850460301091134507800c640c4650800820307000a54040d5440d4000342c03142410703400c01d003003000c000d9034054100c1202952800d0502c0c0c08000541006a0301012a402128520200890594010001092580c0d0081100d545104d044003000c0c40c02401c41840900400003001c209038000011680844101030a00741760b1560008114100c03c80c0d08021b41540c03a020f034401c0003a041d0f44096070040426030840d00203400241049a060b03030018602c1025901200c042000701d40540c84050f48515083e4013281001c0d0f4460304d01e00c3d00f800a541d0401141400c010520541d6428024950b100c40703441d00c03041c0019118004241c802400400d1441c101c0d41d00d540e6540d00d00d6042c0305208812000300c040b48d8544031a410941d000b03500810304245055076130f0300d0345542411700c01c07040304514200b54080c600b40500f42e0300540340e540d01001d0071030b00f034003486080c260b90b104080c480e08011401103440803a000d06040f0b615003141c825444580955029080c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 34283917 1250 34282667 34282681
    0x60504020f18040b0912070506010329070302030a0f090f03020d0306060f0e0f0306090601060e0901050a06120603120f030f0209101101060308030a0506031b0609040207032102031006030203 83
    0x4149421644c09400060940d40b491005d40c00c106d508000030301200d100080007001e0100c0006d40c1e9050706c2c001e2180c820341c0f520740314418106045041c01c000c004c228130302c000b4007814000c1c1d001c0d540c4001c0f03800010640c80c154000ba04101c1c0d2660900304d0312100204c000300d043c5a4100103075514401d0a040c10405641440d802900d0400341c0c00c010820440720340410390050701c0e505e0b1a140d403a100902250424100100c505803580d500740110340015040701b0f10070f80c8614190980d04d0403210081d181040c070500300f5100312074404104243c144210303100c1ca0b0000001d06030f0020484d030414030343c4c2c0d114040b000390b00d4010140c4410203c2c0c10311031401071010060555503d00440508003082c00c0800ca18a00652518003502c00341d440a829000b0105c10004903018580000d0b1040c4011015107110602c007141c6285441ca80c00326032031b0051028042c807846814164000d254040c002d003417801010300010116010b01c1452204000c48031380103c240400801c0e101150030140c04141019419171500803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 34285167 1250 34283917 34283959
    0x90b031605040b0109030507170d0329060c0604060e12030114010e01021606021b060a0f0302160503070501090b01120305030c030a0b1903020a05040603031d030106080a060504020f 79
    0x1001d01c91003559500100e4200740e0148801c41c004550010543d6581035440080c2c1a039561103041a484a000c2c504d000c0301e40b588a44204001140340313010002c040c12010a0f50084a414481e60742d411203420071a600321002c2c00c102d490310481c801c14000c54500b195946450520340d100d924220100701c10300050060040b03000202407008400c1c6030420703868508800407840c0088690b071140041441800100d0015400b160300c2e113080c03070703403648a2410340e21041c20f100703281c0b06649258000a5230280b490529501c44e070003d02c190642c2481c0c010202c0e640ba25003900710307841954100d6050b0340d201599400c010751084658018200c1d1101001d611a45482c050301500c0000d20200740c00c680000082d2000f007455000d50701281c00600992000c0d00404842043c4061070300003a84181707210342001a032882c060142c1e805603581551210740c4c03a820942c2002d808455040340741c0e81552a6500455000020444644214010100815503080c28018820610845881d02c1d0145210b0906094196582 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 34286417 1250 34285167 34285169
    0x1e0c01090807030204020f071203140f010308121009150f0e13081309090b04052a130b10080406060504140c0a090f060c0c05060c1906020906070606090b0316 69
    0x54a0250340c4007c0884484082c1c07161480c01064544240002d061155150b407290300580031440c08400030b5101c841284e481040c0c248070007481e0f51070802429032007009882e4000e40103203142c500d400e0906d8070b880b01442601c0c24482c8401c41420f86c0841040003045e041501d400503c1040303002c18032414401c0e40e58041040945020b45000c0001440d0001b100300c1d07902c403000a1110300d40c1000704550b0362910601c1c14a040d50203031030512401c20660700d0282c2d13000450b41c0c9050038a0004c0c051210f107006200c410020f5001881030a940c82d038484500da00d80071300c44505950250345007600340c0303401c1c0b07486e4084a0344c1c1d400240c01545000c3c00c003040294850442500b00c00b1985407544c42d110000030864024425070890280e2850580327001602a8000b0360000c03101d4414400081090b840f031080c44107601030103190303001551020302d1500341d5040c10741c55021034502464000d4544260300001c04c10544c01200111011070b5602c1c42080075542c20320515400000c214090f201415082041c402919a5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 34287667 1250 34286417 34286419
    0x1d0715090501140c010908070201020c030601050a06140f0a0f0908060403050f0c0c0d080a0207050405101a041e030605070201090f020906030309040f021b030703020a080a050c1e0c010908070302 85
    0x43e00035100701070746890f815074240780003410081c0700f10b620500d0040300c2900200c1d01203025104850300e140c600c0c1b1b030101312a4142c0303001401240046142820440d6000032800c03550a01c08000c000c2204a280c28100404400100d5258600c01c121981c81c0200325003443c0d030001100340c001c4030230320001a5110048615a0602b690801d454000c0751079480d06140d00b0b000d000b9032128500000d041007000000c003508400c1d01c10b400380c503810b583d14000e04c000e0361401c41c0d40295000c1040743c01c0c41400120340000d00d41c081c0b03072000181850345449400c0d40314420784042e200c41511010301003041000500a542e444801440203100245181d6618103590003602c03c0213104a0160b000500700d0b403010000e6900c0307030500502c248480f080e11603820340290300c542020841120905100313402d00e113000044581c01d641c150300a101d16107598079804555007196545008010080220145a03402000a000e201c41f020380040f4031140100107082c505a000e0201d1070501080a10400031480c02203282422a070b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 34288917 1250 34287667 34287677
    0x60f04020a0504021201050a0b0408030f0d060e0907090f020c03030613020c01020d020c0d03050402090411040b090c0c0105090111040b0708042103110a020607030e01090305011d0715090501 83
    0x11a0310001e4031200d800d81001c1e07002440401c803004040b00c407008542c107c80c3d0646070907400039280d034500c175a80d02ca24050019560f004020720b40d100074a40c401000190041500003c80700d44440c00d4040d00300040c0c40040403640082000e1084e801240f15090141c030055504501c1c08030b0f140c00c030688a0200800042c4120010250036003690081e804503640492000001c5560707491201a4600a40000114007000e20800c0700000c8014020700c102c0c1c1c06180c00070700c5c2d0105603880c0c2d59030480001038170440542090715a441050300f07860300205107000d0211114115151040442c105003110340042800c034050381841e1303084036110101012502654150140d155a9400a080060841c07141d03901c946801c2e0028045101c80c501800c1c45000458460703924030f0200c1300c13507841e0700d503460400c81d01c0070354070941c10041c0b980003038018850030300342c0c5006040054600c0d40d00c1c1c80d100c3c01c41c7d0ba0307039180490902070702c1081820408140710b420080c01e030a0b048214400f0815400900e510350500400b41400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 34290167 1250 34288917 34288921
    0x6010e0301140901020a02071a030f09010908070308150a051c060b09101802030f0c0304060f0e031312080409180501060803040f090e0d030c110303040b0402011e02060f 74
    0x52000c2d041200200b01c2c0d54066003240c20101c0900b4001d511102e442c00c0140158180032507500ea140903c0c40d101480840c80a003144c031006090b0b09854005404904603658402d00300b000120440003a210715800b0303403a08110382c540f048004014204a9000d41e1048001c0c61082c131003580c0711040b002d5901100381700401d01492900e00400142248001c06600640d101d00300500b07444081010400c0e1241660118078944510390741c681079000030b80b21007102814000000f02c001c4540d002855000d80a00400300e81100c03410102011a0189284500d09800006003943e44d080305074655401003002000083c282c00142d1184060b41c007441c0920249140c480844003c104400c01956800725000700c020020303d503850910035a26030007441410031600c03d090002402c05442c0c8a81042d0b2585500034040ca180700401c01c60003400c002d0014001e001240d401019401420000b0318450f51103003404c0911414603000141800510309098440c90181d00901c00c030b007030f5002c15a1600a490807901030165 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 34291417 1250 34290167 34290169
    0xf0b0606070204110301170304060e040908190309060501050121091a0c0d050a0c0e1002120c0c040b0409050d0c0503091302030a0b030106060f14040902030403080103060506030a020906010e 83
    0xa10541e840654032904000321194000b0b0540e00850480320350081c0070321a40000d03407107251a40110b204041c0821014003040d1201e04140c1c000414070b6100c0e0744c44503d000980401e000030407040d004041300003540e47c05021f080207820311070305001d84000d08080d0303000e010541007000007003d8420f0760100962a05141c60801800b1201e40281404000540303006d071500154850380c54009190001040c0c4c03c201c00704960810038890b40c4181101d590712012440b80312804d1003a074200802c8076a045100320060320080c0c001c48405020440c6060005d0100000490100010349810a8516210310b151941d40000200001070202c00000c0a0511250310b0b107450070514154004c410b0b086800c074034102007080c4220402c2c0d009501c55070280c1410080003080405250032204680a503a0202e244000d103020344901520f840d0712079403605a081403820b900d58400100b07130b0300b00755011000304990304010b10400140e40a07184d071180342923000307088030a020740018002c245c014000e0f60510210396144682 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 34292667 1250 34291417 34291429
    0x412050708070303120b040b0609060304141c09090203010e16090e0f010305010507020d0807110109050a0609052104030b040302030c0616020c040615050c030408060a090314070f0b06 80
    0x1c05210041e40d009076030324140074000aa1203104841c07481e00d09604a9070a180c60710034000031040103400c0ca420311000c941401035a610150080e2611131400c07a0580384038004104481d0740500b6000250a41a94040702034551441c0b500142034140c01440140309460120b042039038001c0081340348d0f40d084400c184090f0360908664101d42848040c4000f00601300c04540c2086040340c0c4184000c00450340c0c2c0c1501240c445288504190000e00e103000820426031042d081200034000207400000e002419a42d25460b0501414040300c07a1511050f107503091145c107100007202d030052448800e15100d41e1208204540c815404001c20754001c0202040505200304103681400500380708071052401c202800304003200000c1c59070310051081036050149410540944012203450001100500c00384e14420b42c0d071900a44104070951000f44400940e0140802c00103005049041001900c03c03407a05000744a115006034a0710014010404400000c140040800303100b03410020030803540d140e94001400c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 34293917 1250 34292667 34292669
    0x607060b130c030213050609010e060306041d0a03021912050f04120506100909080315030a020604090501051512040b22110405060103051b030403090f060302071104060b04120507 78
    0x2040616101e416030420f6016801028464019a80421131030354a03010130245200e0f0701d01c15400285289036030303002410002c0c0030f15040a80200049000404102108030714211078101c8a40e503400304141809250b01070000341d4030103031440f1080446512503210380c400c00010039084001c20500040c41352014a541060714043c1004801d803004641403820035650381c0d6801d4420a80d441c5486100242400300d500c90304c601e09911084d42415a6260300c908141d40c100120001c0c4c2501642030070074016a1084000c0c0060800c42000058a50500b02400303090860b0007203490060108209803000e8145138844113500c20740c00001e0385100d0f580c890000c0d580030342c08508600c603413560b07803580020002c110004414909055800308070a50760f500044080d2030007540c40c40b4041115810143c500d0080708020b5074003030f0007402c140500d150744465045d49203016901c0000082c0d4085074604c2001040e40b100d00c4803100440b01071025034201365030a1064402d600c55941c800e402c11020208100040c41480 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 34295167 1250 34293917 34293949
    0x4050c0d05010c030c2303060406031a150a060c1202010b040c03020a0e0d1a1503070906030218010303050a03021b01090308010302120706020d0f0507020306010821090607060b 77
    0x40034680c9140352140c0039250703403141580440e080101500d0280c0c8030f1003e00400c0416400101c855484088401a240d40050241b540160316540040081003c2c00055000920000c2e262400d9180c1031403184e5100c010029528842d140c0383d10104400d80d030145204450310f40040d0062001403e901060340108514003400f074100e400d00400d044242e030164041d142c0c80200703840700362100b2800e10400c0000c0c811004001e00c0305468424801d170340802d02c084c1550090900107001c960001711800a0b19040496011703400440d1903480034400c5041010000041000c400403035000c40d41140d0300034007940210505001050790100d5001c0081000940e40d186000040c80204889449030070700405100d024002a030203021411441c0e00540000603111044400b5a03000d00a0000060402c45091103613003800010000c0510407600582c1d0140116402441018010305030f6819100140c0640080d50020700440181400f40c0d445139240c610444080d03031741c000b0f000220b015441d000a448134403005505 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 34296417 1250 34295167 34295179
    0x6030c170730060f0503031b0a080301120c050d020f040c0203040302040906020307090f18020706060302040203090604050f0118140f030a0207030204060504061202040506030c060c0a020a05040c090e04050c 90
    0x100319400a221030b40d0002e0b800855051082c0d03503c9811202c240b032000d01c54943c00d58000c00c40d04c0390008414140789101c4a003503040d07d0061302e0544030381c01e25070400c0e0008410441103581d0303034080007000d0805100805040d03c8144603076140341c00080c610184981c07041d0007141c03203465242c0d80910074022078001e035074014004c201d4000c44ac20040c0080d0400c071007280100c0d007124004504680c03d160b5078421141c441c601e034128901640b51401c0690410901100d0107502c98201100581d21070000e14030401c4054000c10741458641030182c03070325103032101c412911792405501300395034003140703981d00503103078025031102a8000e0380c1011381d260118401c0c100714540008911200b22a5000c02d007017044900071030b8240f003d03546441c00c02044070f030341d0322981103000110a0035100600f465004681e2140c4024155040881d03c2d001043c0ca6070700000c1c00740c109800282c1e000c401c40c5022075008004c1d02094904200c0da2000c2c8001034008001801881803454000d000142004020050030501d800c01402c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 34297667 1250 34296417 34296467
    0xe19080d09030b060603010503060403030f020f07050d081008120c1006080708070806071b03020a050102030106050702040f0b09041e02030a0b010501030f0e0715140f07050706030c1707 81
    0xc01810601280400c6400c0d0714a42c010640078076000003521b041c0c802c020090012611299400e8006080415950601903000d00c0000394400044000d410724a000d2009020080316045004222030002001c16407007994800c4c00b07004a00c0e000589480156222200701d40d1030540200e02403400e540d00c00f04c50811030420b240401c01403000b24403042140ea82c40201e40301607403200c1605444500c04c50313191002a40e8983c84c0002c0106101200d40c40a01900586040d120303161109401da074400d8100401007003001a00c407046041601c249500240000ba081090b010780000056038004003410280040749416940941e00aa503048185265401400c0781d1842041c0d161080c00e0310720902c1140d0110349000300b43c00110081c1d0103480e80841d040340c06003441a0030314070b00641e81d80030040924100010841d07005409a020301c02840300c5241418070039101c00c0300e441c1141c03a02c8803a800400c101800d107079885400729044110080510304030b0081e0348059035056011607902607251410b458401000d01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 34298917 1250 34297667 34297693
    0x30507020105011a0c10061d1503030d0b0d0c03030216051c03050307050c0a0f060c0507020a15020f0102040e04120f0806060f0702060d0509010b03070f03021002071e0f0509070e1908 80
    0x102582c220f03105180c1200440c2c0e2803a005270000c607911020980c05030820850500b903200d01d17a001111582c0000d20080b4904019128040a2a21a002200964001d440d04000e00e14184c2d0901e0003000308550320741c1501c9841d07001d110811810200101804000b10100d8469401001600c50a0328100100d4215042604204801c00c4001005540c0720303103010805031009108104a511780d540141005c1503142c0b0780129040f41c48003000303030704046000d40d45003420040820f00082c4020010b99042c3d42c06801d250410940d41032a05440005000c0c41880c0200074580080e5100c0d0701000c00c0320299214010b200100686110348070000354800400125011030004a40c459030040b00c851008125040291060503620000e500640717807030400d11a420001032420210f020664407843c410789070f1150740c826034611602c200d5100100f1250140405014580c07160032880c0041c0000c49094490b420300740750280c10000c4400d81c01c0d00414a4034003100040206108030303c020142c02c011550b5501d0740e04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 34300167 1250 34298917 34298939
    0x30307051609060b0315040b03250603050f010e0907030b04080a17010501020a060216050718110909011211060d0906050604020c0d0804060608030307050a030507020105011a0c1006 79
    0x104841e01d8050940c08214003080d03229150030741c1d02e1040d0192568075403005107812041c1e040000303903015894481210603902c0601c000d80804004180026021540285440200032107801075420545001c00704241300282c000303264111501c0c01101e071510b0311000c80352410000030350405440f0040c000140700401c4001c2c002007904c2800380c2d07118210070000c000700c0214202c00b841060b0050340700082c11030100d841d5600429034000703100b1701c4c0d00001d07495540d02030800032180c0c001d45851702c040644001c444030358010300d907414a00310710040c5031440700c200207520540180616050901745419180c00c1014600c008000188001c10b000d80fa034100c1031980001d001d019104550003400c004c0850311b9414a4020703a040e00e500d0001034406c00078004805c8807880801003056813005d03110b075000210110f003400118059445a60344603174030103070260040c0c00d8550181040045a00d8400108000c0d1a4840c11150403d14848501d07a2082080c0e040d515144400d50505115032521000040829480b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 34301417 1250 34300167 34300183
    0x510020f0115080f010e030d1509110406110a0201080c0c01090c0e060301060609081002090a0e070e120a0c03080a030b09010f09051f0306051003060509070602070b090307210203030705 81
    0x700c0c013116121850b441c215402e80d040d50560f16040c2d8000d102d840103560690b000240340780c16000c0c0a10b501699030700c02a0540315080d06003851b19400240901a2035070041c845070442260b6001400c0242180d030008240010081884101d5480819801d018040a4000034401900254000c149a464010800c10b0500940b5203d00c0307586041c40025140d80110025800c854014025000c00258424a003010b50b001101e4154480042e520204045e0380c403021540c000c00d42079031640603104101c030501c0044100b0030344100e0a5880144c038035001902c03c1007404140c0b5804440c00b9110b036401c880a4002d0040298036607400081c00c400030651600040c90301c8101c0320b90315002d01040e15045081d1201034003801c00e444004040031003c0c00499059040b150300801e203910000c44c40c950342c0d01d6800864200340e512000302e80011404005582d41003061201600d201c000070741c40d0100d41d0300025910015031052071040d2009144240d402c2d0ba01c5542024455000b40a60383c1da0300c400e01c4c0040d241c2c0d041c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 34302667 1250 34301417 34301429
    0x1030b09090718090b010e090a0c0303031505040e0307030e03011506170a0510090e030918040c140f0f0a0506121605190c020301110d02090405060f0108010510020f0115 74
    0x118604104a03c542401104141900640c040c5526400c180c1c0c0c8101e00c11006210602e10300c221040100001c2c420380c6084025406958006092020b60643c000401003d520483c840d80c10800d04024142011040780c3c4807540c0f508003101500012000300f405440c1030000d00c0100c441c540c200103402a00103000130781144401680c132003a5654502d03880101d60b01a85c065240c8040c03a041444024100e9000b1946c40c1d401c42c044a080c00703402c0e400200a921504035901c2101c50b090144010011603c9030b0001900c05000004502e0340302001041c2400800c07180503200d502c414000c2c1c00e0399240d14800002505014080d03980c2da010904166a00903401d4840000c1e1b041091080c60b28144203005491040d240c2e032a071102d803401c0512040320000491030080e0b030f26540e210501c281030380002c0014801800d4004000da01c913464a0104011540d0052070640503030303008601d01c55160b0380314501c0e0f03042d0740b0121030b41d40302d00b1043e0004030303e0200c50a004840c650310f070032511f40c11461100035000031541 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 34303917 1250 34302667 34302689
    0x1804150608010b040e0106030c030206031806011212080103080d090204090f05010b010f0f0923030604050c01170f130c030813050a050607021e04020c0111030108010c08010803070204050601030b090907 88
    0x40c17030044171801c136000c0e0310000d040000d509105100514010000f0340d0489032a08071029094240205981440c0c000e904c00107001d036a10700b0120402803240d44440149240782840c01c0c6562440d2149005c0d0301c203a605080740b59a40c0c1c21140300310358542e03200d0340059400c010404101070381440c009008108422070070380400d20303005001c1005c900c00d880070324003261541c0e01e515003945044d0982e01c0080a041518001030180003403071040e901c08200d0141308a00031401000500e55020014110840182d441d000381c2807403a0402c901c1c8001e130700307050307412080b06070100104444c10b0400c10500c05040d0002846080b0005a0803d210b41341403603141503038001ca5000854559810030405148600000250400c2002040f5841e10010030105a41510041c00c0546030084856001e03007121404c2084c2c031400400800107006000c024070a00c420740c005803d0000140d41030614240e503a020f81c44d0020301c187e031114006a0079910076001180c00c1c00700a0f11013407040c10405819600c0c0d641300e0248103001c1c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 34305167 1250 34303917 34303931
    0xd0209090624030c0c0d0c06200301170a0b010e060315060306070324060809010b01020f0a0605070c0b0c0702100f09030b040f0b0103150b010302091804150608010b04 73
    0x46440080b00e1103140140c0e603054502079152201011580004006802ca0001401000b10130312007030001040510480c1d40d002e2808801e860107000703c032451001d241444034111414100c08407050b00301c90540c0e03858600c00f007920400050b20f07840c08481c540024138842c220000014107032007a61000e07014005c214259280c0c0f1030102021032070410222852640b517800600400d048600940c07000000400012800c80400c08188100c1c49141c620b6226000154500082048120302032007410b007040c070300340701402906080a400341d07503900d2200000303440e503036a40b404070380350354025100911059841410b1a245280c81180c009040e00007085c16401603030710010802d00036210303100c4241c150426880c0c1a000a007142c845100310300008008072108010100e4410104040c503c54030b00861003481c01c00c03080d0a04104807400e40d03041c801242e06050044c07000000a0f500c100d18210f14440c0718840c20b080e80d8440c00c080001001c1c0c030824121903403424001050588041d000f81d26403400c1560140070407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 34306417 1250 34305167 34305169
    0x10f06050a05040504150b0c0c01030506030606030703080c0f070906090507090b0d020f040b07050d020d0206060102030406030c0c1a090d09080a08030403021510030b01050925030207080d02090906 86
    0x584500d407444400240304120900451506030f000030b480311429560070030899111501c2e80050b50000704820b407a580310810400496902d03004465101105a002e01194103104010035a02c18045c04002c14080011a1200800c20300300001c3e1581ca8264007281c2c0c0d11640c40304034000408a0740140240c0350b003003030006609240952005e000711110070550910780307803250310503e00070b401144000185501c10400024440d6010002c0e204440c0544007401d43c02c040d10b030000e880c040c0c074828403100355080035040000a03038000c820380e0100c500c41d04000c01c507800741202c1261603144200c0014001290080c00712031062034103440c0c41c0700e052080708132144c40501c10020b49450703925206a131081d0b4005480c2c07030001001740c0c1c013a603006842401110408502c2d400450030300c0c40c2c1280c07150003a03940d00d00100188621911020f00500c400d441841a070700740040d07481c06a01303801401054442824280c150028403d604540d241030b008600070746c8502078209048040c1d80518103040c4581e09400c08a00760b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 34307667 1250 34306417 34306427
    0xa060806010c021e1908010c082401031407120c0c020307050d06021b0f2a010f050906130f08010c021009020414091509010c09050f0607120503010f06 66
    0x585050316981c00300060303542000a41a980505040341c050a516218a03a817580f0314600c0b20036180c4200d1040d918101041d00d800c6850004d8081c04001034041404481c2401d5420500d4507108a008034003111210030051b405801102c848035100c1070014104084d09a10001822100c0560300040c0406491040c0031514054000320113507154005100810552521903410314001e807140c0c0000d030030102d00380200c20090f0900043c0003107680241c0440d4800c0741040c010310325800d820140c80c40307a268202060040004880c88100d0501500d1a03414600c0744c0104165401280002c020a82c0d400b00d403c001081c140b2079204001603020310f940e000c41c00384c00c180103603a10740480341d008010003050355401d0009800d4408080e0b801c15950b91004020500003059907201d80d050750010b03d60000c4000c0c100c501100014103440c81e9926180114072038aa22102d001c003102c00490740c0070510200c0c10000341d41440340e158010104d000c52400d091086800c800910b04075620084105183c40e580c40041c0c1e4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 34308917 1250 34307667 34307671
    0x4050a12020306160f110c0301060b0a030e0703080702060c070504020d0903080c030c0f030c04050d030c030f030509100905100203040b1605040308031603140c13080106050a0902071a01030c03020a0608 88
    0x7144a0004059560384510000c10411b07a10034106c0d25025800c10100b400c54006400100054000090b4007400a8150040954000712540200b4500d0310b1a20303081410f000b4000000e108460001e5030494465042185401030203004002310740e074042d0801e81c1802030058200450214094000144001360000c043d68482c00c0d0001e0b88618050728490211840d82c00141001041039007030202140d0b50703d41c1645c02c8103061081e11000016009810081d009010400441003003608190802580c9440410344107500b032000c0e40082615100b80c5405420180d8510b0001246440401044144580d07589501c3c045c1c820307600b03a0a1940794055044425204600000d0b1140004201242c1c06182403800e10604602e00c1c540061509840d10007075021940c252000a2004004201e00b1840c0d003499031604003d00908000700416850580803552503a002e102d200700e030307903400b0401c1d00901110f90310820398100114500e200c07942c1c59103040b50301c02200780001e90003804c0c1f1490100e41039000f40038180c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 34310167 1250 34308917 34308961
    0x140103110a0e0102240f010e04200a0b070510060e0c03070804020d02090a0f1506170c04080703050708120306011b020112020a090513180605090304050a12020306 71
    0x180c0792540001c07040d680741001204083c11449002070110305080040400c0c01420800c0980c410f482c10b00400018407602d06030840102600003000b84800148154482d8010340b4024020860520a03c0001210050340717602440c040303100045c4820401c10081640e540b103043c9404108020f07074a428400c040c0500441715911900420004941c045000b090083e1380f052004000070007118040d400b01d40d9600059810816071521504600d015802078010f9607403010211302d40300ca40c94a017030320041c41400740e40701d04000e00c580034011a030004600d804a0b0040c0c105201100d10007582c1c0c0c9020740c0c1ea43c0551160700000d0084000700f861440b1054110b134052001603680c20700501070b034400009420015007080341400381d010741020440340d081c009407480b80e085481e522440c51800003840307035580204002000c4203241c050300030a00301015000090f41c4c0d401c000c001803642c0e90b40c82d4152561140303411203039105400250004165004541c946180c0303100f581621104c3c0c88a410380c61442160407000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 34311417 1250 34310167 34310201
    0x10110304060f020910020309040b0f01021e0102070515070201060603090803010509090a1e03020f0a08250204060e060f1005160501060909030806120606060a03020c010e0601090501140103 82
    0x10a010039442c0e00b01428601e5403810061400d01c00c440024140800010321002503000840c0b11002c40ca0300e4420018105002d40d0629044590680000c3d00c1c1d113400c450b110f00032140652000e000c44800d5050740c49031540801126414030309488400e500382d4080700c03204015030800c0404221f080c484c2c056500702c80e622154490841c2d083c0810401146e40003422031010f4400c00280c000810f160703042d00c0c1c3c5111b070407407841d0011440d14103000b030505000c03244100c07081c1e100098240019121400b1295100c21032500600721441000848150004200c00039500504000001c81d490b0b0b040d1100754007070141181c52006a940500c144001e0381c043e1206e50000c038000340031082c0c142c90180740d4003813820701c00d40c00050410b4407044110103d50f5029401c0d0b00103102e400401c1650b041c113010022810442800130038003440c00c88006842c51080d8018a02090340100b0140200c10094111054160b00c1401f9185a90303140c6000710001d18091107603810801040d02040225402440b854088080e0309600c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 34312667 1250 34311417 34311421
    0xf08010608030910050d061502010605090f07080402060c0703050724080708150406030b010510050c06010b070f140a02011d090c03060d0b010303110706030b090f100f090905101103 79
    0x100130008505031500018884200005240c2c459580700390000b0f003020095440507080800c4000b42110265045980100030500502140c011a1400c050388003420307180224580e039030b03480450014054220268028491400080100303c80450071006494401d003034030b007030700380d06819024100d10000e02e8000441c44182c0030a00e024412001c0560084040e44101e400e007000d040400c045070500e03401a40c8840e03003280140058600b551074020307a0340385d81c40d001c0c3c2000c124005290301d504040c46840011000020500704204005950069207074004d030a02001e01101c0000580f110b00490040740001c012140441c01e05d01c041c83d440000d603402520700c2d13516a40308044a003880d40043c10f000e03401024040c80c00c1c0010340d00522240030350310031360310b9007a5401c03440e000c0c602e0210580c102c1c105150600d0501700d81038a0780c02c030107580851120203040c243d80720010601c0c40082a5000030307251504182010900058035003103051302c148075008030f0700c1d5040191980c3d022683d91080c01c00c0d0b10707036003080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 34313917 1250 34312667 34312669
    0x705121c0b0102010e16140612070f030f020c1f051e040212120a03180f06020307030b04060b0408070f06090b0c01150e0105030f0a020319050c190f080106080309 71
    0x400a8950301040c0000541881c02c58945442c020015551b158000c1e03410b201030011000601f903800c58490150342642c240b00450b80c4054802c00010039060401c0709213480d010b07000c0d100381c00c01100307158550720841d41c1c2c840c41c03003401e43c80f401690200794040c2c2c094803a41d84000494403a0030311940228400c5030505a464a45402102d000b0f401682c1c04989a13004101100050012590200082c40308554419407a00701030140c4140c0441200340f0401581c401010619581c00800e20603400000140c1d03955428406400170451030b11955003061900703030041a00303000350008205071041d000440300ca40340c3e91028642400381a0080302e00081c419901044090201d10282844010345c0f000418010000441d081183c44164048442e010a0b43d00401c65400c0070f110710f44245e00840702070090009075402290303071000e545902e48124800e03140c8170001d018040c404601c1d072840c010700361030449251254031100d0b82d046001d00310b10209440310005d00b605052007030f4002c0700c1c540d00140d410500b00d90 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 34315167 1250 34313917 34313921
    0x108150901060f02070b03070207061209051002030406020d0606080915041122020c03030703060905070c08090406090e100501050102070f03021e0316060e0102010207150207030203070b0c0705121c 86
    0x1610083c01d500c40c9883c0800d9140c10000a9441200d10368000d050043c58640000c041083c45002441241e1411080740c0200c0c5000c41c2c40031000d81008400350382c0b40c03654030b0648000c1c41503403045403003075103400000306001c0d0380010114000c10113041110946182ca50711781d1803900066800408030407a400048a5074100704100c00131000c021502c07040005448405503059074082c21403151550400801c00106541601c070b5500540301b105030401040c075021f40040d200c240e080e00c002c0d05003000030811610030b03521a0048009030480750014000c3c41e10001c000b07a510a0200e000a50716800c20b00041119440050040111000c02c100d040e107a40c070b10340903c4403200003004654161945585411010780f070401c06c02c030242d612420210302451500c50010075103402000c2440c111390041180f0000300321000c80e5060816454600180d8402c1c2600c4d05901d50310505d8801002d00311140c2c20080c49142d2172014009190041d030a40340c00d6041c41d40300144ea03201c1e800081c0280d48881d520503900000319 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 34316417 1250 34315167 34315187
    0x10e090a0b12060708090613050d11030f040902181f05090402070b0103080a110d050403170c12030103050705030d2007050a081b03060907120f0204050a050402010815090106 76
    0x15203080d0404005082c62400c040003143c442e4003141c51030302804060780e0300700328207030380300303040040040d0041402d035280da440b41e140381c0802c810030090101d881102c840520445185400030112156a245c0d50800c0002079040056545a6402e200042c00040c2c20560a0070409140300c440080c51030040c08420b441a42011382c166410aa003440007200060b56820b006001c3c0d801251610749800d0140402022500940800d6406030012031101070b02c0b13a009425182560b500082c0100b0981d11160740d900350b0700403242c52081500c1110340540305000c40c03c008506880c01007041e43c1c540340d110402c0c1344d520301d018400580011413841220002e0700d840039601446501c0b200035545c0c601c0d61070001a80c0711760617030030480b441e070070005e91405c0c07080086001042c2d00c001a0040d02035450f183e2403c1d070311100e540c4906400902586001c0040092400c0707140002a0300a00800c054200b03103101000820040390120f000c140450701003106041803031300e05602c0c10001000403645a00340401200c0320020b03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 34317667 1250 34316417 34316419
    0x70501021b030c011b0b04080d0f06050919090602120403090605130902180301060806091905060105090c0c010c030207030e092a0c100c1e02030f0f04080d1706010e090a0b 75
    0xb00c54000b07240b040f101030040c8c0c007030f16406488804000e13540c8200ca45031010907800501d0011f04100941b030740303010b16901461460380d04150220801d07001c40075021000004194910000701100111596061180214042d0761540c0855031101401c0d5200d20414454095400610404000194058004142d003441e40d07405008400102c00100c6d0a540355508012301c2c5402503410410181020840d4022000d01c01017003440404c5141c0b141601c800043c0149030103204001c00081e114080d2404848008200340001c02c00b1841c900c0b401402034110400480c002105c41c4084c404a2815511480c0079103016500d085810380c042c9080901c408403218000c001c40300902610b01e4a090901040b40c58480c1c1040100b02401b01107401072280720041e800c10f0764a1900b4100d00441c81e80001a15449012501501e40d100445201c40503036005030b038415007030341c0718164400300103c1e882403500c007907015007140d11341d01921840700542d1030606480c40c01d0b42004a000015002da030311a0841030a400c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 34318917 1250 34317667 34317707
    0x50606060315100309020108100308030f06061b0601050a15050a121e0e0c04050106120f090210021c0521060a03020d05030a0908030f0306040504020f04020309070501021b030c01 78
    0xd42d41c0c0464000c011400220340800d5941e16200250f50300a480c03181d00001a0b03902d421544d00310341d6418180d02028040e5440c1e00601400100d1907164101202d1020240d5400b00110301401c488080d5034500901889000300d002140000b9000224042800e0240090716501e040c0b00f11010300300c8085059056103c0b1194503440c84d602070100c2c0b0710b100700b0004500c3d0000300704544112800307860440b00c2c4141d00c2c001c0d49050010030ac3e0301da0004180510548402e0081440d034100d800e644090044034030081e500c490800320607074020740c0000d00341240303800910070110220341504003540d1a02403107032449800c9050303d9105603080441400b840c1c1c003890040c103074140300344c0700e802042d25100d50328004c8070554000110412102e802c20400c90040a03c2c0c40214a003041d91480320100313020141400d8011510b40e0040707000c65848500c01040b585011300115140e01c0c06c11110740d82d9014500c1418054000e41e0b0852000703d00250000b0701c4080c1c080c000f8035008200d000112540042000000c601c42 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 34320167 1250 34318917 34318951
    0xd0f0c0b0703092103240501120b0406090e0c010c0c060f120218010810050d0b150405040302100e07030b1b070804030b040611120403051803071205060609040506060603 74
    0x15182e8101c200d0fa010100c1480c40c04d0018094015080340c50020701c40e00300340a00b2001e90030100020740d10405a900a01e403a5003480740300310f9188064001244a40d5000d0708000b030109441c3e40e590302c001c1695030700000700c5000c1c0001d0001074803c7c081e0040081e114a414000078850240640f0110305104d41602d852264400741d480460102e07081102d6400c1d8400580455840310b60340b03c03240781d0700014040d04540c070040c0780000150718918411401481c03440304030009110600f4641880f109020080d1040c441c80c601803030300035260901c204410844501d04826800000000583c0300107903030b80500304410325103401200d051589200b186d000144801088528001400540600003d40c419007002c500d50400e4903245042d600288a80103402c4c00a0252180046280c00780641140d01410280c0d0707076205030200c02e0070fc10002c0850941500c92584000b80301c903a06040c0b59806402981a22000d868003010048803c2c0242c40c007030140e034420800b146046c41c040005507000744070500005014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 34321417 1250 34320167 34320173
    0x504020306161b0b07090806010e01120c0b12091006050d150e0a0609030801050d02010c060c020c060f0715020c101a10020303100b0c0304090906090602031003050d0f0c0b070309 78
    0x40a9854084813071031004403d0081d05074004c4904030141140802800305036040002d130040203001486550700a20b00c0c0d0050505009602c0c54060140000103811540e400e1080d22410a221055800c1031007849050045084c2589a00c82d01c801e80d00001d200208110325a00e900da207040c0d16401100c840741c5c1d64003c8051244007003003580e4400b4030409002c2025400d90501404902059100d07031701810140c0300020050780d0007403400070480e91100000800301c0d11104200e24020204550b103400c02d0700002c2c114003603c0050058070085100b03e00200100000882d102d043c1d002d00c0d8850840c0780d0058807410f8000710070f50081c1101e42210b03540c1c80701c0040b5280001d03099501c901d20580142c2c00010030b200d54042d2228600004c4d164251103d40307000a041300f40c41c2c4d00e1246100e04107080da42e451204081000c1508035040f80e58004c5410f640324203000d080204205003d11003103645100c1c4101c00c402050242038081c0c0c1982490f25010f42680403521480d03021440285050308160f40d440b510400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 34322667 1250 34321417 34321457
    0x60a06020708150c120117010f06060e010804050106050603010612050c090a05060f0c0303070801050f1002030f0903010908070602190801050a03020409050a02030f07051003060803041721070303060504050402030616 94
    0x3c07c020740380301c040d14211502950071641c40c081041c08580c1800d0040c0f00c499000101d410250200b07281c40640d40d9114103110f030042c00250486980550008000943c01e50301c20a6012240d0300744104011a466001c01d005040c46419651600494010800c01051600000bc0c3c0700035000420303158a85007207150714074219481143d02c0d20129000100600003400d0060149200c2038095402c4106d01d4400403000e581d038010a041c2656030000091541c08986003900007410890f400103219407100d01030b15001c4040d402c00c1035500e07044290f8512210045104030356490403981c020307203103881550440c3c0234403024044606055400b44a54207000300182c5042080310080c03a102c4e00501900e9081504200e19a80720410032000c25050000c14041c000c00402224220703281c0b000c00841944030025840d0030080f4507200c81442c500c070794003e80032100305500185620340c4a030380c082010036180c0042108449003940c000e0b4041c2d000d10f0028288600c00d002800009441d0305126211082029a0143d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 34323917 1250 34322667 34322669
    0x60f011704150506010234120b0f07020a0804060507060902060315010801120c0e060f10020606090705070f030c1e030e0301050c0306090c0702150d05060a06020708150c1201 76
    0x414107201070035840b50031220f01c42c42d40c000c1d0f000d2010707110f07942c2000f041c0b40300389255200506407d996a40c80c4000c0207503290644004003a81c1c034601c1d05032103d500f010303c615a8119545801d5a05a00001e80c0c5030784049034000c1615440b403c5d96041908113a01100c03d41c01c01c0ca01101e503c1e94030440380001d40c0d1580d02079881703a80714035102a810400c5900041500a040c0d204103240d01501d14904005a00d04050009513952001e80181640c1c46100007400c1c4402d1100540d000311620040741d000d184d000c105a03210704410354484c00c080c1ca440c1421074247c0318100d400b50040380140c0404e00001d01c1603103080c2001d405111034403880c000c420717065a030140106000724003099019500f01018202070080b160b0103018103020600b07603e80030020031080e100003030140843c260f00040071001c541d41c105401c050070410213026611030101d06101e800824041c0d840c24862420700500142d600e200080d100165180500130344100ea03000381e02c1554250001d010707562018024025803851100807a00c00c0c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 34325167 1250 34323917 34323923
    0x7120e03090103060501020303060d0b042604091407121d070b04050301060b03130807060212010e01180c1b0804030602030a0c090b0906041503020903060f0106030606020c09060f011704 81
    0x60350750341c01c00c0015040b640940c0c0528150b41050080104940c0c0d521403039000550455004c400e40e03076031071074842002d1180030f610300c070b007842c200c11101c12100094000c3d2064480c40782c410001c14560000801e031003034045178480e00140701404200001d44040e0031910742d03040c081d40720124054100ca00f16081031480c2c0c02c4ac00c9001c10101d0108101c1c5001d000303220040403800516841c40c1005421411901c040000143c21200d000460030104910f0b07a04450040300841d980320101c0d6140c021103001c0880170701c00d0b0164503800c25040ca9200c0440e1140c0d00007103000b0344980c03101311512680b4405c8426802010760b116402808001701003205070004620901c2c40d4000050700000300c440c058480ca00c01e03000224408810f0050324101e4503444115402e4030355112003121404038061046020b4821110a503416000314400c0c0190303100361070310309816200306441c203120f515102c3c078049968511003aa00790744072541c4804101c5900301400c40200d040418903000b882a8903910314841201c406403021 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 34326417 1250 34325167 34325173
    0xb0306120a0f061a0603010b1917040501060302090f0709090b0609040203010915171209040e0102070302010501060f020c0108060d020a08030309061506040e0402090a020c1b090a0c0503040b07120e 86
    0x300c4154a040300c40c16040c0700f405c071a02415941010a505098001c070309500d44155070241d9006144c170300a81050502c5e40100840b880c140ca0145081da0207003520b440200d00404031180070801c0c44681c0e400e014420f041075550996881e240c90152009050803045e4141c024100b01702c1c507900780e20b5500040d80603021003640425500740b10702c2d80020a900ca9402908051350070049038030005400302d05440005504000b05458503d01400074004150491403821075610014400e4100f6406401041c1250070646503200110b441c100240d0322000d889800b240041c201d000000d5842c030300011050307942400944000d5205403034065091841c2c1c401c1d035520000342c0c802c20802c68814a481194a0f00d10000d903402410240f038072403529030200b4080c1c030091150701e441c030000c2c01d4102e003a4140c8407140050000c81c5d02c0565101414441ca102c008034441c040c50f0200d002485002003809001400141c40d9a12441c0da41c07962038000205e0700c090031b05010004900880340040c038071801442455090000a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 34327667 1250 34326417 34326431
    0xa05010203150f030307140c04020703020a03080604020408100e0307050f0714060a14070f08130f0b040305070302010807030608070e010503060717190212100302090a060b0306120a0f06 81
    0x1154003101c100590503100340742c0c0780712075015130300c0c0401039425071603220600544098500b0381480c01d00131200151f40d0000c1c80803400c1400d06d42d00080440c03244d4002d8482e00040d031910001e0000740d00c06c1c0e000d181070701c0c0d10103452141d501d0a203a1101000c54120001c0d20308042966072501d00301030201e4100207607070340010b40c140906888008040840a411240c01d480c001c0901e0001d041c01c0c0f241c0102681d1080082001c60620100d10b201c0f4501a500c80034141e0f84041d101840c4004000074000c00181c80c0d0140310104951003203030200c80969030018010f28015146070300444408030001c01040c00c02d038403060001401d41c020000c00001c0c0003d81690f1240d903040c007007403620b40740009102404101c4510f1070290500d18910855801102644201020300005a8108007a12070329050b004540303048410489d84291500306075003604d2007101d50000b151922640042507840c0303401190410001040810010315020038040c03581c59040e03059850b600e5040e240c44030000720101c0c00f980d4064407014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 34328917 1250 34327667 34327681
    0x8030a0608061e150d05010f151703070813170309010e010807170a061a03041b0303080a0b0411031302010305060409080306310e0705060414130e0a05010203 69
    0x200750ba0200610b00c0c408011043d11007003114100c0702800141080f02c926940c410281c4a10304130094030781d0464001d0001e5a203190790700c030042007846070200c0381c80680c0d000480d40030b4501c11000c03110f80c41d541c01581000700f41d445140c0f8603402000c02c2d0004180418000400b40f11001e10125490b600380060360711216520009008014100e41c0c00d410024202c041041c8a60020101151458103810524a0340e42e0300000d0002002980c1081881c81d04031100c4456242d0128025482036110f03601c0d1010400c680e65036805481140e00000300864807644c00240f02071000d50080e204100010404a20070684140c4c2441ca60300c1910046800803a010280040d960503000c0e01e83c000a003580d00300b0103034070542c9a035003080c0000340a40c0e106102240c1403034042c0080d01c08403404803a41c040c02071208403201c00c030307175000b0000c4401d003074098060507100041c98070300318080e2004c4510543c1c03400203203a0040d00700060540308820b550800b070750b9100c15540043c010408801d8452282c2c00041e62420700725 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 34330167 1250 34328917 34328923
    0x120a030210021204030f1103070f05071a0301060e06090a08010f0e19030318060e030d050c040509040204020c0a05010501120506010801060305150406110a08190b0102120a0c08030a0608 81
    0x525005141d42c010403a07206001c0e000400180e000b0341514101c0d50282400c4e0301220300c402c0c2054107010611001c038028003407180d85140d400c002e600c9881142c82a554400000c11601036110075242d130103000380010081180240d480c400014001400545483c00080004e45290403e400c81001a07640d0b40c0741c074001c150381d0f201740d40da00080040280048545000c12612101c00c0c18002401c140e2503044001ca0012510074005d030044e4465024415100818031480d41d03600440d548803101707400c06012408110003e02150103558000d012000c40756074540901010b940030000f02d42507481a0f04c00e80c00410b000388949401b0f0318010301c41002c180c502d414520701d002c50603006440f980c0d02d4940104006400000e1440c0700d10311980145070203070780c1d0b82007120047c500600c1001c01082c0009141100603484801144210a82481d04030485803001d0820100c503000102640940e01010302041c0d9010410060081201e182c604240030220a80e00c80f41c0942003554041c40d0240c4804040c48000028 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 34331417 1250 34330167 34330183
    0xf080115030b37020a080f0103020906010507081314030c01030e0a0308090f070603090209070f02060606030c04090204090608010b0303070c0e041e0b0603191505070e120a0302 77
    0xa1000001141191202e1601d524068001540248040600d84010184005203419981c8440074a40d60000c04040c9802075407100b1010000a82600001140d02510f40743c240c0c160382d00038040601c41e03600c2000545070f507800914180c1d0135002c00d00c2130a841c0c0d41e004001c3d00c0a0701c20220a501030041c01401c0c03500d4081d14030f220505050038902002d1040303000260a454058040c50490019110403100c1e5051911212489002e03008003070012076215056040b05010307e1081d15006010360360b0702811200105001c11100058111102264a43c905400515000132aa401a42c90950745841e584100d85c480e80c0445a401e07252082001042c4003841a50013901040c1c018500d0030729550760701400320009000318001a600030700420103020020f031500307034440000d051091401c0c0d464117000c014200129012803103881446c03210141032145070b0402d015a9840705513100159035191300c0d5400341c032005050804101024a880310159030307020054860a8000001d01440d540301d0400074148050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 34332667 1250 34331417 34331441
    0x30c05010e0a170703020319110f060106120c080402090403090807030b16020d05040b0f090409150b0a050f01030504050a020d030f03290103020c1e0c090603060f130807020603010f0801 81
    0x24041320340820380200440d22a0301800d0509001100c0082050b1071446840088103405d100d0300601c000c00b40000503031075050303440c0c949074000104030b0f010506099409132140000001d8503540400c0050030403a90142e0820320a0a0025079035858042407450704e1030f1075000780c81d03801d02c500c20700615000c0c2450000c8108060701c060a021407070400082d00d54810f622644005410000380c5840450130176040e5548184028000d005148841c14000c5401220340840951240740416928092030300060107422a00042c244801c09040340b00150014079000703100350303200d0090320799110069403803817811203200d84aa216056000c2c91314000034221620303603208607107004600f1009030f02000016000d41016209103030150740c2d20034095079035041007130560500755842211400707202d04c00b00100b007107041842c00340c030401303060368660b41050790710281510a090089428000302c3c000c403500c1c40144920501411a0364a00001036021507101d6009038002000389208010900c41c5a0081c02021074020f9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 34333917 1250 34332667 34332713
    0x1407021b0a0609050607030315060c02010e03011509020702030a05030d02071505040309030210120c110c0603010b071707080a120506011106070e0114040306050603060f01030f03030504030c05010e0a 87
    0x10034040007400e68805130059500c294004141002058401c3c1c0144900944611038402e915607207400c042c2104542c60700480c08540041d01d110f4440c10141f0444003003054415003c080b0626000d6498002d500c100420390f00360080412843c04500104000d19020f01d68042c0103039203080702d0600c0b130400681990742c020a54180300c140008030303510651803420b907070301205d40350340d2182010010345520b0948081e00d0105d50410601c00500303078001c40000c00244150ac161140400d140d400c0090a101c24064444610014404240451942c180a02e00c1012001d1134514050082d211950250001c3c2042d00003d00c01c44036082201c20382d4020241c01c1482800c2142c0207400b25801c01740c80304da00078118402c226450810492aa20802c1c0140701d1202c6038500c0c65843d5203070b003403040c0600300c1115440d01900c5401d011640c01203480809134100c80d084841c9a42d1580c02d40e4045014040141040e020000c3d2100369901165080c41144034415252000f49450300c45490f084420703c00d0580500f5182d2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 34335167 1250 34333917 34333919
    0x40807021206040f080a050702090f160203091309020a0b0f030412031802010e0418030201020d0c02060108120901020102040b0c0c040501060f0c0303050c04080d080a050a06051507061407021b0a 85
    0x349614444c1d4140542c000346060f1910f0240204a07468051070101039400401903080c02041c10411100d1401204c0703447c06006910030643d0240e0307036440b03416081c68110fa03402c0040d9500f81d01c01e91000d83c01501c01440c3c08074095480424810540103501c03040c10000c0000301340000c00549090070802440f003410140001c8226008164080216000190501002d001c1c81803040d500d0f0747c4503011411103428a804000740303a080090007034020a4000c40003e02d803811075001c9a00028000d41201c04088c0109150600c418110150340c01200081e815503409210104030550341c003001d02a8035030204002c10104020307004000503228182e10a400b40710340e803901194a20382c040c4c000c000321901400c01158030b80700c1d9000101c3c0b51142d03a00c608a68090039003403088066000030b081c1e024000a1100b4800d5850341401c3c1801c0760034a03c0786c1a48102e03801c00820b01008d0300c0b006080918041c04000504021181c00815203480403101c0b0001600003407100b08044085007041c0f0080d90040d6003040385a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 34336417 1250 34335167 34335173
    0x2010504020a05010c150203070201022502091906080304090b031603020a14010c060e0d0207060206060a03061119020619020408060c0f0708160b07020d020c01030c120504080702120604 81
    0x107070700c2c24010381e810401e01803200000d2001842c1d0110303c0301000c580c115643c1c40c01b200000d000350000c040340c1c01208200700d080119802405140f03103609400400c01c0b071480d115840030080e0304070384045020401c2e4681000003140e41d001d001a000400142601140b16480342c000c140c1045030105006d84c481c000703168180096201c050340c030702c1950200d0040780180c0d148a030040c1c5080d00720a000612250912400c0018128082080900034506408850107241c55080c2642c230f664044035647d400a031501400c00110f03460307401a960184940e00d060b031428125102007207180306c03600500d07409a8000c01c18880b2014910704489561001c1100460906041000d40c1e900d515001c0e020300d40260f03000c2084010344580504480c0001d038032022070340d0340e50380007800b030505404030040c144d5426a40c0c0f400611710a0000c910b8000b224040d80c044d08500752101c0054008000c00e110060801440060801d02e44440d4440c0d24000c0d40504200b0303031a90014410030540294000080d21076420043c280800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 34337667 1250 34336417 34336429
    0x30c05160602180d060209030106050a030b040305031314061911190311070606090506011106070804050304050d2109050109060c020f0405040b070822031101020f0301061107060201050402 82
    0x10990020700581d582c5807000b98002c03140004150554401030ba0913212003000910b90013020640801d8000740901a41c40b01042003880c001d210140c500c9e5101e40004002910510003584d000300700c40220f00508a0b00d0b10380f4000b59a00d4003841e01254010014400710703141055520f501c90320751110501070100030034a80341d01c40c0131b140b010b02c1c8404911088801040e001e5041000e003c1401d0340c1ea1a1107040906106000c1c0c07809114000c80549003c0c08208076501c11480040c107410000c0080410307485210301114150402003058419000c1130101081d142d0307800344100855400b640301840340e00c4c0404100d00c00c0c40c0710708500a040c402402010045641c21040c2035007210a14100245180300d039002145400d07a0001089034090314080c1003008001460750058011a5541d41d07020580c5d560004001d410000f00c1d44202c2045085215000003c1c4140c80407400500040005424441c1c54840b08455030401c0c0c00400c0815440c2c035080440d00d4080240e4802031009200a102e181032a4000c1a4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 34338917 1250 34337667 34337707
    0xe060f0405100b13170a08160606150c030206060a06090303120b03030d1b1107090e100207060c020d050319020d1503050d0908030903060a020702010908120a030c05 72
    0x8069901d0320005504000c082c506400182001c03d10036540d00c1c0c1d01015521003119078011400c2c241004600780d1190313a40003401c440400e602902d0185843c5c020005074040c004426812586192030300c07130200d21102940300045ea00c040680794510030f0710880c90301a0900350001d1050303014285540c010400c59500c034000700201c0c1d426081c5a0050340030340034254003410741044035580511000800511f0100b9030341c0000460054415014421006110111200d04242003031055a5001000521030140c8541c84008969008011a030981038400940800c3e608040703015107a440e52150030024894040c026800314100500c0c1191561420240c03d100c4010621401d403506640450075204040d070300c0e80701c0229134541c100c0400c2c00649e40d02e81103503034a00c416030b05000603250220015200c240041a154482001806060140e40b0101c40c030000707401c02c000a03810010708890025210b0070507c00407913296694482143d0b81c00407000050305440e402d9582004009080001c9840b8603030a2054003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 34340167 1250 34338917 34338919
    0x1e04090e030f030711210a0809010c120509190b04060b0108040305030411010c0501051f080309030705240f0706050c030112020d060f0606020709060f0308120c070b010605070b010e060f 81
    0x84100b140c2d402e8081c1c901014445c800105864030095218141c04200c06000706030700702e03a00c0e0951989c0315000542030f41e041c41d1462000c07507a1658480c1c1d01300e400c1e811182d8844040000c995100401030400070031401590020f50341d65001c40306001c02e0001c06d01a40c1c40325002802c001c000da0915641c000c0041c48003c10140c0030382d4030603c07460704c0c580c820b0702c00c903980d070750400024400f40c20b114890645007000380c030b048036400c0e20314000003451180120590300d0601c401406440014580390030b000030010030036840c00c540d44100200300c0e5000e43c007802030031325064810074042d1a03a02038a070100071035401501ca031b107044905200401c00c01c00c2500343c400c20035605032864040420070386060030191815a07201407081c3e040c607401145080e80042c2ca0002c07140156018002540e60391652041000ba5001c0905941e00c00c0001c01c07801001c41c40c40c10740180071145e4036491b20300141c0b500042e86d00203070017140014100044800c284188400c01c1405054030b00e01c40030709424008001143d50814080007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 34341417 1250 34340167 34340177
    0x206040b0904060b030c19141e19080106020c010903020a0306090203010e0105011d06040507052704090f0b060406080c0f01020f0d08160f0e01141e04090e030f0307 72
    0x101c0e5090729a41c015070010601c0c0032081d030700d90800c45107600c0b10b504080c10006d40314801d00c10b1310341c00b42d10a2182d000241c1230f41c551289001040000444ca04131078940440c0306440820003a201c800488103a80c442000d036980780d101d02c2d41010402402d100003c5109810408100302c01cac000350352003141400459074481800500e524541c800729026111443c08e41c1d4140d46403d000091080079407103e01c0c60700c00300d00c160108955490b4100400c540095601c0000100c041c80708040d00d1500200b1018101c00e00030410031200307040b100150544202d040d0880b800000d800c242020401c030070580c42e4004004803014840c450400d000e09540e1a8416110752245290018118070b6900038011030f03480b030052400b92043d503c000b810142c0303010070503210542546010b8040007203141c403602d100b03c3c0e445096960092109841401101c2c07209942c03880d41102c060401003000c2101c08104a150400309290f1034640f690714218482c2e088440d510681400e03034000b00541000601c0c0c038011603030f000341c0508103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 34342667 1250 34341417 34341427
    0x3030f0a180b090112020f03040209060109030b0916090b0d02040b040e0106090e0c060406020a240e070f0f0509010302040e030903030705010e011b0516030201110d090203060705070206040b 83
    0x208a41e0040540c010358400c607905100440d4040111000b0403c01e031080c0c032180d00140150355184120f129641c003a2040c544c4c01d03c0458014601340c10440d0700800305250022003d52643c8588103495070580c0c10b641603501c02a080303c01007420400440c0108000130b0b0401000c904000401c0b0341d1600f126000780303c3e80d959000c2102613951640025040040b41c2e00800c041500e4500040081003004094505031140300010a11442c04400311800e503105039014040040151340d4100783c076000a80756000c41d559890454100020070301c04d00352000d03045001400140c2c038100007000800b03050341241084000040c000c0c0032544601c0620341c1100c0d03042c0e5001134146100700c0034500354040e104031035900d8000000d5200c1407100540060802c0c0b241c0b0030003084124112030300009007181c400d41c170802041c014030200e00c4003011020302a01d47c034040e000100720398250021741da41a902c0307000281a083e0361240c00c58150300381006040c0e4000d0650520030725181039500021018040c40c400c5403241a0b00180f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 34343917 1250 34342667 34342687
    0x80603100908030603010605060f0a030f02071e1a0c12040c080d09030623070c051c1205010806060307031202010b0d06050406140f1326040f120203030f 67
    0xc046039003500011000c02071038071940340c41241a401958542e1103503003481b030701040d507282880032941d0040b0384020440c9410718a85003038010306040d1100924584d0301748503d10100c2c9041c2891101c05660b241c08500380304452502290b100d40402405070540f6030303803081001103070050044640f5004495611111990f0760325010a114016411504540c040c032582001c1480d0440b00400030b0300c2c4154070174460080c91054034082161031001c1460800f044171f010903841401103a1340d01c0028010410368111120604400c0310000c0c0c0e058400b0000742c1003801491880c0c82d14858203014100440142c1118103007180001c0d03641c412800090040d8510b02200412603000750301440d01000060a46440c0c0b824609140c001014211307030503220681050119403262100c000110302c0380345080602e403140c0d251006008143e803403000049800382000c110000c60b2612011848440190704899555a14181040c414814003180d1080074000703c00600c003001a40d010007901e0403c04a0444980c40310400d40d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 34345167 1250 34343917 34343923
    0x11707080a0b1602010218040903030e1b0f0103020c07150207241704020a06051b01020403060b0307120308060105030a06050613060206010f180c0e1924020d080603 72
    0x548124101d124044911003046070070b031100340c0310301004194004151070400007a42070780714008104103068040c181c02c44180c9060b60100c603031540286000116004800300a40c0380990618040c042e42c4079841c0059594607101c540b00070106003e01c1c05506054403d00c495643d11880c0c06544e141c07044614080c640f0070302c07c21002000701004042010b0250688440000281c041020355002946070b0500c1c0000e0b840406595004d2a40540a040c41c1440c140c421140703500030088041d0082140340107048804000d00140c0081c0d4040c290000750580d180080518002d6141d01044d645000c070080000841d401c502c800d68042070a0070b00d01e680c0c2d9210724544005102076002681d0140c00812160f1003ca841c007075400540d00f05408458642c0d8030741400604000051241c40c48050000c6001d51654403590054181002581401003180c56544001481c4111001e414070400c034504400300404070481710340d42a00a1940c44614100d4401d43c03000351200d451801042c14040b001012981c1d5460030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 34346417 1250 34345167 34345169
    0x703090506040303052a2a030703090512070302060a0804050a0c080a0c080f070b090303090312070c0506030105010e0909070e07120f05060612130c0f030303051806011707 75
    0x3010655205107818500900100300c2555805400c0400c101404845d122030b20175002c100d130703c282d09242001d10403602494409500340603500d031204400305910081d04100058001c1c1da00c2a04c4d8409024200740c140580b00fa0000301d042010741c880f2600300302507124101203c1d4090407615080e04155907a003060751605151043c002c002040c180b20006d20710340d0100e0741300200e900c030301c107108072907a52000065925050162130300044d8000e40020031a400d04d64009100000c00034066038202141c83c00001d0402038000c450b65143da0780051040c00b00003240030038002906003110514219410f03c40001c1030f080041400c140240c24660108010003000c108680051814a03166042e91400364401041d620700301c00719160540c1401400c2c01a940c86018452080b0740c0540184c3c102034030030508080303100d805423503503080d02031618680300421400076a00c40604191012251034519601c4c00404413100140f0325844d10780c14a4843c039801c40702040f118119103403900300b8643c414012101c80e003045e00e2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 34347667 1250 34346417 34346423
    0x705042322030f090503060c09030606010c1101180e0703090507090c0203040522050a1506030b090402060a1103040b04032d02040b0111011506171e07030b0d0b19090c0e070309 77
    0x2000b00300b007023540c10040200360720704c8160103540080d19564010745020907230100040c0b54450140c0c841101754825400c10100144883c2003000c81503440ca03a1560f100f00c107a80890019881d082d04e00b081c0102084182d00a0120890800c25851984c00007501c0340500c0c010740f480340007a076043c0d001c03003070168200c009000c2030080308102c1400c0050b10800101040760540b005207103003510005031180248a0340312001400760007591070b60740e01d90030016180d20840601c0c0a011020102c3c130f00030101040544043c040c03081070650360718154100a1072082094072024082d60302201050741e01c0d0282c080030a0225415500070807040c01540058590001c0c4d0701c18240c040d86032034001e2095418100303d45088074800c0c4c0b200c00c6407a2a40300309002d0500c2c01c0b640b003040d210703017150740c88601c00030308514581c4480d59140004140303001000045005c9000342040e1141180e0006011090403244543c1100e040d002c0703030402400342550f5440000401034440d0005079042100010a903d000341c0001451641c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 34348917 1250 34347667 34347673
    0x60409031710090501050a0807090c0504030c03030f1707020c0d0204020c030d09020a0e0c070b040c0b03010e04050115080703020108040510020723150f04050705042322030f090503 79
    0xb40070302c409142c16000303108104845040100000302424145050820303035501c2009040b55a0803c0d5021014103210680041042020000080450a402c480101031482590340e01d03140c0d189030300d008141c14240b4075641110359a51060250143c0c00259403030100340203540001070001640000fa000380a071009507100b901000905200060141d4840303a100d52084490028031520303507080d2440a8801c0f10003c44e0702c003040040602007040d0050142d030091061040490280d02d40c011007485820a078001078030b03040c0e410180030400a003030052100307020240725401c094034076083e03c032642c48415100103414800350344081420b0250601100807a000320f42001d40d40c40b40c89181190000c000040315042220350b4400102d803100b1302007820b064520351548400d081d80c40305a00e1450380c040260080721a4481d0a00000e51030b166802440048114a0040414501e820006125803280144132103820480c0111082883d40703c170340703502c200907010f246c000002140403006880102041d004554948 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 34350167 1250 34348917 34348921
    0x2328030c09090510060308070b130501060905070f080c0901030903090819020a06030c0e06030702011d010b040c110703060e102d0902030601140102031c0507020c03060f0604090317 79
    0x4422900036400043c4075108441030403484d509490111415408001d2001c001040104041090a41c00980080740c1020092501c1c5d03040c1e5600c1c2c00c45071a0350141c010b45480c0e0082143d9135401001c480c84040380350424154074503158002c643d8920401e95141e050660702c4c0d0a45007454030500d4442d01512160742198844940307841d1800908500c200304038854007152002188440c842c1c06190400c0c00d40e500c4105000c01201e080001580004004004565913000c0980c00d0010100380303012600040d00000642c2490907052200f0345942c0d030000014030220000400141d840001c410003183c2e0080000190310844000090920090510030030b00e003820f11201c500c803049032070071010012001c0b030160041494609070480649038101e8010f54185c100c2c50040203000c1c02d0940c1c08a586034144150783c80c03e807645520301c0f1114a403441442100359110200901d49404110b102056541140140364528201e00340d05003881c4010022800365858500903c20180507041c5504052400c2290000340c2c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 34351417 1250 34350167 34350179
    0x9031e0c0f0e090d0509010e010c0210081f0803030a0906090b0108010e010f060302030a02040c050f0f03060906030604020907110a080408030c1002040b04050910050d0305042328030c 80
    0x40d02040c041c80a0208440d4007284143c034000a4001e544551501d030745040407080d5005562401150080300e060004801030400140d540d8203400181001c141c48104650900c0701c80b0300c046140b0784e00340f10f45550503628140854203000040c1c1e0f074021303444080030540641d035240c48005860b041e0720080940000c60b001013601d01040d000000340241020003001480b2942101005455031440065059040b0f80040c0c0c025050036001048152480d00b8000c0c60f00044001c41950ba80c0440b49a84075400040b00b4008240703041901c09030016022001800b503030a05400150648402034480ba00380410440d96281d0b0034001d1102080345600500c52075103440d82c5015a070380302c0c4d04c44510b0f00414013030102203034074660300ca1003541c00380c0307044481c5281054141018805500000740011a540c25500b000280350750300e1407104c6007141d10a581d0941c0315898125400c0111011140c07200d03003c01c45d02c0310714200382c42d9003803c802071001c0d2160301d030940743d14070b01d400ea00700031b40c1d4001a01c1800140c002050b4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 34352523 1106 34351417 34351439
    0x10909030e030601060201060e0a02090105040e15030307111804030815010c0816050709021e07020f0d03030b0f0105040f050d0305300a05040309031e0c 67
    0x80c400c0c040700081c940302d426031041c0010f0f91a80300a1040d60308200449400464841f402c0d41071508030000a40140594020010701c0030680001440902c0c0c83d62390380d8100c3c0c1d00541525580c1580e8101882e0003542c01c8420740c0203100c041c528800680703c44404501c03803a059624100380e600c0c1c0322a903200105c000c1202604010750006650701140d0300ea401032810511806035194903e455280042c240391066005001451042c8641400022100307603054a001182040554940d0103100044100100e824156002401e1500ca0410540c055002c3c0b2100c584c2200c04080e9002407400442c1c1a200d6030040e214201840c2030b00300310500700001942c8585100e418041d003030002911860341d148401c2d0b40b4409240c1d01112800034070001c03e40d1115040b07440024140001d1510343c40103081c0419621004012001012900000321601c0300142003413940410001c04841c1d0340c024041c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 34172667 34352523 := by
  have h0 := BRFrame.cov_init 34172667
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34172667 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 34172667 ≤ n) (h2 : n < 34352523) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
