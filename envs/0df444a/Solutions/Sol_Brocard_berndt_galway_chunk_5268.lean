-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5268
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:18:23.717081+00:00
-- url     : https://prove2.me/submissions/0d74f778-b0d4-41cd-a2f1-39b780d195f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 947302158 ≤ n < 947482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 947303408 1250 947302158 947302163
    0x60307030b041503030324120b0901020c0708100b12060609100e09160e060a0303110c04020d02071208040b0a180602130302210618120f0408010f02030c07 68
    0x2096140c003000704000d448010f4a115030510b414601100300740c0c0550041c0018412240103503003140304089994403070882d03405200c440d0007021100714002030401c0c080c5a48000801d0016050541d07402d141890005c1e203800405903038014914080725943c082c42404a803010403100c40030340c134106054690315600c0140080c2c2c001d8085400090840790340e01139480040c0300c0e4091311086880d02c4d807902c1c0c0d2207503650802004e40105814000a944501038412409500010040350f60701d451554181c0d00200700702901c99941c0100c820040d010740c0c807440a4141d0100043c40540d4812030fa290040c141c0400b00c2204040c01001001e2002040720b908010b6400500b0620000e010b244285000c2c41c0c400c0f1020b001880c203400012b040c040e651000901071300702c902c280c5445080002080407a6602603901110f00207503404980040c05003c41030388440500500c180039200013580300c010610580d405a141019812800a01045141800d10411002c1405280c0850942c24504840e4041d8407580501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 947304658 1250 947303408 947303411
    0x1020d1407080c03070605011805010513090203190503092b0321051807141003050a060f1710020708160c051309111818070317040509070e06030703 65
    0x4020016101c1c112a8158940c0f411292154001d10f421005000d003400b40946610b480d1000302c00551031400f0345816220020f10610f444813100700c40000a000310a0160f9161007010030b0801c4045100c51840e10080c000c001031340d52103014034144140030700b0005240160901010b0390003407031100c100b072041c07034254180b07085800000c20340c0c880c4400d121045104034130989040148a521912021031414052003042503d0702927588484c603c500140041101e9005414413101030001c81c4179500169110b80a02400940907403242e014582d499983d810400510100590142d03101c102008a0210383c4c000200c2035281000507070f242140f6004044680603d0701c00000c900041101507600d02c006008003401c40c020401c88002400302034490038606640d1101c0c0d103401305c051414600341005514030480d003028215240c41d00301e210003100c2c90482140c2c0c9c0c000e141000c8001040c00c1004100e01220600d2640c485080008000e07400201400c0041030100c11000f0030380e55250b040a5903800714403401d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 947305908 1250 947304658 947304667
    0x1404050601181506050c150c0f0906040e0c0304150b011b053412080313020303040308180a080c0a0b030a020c010f0c0206070822031b0c1401020d14 65
    0x5400504440308080f01521065a400b050003940308001c0d00c118a071207400c4030404404031280d003440e098280c402c031420000400000c041d8514103001040c10700c0c80030300101e142556521440c10318500070340d01d0b0000c1172000010f01c01402900c0d100c2003154541c8100c200141220301001a1650072a00d407401c04201c010829402484014011b240d0240c44d0416030301d01c25000c0405241300194002c00304240040300b100041074142c4400810050343d544400356928640301c1084443e68984003a2040341d0620040101100040501c030141900100ca40c42d0076844c11809000c00c1840ca007143c001c40c8480d4046102c10490f0b90700c0d03280030401c6405e41054550b0380c0e110000e815019101c0c2c8440400d003903080be200910101030680c00b50740c04001c0c60f400c1c0e52941e101c1d101e04450039101a9100c51a0b04900c160200a12062414000005200e804e10000c1d040d0005031075260040101025942c001c000301c0c00f040380011100204000c00b40c01d01c040e082102c0700300b1000e800da0f801804544195000401d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 947307158 1250 947305908 947305949
    0xd0b040902041a091006020a02130e070f03021305060306070e0103060f0b0415111005060303040509190e030a0c0b090a0b09061005010e06040b0d090b070c05011404050601 75
    0x24022100c040e000341c001d010020f02480d03500c49603000b0040c8240a1480700000420302c03091030303641c0c50030340c1c80582c050302c0c0184450b003c01501a03102200541580d549040190640030100b205000411502003046001d40c914010404c8840700800d909562a0420080014954002c902c3c9980700ca19410312070303030700d26414004900501c841e0f0001265482c1c041c202003951510003000d0001c4500c00150b06041c81e031a26001ca0b1a00d000d42e0304004294010766a1503510340041e08640d60144000c0c08603420300e940e90f40000d07802e910076564004440480380d5291044807203805000315550b1440021440d21400500c014144417a06201800d10324111010641c04402844400c003141e400070104612030034110422516540309803801c0d903001c41038250024455000f084c07640b2520308001e1000342041d2800d81c4859080d880f1147d4151125075890f01f801c00141520256400f0340c60340e50310a034503900f1924000b4212910000c04560034141c4030704100005800280a90566144d4a0240100d07c6000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 947308408 1250 947307158 947307161
    0x60b03070804031d091f05030c010e1011070f060f02010506400b031917090f0307060e0a050a0315110c010c0305041703040b0f2206060e0906010602030d0b04 69
    0x41922580110494103008001d02c0c0d90f44011b40300034100d00c1040400c1d6a03003040643d00c0c0c004c0003d0502291548103100081c0c508050110544140c500340f80c003800000da00c905090040075084403503035001101061002d2a40244c100e8140c0c00d15000800c00d03402e2650004004020030006000090920301a4260b6000d0036401070484940c85a030b0981c1910842d141100074040e03056900d4081d20800444050070350b040e02902b0380d030607001105031940e020008070300080340e8072420710030350801d0360030052140d6a1410030101000b41650b40d00c00305016181d1040000c81142a44500e1040211400c01e01c0490040b44960b00c111058107000980d4040c1d0301c0e42a80103001300c40406403654070700344c140d5800a4151300003038400c51080e014440050050030203c002c3d03020540d005045400c03800d0005142d226400301040d003094030f020155013070381c00d41032441070600c100441c200d40640c0c03580b00821003c00018402da0b004130039680545801d40c100070002f0342c2e0340501c1c000c21686a0b00c904036040552280e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 947309658 1250 947308408 947308457
    0xe041a060f030a0b100806191509150e060d0c0207120f020a0b0307050922060816080316060506060d0504081207030213060507080c01020c0709060b0307080403 70
    0x350049840384220066041c441d00219041c001c058100010440d840c501350f0403244600300103445148032902e58109101d00070000306a0000164542c02e80481c000080b004030354020400742e65042c611500b0003205034441c030585140c000a1160241c200c28003596038000fa120b480c40018400540040460003c9150070241d90080105103051607804003485411032800a2260007070380c0e1011420764581e0301050902c42100c0d40d00000f41c062010300214a06040000350031a41c501c030704a00f80702c040124a089070095442059587c0c02549160300c06c52442c031141d0700919424000c0c5050800c00a000c0c40050300e41c0300010309040d42d0780002106941d40341306480708944811000c0000b440c0910f4a940d480d84200110350b102c0c0030700c0000403801d5101c0e000312100000988410f000151030441c05940b02e0700985000c5a440c8410710641c000884244064141c0c10780443c01000482d203014042800c8400316003059000ca402001044903007600308201071f4001d42e046c64224202520400b094604c00d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 947310908 1250 947309658 947309711
    0xb04080f1603180b0f070507050d0309060305060306010506070f05100f0c02011506020307081608040f0e0a0908090f2704021306150e040209030d031e180809130e06250e04 75
    0x4002b00410a144d804441e201c103480203910308000d29240c4a01705a51080244140c5900c21030030000c4c00c00044c840600b40d441248113100b212070740b502c602c00602c103644040c284503101c50707514852103201a60902500c0d9000940140400045081110003503da20a8101c081c101c800000b03141c84216405035289038645412400498443d0f07156204080c10200c544507120301c610004010559500c03040c4240b20400b9481100949081c81c00818040303080c011114190303201c1d20902c0d950559241031180c0c4201c0c1401130580000350f2030103104001403c0701c11481904158035000c5d09106103000030751001002c101d10300700384400e8806000001c010703103e6690f04503011301074041100d00454142c1c0100c942242c7c08665a50310b840300030b041c90308403240190701100855412020b03a01062002009041c800341c06481e420324020f041d040d100c16960394403014075407944644200024490380f003090b40b4680107925025406030010040040100b281c2c0844244a25940c040e0801088004004080340c4107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 947312158 1250 947310908 947310919
    0x21c0c0b07150e07170c060c060702070803070c050f0a03061a03010c02210306190f06020610030f031110060906140901030b040b04080f1603180b0f07050705 69
    0xe4850401110381d411468049034408030350344203440800c0d010700441c0c1c0080109802003032264900882600c6050f07807440803840d5401904c2c881c1d011a1203800082206103290001000c0b20b01309140002d20f030030440d601460b0039400030301030080041c041d14100001c8510868424101c49c41c480c001400c031114590004050350710b001070004025201e082000c0411008600070400011804000c0e41c03550701540b02c81c40300c0c1104000390f01c9180080405076800290203072001402c6ca5140350741040444240e0007445602c004000308100b0542c1c1009030a900018076080c200007586035981d441d0400804501c010240940741c048452504810403a0389103403050744030141324461b0b0b200d4003540206894040d0018050503c03500000a090980c1498100c035800032031070100b60780b42d80703c644800c1000b070001ca4903001e080003900d1240e8090790103080c8810110340fa4001180840c90301078250705000010211094410318108280c0d6071501c00c1c0d034040050a0300d50750352403a552800070300300151600507d9005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 947313408 1250 947312158 947312183
    0x13050c060313020312090105071e0c030f060b0105041d13020a060e120a1707080c03130905060405040b160c02030607050c0709110304201e0a06050313021c 68
    0xb81c01d104619a802902a00d8000d5402612000310780300c0d0840f95030202d0820804c000c00600c040088840f20081c4039400c0b840500c107583c44d1000d0368003980c000d0b10388404404552092204920400300884000d007842840c2070310703011804150102154003400300c10300d4680042c2d1195012072402c0c1d440c1d41e004001e00e640c1d58a801c00944000310001c0510300814444d0319042c6102c4001a038806c502e0340013109292244d08a520894142d4400d85c42103409840c2408480e014010810151404601d000f18540146003080405011190001d12141c400c504040911011550494845412192065000d03415554001e01650b010901d010001c1d014881c0b1000c000c1d00c540e101004d00200000041500d41c000d5440302c5140c1940c29080074800704000801c04500081c1ca040c06001c50344480c0031103500d20340e4005000910100f16900312110480c412440140c091a002c114900501107030b00744181103050804031100111440d2070001d00030b0701d04440d000317500d64050014206669020b140d071804d9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 947314658 1250 947313408 947313421
    0x18030302031803094f06080a260415020706110a0f0206030c040b04030b0103110604080c06030a0905030c0106061107060512100b0a0215060109141003020d0e070816060813050c0603 79
    0xc07001c5c02200305426515018000c0342c5000041031142a081c0c00c0f5034503d40c8100100e1156401c0c42d034017540c0c8280101c080000003038010303086403131a06814003074018241c441d1a210000e020310f05008002010f940000300490000360700c03140b502041035010f8034115265640c200c0c0d03810381c0348a5900104e50010300414008100155041c0c1d40c3d041e170340310f6200b5030080e5480400b4001e0742e01441c0144001604801c0c0e108459040040c00b85610401902012801c508d030364941e0b07410b69000d0906120182d46506d0148145508041c810b0b00c942d4816000f0302c041454504010058001d00ca041d40c240784034880480c58010143c51000082d01c1000c2c542c1d50b1720300301c4081c00303540c0c0c0c842c80b000c01c1c207032405010002d442913001d072850300205c0d402d0300f01c0541d04000c040c04000b080542c01c10b588060541c02e1001d520300d008a889540c20320002c01004011041c101811039281c000110b03d41004e52481b01c2e018065103030700010190304846c40444c0003031400310a1400d00d00b028042ca40c95908400c3c0841041791 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 947315908 1250 947314658 947314789
    0x10e0f04051e0705120a170418020906070f0302340e04060e03042303060402010801030605060a090c110709020c03071203020d05150f0d0b06131803030203180309 71
    0x4c005109440802c2e5100301c1c1f00d01c4103d10b0007a031050304c5134410304038a4214040d145800601d650368006080c946040d000fa60349458044424606a006900c0807142c10700c484444141c0d0241c1040764030381981d140c4002c20a515050322980a034112202d45103000c5003c11065401211b041c2ea81d01c015203440c1c54441140840390002065a02103140700348840391403504012820500464044e92403410303503804d58940c5005842d02900b4540c018070415000105010141304850840050387c1d600b00400c0d045080447ca02005600048051341c4100301c2515445c40010481d407090ba40408104070083d64204150024066000303102e441a0070041000f032000c0130079060303c1d1440003c5a25403680f9001c2001d1007007009a0f800010300c400b22690120b1018500200c0d0030709923241c440004611448006130780c5140d00282802107000c40e80202c140b1420b08d8698403000d2202c4451002903081000140024111513110005e100001c0000036040000450322404650086550000440300b900e010721a440c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 947317158 1250 947315908 947315923
    0x1107140f07090b0a270c030b0117063001020313060c03050403140f0903241825050d15060501050a1d040e0d020105010e0f04051e070512 60
    0x2490350146900c00326180c190ba108001c0040741c0038240ca1011802e0001105000741080c1a0340340030142caa1000307898441758050030b041c414680d03502040001408001408140401034407001d005004001c00655456141d410009a41e031401040845807181c8201501c10120300c0c1e9400b0a07500000402c0301420302910079000080c4a41e01c00c11503100580b40880032110140d070300a00084443c00200000e0039018041d0010690305900719203000c00010001c1d1074a22030f10310643c3c5000100d203a01702070b0055240403a1744000504440c03d50340f4107a212068490b51900b0350185842c034030b03004040c065410900b50602501026201040d07511141c2001490100c0d051011f207081410590041540c0d4414829a0500130041c2c40d0410341d9115450035541601078030a071580c0241d07403100d0244505408000e0700800f8103007600005501e50500401c1c1380281401000305103000300441c1808006080010300e08281c925110f50760314011407400000e41003501b107a00441e440307214000b5a00c41c0800c0030820b01c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 947318408 1250 947317158 947317183
    0x90e0a0c05070f030e030705040218090a02040b040821160602180406030f060c020102040501140f090405130507080a0201050909180d090609080106150c051014090c12060a110714 78
    0x1f03480d8181e44004010580c030404001d18483d0360350311058242810880c1005400072090f000150419031112010700c1d5540260f480b090281e440050307030710030501a1003224800803802e1858035140407a5011150103d900b13540c0b005000940c00245c0b4208030044500015412000901c14041b03241d5a003003070080c0313190701d1000744c94581c40c0030f118800007801407080324200c4606840740e44010748090240481e54000b4030700800ba20104000035605540c0c6c2d48100d910844078214103c40806407401c06515000d51500140115807214015a0150303801100365000c440d0103c0d0801441e03070f1180345038070f80321610007042070080c49627030310014259030054140b8080d41c609a403440b280b00e80d00c070405801c0c1c0c1c40c58868070001c181c1c80420310245900c109013100229025030105c46e09007850100840c111503c4000361034001c0030785018050808401d2010401801c030403174a03103581c0b0010385030040d11110013400c8407542a40d00e142140c106204941a1a820307a04011603143c0c00c20800142a00c800b8a501c40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 947319658 1250 947318408 947318413
    0x4080304382203020a180905010e0102040f060203040b0706020306060909150f030105010f090c17040c14060915130315020306031e0d030b01210c0e01090e0a0c05070f030e03 76
    0x56030750349a14001030040f02e400415003000c042c9800090007046a040c1e4090084c0d80d100c0e014800800d80c00d004841002071158001a5207900d0090304610354013a5401c0103086400c1000b01b000420b42c1c60f010303541810741180006176281c0b43c0c14005089481104c3c1c0c510b03001100b00040100010242690100f00c0905807000103c014090f0100341c200d88090184203848415030790180452155640044500039543c103008040260094a584100808a80071600e44040c14001e01004644039404808080c0a0360000d041444030400151210b00000410344420800300b0754807414202812088021074100d4207081d2006403e907200d801a5204882d50f41c02845081d5010f5100340b03003041030100c10340700d18020b0562009401c408401030010301180030f042101418250b851840040f0710b800502c2a06040003841101d030550103440b80c680d1f054090b0501002500c10450f8000c241e02c85580308444510000b0b100740303d084283c405024000014210f202d00b0401c1074101a001581e250900104504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 947320908 1250 947319658 947319697
    0xb090109020427090516180506030604030e03070b21180a060b0a0f1214010515010503040609060e030d18081b0709020f1305060408030438 61
    0x6038900381e109a1041c0202c449420311810516a104000400c044000600100c3c041c45162200d900d001900e0031200100c0c00b091908100c660100c44500c0c851070784c9450240070510742000060746901c4000d001600303003ea40714038000542d909002d0130024001107100c840d2245041200245007000052402d5619030310400441c5481d840340203060914580c1100401c2001c4441d55200060544101c400b504072480480c00f0802c80d0403020700c00058445480745402011050a120203210400c44241107140d2600041c40f80d10f10411303095940030142030901700c0e5207440f5450924004e1900043c050007442c50001d202242075401b0005120510b07a1080074000451510030030102d02a489500a00c42d20b01000f07181c0c00c10920343d51510766000400165140a903903500040240d0f8041030403640100c5000500c00342c03138014118008003a11069454230700742400d14502980e03d20990148007080d50004400c10100303041c540301b0b98411210001c100e41c0c1a0901040f01c1c0d0302d0b810200c1289108058801d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 947322158 1250 947320908 947320919
    0x40b0603090d11030d0203040b0403080a06060e040c050c07060c12050a08011a1902060702010e03161113020a0206270a03050c0a2108061203090f041e0b0901 69
    0x4058a01070310360760340a88041d07030030044159882c001c10342842c0b00d1070005011340c441215561015611481c0601d40d0041c0c1c9144c5407900401c0c1440003030416010314034116090094a90006030390003403203020340780001d901003401004ea4681c001c0025071240352040c68070120706207501c041c000180d03d11580040c007484143c210141c419000310300d608400181c0003c0100400507040c2006d0940356126110a0b1038444000c940d0782d1480c041080b10009a84603174103010213942c0c2442000001c0382e080000d58101400035080403000d05001d20007810702c10b0b403440ca07015103580b0b800150940032400740d0210340c0d5400e684400ba485802c1105d0f03030038017403106c0070218a07151204030f07504004040c810301401c079609450f40c058803280c020186040d014803509260780c0001d19642c2010070304003500c0740b807103000440115006117513141c01031020f4014040781038442c0600000006a41e1098030849001c8041241c18000c507008012140030f51074804401403003200c10002c01d07440b22616000540302d1020b940e0300c51 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 947323408 1250 947322158 947322169
    0x50c07020a230d0c0305010510030b100605160201030e030c010c080a020301180504050c0a090209030c01020111030403080402270f071e0804060b040c050309011404170306040f020406030b040b 84
    0x614080b0a080c42801c00400e14540b0980e8845100d1054103500070064890303c840d400c40340c08542c1400c070110246001d10138080a00306443d4800107156000700110301304070000b020742c0142d4181105094020354007104681c0a50060b0f0440c0c1c0c4918100c1c0d07252520b03441110b018140707442048010075240d0b400310b0350010707041c002c0313034141d40004240b85801490074950394000e003001001620035000344054801a940d500301c03520020b243e08040941c07540045800c25050003d544140c50540e85010600036240c0320b400d00b070340e03480354060074207407855981d900202e0702d40811591404086500000616402642e565102e0700651781e880314044260307103810094940101d0040d1804007041200c1040360000d119000a80e8410f100b4103000c603c0c00f0ba004081070560725440b90b964041480481001401142441556801e00d08078100781c0b22801c041e1030350114229000c0018044c02c00c00000030b94981c40c0ca411400c410301c1222411561a030b03940300010f00809651810030301c40c0c0e0500f07a01d4015441d05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 947324658 1250 947323408 947323439
    0x1d0d18060905100507110307060908010b0a0f0512100207150c0206040b010b1605010231050607060903111b0307050303180d0c080d020d030605090433050c07020a 71
    0x605944241d28400f60b0036109600003d200720b840d64040801c035030741a2414130003032000b0662520342c10f03110340c10600c90909468106450500800c1c8108040010b404042c00180071585c00703450007072542801c0701085080c00c40c0103164401c8140000342c914104100c5070b402520354042881d0800c0803604e4000b0482e1942015107018000d026178000520143c60b0040060041841041e4080040c948a0b036803d03007641c200f1807044806005101840f03401d1811024800d60352100b00101503e0346081c0400540c15001d4050003928080d40d58014200b0103024200c0604000064030449801c100f202500341544012040704502038012581b0026081c14008107407040210f030b071055022140910810f00641000700c0a05540f00c0501c080001696241072100100e04817503079028090065009601800380c1303030160f1101d40101484c000f00000706420150407006844840001c001040000c010f21100a0f0403001c034070721045c904000e10080006940c001d0030680e2003690350004a031707500d0041c00f01c010103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 947325908 1250 947324658 947324669
    0x1504150509011b0503070201060f180b09012909060d060f14090103020f010c17090901150c030819061d1621110d1e1803031d0d180609 59
    0x110702030f016103041c0254090342e4480118400012141d5a603455000444d595a00c0a18001c4100f0544131041c10103024080c45002c066070354050b59498005a40502140303c804d000c8096030303098125030201d455000305d0700800c50043c1055103900c1e0202030000200028840c200610300b280000085074179403903600c99905540200310100603032842d001e110400001203000d5041200010055001070051044140c0e01185128a03c1d2290070b02803e100030310700180c00691080000d0a01107a0007039202d013041c944d0981c140381001003a16460b6100410134428510321720300c0e80c1042c001281400840e060411105112040d00d170b17140d103038201c0c280c968a101e181c030440012105000e903403001c0045403600400d4000342d40b00041d070a48414803108990000c4503201d404940300c1c4c9030120528891501304d100d003129290200300c071006c10a242e507040c0d403075143c0c000c040c03545540682c0200078081139816000355804080c0c4c0c10f55810300f034004201d00c1c501c0b0035041c1c40040b90040462064820340400f000c0c1c54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 947327158 1250 947325908 947325941
    0x601030b180a0e01090f0c0b040f09020a0201111b100b030a02010f140a0e21030306100309080403050a0308010e0f0f090a0c030312060e15060c150415050901 69
    0x14120100c1e09181c8800501c0c4814864035032000300c000750300074072030b5030109802134880d03890003155440d09044102883d407110b0042c110501082c00100000c403080d070115010384000682e00d60f01c0304001d0f805014041c41113984114041001c00031414040c0b0076902070082d4406440f0000880c0519000300d41c00009050f80540c80214050300550041c0090700c0d00c0441c80c10500031000c85401805441c2d40041241c5001890b11f44c880c0740c160030700c2269800242000c021b000c102c9151105155a00c0c00300605161059484188a62610f40603a2100c4003050b0842e0703040d0f81c0c071500c07170400c2a60707000e1a42c012000500c049000007858040e480026000c0d50b900c1c40c50f0300c96600c0d903041400540c2009010900c070340c01a09110b00000740c3c800384010045201c2d1711030140c5003100341b811608a4019620000c076554519003040b0030911885903103041c1032803c9400c241c07a005c1c1031040a14100c8803241c0d880c0c1d0b6189001c24001402040c0300ca031040c42403464802d0006556280c030180c00d07100c045980b0401300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 947328408 1250 947327158 947327179
    0x311040312030c140310030c05010201140a0b18011706010b0403150504021203120106080a020414060a17090307061a0d06270605461107030f080601030b 67
    0x110302c42c1d08070030301090103860010301d12550354a8480300c55005540d01d9501803802c98081040000c40c00c0c016005040c02d0000300004400900f0001030f201c0c0041c101c034801d959400d03048050b076542a249000d2103510f940328008a42c0c59604c045800342c0d02020a0400744a004000034480009000b214140c1e507105c0d080d40440702d0708604d0040a0280600200c1e40001c900d012080322541c01c2001d01081445581000d68a5251810140c280c0e034014226401d000d00410040c0303e11040c0038004c510b00d480c1942d0301641c03041040d80888008288020940300c00d425203040c062121000800391000c00d003c0c0074100580700c001e68850400c4000c4d6039986401044506070322011408642c0860807080d0302444070100d00c442440e0782008500c1081c030071500303d981d440a0283e1501d18103080141e90722444842d00d120324087e541081104102109050b1880200b1036a9210f01050f41003440d031b0300c0007031440e2504e80403140303000303400c42c03070710900310070000c2c0700744000619640c428000c080c4507001c00b80c100c1245 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 947329658 1250 947328408 947328443
    0xe12090d03030b150d0203041106031509040501110712020c100f200706090603050f0c0f18040c0906121b140903071d1e0f0915010b040603110403 64
    0xd00709542c1c0b904c0c0d20a6003d1350141c00310584d0742c010040c090400380300580d80d16091900c1c0702c890005c0c00c1c0c442d018034001c0c000c000d9941980d4035100381c43d01e002c880180071660f45180c02805459544003003d051180170420004111100c010850b9021b41c0d602501c48420300401840503e07071005800c14001010800703804221400307000d0b0f2004499100c00b03411105007040c2d0055140100d903034460703800079614480811803541c0c184a1540c21041050519070349060022411001d130040c03201300e864075600014070020420403005460301102c0003a105001d030000a40c005003a1034410712840c00401d9640303a40091040092042c0c0b08062086940d4944052007510125440364260f441ca1603c80c5040196117090355080001d100100844c445502030003151400903002000050105050101384045011980402446c2654402802c0c1400707107259481118072403808151030300c10414100c0e25030000ca64244010000c005807292a102444007100c41e41d00703900075200c2c500c400f078841d09441045045 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 947330908 1250 947329658 947329661
    0x80c031308160507140a050618010504170d17060d0809240a020c010503010e01030f081204140c030a1505070203040506030a1b091212030e100e12090d0303 68
    0x103600848215050400c5450740000700c2d4000070064a4990014070204140000b01421194441041da54020385078030b40f8020034007030b0088440103207442e030340c41d00f5024050340300e94141c80003001c1030700c031a00c1410328010010303072110800e0f5441c80008490402c054864a070031001c0d0350181001030000501c1c001d25803940407003600005d0405070301140002ca1b2003500c3c854048110901074202c05020b0b40d0342050000607181403000124641405014001080b00b08456a400750440b50090300003900700306903150910b0309100e90b502400c00c40c2d080c68240000d004049080f80c014040171341c1190700c214044805c2556600d0104401800034000035644071481c83e141d00002e0300281280116412300303483c0e80c0060101d4000719100b100381da81d100d00c1c54007008282c030003410815501d130800c00405030601000420f07981207201c02601180d100800042c02620035400403840005c0300040c1c03800314140c2407040b030160410200056030f82c802d010344c8011201003a0304440c2c604400404c58203000e03456039410350 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 947332158 1250 947330908 947330941
    0x60d0506040b12150a14150103060e0109091b080d0309080c0f0a0b07050a08071b0501112805121803030117060907032004020d14010510080c03 63
    0x350000c0d12555001d6482d191000903e1000c98090003504d02100c0c4400e81020b40c8030010310f10340d1402d003809225207040c0001d04004d07405c001c061001d503203405650310059000e4051603003c111144004400019801c20540c415001d25204444021000e11040d0580351007980b50b00134040300340c01a52940d031502d0f0195002021403485451000d040800300030601d4107200108101d00c0e001c1d00103d80b144100260000c0c1f855110b2400c2c10000d007040519040241000c0c1d005000074140320000d4581190744549070b01c180c042983c414028440c1c041984815090b54010010748032101d1707404544e000b4091a50801c4180f140610f559250810380580e03090038150b04083c1c045210020000f00e401d418490500c002c40c0070b420540c402d0f6841d44509000385140810060412001d50002e440a0000864401080c51a01503a05510300e00c42c07002e20005000b84a002c00404115180c00c110610202c01210018101c4030100d48454000e4085c0c01c0944008a044500c141c1c41d0b030003040012240c06005c003400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 947333408 1250 947332158 947332171
    0x72015180109051905150705060402100201020d0c0e030f060c09041508010f0219020c01080106030c020111030a09140706080a0203071202070f020a0b0403030903062a03050405010b010509060d05 85
    0x114903c0d56600418004145400d10040030311102d0720a01c01d9080c9500190600c1d01031054076172500000b611403070340f034074000b0340002e00c030329084522106d4a1b03100350180c90548a0300d500421911745c0312070026048168840c0c08500a00420000d600c14003401300c0c3c820b10842504c00e08a140c5050b54040000078015503251680300c0c060384c13801040da410244154109030000032001070b0380321421841d45c0c00864007032001c0400c6500c211140403669034080356482c1101ea40d424007080041c0c40c141700341c1c00b401d40c400384036000450100802c00c0704101c58100c08100790280031410303e4401900c100ca5100e44030b90013135201003031140000c01d80310090355004541c01a0076151000841c1c81c0103407090280d034803c0c1c0c420350b24940030101e10800d515028509100419941c0305143c94035240d81e03800b13005070640e4403014101c69500c55112107620000d0109101c04181c4503020109002c52050140c001c0206840a03250381d0710301803603e145540104112001e141c8001c01c11424500030010350400b6103002041c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 947334658 1250 947333408 947333417
    0x20c0f150d0f090c230a2103030b040c0206040204110f16020312070803060f1f0e040b0901080d1d010e09061809010c1731080720151801 60
    0x348040b90b905500c0764043c1c4481011840d0000c068200320032543e0802044600c078000b0f02c20201f0959441d08829540c0c05401d03840f500c102001414103400400c0503448070ba42042c10001c0c1100c2065021540501c038a10880f010068800e460a14121038081d10a035111505400c10058030990701403803100e202c3d103100504640d0602c0c9c9440010809401201d001c841401001c0180485d43c5407020010074522416141c02e80713944220150402c41007117a40781581403210021036204a626150040500c00704007500c030030700a5030b40348546036039058005840c40c0003500c8601900c0d41d080c98040080fa40d500d05075100b54640a81608122a02c0006000c5550043e06410504800080c961801d48103140c40400010251040000500308c0c4819000000c6284008800c028070741000c07460194540b1111811141000c0302e108112100b070804986c00750000e1004112035040007038040a8201c000c2c007990001030340711b40d880c05000038090910b0107001101800e00ca00e00000541d25014000c00038149003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 947335908 1250 947334658 947334671
    0x509041529210105030d0309030206012102152d03011512060f06020c01091a0f070503070c050f09060a0303082802090109120b06010507170307020c0f150d0f 69
    0x10300c82901c4101107800790800755401040705240034801b000848030181000d0000006907a002911500c05003e10441d084c100c003011201c0c0340034020790030842d0360b020b807940986c54040d8101040d941c1045064080c1c500d80c814241c0307a911030a903202c0780c03900b007545240750969081c070004020002c10340555608110301030310122040404d5005140061100454010003641080c1000b420024403d510318144030201d04200880c104050440310720a51081c420354890100c1451400540f060100291040c880841c1d05414441060364043c200d400488440e03803000e2542c001e0005000d01103607450703446038164200300b0200e40503009056000700007100c0040c420034260781c0324000c818a002c103602080c1e80031680184651308410644003a055483c0c014007400c070f0aa46007418400d000785064104800030401908000c020704031028009118040b1581324980340c80c009541d00e003a10341c294407c0075004209181c41c00e000d900303610028103401c4950302d0017420b004c01c080582502000300c0c49143e600e06 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 947337158 1250 947335908 947335927
    0x615010c06150501090602010209060f1608070303050a06140d030f26010f05060403052a040905010507200c0123040b030109050610081303140a0509041529 68
    0x400c1e4208128005005112030f414800010800f00d03003a04604156071042243ca601580d6410940d01404981d1100558600c0071501100078010001c40040070090b012910500300754041d04460f200320035a04042003d640e0715102e6441c200250081b00340c200c00000380c40c0700864031072403d4800725003850508100d54280c2c0b0b60310880c248050401ca507070f81d1030398a005011540c88c0021540c02483c0807261076091a0841d110640c8400c19100c59918042c00031115800c01503080140c0ca0b80d400c0001c2c01003000c00c50505095028040403075040700010030020020103003050380c0000e03a1482c0d001d00002c2c0380019220b0b0055a030404407208141c2c81e90034640f600d82d4681c4a8100030b00240090a03005c98070303035141010440643c0c4010303100521440c0b410080151340c3d9071002c61207034070020404200d504024241029520035000d0070300c4612205002443c10012a00400144507940060382c081100c0e20343d80000520740c0140f401415503032000d0091084201027000307001c80c41e00c0a030005551030004100d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 947338408 1250 947337158 947337161
    0x504020d03050711090114010207150512100f060507060b0307060e060a11010218091303121802130213060c17070305220303121b1b08030a051005120615010c06 70
    0x91f403100c0b440581124814010756030510a2100a00c07000e581c2d800f00c0e07074030000090300500500385180341c2841080c00041080e20601c203110004d1001c4040c0c01e92490312508024016480800d0540d000b504200e01e840c030728100007543d1021100c40d95124440100000108074195101c032400008010070030300d00d1880440207200501442100d0380b0402c00d80025002800007a4800a006203564400d0400d900042a0400d180e1301942d00000c41c0042d00d25540c4450960001c01580040d41010f008a12880a090a0390081680d22406420601c13801d41d9200c00301c81c452014100200100c21000d0284012102c00001c2d2024910a081132420201c1c000c5004104050034500f046400e00041010814160003030314014450407a80410702c081059054080100002a001101001181000c94850301d48801ca400300c0280e015210550724140325205a014190585034841d500c00b0410340011a49842c8403030045014210000d0b00c60b075610f403845103400d68410a01c00b418030500b40c02140c0024900d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 947339658 1250 947338408 947338411
    0x6050a02210309010c020a15150e090607080a060b090904020607140304050a0504141611030708090915130c05160501020c010506010518090903041a1b010504020d0305071109 76
    0x364002c2e22850610200c07425a0000203060003950071580f8a44040f904521640195100716403001c9144880340c9100664091140c2c0140b440416400a01c40c03010004111180201a02d9403031081c5a240c000082c41180e909100726902500c080000c0e2030541032001459078000e0000386130303508005158680082400201d01c1c082e88a40000800303001c2d6140c941000b0001d0070050741c1c1044202c6014000d034400c100060402c0b064104a03c00182c0c21740d01c2007034071105107640c0d1002d5a440d0f043d145041c0f803d94001800380c6202d41a10030000354002c000140743d45550074000c0c00c5071602902d04411030b00400411000c242002010001505c101181c0046001843d02c520001039650f0f8040c840d56084070b4001e003200741001410004a00e2940e04005c100c0d22001d402c48005000741c0300c22108a01d03500c01c0c2d502039091008822181c404904401c0f002d0640010340702072070080003c03c2c5190900701c0d1070485000b54031000c2c0ea682c1c0c0002c00c0c80780c6d0191081034843c1034581059030105002480d990750 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 947340908 1250 947339658 947339713
    0x30405030307030f0f030b0a03020d0510020a0c0203060609100b0310030221060f0606041512180b01080607140304021801030b0718080709020708130b07140d0906050a02 74
    0x10002e54541817a8410701d40124440c851400f0010700c82001e001440300899444003a02c00ea19504007541403007000d124100480c0c6400c10119508c07498440c01400d07110400070140d02c6402914001540360400c2d402e1940300c0c0c6092840380ea0000c1c1031084409051708050b202120700310a008000c401030711600504003c80c5003041110440d075a040300310301d180c007000500b5001c03086002c0c8140300c6241c5075501900c040d204c140e801620850b101c41f100304c4009405c050005249070602004c400c1199000c5403c100f228013a03481a140c40e81c0392901c035640c8d050b060300c9100000b021110200c502007002c05c06103410501c010702c0110b400c3c8103c0d03c00900c090081c1c00555211041200b800070b915084040328081f604141c0ca04002039142c001450b8807000a8403030120360680020b1803904100103030045510015140300c28200940c0c841c801206141c105007c222450280c122a0314016000001c010700300c04640d6560f4100c540c240181100e040cbc1200c0e541030b0a51013919030840101c20404003080307141d031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 947342158 1250 947340908 947340917
    0x130f06050a050a090f020906011206090e060906151005040302100914100e090709150c120302040e040210030f110d0c0302090d11060d0524120a1403040503030703 71
    0x10402001e40884901800d08040c035032820507020009203c0c174540446958040b610403e050741e5002c016241c803006030b805c110314076282c810b002c16000d0066020340c40703015650085030402d83c1c912030941d6880c01c0c19100500b01901040304102c040c64980041c4076001541d282c06170802e5545d601140c01600c0540c50a0013242c00c5500074040f403030710000840e40a030402c450722a06072640301005031560003607102460081c3c4104001504190203464484010106006201d1010350b04a80c01000300759203400441d240040100e80714082031190007a9003d48101c900000b002c1c0c1c9580c0d003000911409888403406240e00c41c0610b000d89010340c407440a08200c0300406980d903d1904070800129040e190220b01454418003007924244c807410305150460743d109090781172040c3c0400010b4030501620201c030703101c1070806040040e8a61005000740c0101da0452405860440c1c0000300100300343d1125021811b58010142c81c4081800402a415002400301c01d0305d217050b4030361000c0f03400c50703110903016004034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 947343408 1250 947342158 947342161
    0x3020c0108060603240d0c0f060905090f2202120d1106070e0d06140103060b01230a050d09061407080a0506090c0f1201090b1503040812130f0605 64
    0x2541c0080a007584948100d4006185240c81c824000d41540c2c964000510704c00c51030080d07201911502200c80c1d0316904407129840107a07413241c400c580c40300380c0d0080c60b00140d0200000292404d0a00405010310755001035888244d69141c10030420200750042e002880c003c0b80420b2026845403410034070fa001011018080107a0702c0500640300c5070400000391a03651004c0100301016a05ca0802420604106c13082c5035010103500304a03002d042c072100903146140c0458000020802e0399480703000300c04d1082c0c03140224403140303801045117103800603200e031510030301004007050b200d1092008100220140c0070002d0780c280b25464050450b48060b010007280c4000c40e007030041c510307003011141d07038041080700c001e00080c81c1050116004080103401d00d403034104c0110760402040c104005444960a11044045a0f0b680d1000d18501801500410307038000c0c090700a07054a0100000b044034861608200701c01d01e050901d00e10b0390802c402c000c01c001c2124132a0702445000445c48003504040301d000d00382c0858035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 947344658 1250 947343408 947343433
    0x10e310b060304120305090a05060c030f06060702030a0206090612090106091b0903030c0201030603050d09030c060203090a0e1b03040614060a0810050a021e0706060f050d060504110402070302 84
    0x844040c0412944185418410000000c40c0751202c0d4107150b02c03502e0080b449440e1308440074684100400014094068501040300f004041d5020354802c1c071440101d8030360350b1507901c00c1c00f44074030601e407001c6d4064014a00ca400541170602c000d0000190180502c0d1801c4840d203400580c515041e19000c842e41d4640104100002d040c0c002c5031580340c0391420341c10a40001141c040c049011500c402814401c81a820009580c0a948950f0086403c070b801e54407070541840005003409501c0c0807c50305901008404900c291000040d20b00303070003010300002c140301c1c00d081520606c0c0703074010300801000103e004001c40c84895200598021445121b020401c0002c00c0308000c01c4100c0108190302800c0180010840c59034005110317605183c44c0c0b040014592103071150140a40310f81e03800354441b01d9220f0071203451030703001800901c16580034950400c00b1f151a045960003940b11071207015403150700301c202c100104455a00c115007082c82840412010840080450300360b03000008107a015820038a0010f09 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 947345908 1250 947344658 947344661
    0x70807030b18070311010e0a0312090e0717090c04090827060405090403030905010e160e01061e03020706151e180c030e030d05071e020a02010e31 64
    0x1042040d0b000100a808025285540d9400b400e10010f0240702000d848640d442c0d000e2511920030720000307004071101d50785904040c0c0e8841840808600003c6c043d041c0000e1000940803018016030060340c500d04406802d0300400c8400c1b4024085201600400300f0503025030f500c0d8400d040089210303a52031900c40e044600306101000c0c0045210601e020549003a010542e11034040320300b034035011103028045441d0790900f14001c003403401c0001d0880d840c1000b074185203603002802209104285040d10b00407030301c07050680950311080c0318100220b440080c8171200b40840380c50007140f070850707441c0050400c2c40603210281910400f40303030050fa500c09030342e080c03058411b081d0861020001403184034034200d261a91483c00700c601d42031a124040c0d5078250323230701340140b10350811907004d808001183c1d115550128014000d00003940c034400810700c0800001c000d00545201d51110f8962034015000309034441e0010f580160012000c0c5622950031400c40b1a403c1d42039855206161141c4400030408600284810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 947347158 1250 947345908 947345911
    0xb060c160e0115080703050c070b090606271b0f04060503071103070512130806190b10020a241d0c0d0f110a0305060f06030d1e20070807030b 62
    0x103000303400001501c3d981c2500215a00d800125078035000406550300f40c4c03180c800d801190401006203c10074180540920000ba59500420040b2100c0900c3e01442804c0400801448243d048085608000402c0040e40b003202c1c2e280c070203d41c2701d000d10b0640d050f4054510780d0b0107074001d8408580702105116040ea8010700c0c2d001c8445000d40214944041a1101030f9100024602034141400008030240841c2c1300e0300001d00104200c0080302c0705810968040d0040d1154000c51a80f50303450a80f40050074901464601503a03003480d009086030045d1520f460101403194801d45560030000300c1d1101e045051441035280050607082038600401d0750303a8030141010804644107204988062100000c2107044000c80d00c00c0350311111411402180744049400a441d0740c0c40a000390282408000c0743e841d8001c4083c0c0309450031010380311007546010082d10269140c50803050100b031484840030b01d09005260318081d1030a8986144404448004000e180c14a107401000f02600030300010003c2000f19040d4a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 947348408 1250 947347158 947347169
    0xe090f01030b010905090c10020c10120506030a0b2d090c12032703151e0108071a0d092112020f121005040204090605101e030b060c160e01 61
    0x2404241400206e0980c0d9000586417a8032030008584081e03952402005025000c4501400b0200c801c216002e0150021050301c943c0c000090802000070060300d400310b070105102d0b1307010341040c0c503d8030340c0e10564800704400c42720b02110000100c880200500030100c0c0900c5159208000c0910b00d5005040c4580c03404e841629282950051100085140e0100c01a0151020700042c0381180c440540c0002c2c60400303503c2c030814402c89080c0c1071041e402d41420340306188014020b01d90354107907666004a80c0e620390600c202d00800c840c46091418104d44500200008100303024081070704201903d40500781e00304420082c160703c80085040e03840c5034105031003e03480f92060000714201010203480c1c036404d101d210071544a082c400d00000b0282e14031107088902a0901820854841d620303030ba8039500501c12801101e100302d0883d41c8a1080078401d160155880351140112004200c2e07954040e0080c1c150b03105e0156210038207002e44d14012004002d0b62081d40410708101101c80e20f0a50240704003e01a00724 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 947349658 1250 947348408 947348411
    0xf0311060411010e0607120206010f0e010506040e090c0909010209030d0804050c060a12020c031312150c030f0905010614010f14030a021911060703020909040b04030e090f01030b0109 80
    0x100310219030b14400555407000c00303080072904c03045071000190341c0f4401c00d5402032841072014194103800fa40007078800c0c1600c2aa002d40305036580c4034420351600000074414598040c03010030050003c40002e20020760044030520480b81020b038004d000441945040350307014026076010500c16101e03c1c0400a46890243c2e41c10002c3c558101070304c880e52180003c0a241d0301a050006140030500d106007170405502d1560340d021900c594204030103c2c1c99074071129080240900c041c0740801c80074040001030341d01c95480001120308019038203101c00036001c808540c1090503982e440145007c5454090344018a1040c000001d0700c600784541601030100030812241001580d040c07800f00242c001d40b00c001e8000000041c2070301ca65500790047c010780724604505403428034803103010f900350350482168081050041c040e207069640345442102240903d10515030310001000201e00881c84901429400500a280c0030601100440212751201001c0c2c030200401c1c030420004206204540c01d115001d89005e110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 947350908 1250 947349658 947349661
    0x31e09280f0302031504080903120307180e070309060e07090b120d0512280e0d0318141006080703050f1212060f040f1d0106080a15020c07030f031106 66
    0x2190795103050646000c1400a51720104d828001c01c0c030161440700100801702c0310385c01030719602c07285581c10940b018000302c2c041c4003000c42c4401e0055100c0f0203803040002100007d584800307040380900039000e01502e0055a0b4841807031413280503c5018090030030200040f0b440f2010700c1c01d0251488884000d910283c020001c50030b0310a03841400c8500108443d02112012303110001c0000c2800b0030340e590380c0c1092850918200c2410b1058000e5030000035020140e441c5880e8061054003524030441c0403d141c0403440f9850700c0020714480544210b11068804c80d4441d41308880070004441030fa4203c076000d0340c8203880c1041040420801c0485031002140a040d00160000b0028154040d48680c05e10001c20100000d4803138541e04203000d0240001032041c06915589207840004290148800307401109125203485284d005002c1d900844041c1d0008009692094680ca54a110318808605549400308040f035003c0e4404c01885016500540315034800d4401483d003c0c0450250403032b041d206030841c60 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 947352158 1250 947350908 947350913
    0x702010e0607030e0d080d06030b0a0f14010b0a02010b04050c070c0b0a0e040c0201022118060412080702030f0f041d06090708060d051c0818031e09280f03 68
    0x1405815001c00c03da07507101801748180360241d1306000728403243c020726103040d200005004455444a000318240c907000c00c01421a0801c41d0141d5100e4130070005040c0e20380d4010044080341100a09400c0380c90320000800c00108800101174400903900d00c032000201040301410300010b4201c100003041070207945884c0c10782c481c0014062107a8994034078400c564850604a5880c000c0d011900c0900b5072100075440716007000c20a41c400034054034032180300260b01c0510242c00100140250040e50006101c5510f007c00e0b0354215a41400200f5041c114001032042d1102c030b80c0c00c1360190490010120000351100e05210340308041d614021070500101d00c4a50a020325070311040c041c1c036000442c80c46c1c011125034900c00481c4260b62011b100407c944107a950400340c5000341c19018542c50013941e200c50040d2141d0710f210304038500e4500703180441c0e00f081004a20710034004288204480c0c1c6d6804541c24035040382d0026001c00c4134a0b40f229444034613175102d14101003900e40c07120040e09011605050b50b60030368 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 947353408 1250 947352158 947352167
    0x2010e030a020a11040905010507181d060d02010201061e090b01050304112b0b0610080402010f0c0c030614061201270809150d0b0a060e0d0606080609030702010e060703 74
    0xb07110152051368014242c005644031742d000081940d400030021b100a080601004100e6509441c03440c000e092910b0b4085040c00e18405800303840c001c01881b024498032214208020010761900403410b540d40c0300400101c251a240148800c3d00707007840c3d000381540ca080001c109450701d00440c03a040207000c10402c000503041c1d01d01c010340030b8408c2e030705a009030304100c0c5081c0d000024003c5503485c92590185070800c0100405165200d40760558641031505003550003605d222006580007800309599640c000d00742441040744003a010b0103100c04c2064143d507030301e82e4030031141325416108040c221031041005500b45803260004406680c3c001308101125075400004203075904405480600d040a485c906000107403042d03c135455801081d280c01c6907252540792005030b0044034334020490601d818a4038515052140c80102c4440c0e440c2c1001924800040001040e00018100c1d242c80c0e0365400820988800c21485208280038001141d9030242c0340005054485400c03107c61088100f0042c01c000a41e10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 947354658 1250 947353408 947353423
    0x50c01031808030709050405010b13140d02060705010f02180f031c050d1d06010302130b060403020f12010f0b03210d0c0c0609080d0e060708041b09061502010e030a02 73
    0x202004544039160743c60f01715030072800c1d68072031540f00342000000700d40f880d007800c02171031040c0640c41074440c0341e9680c1c000e03d8181c2450901071a032040019043c1000b40c240710b00102300e141d104100024689408515400883e005010740701003c1d294112519001c3c142411701150142084000344032600c01e9040f511041900444610304110001c03440469042c403a4200311080075918140040f40d480034500259214424481a40b10b070345000c1f2a240407500c640301e00721841d140a001e0034685400d54003440031100c840905190890680c400100649400f8491802030304980c10002c140805034104040c5410111010760a00418070150100300b56081c0c1c044802031302038214041940114680180c80b48043d50030050401030030108034004000e0580e00401c03d000f40350108024074405941c580742e803207800726400c43c0070036080c1d00401e0200309a0303034500c040c41c3c142d000c1c0b045116450341d4101c41a11055840050000840e249003040e003a028015050240c00c403000071402c10b4a0300000a5503a00c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 947355908 1250 947354658 947354663
    0x227070513050a080607020d05190302180d050c0109090c051812070b03090d090e1f080a03120b0603060a170102070605160e0405060d151413050c010318 67
    0x10140340003081842040000c0c88001c040c0480c3c00e540700046503c403d0100e0324180140900188039202601403000c3d80e0400403180c4514540c09505c8209034025400615201039030b500410221106035101e4000b03410480c844c80c09070001e000304400151102d90150403103240c480c20544203004090380a01640c00d10700c0724411404246044d040840d42100e4030030550410b03400341040200341c80c80058000d60242480c01c0440d84403c0c5000f408844140650160014400143c80440c8030300011420220f03447c9011000070514980d01d850142c9441d100f15800c90200300c0900602d00000032512819044590640303080e031962904e00c0000b0003030089801184160111030403030701c200d58400d42c15104221303400340b8108040e08001d21400d4010380001c08202c0007070300b018524a01c81c10300c0d02880e030165802403c044034a101554460382c00c81400c0b110108901d540d80d030050840c0ea0240c3da142e00039003045c00d070150301c00c1d501d00342142850361900f4180c0c10f040c00c21143d084801130100081c000182c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 947357158 1250 947355908 947355917
    0x70c2106050f011217040e0708040302070b070803150a0807060906080a0b10050a02010f06330503130312060303181a0306060702031005090c040f0e030922020301030c03022707 77
    0xd400d252100c140d001b00e801801c0c620ba60b041c20064142e8011031401c0c01180039801b120325990f03481c18505034a04c90ba81004080b100207002084245030009005804604001c002d464940e40716000c0da850410203610200c0016443d01c0200961504031703900c59000300352080c0a10018070030340003161000c1206e0103800c04025000030b00c040c1d168802c0d0301001d810300d602c05061002c0f036600c030010380b1015a0400340c0601d498040b44015031080b000e040c0718a07244015201d090560f41e0b80030507503020800244080e8240303c0c011500110b0f1903000c1c460b4401942c840d407a00b40513078402034120758004c0400c0e00001001c0d0103090500f009602d5141c10390740e01c0702e0211040c5540d0b40b52840800c1c280f220302010000050b042a0a001131041d011032405044e11095804011f08908540420250790b081502e03101a90020440e02c011410000740034a810420303c410359140d15074503030b03540c01240e100768030645840c08440c1040c021481c11101e040580c00c5060b28065500310320b2960f03224044d802808060510 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 947358408 1250 947357158 947357183
    0x30a0308060102071e090501050108270a0204092111070311060d0c03051503030a17040f14060405010b180718080712020a08070b0f070c2106050f0112 66
    0x5a10800100c409040210060380700d0320001984a6240c5405d400b0304000d19007403000114055205011543c80ba509001d0140c50000e0080500100340020484600c058068008010701607181d42c00380f030314400d00c41d421640504203038020707411407540d900c01c0300000c2010315004149a0b02001850300283c0342c200400d40441e622020000310341d40310307684455200d1402c000c07100f020190541d006921458082003c0d85001d482541011740360710426101c6c40c003045004114005080003541c000d640284540b648420140440c0c0364620110340382442c8070364603401075040000b044803c1c042c0c1c0c481040141e40e050b040e080301d51556203016800911a000b00810b4880307a9048108121301213000b421048182c4511684500090380e80c180035a2043e402008103800c0020044800602941100e41547c0820704000324503510f02c07520b52000d2819501c552034070b980401c058401c80f043c074111101001901c000f01c480c80c075105068800c001d26803d50394002500400540c0d4a807504803c0440c0d001d21504c6d0782 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 947359658 1250 947358408 947358421
    0x80706020714040f0924060f09020d110c0715031a040f06030c0f0501030501050307141e0411030115030e060105120f061e010801050412050d090203060c0a09090b030a0308 75
    0x10028054980d8819041c100d8075400d0290140102017820754160795071074000e11b110702d003400783e07100c3d880703914450f084903903082010440c15406030203800c8601101042c01003c8400c41c05068100241c8402c19070840801023012401d4a241c810faa00306130b081c2405a0703030030460700300324240511030b1560040c3d495008035002d82c51141d00075805581c4c0035081070310321038607030710000589403032409803502080ca090f002240c14540000e80104480e840c032038400c101c1400c50300b030041d844003080c81d1610408021a5892003a5941e004200700d000406500303030385a41c5081845146566001c182d50300341480d2840040400360049030080c1950820f4840803480c08420350303201d14005458038483e40f107018080c20b00041079024180c824824900d4000048980d8854400c103080712415103000302f02401980c0c080c0b254601804c043c00d1002081030001810030240d401083c18500100c4010300031110000f00d05a9079500600684050700840304100890078000380803e998007104c403c068144a04900010503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 947360908 1250 947359658 947359661
    0x20d02060717270a09020f0d110706050c09010906080c040b04080d0207080f1b060d050a0e07150207050411130609051c020d0f0c090e0a060608070602071404 69
    0x581030b0b1158a1918164689440c04559040403002103e8141610803194442c00142a0080860401010000502e162190f010025030100604503010b07401440284484680b52150303c080d2031828007a41e944100d5460030740c3c02c448009140700d007504000e1001000f0340c1d911800041c1680c0080c1802c0d440c2ea11002e41500550240d9802410104d40c0042c011840306004180080b180055030202c408082c1c540346826100d801100c03150b045680b0010481e01c8500b0010b11811405502401042c6030092524071403040e240700f00d0f0340600e8980c13170300408900f5007810055a401400c890303003d000c010103550402500c03225507114240c420750321025200d020800c064201c1c1e20544200c000d4050f2503071380c0d03c0c0103008001c01b40b14251003482c41c0150740300c0c1d903100140820315541c1d004082c0c42d600b009658450210480c0b9034810344d255440c00c080440c00760748500c03c84100124000040c0700348034451400c0d0095030b507103800c02003058008900811626070000f400c481034401007200040d000000390007280 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 947362158 1250 947360908 947360917
    0x90302241302030127050c0102011b080a23041703070e010c0c09051305300a03142a09031e0a02030d05182d01181d0901050c0304020d0206 61
    0x113a91140038109005e40340e80b08045110401e01c2a0140d4a0622455005908880070080000c0c1d110501c0d0740d44080f038a100389000b90f40219501000a5030303010020000690707003044c0b403802c1c0e03903c5d03440000d00c02071200742005200c00e10285000107296180800c801005120300b11260703030520103000c03410410003180340103107000b41228036400c01c881d2409100d14482c5006404060380c4e14000c0c15200e820035039803c04500406400800c0c050b03803900c0c50310802c9095620a4021004050b030780d22016402500c0c00d842507005070603c1c064282d0352031130026043c1d5a82d9003600d0b0a01110b4080184002c29200411078000c2e1140071960251003940504000703060501001f0b000390706000c0c848100111542200140081040c50030b0100800440754080c00b0000030308042d072403141c2d408890804401c248806549012040600d4a00c4070348082e0903c010002c006500085d0350200060081000c03040c5d2a0300b2107a0180b0b5400082c095070520303031a48101844003402c0640980c403031044023415510b800b002c68 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 947363408 1250 947362158 947362181
    0x110a020f1c0c030e120105061c020d170d050a0209040e06011d04080c121201061704151e060915030809040b0103061d0f0115051225030903022413020301 67
    0x40014005c0390581c0c1c0c001c00044076010310410f20714000101c0c1d81c1e80a9401d1070010f502038403c0880e0000c60700c0b40e0005540700e00d440460303003204003e810035020450040e94000d4006aa0242e21404103008110a69815640202255204038010032589034140001038040020802c00c81071526a41001b000d01d00c00ca2103d0541c07440b4454581d0382986d070100081810540c0e01080761907690301c540e0100c5510b0044151b2068054041000c14007194800400d03101c0384070590303400611034858039007580002070485031805c5101d0b66107400b04100300c06400358080000035428010301080c21551045500d0081c5045030780690765442c3c242101c0d0740a503003c1400f902214040a002107150351200403001c40407126040c125802100020382040303a5140842102c085489003400c0041912200010b18030042c407030384070a80184100056078a000308101050302e001e50300840c04020300c0c03c02900d081480712101c03042250080000450b004035154607604542494251207101406000003405001d01d280103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 947364658 1250 947363408 947363419
    0xc040f0b1c14090f2d0120030f0c070510050711010903080108120f041802041a0d0f0e0d1214091623010e0a0b16050c0d120c030c0501110a020f1c0c030e 67
    0x4a1400c0010700d01961207882070140151035030381d80c0b42b2030307079032034015180010025800f07a03070700d00c18846158003c40d0b40988185007100c0300311043c510380c0d800d407081d00d0420740c0450083d90050043c140180100c0403240c3c043c02d060f9160096541c40208a80304500c10401c1c0c1001820011400c08440c0d0115002464424400e80c5890403410358500315034802407091501c40d1801c1c84001c948000341c01840e02030b8070414058840ca8042d0003095178100f1900000150496455008128034596554914091441d41001340050000c658007074001420700d820000c51100e4018091911000d0041500400002882c21180025003400854801c5800da0001c3c4c0d5800320110700400c200c00880348904d0207a0140e003c03146800c1d58842881100f4913184d001800b02d42201c624a00035500500300c80380e030350703200b45480051032400d52140f608445100c20340140c151000140078860b554100303d480c08019010300940048412010002e200600d9103e5540c18070203d40e03107040038540103a500100380da10103080c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 947365908 1250 947364658 947364701
    0x60e090a02280b13080c0103060e0c070c030f080a1106060a0303030c0e0a1e09050606070f171201063b030f0f07030b0c040f0b1c14090f2d01 62
    0x130080490f42e140d000b445110f2245c0380210b40103601c680180c07012204001060400e5440b81e904070042a4008a8240e5038003c41400000008050010340240c250103880019200c041040c0b00034840d0110804400b000e40c000c60900009d5030710b001103a402c0701c0d810700300082c580c11030440941e03000010408941c0d000f481680005580d507101441201b4003400c3c0311080390007076141e078040310840d80d0503104680c00200900200c4c00180d02ca01c4d207038040741d0003251070011508140c40041e003268002840110184540001000a1078202f071781e8011000d0640c14454114000003071003843c1d0700c2081c3d4800311621001030608240e480038003074801130306510006c4e1035004903400c181c3c1d95208654881203031069015030001d21501c0540c000e88068400613200307042c03418641408041c942d00b1001960380120403442e0300d100204885e103c0c241c0c0b00c1c841050442c009192058a282c1000c110030000c0030190031421000070b0b51400e00e82042d0f44a480c51014411820725804802d0040400c8182d0324440d549009 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 947367158 1250 947365908 947365927
    0x50d031a100e1f0206011203030908070f0c050603040f0b0411060c01020711040509030a232a010c0215190e070e070935030409060e090a02280b 63
    0x2070a42c0300610066400080c0007861050001d400e4100321810001600a41c005111081e117115650815601a150214442d151511825028ac0c0180c0088400f1180225440100103407105035400400c408c5680504510b000e44071a6860210503000410310561030300024108101084020620800605900d1f265040313281006d000b98030108041d41c80d502d2880303a0702e03030518240c0500f62003081d8450186003841e5020400f07035044401c0b11840544075401c08111303803c100d4014080c142208500c03a02c1105401208110141180403072502c3d03e86034102440f5040154000509401c1084100300d40a055038440c0d0b000c4400030f041d41240001e0604001c1c400c841c1410000311070040d900d12003010009619411800c0d0342501080c81000080c11702401c0004400038000140c18401001581003001144262501400c540c482c1e0444940b5556071001801200000d07560168025010401050102010340010755180111103104038980c2c0c0001210b0080c01a18038102c005181a0941c40d07100e1002c030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 947368408 1250 947367158 947367167
    0x1206010b07020102060a05070f0c1e0c030201270b07030e1801080d0f232b230c09131407080901050f0606030601020f0a0602090a12050d031a10 63
    0x48009034014420000446d2485074a889441d00450240c0c9442090944034501510154040d04090f504c1e40ca0780a682d00c0303520440e045000501e845204440003c90a601c0003600c0c00780717111042d200e440e1881d41d00d0442128401c203d01c00380c0d02c4071075400e615040180303021a00c1018403200700ba0000d41801710042e2050401d00741c24181c0f5140c6058401c4101c0c0703860100d40705201c0795070250004e208041c1c1040748604d2103641089819003558281e00c1c24072000c2c6400074501000380001c00703030003450300300391600f60651040840f450050b5074052000d0f100310341411031541020f451980ea0010000d440308081d500c5e00c1018003824814041407061a603a42075000a0050884c3c80b5008a00d1001c0020b2030643c042c0f065030300c15000d09009d107a45485200601915810041c0310506610640044040301542080540845481048096540e84000003031180c21596030380400d40e11400c5840003000a003010a0680450340b1601c0c00190b5540a20405021000c0748c03905950043c44075458010040d901 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 947369658 1250 947368408 947368417
    0x3080f0408150c0901030f1805060a060602030906070b090106050d05010b040605090906040b09190b010f060c0b0a0c0c0804241d010c0206040b03180c1009060507021206010b 76
    0x36002d40c2d21a101c4082080c0005204440a070600c060030000e814456000750720681c45803d6400000541c04044d00403030300c0c2c04100320f1054409034131842c20807a40082500440024010038400b0b142410542400300c1c10b0380c0910031009094511003800591070080c2584400024800180203000020090a210303000384654070006001c2c90400602103114100010a940100c84110051401ea52651205603411070003410269940c010340c03811194842c80290f0010100f40666107100e59075241940302c510300c3c0c556030302810130300540314203407804a421034143d036074882d0600030041481c0008400440f008003480300c000740b680c4404680890b011030905024a8158003904001c56a0311207000f0035590701e803406001d0511090b0312074940350fa82d40f01d6030f02c114031248054059400c268460000200c0b0350000c03210810035820301c16034000100d800300041491144143c4003840d00650301d620080c40603201c0d0150710300b0301c000001d40b04115194038441607881017401040d1041542c450110703030700c140e10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 947370908 1250 947369658 947369669
    0x2b03090e010509100b0d060e0903130815180106031e060b0108090c040f1401120c090507230d09050c0a0b1603030b0117010807180c0903031803080f04 66
    0x104800041024200400f070a401408040c03080500c0d40e26004240c451341e0b1240c81e46810264440388001070102030200c5280c044e0480c40051070b100c0c03450007518040365615500a050950200445075903990380c2001c455000f001e115404080c0071411600c060141c07003594030040080148201e2081c80b1500f003580020304034402d8070107003c2c003801d140c011038503a0019681030055400c071858004161501d83d100460440c2001c4000c503a80322400d0710200d60b40426407001181e40040f801044c01c001040e00820090064200104564101203800071301c5000e940301c00c1d00800c100b403250a10650048401d83c4c2070207081410a108080051902c01d4907140c0b03403900180105480384000c203400c0318010940d22070320b00e1800390604e0b0911503103085026190086005040c80b10111808005c10718220515018001941c01400082c2c6850b1038981a41c6580e0a014001c61410b0440e505642d0f0040d52603089940500d0720107401402c3c1302804190400a9000a1860030300180c00c0740e00c41f2009026004440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 947372158 1250 947370908 947370929
    0x80307080a0e01020a022214010306090201020f1b0f0105070f060c0305060409051c23190c03080714040b0c010501150e092e0605120105010905030c2b0309 68
    0xd0b42c800160307501c41c4010380003540300c01402d0064910400b4003411404051440c5000b28000014410b10034501d01c2c2a002503d101b07455082140075541c0401134800da6485050007002603d0f0059460400c2d11480c0c205240300c0c1c0200d00034049a60f1240083e140f04603049004d2102c044101d14100000740454560725001c039007411b00058003480c181c450b00501e40d40040141000400b06a100c03009010008440300a0200b013402c42800c0a14401d018600740061171350b0295540c078a0350202c4480d2500008800800000315140000a98004500740c0c2101090070032500003054211008440e00446d08038002c20740001c5070310009981c0540080307040362440c1d4135440c2c1c00d0f06442c2045620222401c55660864444404030b1840010a843c442c2c2214410005060460505511700c405144035071202d00003850200c0c88030090030044d2401c030700400090800c0b007419807038a2b01080e1a80e0080002900c602c0300e040039003a400924111420051008215440d00300101c1e140141c40803070079005504020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 947373408 1250 947372158 947372177
    0x605040f0218030c0307180e0f15010e150f150c07060908010e0705100302040503030a36061209050a1a0c0a020604060c0c02030109030302090f0301020f07020415080307080a 76
    0x83c1404590030b0722496002e8080c150050522010000c24803084100d0b0858554030041c1c00780c015001c0c031441008064000290041120720011085680d00607000348076440c0b010301c00d11650a03402403407440d80c50b90a03100b6400c0d000740c10002035105551421000340c485800100c500c19400d000c03400c1d03402c0d00c2c10b640700c103140302d0780b100780d07030307400c0302c0001900289950180000388190b203131850704102080c001b40b40161070320303486501090558000504d0100840c00900c445903454000410a55028400c0300f02c119221034a084c05000c060343c24440c100510480400c1c02d54203940a0b0024401144c00c1030890317800800780d152010302d0090f411180a03564401e1400b16a001c0190030480b0040d000380d40c014201512103854440c000d0100380c05010602c050032500c0c9005850038019100c20324080d44005860741c940b1010300c020b49407800b21941c0300c0d1344100180d49221505070182e510383e64050300c0c00541c0c0c80d001c040c01441404503400101d400e00c0081605002c03c00341070020185485941e4441094 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 947374658 1250 947373408 947373457
    0x15070f060632010c02060d0c030605100f0804030e040b0d0804060201050708040c0b0a1e08100b070206040311041e0f0b09011d040c090e0f060105010509060706050405010605040f02 79
    0x10b24808441c0100851218011854158451001451000d00040c4501e01e481c5a99003890201d41130762620401294580c24100030302e191070741c441c400106660610074131150003020010220480144020709210100b1642c0c402a00c07160320a00d041d21014250b80d00310486802c10304403640240c42040015030030b2000198109120380fa00500550b0b01841400900c0e050030700c48801a0010705841003046201a52800031f1f0060300344034460381c181c1c1c0c3c0f614061800c0500401d254904550030191035007030100710880058a070442181d040b280c000c2201488680c10000040190200740b4440d00c42c1c0c0d200120500268450754040300e8546800c1104214009142061100c500400d200b03c110446103407509588141404118681c07051003403c030388842a840711000002c88142c4e0400c4103c03070307111000415590070b0810100340035141c2400e045003003c020ba40010b00c503100c1d407440100899112800710341082000d401c80da001c0d02004105005000965410174001e400a250000c0560f4484111034071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 947375908 1250 947374658 947374709
    0x303180609120f050316060e071e0e06060702090c0307121103070806190f031b080304170f0d0e030d0c1e0528030807110c15070f0606 59
    0x202c0b8400c50440e40001d6854403102d1080148400c1554140400c209040d42d40318110210301d00306c4e10404000810782c0c900f140a074a0030f00c4580100704a900c007034055422a000b0500310b10100e4030706018510351a07540c01c0200d102801070980094000e2920030a004060300b0180281d03104501d66990502d94015000c4200c003a503100001c2e0309031002082000c40d08642c40396070520f030f0002014000400307540726030400182000150b0700c8041d07500a00d09040c800c1000c1c2c10040307007907111014003503d0004d0410358030076107a108510801002d80c1c00096607150300407050000c800009455400d03950090280352024060b000c15000c4284240100700410040b24050070301c80342d22035040041142c04004455640f440c05015400584041c4140d8481d1020301d0b000c070ba2290b00316241c40007011f001d12a03501c2d010340005805070070042882079111346180105030014614080754811034001050100300c000e01001d9104031303100601070480c003800c580180304940d0401021a0170680a0350030030b0549695900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 947377158 1250 947375908 947375927
    0x2407061145191d01150509060d0b180f1803070b2212031b030203091b18150108071b121b05010606080901060b1c06081009031d090712021303031806 65
    0x140c1c45401404200b024001c00d074808040c1590141c10407000d880f5240bc40f4058541c112280d14060071203004100d000b40181e112400480c05d0f1000641c20801c0c1c030b40d40c0d030300b0385100200781d413000320305444001d002001d0004803040c0321608092168548034029000801418090010164800011403803c002070300c03072700c02c6900c10395088001d809090580e15450b01314044507002d6542c885060142a003900d1030241210340035850412080c040c0317000d40400580441d03001030000090142181803d01d85e0041c201803c0100c07540a20343c05180301144c003050304c0b6044401042e0f409218241c114030300b0048150f00803400c1e10030390345030403265680e024120340c00c1c3c03810382c010200c44c24028041450a41d86440c4c2100d803192448002041071130715050f80324681449041044a0140c0352006182410f4001242102c00c028083d030601d034410143e4003044501c2e801800c88000c01102507110301403501d0550641d0003170b004e0b01c02080883c0e5a282401014082000031200c6078041062001031010302441130b51 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 947378408 1250 947377158 947377177
    0x5070813030807030c021204060513090501030c1a1911060114010207090f091a0f070f0e0d050c090a0e0c2407061145191d011505 57
    0xc0340b03030b9641c01ea0403405000e403c0701d407500b580709000c4608250071058000e8000b5110581e9055181c031600076544602d238030240d1101440d2441c1100500c003182040c403500f4150703024108103000103e800100662a4420b0b55003000806030103c0c0d0b01850f085c3d008007040990640030f42161071598803490008440f03030741a05940c1c09a800854104049086600041036a124402c4006224207047d156011070f40b0f0020b00c1d0a50140ba08003c02c54106101c600c0c03240c200e1118582003d80002000019041c604c0c0320403200d1003268116510b104011303041108580d2680c02600d4815075051203850100030303010300d41040b6205e009201c0c000180741001c07280d00ea40031103e400750b841e072060505c078112100c0d4072400040d2195921018503003100140c0c40e005001d8182800c0660049040104041c00301080c0ca81e107405201e886581c03070602041c44c800d110004000202c0700e281103110800c800300f002070001d6104103000c01a103000c014000b04c40a01042c12521041160340c03141d4040d1004681034402c00c0713400e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 947379658 1250 947378408 947378417
    0x3030a050a050a1b0f090e070f120501060c0602030901231006110606060304150c0c020a0902031905070e150d0c050307050703080705160624030209180307020a090507081303 76
    0x1003204ca441440070a407010154100a90f2140e01e4100ca03105880d0211030000c085614020f880c0130440d48124803640d00b640c0070300204019410510001c1100105043c050405500440030400325413007075100c500e040720243d041d903252038201596020340c0742c8101c0e84c3c1485001d041c2c0e000164580a9811040103801c010090300480d910310080041c01d803c052306c103442101c1138110304680e205461158081c00c0501d500d99a0301a001d43c03041003800102500303e80c0e8428018024000c18000d1944035000340c1840070404942950707458000c031070058012580303a03801185808014040c3c2489001840c0b00e051104050141c400e050a0540d940c0c80b0a40f020000a64104581e0010a20500e81c0c039030052801d00d046031078601040c4207040103c041f904103680040ea5545c5a400309404c0704c01d40e111518074079140f4941c072861a00000c014100040030041030303000190709011501c806000300e4810304e50007040140e105449410040c0242412101000810300c0d600102c3d01903c4608408020300c0d600d940c9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 947380908 1250 947379658 947379701
    0xe0103111c020f070c0308040801061706060d050c04180c0e0105010f0c050a08030106051b06011203030f0605041803030e0102030411100903020301020a050a3203040f0503030a050a050a 81
    0x41e0007000307502080040c20748030400e101c07010015040110071002140188855a102c60410250908442140d8040b41b41210454031a9201e4000030500560160044175030240040c520700700395040c454002c2106170720501c2d0502e03044040c0e14003411103c80a0040488035407003030710b0700001d40c1d4407442809554007140c004690890b01341d2117410b155502c42c3c4128280c031060121503880304a20781080c0c220401062000c5440c40d00e00309559480f1405a004400401c89035240541b4040900320910010f0105038030f0307005941c0f50b0b9a09410490003404098400c00000980d42003800c1c0441c074145080300000c1c1003160900e450034050007564000c80e00100c000b50b840c510b2600b003000c3d0124034410041801404500000560350a1000d080025810344942c1ea48507020540103000d0654640107a25a0300e03103d0070b030a090f5109141d446915412082015905e0f00c85007404500e6080082008081d403100100300701e4880b8054220030f000b11a032031400c2c081916a2a0424142ca1408491041c0c40403002c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 947382158 1250 947380908 947380957
    0xb0a060522030803010902030f1f1701060f1413110d020c0c030f030d0c050c030f0c16060519170f06040f02161b080c06070c080d0e010311 61
    0x41a0140800404034050301c5594a03501d0a0242d0000d030701c100c10040d13000c010805029031900440d5802036810440100304002c904004c4400c2d0300714010180860003880809864001c02d5018078040d201d140d21048181c0c0d42e0b0300c424401e40031040140c0d801804283d00c003006104c5075000310b03001005050350701801c0c60041d20b00c2e40000d400103071440c2c0c030911444694850a40707060180103070f00c00340400515516601810014159014900c0d01810407500300204603028502109031503030030280e43c2071070744c1c0c07082d001201a00e4040c502c40c0504a090401e0000a02d0941180003040c1c0044954a8001e00788041d600666580c2074620b045032194030300300d0010f1405030f0b608260760f40c800e00c0200f0009410010a0015040f41c108100c03035000b00000078002c405020788100030101100e00100ca02d0101c07810202d03201d0700e424141000c24010b40e000300e03a002c10044890680c0002d0000002100d0032541801c00041c8070a500c04910790210349861403a0018000b84411100d0302107402086403041c0340d205 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 947383408 1250 947382158 947382187
    0x1205031909020a1e03110f15070c0b0a0c060b042c1e03040f170d08091c021b0402041508040609080a0f03151211130c02100b0a0605 58
    0x6010480c0d00c81038090000c54040070641c4002071030310305a00c0c4d841a041c00d40c580680708682480b0280e00ca44107244201e00070f03680b0802c10b844460340304548030b034403150b0070705c0d155413a5401170b04866465040402d00c0c015141d446800d4044460281006010001414042c001244c041128a035002442080d40c84c1082800c41c100812070900141240c104800d000e09041c80c1c0700461003a05080d40000034208180c0640400007405400600c200a112a09842105a5a606070110a01131207a03010000f603440c0c0382070001e075208444001481503449000c2500944411140b45d82d07001140c0000080074090a203882900e05071520403d03080c5001010b0394068665170402002143c01a0b00d4a0741c03440043c3e07801c1c0c05801c40b05015101c0c00d0260302c1c1880e0281c1561400450700c188014859803c010382d0720b181d050865000d40000c8041842000c4101141c0d058210407125a020350510440c003890944c005510481ca049480c01000701182500800c110003100c0d10880740050350910900c150b20006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 947384658 1250 947383408 947383421
    0x20904060221010f180c30020304030903142d070b071209170304180e01060e01080f060c090108070c0615033509030a020d05030712050319 61
    0xb00400d201d510145540040268402600000e40050194904000220f40c40002003902c0d05031034428088144d10710001003025140326491401102c001c02480a1301c0030300d070600c007002d401500c0706654900c1d21b03040181407131400f440300320341c444001d86182c0003400c0c0c085170301c103006c003089403000500640c1e034002c6129181c2403481024050003160000640d8400c1180140a15032040040008058070b072040500a80042c1c1c1c4039218030345940b00b80018845000c0110b9098070150401e00384204027800b01c0e0001085c00d810715403142d42c80c040002c2050f400d46080c0710704a034160000c461904000b002041e85800b4180c0780811100320501070120250b004045a0303611a000d840d280e014405144c03118010385020f00c026091000651405200b400001814a06543c0304500100400302c1c09900004114228035800c41d5900b80205400076195000c3c03025002c89900140118048010360600548990041c030702261aa40c4400424800714000da054030300c10b11501c10070780c00c00c44841e500309008c0e040b07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 947385908 1250 947384658 947384677
    0x190216060c0e0a080d0f0203030403020a03050708090405090f011b0207050909030f070605060f0f061903110f0d0f060f150c0c08060a0e030f090d06090c030506070801050d0209040602 80
    0x8602480492501ca844043c40101901402406441c10320740001d0500303040c40c0e08880854104004120110750002808480c00b5414a044d86c0d480c03c40b41030a80c01809000040f650203070422041c0007200000150b203000349101200200a11b4450380e0360410022203890601000d40c000f500c04012900d090310455922030301e02020f0307030301d005404820704c181c90340440d90454a113a070344e0703051140d5402c05150680d100722040c0c640491000c4207000199042c000c3d10044c1c0221a02500e910108502c260020f0010300300d440100385e02c4610b4000410108c0d04602405130710146031841c07800713402d107041c014002100c0c3c1404000c0075550400507400c0344001040b0140703061100d1030788070300002100071401c440209040d401800c0e8a0600400c2070003925502803012105602c180034411500640c90201e6100120071078036000b2080d02071900d440a4699548003a282181c05000041481804240244a26496a0b03008a50b81c0c1741c0b01080b4401c400b14402a4002341d000b000a400940f41c0d50080c84141c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 947387158 1250 947385908 947385917
    0x1608090906011b0b09280506090d171b0c0a0b0f0f06010804170301061d010c050304091a060c03040501090e0106140307120504080c070801021215010c05070e190216060c 74
    0x58150441c0b0620082a03051a01b401c58118210b2050003000c2c00966040304910003d00f4414411000042090107001400000e1640000110b80c808a90300030201012020000040d221a40c121820341ca40841403000c6c1c1e5003500a000045a8200c1681c1c1c0900c9091050482c0840b038885000454982c3c900410459072580e47c0314181c4018811074014500a0000d82d540142c881c100c09019000341420f801928188440424501c00003100841620281c030011200014189003034190044100303100009190444000202104081b501100400680e04203072680440b00e5078802400a002400f4443c14000408080c000c942400000e4021600803105280c151000d500804c450412104107a0b000c031412400002d0510914405001c01c100400d0400002c504051051941d00c061000c01080600c002a0076502030199078092000c0d00500b60300001282c4060761905844400044191602803d10a80810483c41034504d0b000301d400b07175400c40038121215000da9580784003134000c0b105880c0901 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 947388408 1250 947387158 947387173
    0x30504080403080313061b0e030303060d110f04090b0105040e031908040809040e0c15160b0c12010f09150522020405100302030a0e0c0904030f02031608090906011b0b09 74
    0x6d00540544907283c5124a165400000ca0340400b41002d08030445960007600103000308030003507690050380403400e90411401c0701f000080b20005031401007506142076000e0300d4440b0810900c890b40410034180e401c1a0b604101c410340c0c0e80c60703059490260341d4107a41c034415a401051600c601c50000743c1d81003445442d800d42000040340002e03040e542c0d07511442c2c0240d441341c0b12414540c0f504021103c00365000390b4605142c4401c07611280c0383e01c180700802800b11051600402c07180c5444d0740440314010350800114506c0d586960010302040034900c1580c4d151030a2850b081c80ea42428511749080b80c50040001d045000b442450030300041c0c4403e00ea54040f6403d01c00010f890701c03560700c3d4000320912a0b400680d00e03c1c01c0020141150010241195030740d1103803403c45815224000c4158000c0c0d0942041d080801424500324038604c1140703449504030301846983d1040003044005042484800c42d000d651503950000110360301d0489148c8280c141d0000d1140b6030224a080310440d4100301c460042c1c0310f61 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 947389658 1250 947388408 947388413
    0x3120306120f03030b01092102120601030b150a0f090905010f0e030901090b09060703140409090b060102060a1e0905010f0903080f0f0105150904140a02040f06030504080403080313 79
    0x706162a4010340e036181042486a04240c1e040c821090b01c1607003420301e0b100c15400d00c0d24418140051035182d40d04020090602415540d03001d8050721001007040444006c1c1d030b103074070b000d0580c0d11041d1801604400914880f050525040d820001030313410340426026082d00c0e201c0c640e0040d0103042d41c01c2d00d0a55942218440003121401146418080f60000395660340000d00010020300056101e86c460701c0e014041080c40390359200890700e02681620300500310b0588003100c7c15651003260322502031280703032103144002c10014000c8a031103040240c080d00d01a07564141c12006540d00743d2407000401011a86828100065500010680740210000900445c06800c00d00880340c00c408164082102801040203094043d40e00380e070b020b0802d4400fa2900d51401010801c3c03041c03040546d038a0a84042005180c54403164407814109181034411741407801c1070310b88a0001d50150041e00a008005c0c0404030340c09029000300340c040c0e640710340c400e441e0620b5511100d81c240c2016010340800001c03109440b01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 947390908 1250 947389658 947389679
    0xc200d0506070806010f0908120708040b040305010618050f2e0905040606051005030a02072d032703150b030303040302010b1008042303091c0605091603120306 70
    0x1060b11583c4501c210750a1010016140c1008083c61004206500c4400d22207902d0201c2c1444084014620003a03c50ba040d1030190010701460304500815a40418004140441504003d04464070502940060444140040240c5108842c01c07440c0e4488140800d894118040c0c602411580b2a103d113400c0080241c1c00b1080e40b0b2196000c10012508ca00c244024084e0138454100200003c968a00188514500141c0316000003017192039419808208507060080e100c020000e0740030074041502c0e012444246241921007040c509400103542c03030f20304000700c440c0540130b0000b2442164484400c1ea01e5a6207034202811503040b09401c880d01c03000784020b10b88007040550f018034881d4001007600124542404054140a460f100400410788140f20200c1e04011141d14413103180080c0000c884103da64140c5140b117000303001034000d06103110780f6202480030501c07003006512900007401039031141180195101c5104440c9501c0703c032000347c1000003680000a080504685080c08110070790b03202c000da217 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 947392158 1250 947390908 947390911
    0x18011b4e21140a050906010b03060409060f0f051b0d0f020c0109120f020721050114011404061d060603092b12091203020f0405040e030c0d0c200d0506 66
    0x2074468840005091441c06071120310750201100108110034a490a60550b0302c1c4010311441e0400500000030440c140c0b203540100078180d810003030070b0020305040c2d003807140100b9005c040752804610b842c1c08a113501442c140340c0115405000d800600380300d200c14580c0010807d281c26840308540c02c00807030750300301c4081c015460340da030084a600c0207a10b0403440182030100c4e400705610440d00040c40602142e510207203130b440640341e450207014179440709292030703801421154a5201845150400060581015a280ca640c0d0350150b40900106a5500301082070200c420203441030305001d0030004002d03007010409581e200d1b00340b10840d120004421140307110070341c50904210054103220b41c0d0400b0036070042c44980c3c1c4100040000c000707069050325841440112201c20008054001404240014000d82542c000e0b10000700f080044000604441d99254041151103a250041d00051588a4091404005400e41100380c100f40c00842c82140e4800c0c400041010358040c182c800543d000c18410440715 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 947393408 1250 947392158 947392217
    0xc210d0302070512120103030509370f080705041e0c0203030609072f011d030c01050c0403030804080306040f020a030b1f0518011b4e 59
    0x503503a01c49400c1484c200003a41602e83c001d11420400c3c40d040e01c8000b000c03241140d40601e4141d0b268009100000c01c40d8961000014000d40c5d0341e944082950550611004000070040c121040203644000301c0151a48078841c0c0c80840e08180c004000908141d000001c07242d0b0684501d5802c0e02186000800320307003024082000580c000300c1000100d040070200150000d205050621020001001c2e8002640e01c074a41c200702800b0803003002940450075041510481407038091042c1400c0b01100300e6940b0313001001040a0b940c20a4003203400c0e20500741c12142500d03090707540c5203420340e9540c0311712072242c0c00500300581040d03481b04614040080391024182d154042d41d0041000c030140c008104440c08600b030301420f01120501850101c40c4c0001c100c0d082560b01c9101c11021001800051b24000420480c51192540120301c0000300502031081400004075040c54490344131115a034110740c0050500c840540308118200700800d2260240c440340b10151600d842451010b64a6990340e4000580c03414 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 947394658 1250 947393408 947393411
    0x921030c02090f0103150203060607060b0103020903010c0509030d08010b0d0915020417010605103e0604120203030403090e09010915090203060f070e0108100504021b0c0102070303020c210d03 84
    0x140300b000008903d2446d10a41c0707410950070f500304540000e285111f03003c070003401c0a6a5503d07041c2d1590094040d5901e0a41c010020043d03092140750290940d400140040e03c031780164071070520014015168541a5036401110034103008a40804100808541800350359a100000340c01000c42d400c0d000820251102c0080405407412000c8070500f5162070750002c0744a007030440740700e40c0381b01e41c0304e540e80060801d80d00707031128040e00391820401c2103500308403081070380c14640e4201c40300d0020010b440d5010720f125041d8401c04003c6c544080382c4900050f14001e0004104a50400c102c0301c500d058640c02910007800041e000e20980d41e180c500120900d101140c268407520840c040d40360601c00160f02450301080f0b040c2c40d103855400140a0b0712603800440c180410f46001c1001c00c00307d550b00002034800500110b640703402100d154013072104d01c0c8a90b0303641d83c4188140c1d00030340d501c0429448111399242e00203105020340141040f43d000c884a5460007240c44080c6000c0c0720f0301c805c10880d0075010281d02c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 947395908 1250 947394658 947394661
    0x721030609150501141305060d1d0d080c07110409030210060501090506091504080a0602090a080a0b0a020f130f0302010216152a0b160921030c02090f 66
    0x3060429680000360300300c48207160b0441040a070340c02c07108200d1441c41102140343d0303c60080f510603800410b42d030080742c0c210303001250310081e11900da40f0100030709a1038a4410001c020701030b0700c50303a83e08070148528005000b50b03010170240040000900055445912030400c00000000440c048503503105040d0b0069001e2050443c070440c1c0381c4070b202e014280a20700b2001c51420080412401d21400318203a00600d1100c8480803d1a00ba5007580c0203420b12000303951181c403290074040b0180d00040091403250391818800580340e000011218000b82d07025264088940d12001020002c1d00300f802d020358550800c008484004080e03115840103008800c401d14000303801c50000a1030090011081c000d1507076205010320a000e00107880201f500824980456105880e50203056010500c40785c2d03550040c0c103e00322008120719600034911607603002c0081c0391141c07401c1138100c0e01420903120324588044d1308100b80715500b54455240080e1802424a00c42209103035004c41c0100702c04841094000c3c60420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 947397158 1250 947395908 947395919
    0x4050403181e031e0c0e370f06050a0b0c060c1e03060307030204090f0201080f06130510030b0705030a0509120f0901031e091109071407210306 63
    0x20403035805016075076225010a100900702c801e40c562240005084180c5420501d0a45510014a1968180c1c040b04003401c0540e079500302200b400c0c1c00d0312155540711b101d030300209485840c0c2a01c141c000a115044000386a401c0c0007a1006017052a250800d441d200e070b00114080d1126030410008041c0e0801e100c1c0d440041d00085410250b0107440c4a404400800c296566550700348000162284004880c0d6900d48030708000901e40760072130344020742250070401500c0c01d12040b810048005ca000b81c031103008954640418043c5040112551a80858400c11500c2018226482240d10258140b2549d14494030b0381c42d102e5114a00300d0301600040c800100f00181d5032118011145c000e9008401010032612081c0e0340c90081c010403d10016440d800b00d290780043c3e200c0d4020365046017940d031444000340361041408001d803807a400300740d034020340308000301c901820081c012341c5c450751141d075403c0c840003541070070075459601014099580499100d0010103004d9010031000803018552000104035182c031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 947398408 1250 947397158 947397197
    0x612030e030727020405090a0f050f042102212d070303270302070618080703081e1303030f0203072301090b040c1703040f0902071104050403 62
    0x80514000d41122008001c1c41d4200600001084491010229110031540b00b0f900203024503440160302031108000c0c4141411990702154018001c0082031050b592000e454a50104003900c004180d4411106084218441640c1d6400d002d1030910540c0d80020700a004070808882012a06081d82c00004903480705031030207082031806040035121000d60080300121541c0768000c51001400b41615030281c82c01101e40801d05400c030920400d070b240600d412383d08009542e5003450045501042c2d20041c45401600d10105480459044070000e1a24030f003941d0b40c0d00c185801c0320242c03041001428060105e220058000f5001009400114104640c45c40c1801000c10600308000d5007076400420002c4089001c1c0d0350500c1652414210100c6140c068480386030050103038400103802e0280f42ea0a01c8100410409684c048420300307503020880f00c8040346950b03140c0c451842032241c014020001040060703d00c0e00079240480c0103c0214480d02c4d00c50740030400350b400c2102c00b1400542514981c81810005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 947399658 1250 947398408 947398427
    0x190e100806090d050a030506010306080a050604050607030b1e03120301141521060a090e010e0d172214010203071d030d0c081b0706030606051204030c0c09061203 71
    0x2900403c54031005500242091181401c0c4004154803903000504503402500f00e90000c21005d030032180682058109a0346880d404d503012100c2d4052040810a264401e0003601c0030820010400d424084400440d81c0014820500242e0135004070b41039203004902c0540a14020710000501501164155040201007001c001c0c1d0840c0403a024801c401e0200b02c001c188040a610b81d1000c0040354640d6000240040038031303848000c0700307800d2065100c040c2a06402c94085081c44004441c025a00c8a01c01d0342d5130020a0409100003400c00c002a4624801c8160080d03960b58442c00c1170a180c1c0c0b540c5410b04001403080c1c1c0c400c0c0720781d00001070008103540b140302101924003007203c030146e101c891400261181900100340c4100000c8000410608c4191011a2260600204800f1395003d0323594404d03807121518442c08020030f00d00038000606c113001d14212640f41035044041c4125a9496030256403810040380261401514000c0204900c1c251744500e0025100c1c6040c80c0c420b140c124500140240103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 947400908 1250 947399658 947399671
    0x605061507060207140d02030d11040e0c0d0b1c03122007021201020c010b150a08010614091305190902090105091e0118050123190e100806 61
    0x3105a816910103500030585800680c4808096503d000c075081c259141941804180c2d014024055420400b0380c0000090850402e10942802141e102c101281d0580c0218031540284045800014107903426000050020829407400010f64215100104841841c4180342e02251158880000141500b0400310030b0038803442c102c1405441e07a644e20f4100b40542da1007002190700400704042c021951403143d598160208034008640300d41c1c02c040450b000c0c1810001e1a07004500030304420051010242c00c4801e6802261100ea20607460702d04107c48044c1c5180d0f5903503204100b8850348901d5951010880c904a0a25202040341d0420005d1009200703d40b02940142c20700c2c01e0100780041c1c8480c070740141182c4040340c1c81415a0b84942900c00b88041036020304000c0c1450301d0005c1031361141910001005419002c00700300980e00c807416940703120f0300300d66044807000d008082c40781e080ca8542c01c60203800580d0840d001045584010310200e1803000c2da4120507611041c0018000b191080294652010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 947402158 1250 947400908 947400919
    0x140c1e03042d03140d060909060203150108091c05071b090e010204060c060b0607170403050d0503041a04151d210f070c03150c080703200309010f110403060506 70
    0x12203d0354040d0145080384080741c1186408940c50414100c280d1110004140303007001480011301500e8810020b5008560268140f52040081c0d0569445180741c2d500c1b50203200014104641c1c4131903000854107110800100b046010402d1800142400b0030359642d07492030211842c0c4040c1015011825074860440d4180780d80c2c4140420050240d100c20901c440507002000003031000010408140395104506028080703410310308a840078459200001e00841c2e0103882941c004030b180440466261200b03990280041e451502d07035100984d00c12441640143c0704482d0001480c45900c0c1c003034140c902410340344074207202003100304408100c207002c0400d00303018aa06c0b10b0700351140c405620b0880d008030180714106c43c5000c2462000c0092429000d006140c008580c0b0300441c11042c407083c05085590b04a00020702941c000c03618541c0203000348040e800520300b160301c110240d0143c00001e50070042c2011050740d240c0c82100784064440c03269242041140640751760311800c50a041040da000604240c0c00348 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 947403408 1250 947402158 947402243
    0x405130c0906320723150402090a0228020c03120c07211a01090f050727030b0103030c1a060616080c100218010201140c1e0304 56
    0x115a03101d986800b18010030b50310b030030003100c0c1101e16850040c00801810b11108025a140c0c001c020440b0341ca020500c0c174110384884464243e51420309a003698029080079030032010492420b280d401038200003070fa00b0041120960070f1031003108000403003480c140158000c1b140c0c2c101c05007014064004001180820f45140ca205840e005540f0403540c41415a9406003900c2c049030702d124503a18056294000310340b030000040551401800070000c2c810310030920319100b08001440141e00620b4461122503e0700b04c0069184c10038000c86d44207030103e41c0c000c00b41c2d410f000b00004122140d654040c1d07000e551082c1c06160540f800064500c070141002a4940c1000104000b658802c0b00301d8001c0034144d07a04080007210b9251016840c0254004240113010300003840d84440c0c0030754050054171139450803800101000c43c2c01a4200c4681203588d010081e40c180004040200c180002d085d602e40c0300703030124400c04903004a5007103500143c0702160b0402241c0c680d902d0004440407000e1000303a6107103904c19007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 947404658 1250 947403408 947403437
    0x6060f05090a0e1e040b07030c0c0203100209150d09030206090703050706050d020c370c030f0c030f03020c04060e010803030a05091009050106030b07050906040e0a020405130c0906 79
    0x40e028411100d0683c824000a0310a1909800503411404088550720090810349441e01c0031410440305000002e18048501100901c102880100c054024025003030310412104071030302950040382e41c20f07003000d100303551007186804950043c06130f00469500000c1080300b500d0003c0c100b041c09000e900c1943d114250500106070040f85e08422103045003003850b41c0c3d10034038060202900660b440890381d0b010340ca200350008044030040001c80d20002c2042c03200d480d10000100c0c04024091070152100501c8041400000d00190303110000c2c0f40100e03090f000540e5a59540350a030100c261045005030072040641142c0c0c20980105405810a105a0012581003d40e0395036030340001480c0440c82381d1100040780500c01c040c014040f070140451b000380f00040e810305005000c0c008601c4100c1d4040075010008850278030880583c0c200c00c070b006103043d141c51f103070980000080102400745c502442c0c2c01c00002a90380d4130100d040c4013000401c800454030552022010f48414810b5001c40140010701444030701 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 947405908 1250 947404658 947404669
    0x2130e0304060f17091b0907050d1107060207051501080d0c081303050f160e0708180f060a09050c0a080c0616080a021c110709020c0102071506060f0509 67
    0x50b2105403425005a801c1000c00316400e9080e241303440d0603c1c1d5000c0c1417043c410303000314142020202c0710501c208108480010b00c43c1b480800c94802e800950140640043c007080364125101050003010860308042c02078640d8400c982c011981100c2079400032311010b810710440416140140b4040014225034110140060311039460400020043c0070005aa4100000000420710107150000120380d20b01c210b0f28507040e40e0b0381840365030070418001804002034110b840b071451407003008942e441210700d031148103400361700008a145208060140c0491854020010806076108241d001404260307410386040c000c2c14810300e0f04021740140a9094103120503000016004903004059170b0483c0e035040d03954520101c1d550030550040c01c40d40000b44080b0741380d03070004202c0801c130307103603840c0e03012940900209030741400d0382d0090540680c00c00201045241030b41c0e800380401c40b020000151800c0c0c81da0351000c204402c04070074103138000c0c2d8420041c04804d81c005215500403206040083c5440038641c0000c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 947407158 1250 947405908 947405917
    0x1207020114030c130825050d02091305030d09030906080f0103080c0705060315040c210504060f1d0d0c110f01090510020616080106081f080a0503030402130e03 70
    0x10711120300040030611410800c0102e969800c0028011002d850b1205001078841c004e00c41c001a5030b040c02e507940915200554840c00c122800148800107940d0300b50b00b44079000200031300601620b40f0f00690a40030490600080c2014180440005102c22251902419801458000404109181041040c0d44800003005815642c00002158450300809a11480e05540390070158208a011082c0043d00740c2d410380c81c3e000654112801e0004106134041100e03042c014024000d98060761b1102c81501e01c0059012903000750040801040c04141020000e080c0c0d118102d07071510b5446c821651107000581800100101c070b41130318001c0d10340441612245044c100040d500c91095010b203455098a03070056090340c00414005d00500700c0d80c407a844001e9200c26080760f407080c42c101284440100182f0942d6903034141c1d9519113804501d5260214070380c2e12a0601c584901d623000400e070340414416810040010864170a00040d5a40e10b001c0c814405002107060010603a6400d2050983d0b82000200907103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 947408408 1250 947407158 947407187
    0x30e090705120a0902030f0d0309020f0906030304031202010b09010b03090721060b041b08010e010803030708181e03040915051c0302160b0d0b03120405010c0c03060e010e12070201 79
    0x220380f5055500004e41424140c641004188c403c640c0e400b0086600358002000c001d00841e5800c080305500700c1800780f101001c5070b00c150705400400060001401d0204507450100e25031000041061031100452000c24080c4c02804031442c011040044d29a0100186405090880f03281211030340070742d07034100500c041c1d039100a0116441d1218401e507501d40f81e01002459071030a21a01030711499100141002d00c080c003a40b5801401500041001100001181d0040b0420b070389042565a0340c1c103422803021220040513000f030042901e250318015844100203003035190540a155501e1501c60700e107040700d14043e00c9800101168408021507641e0f8140e00301c0c2264046000c0a04508528007242044614008860140c203080c8000ca01011490f02415120302509400c10000f5150700406949150042e41104100c0003084184002d500c0b45401000c450f20034407000c164191290f0380c642c2912218420009c441e99180002400010308002038088807e01c0524103140c005640c000905280804006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 947409658 1250 947408408 947408411
    0x150b070201050f2a03030603030d052505130f18021b0109081309090c1a04031707030305100806220f0b10060302090d060c0318030e090705120a 63
    0x519040d640104110b07100700143e030351240d58824108040411410041005214240c0412182c1c0400e0900004407070281c01c00400560038804800d110303402402000340a900300c010080030000098000800340224a031071500c4031510340c0c2c2c0458561031810000d03800000c45861540b000c10000b41d00c00c80c0c0c9114240324990141e0741d0b003820a1811641d101d90626034050b5840c101603142845000b07009040581c060003900070280f40c0d00c0301864151454060040d02d1542544000c0104030111f410384951142d0840210342081e0b940e480b0048650a94503104404403070000d000302c01c15506200c5c07580e000c4c244001000d21070b41088030316992a0001024807103404030045d0100b8210710320520984a413680070000c00c128441d689024004c4020580707412204240010f00411468040e00a035507503040f018210b0013603812641c40e40310150030449054030078551b56000c0c052650101202600c5050b00a46400b06050710603001c0c054019002000d64042080c10b0008410310000e60704815044240b40f00b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 947410908 1250 947409658 947409667
    0x7030b040b130212070e0f0708072a1a090a0b1609150f020601080c13110d050f10051504140f040203151c0302030a050a0c0209040f020f0301150b 64
    0xa00d010101a8850180d40100070200360400f4904c005152010f0b25114845801e50703803202400c0008880094603000003103552040041d00d034900c46c01e00c48140071070300d00c00d007010148079503061501c2d01c10668081c2c0b00a00d01840c0180d03502d14010440c0d803c02c0354071004008800c031640307500848900c05048070950080445c0e1244016100e80f4080b40501811b0b42241601c1500210150546010340b801601500401000291a82011680ea004410003400d018048195404032200030400c03410300e40045801442400d102c2c10a070b1080c580306204084ea0868982012581c0203103841d5142c2c4030622a0049484038455018030314183c50444007407032220446070407100d00052114215802d869041440801000006140040d40002c4524141c0f5491892400310089010504081d031015000d03a008100301140244a50300901c44400c4610741f42c111280c1650005039186d205807015a400d00464103d0415460314200300c0000f080200d000704600c800010343d015810302248210400f0850105 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 947412158 1250 947410908 947410921
    0x512040b091e06040b070b15061c060b0705010c171003021e040f0b0109060513140310060311040b09100302010503060105090604030b22030503130c08010f0c0e0307030b040b 76
    0x125007480c50300e0081c103ca444035199000c84000f81c000c0d0700d099942c3d248440c00f09820306000d020000f04040040c0c046450300725110f44000510360700700010301c0110368030040064889243c601074111507224400215908001c20001825144400c00100e51800312a007480340c60009880c801d01140d5058443c100f0340c02603030031301d0020103201c1030009401506210010341d11948640c07140200350000d881d0681c510b03441c0c1408403000e000302807000a00d0340c1b03050001c0c00031014600103021211401011105013000c8444d1100540c0c0c1e0a503c01c861000610080340760500e0b0a0140f0500d4140654100c5518a88074036138400810f150302c0301a040c00800008969980d214402311074940c9409090305d95112b60306e00d080082103100702c950048038810000d00602900b1a1a032004070260142e45c0d290654403030030706a20303648801540c11200300314050000180c0f0f00e02070050301094440214006030100001c88042c00780c140410b5034070310035044644148002810440c40e140c00c150408030320700b1180e440c00b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 947413408 1250 947412158 947412199
    0x3070203090f120604060905010c030e1009170708030417190f021e0a14150a0b010917031201092d0e01050c07030212090a0e13060c0306030512040b09 66
    0x1084402084c01044100428014207401c01520329204200802c01e00c010040114210f0b40002041c040d2500a41c0c1d1184401031141c004040d500c0c0100c8041010811101c07445015500c4080d080300e00c4200070040205200d94151b131131031002c41b034400c1a8a410411015500c583c418002001c040c07010140f040011541308100a254501d4481e0642540d03105070441e180da105101c1400702c5501005244168601d1404503526200e440b03a01c0c40c608664442090050151048a20f000d04100103400002020020b25070442c41054501c03015607520750307895049003401d41050304072600150802c2503264030310130080c2c03404a0681224224404c14000609a400504040e890300c0b404c941c00c1106000002c8002c2005100b4984a9001c40f0410300c1080041d0722180511843c06611460001d001c001849503004265440302d900808402c0d941500d60b12842200c804903110310000340d03102c00600401500b04102c821042a16005604042c5440c1ea0030b401446002d003068001c0708000c0a006010201 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 947414658 1250 947413408 947413429
    0xb04050105090402060c010615020a020f0a0b04050d03020a0b0a020d0e0c01021b03031c020405100c0f0201080a1401030b01170106082d060403080406240e0c0403051609060b03070203090f 82
    0x18441d4000d60703427000096540798100e01c02e81c41814000d841748450318040b0040c20440d05c4001c111410300340342c0b608101c3e1300e0300d501e541a07055021f008145400a1040c0304001c0c030490f07207280016210f40390b01d40404121820f051041d29142c0c8059192400c45e030700000c2c4c00d008000321051080580b4030f404080790540c01860201c3c030b032429141088800d207171002e030003400503030340c090f5182580b032070101030100d40524000c500030b050fa441000200d80954031600760a40d100c440b030f00d404130303400014550032400c1c0c120907481070702d0b0300303d20b00d005104900b40c250403450700703180740c20081c00303114202850b440d21070380c1c2d546c3c019a204840301c1064000003045a200802082c0362000d40f0010710b450304000c1c00046c4201c50850f00311346801201c030030002000c00140c49501da5601064880350425a403a1007203240600038032448407041c0000000030300d0400ca1034140c1462916841c081a26055072182951400d8000c0120b40c5400c2c4100440702e03070b0002c155011b181d811a11000103c0c00040410040d000c1c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 947415908 1250 947414658 947414669
    0x150a0608031306080f040804030b040201030207080d0b010e04022115030a3503040f06150303200715050706060906150905060a0e0906030313060804060b04050105090402060c0106 78
    0x40840e042c4010307a1510b51500071504a5290103656070b94409401070f04850071240141036075000d0100784045598038260341d03401441810014900041625800115000140022507264031059185041d590011840d500481c1c151000c1d400c21991480d0030000401c44164289407030034540002e00d210150108003210124098151442a10203083c0b505040400c0c140c00700303840300300055410030388650b81960701d010200c4000c013170b00310f0b2075550354a8007034085c0c01401e440d810340b1119106002150724403200001c1d8429100c21052600a000da811074800002c519040c0760001141003000b554912400c028241c0649032207030350b50440b480c001d4010721442d0480382c000d600d4088041a98030040001d12400c8069854245c43c850b610300800080e4410b803684280041e501c48010760040c2010390107140c1060004099a052105000b504544e14901341c0c00b040002e03007007109101c244460361144107141c20080d1000d100d1b0350306040110310a440050700084c0200c80000e5804145407007944004068030307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 947417158 1250 947415908 947415913
    0x50a060203070207090c09060804080309120c03070201021006270e1e0c0910050402071e0f02090c04230105121515090306070c05100f020304060b01030b0102150a0608 73
    0x140080c00958070f0f4024000d00668a246c4080400310500402a01003156480d40d00d100444e41c40750345940300c0342c0014040040e00e1049545070b190020f101401b820441e102071006581b11030150000a14040b00360204aa85910b096024098541c04680068225040704000400c0b0b94441120394000e180703c2420040034007800b9200203840440b9041507000901c60401c5414455104041000e04201a80e58146505600307074100b10301d0619801414a01d8002c1e241503c0300030618840180c14004060102e80040490a81c2d0307045180800c00141c21601c580070302410113003031409420242048000e1120b5000b402401450f15a00c21800c41d0b103c000e4400c84440f15052028042e041400540503051081d011251014440700070001500c984140c01070041c011b58950200583c0c9480c10a5400d540c1400780c1190052000d0300e038000e0f81030448400b0030050b9246030a0030000e040f43d440e404000e04041c00d2259840e441e83c2d00255420209080318070702e03010782d01c400000400403c000d90080d0400e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 947418408 1250 947417158 947417161
    0x5040b030a0c0b0703110c01120b06070c1401090803120c07020a050d0c090f0b0a1701150e09100b03032a0f1501080d0801060305271c09140409050a060203 68
    0x9000034044c107003a520a464503d106000d90051039202d03804010504c0c005105a06050350340c4460b40c12076122444007401c40e6240101984030740c3d8020010382c0000e4181e074665000c9402c507590145020000b0510003000d141400c082c3c812481c008000030303044181c41040414120300350b43d40c2c40044001041c0041c01602c941c0b195240040084c90a4030a4600d030502d0030300790706100009070192030f18006000b01000c0c3c4060510781408482e3349000425199990f81d0b410b40d00d07186020040d0740010740300d100449040d5180503660586050310052161400e24104850801c46840000030b440380d000c11280041c0030f40b0f2891300000400c1c030503803110004600c141e0742e00c40c5c00d1800101e5100113243d400201462035a03201c40303000360380f50841d5200c41d001401d59801000a10b01c242e2180b504440311600542c3c01c040c40c003ca15005c403000c0c41845002d07400555000ad05401241402d4022900c2c906025810910300380c11131184000301074945016035140c0301d80004016043c84200c04643d400141107499 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 947419658 1250 947418408 947418419
    0x316021212040302060a110901032a170601031a09041b06051315080106110c10120c030e1c0c020306040f020a0e0105030a02060a0e0a17010c1805040b030a0c 69
    0x2825000d0b103081d0058080d4102040842140303014110307442242114803483c0c40d903402c6c011030023000203110b0364094400852000d220803480d00e1400090f42c216581d90755100521100450080c1b03006820a4149850500d103940c0701d4031314802c60030880d1002c99030340d00309550342d041210b1613030701444c1303020310b40782d011180030500c0c0e03403c5800703880c6150300345e890560381030f03190084c50044240b00c4018030049040c100040002d14070400c806581d5000e08001d072502d240c92a40850342114540200e10f0200b4004e04200f16050f040d446480f0b4032144038034081c06180515a4410303124500500c421500c1c3c61003210015202c0d001e214100c02d0568090101c0d03106240c07a040c070118510b62103104a100d5060a68000703072002140c2c0003e4140c650007000341c005288140c3c01c004080e0b1041c0c213224213101100306551000e9480d8610b500007001010380d5100e0006034089030a084074006001c50382400203052440190f555400803034010350b041a02e00046801040c0c1c001f0b8684681146e0041c100c141c40b80d404100c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 947420908 1250 947419658 947419687
    0x307030f050a05060c031b070807022202070302060115020303070801030201050d060f0e090d09030507300b090705040908030c070302120301150e150304060504020a3809010503160212 80
    0x801c030200c00d50606861040034411f40b007407051510181c42104244502005803038500040341d601c0c10364240041c84003441411a00590300804810740c0541c2200c00100940305241c2250700342242c40f44007862851502c040050410041804040d040120120341380c098000341e94403500143c000760916081407541e541042c42c01000840f5240080e0284204060407580550580c0040d654068040d154060a00c55a1a056459600e401c50300300400c0012111480a00020343e0940740149115881440e00000c420725000315640b2aa0244d45800280d00105000000391390300280c980040315035800840c1012460002410840640101c000000096207164000c82c01304260294681001002d005000c00c8140f10034061001384003101000014001000c69000a501a10062a0050481d212440f1050180d1000040c07a091f4058605007510100d0504412031089000400a032a124030440000c01034040545030300b02d0150905515501c06009104540002d410307800107d07241e5508a805d0b01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 947422158 1250 947420908 947420911
    0x4150c0327051c0f050c1005040b060910060903032106060804060e01141f091503050c06160305070c030209040f14010b01050f0901140d0e060708060307030f050a05060c03 75
    0x103030b662042403c041d0002c00091100000c8050315118600200b4051200f641c0691110352119400d0241020309185810544640c0d401240109446001440c010050243d802800b40000030300c2e130290041081140e0b4441d00307001c1500d92602c0c04120604a5080000b801188500300c00d0100303003880350108040d03600c010254070450013500c040c0034190103c10075500701d40f81d403151041400704020005030240460140f20010324542044607a81c00d5840c00070000f100c0c204a8030b00e683d4142300e6405c10134460104a51051480d048413114508035032034202401c1e000100302e00806100b000b289110911402e4003440b4029078010b00030741a545094940f000e1200c0b100340017107813101d215851007090004148a0311001e100182c5520f450051200104242904070421480c10410440b0a0b4881058840c000e002400e19048000c21038a0215440c641410001050304040001060400000340e900007101000c0365000b0003201005452070501900b407203c0e1840140c65407040805018000703100ea00290b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 947423408 1250 947422158 947422163
    0x90b16030510170319020d090503060c04050d050f060c0a03060e06030736020a08061005041a090d030c020109050f030615040603051e010b040504150c0327 68
    0x21a41411418054085500a4070b590080340b4200c41e0a00590211502126040c181d100c00c0300e00f00850080e20716600d2060303a443c40c0041c0c00c9404443c1c0b54a0300181c52602620045018020b94504010711221500136442518440d00d100c160340014440103224508045940e40d00391078103441d1541d4480b400e640408044800a8540304000401c007034103803c41c070301402004001d481d1952811700000b220903081d944c110071202600c0d680301c00c0740e00519100f42c10501e4025000d85c07100c6583d003002e000032000601140c0140c80507100d400c0c0040d03002040700e00760740d401c01c140400f0f0030240c44220f11501071005125004050a140c030801d040c3c0044039540402d1007680e84400c031644450601200c220031054040c0c140c0d10213000f26074004030382100310600b55005000000c42d903949489940c075180081490404981d8801c00c540c190440c2806503290f000010340d414440c60401d0782d43c00340040203500c03e51030070b02d03a03072601e844440744a038004030054080f00840050f01e0700368480006506110303801c00c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 947424658 1250 947423408 947423431
    0x4020915070327060c060b0415031a16091505040b040b090301050a0612081e1b01060803070c050d03200d03180b01060c030c0b040b01060e0111031903020409090b 71
    0x41c003210003a0f0f40f140300107980050396901c041d0002a9100005001c15501096000e501c0e054104050b8100d0381d00f0500a6004d8112101080c0e002d0404a50461000d0320060740b100724030012030400f98009002600700c8050b0920582c00200d00307542110103001e690070140320f0b00300008000412014800c0603189144048008010b507494500d83d040882d1014402c0789a000c106071030320004140008060628000ba014103044041100082002d180d8058040003040302644502c03d10f201c1c80074460390015100c038600652510081c0e444c0d5400c0d4640c1803007031500c264654080641090310402c10001900c10346040012020300240c0080d48603003000b44c1c60b0000a19000043c82402801481ea003d810f80203038607804240d00b0725008580e982504241501401001901e460000d400d0602c000d114500030f078005800c0d54180007009010080154200d410440007050700c1c1c1207002c0c08002c594202c49005540541c0684002066019009e107501c000d11803894001503000317001c0941c01051040700c51024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 947425908 1250 947424658 947424707
    0xc0605040306140103021018050402120403020d08060d12110f030a1d0a050405090a080f0403020f01080907090e0f0f1510031a0c0f182409040209150703 67
    0x3e00e032040060910000c1c4d0700000c8945074000b140d000b8000410907042110907005040d403036401180503a40804000c0c0c403c0c8110408202c285941400300700f50314001490201c00605007000003c2c0c0000f5000c0001d465440c101c008601c2480c050342400c075800c1d1420003943c8400c1c4252040a4994000190361030210300107080144140b0701d285a212000c46005101809050800b01480005c00c4000c021103950310841100201244015010b031040c480c0d40100c03240d0382d90861051100b8140c003040c819060005807801d00500384030201307054055030004500041c07001c5000607914079049504c40f003e88a40a440c11058004501240c6140c0c0302b048040041c080382c450125450030b0030300621020f44554131141c2041023000e0b00000003508040c80e2f02c100360034034440c0182d0038034170b6004855500600c0c104c0c40e40c00f50941070042c2520018803042004d00c060301c2107040c060800348520a01035101d44e034002011011a500c0e100703e0200d0155148506031190f80342d00e400707041c09568081640d4a070a40e0302c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 947427158 1250 947425908 947425931
    0x60108071508180304050306010902040f09020313060e1608160501050f0703180302120a15020306061e0c012c012723010b0f040507091802070c0605040306 68
    0x81121403200c1e110341c1c4400700c0707a480040304104400c900e555060079000422000804e50f908210880c041c0c054a14010707500c62a00c42485c3c8548202c6c0d0015550500500401a02095184400740484d03000000441c5100e159580d031410001803080030b80420700508408941c02d4000244618400301c079203458030b43d03141c070b40c001503410b8028483c2000041208001220004e48222955940311030f10044c6850a651242e000480415248503100725a600152803242405110709109160f030202d02011865800c2410101d1907521030800c0a8100d0340b0084054101001c3d618200c402c0900d455008000140c42a540c400010300441c258105201c03104424900c3d01c0300c103110b0301e1070382018000100a1001102900d00b81d5150348034041e07516500c1090318008800105d100e0762520b5405000004000a004040021420503502d045029070700e44800c100411760800900800c2e5908a00620b00400040344408040d226452005040302e08201c0000740454000c8094001c4c3c0f44a04001c1c0402c0c000130 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 947428408 1250 947427158 947427179
    0x60a0324050603041202070b0f0a020c24091807030e070614190c020a1403160e0708191b090b181e0a03050a060b06040321050c0f06010807 61
    0x1801003030b910480c10000b10300061129002d044200c000b900541e4201d994406c090050794100c0d0800460b030100024045181690500940305107020440f0540301195501c1041242d11030740350000c00e5402e800045144682d503904001a0303c0b04043c0c09680314600e407204004019203c0c068050000b0302c25040c0106026005800111190011151417410225040d000550150602505d807051240c0e00d0b00000250301e844150501070a400001491400718034018540381034556402010f8202001405101d0b04034841c04040d001592850300e020079450b161161000307695030140401e00c180c030704002c140040280550b0310b007540c01e4945850000365520680c0f0701c0c0c94030411903680360f41d020384080030f0000d1411464614181d04040b102c201c5001525002c42d00d1a4090340094925074880300c0240c0411030140a0740d020740c02c040d15079a00b407901d580d0b1002030725000310a1110340d40c440c1c29403480d0086c0c41a0182d60629031102c08032079034020000340c0207448040c280104109402590300205295494 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 947429658 1250 947428408 947428481
    0x190b0603060f04030c0c0b1b190302070b030705120a0905010b100c063b06010902070b150619080402040b0603072708010e030c0c03010b0108070c050a02060a03 70
    0x19200840d010f580e880ea01203890440400c0100e0b854459100c0100311f400500e8050302d03100755505c000304a066600a12189010f070380c1400b044c821001242c174000001d0380411500c0850b4000d08081d80c4940f44c4038004c4c1d0740c6000d44094075801c0055242000035501117904010034081c0100020440c0b40345440c00c2c400050b8655003d1004142c000c00144d00082040d8402c2400340b5000b200000d4062005110410328141c7c808800b21350740480c0c00c0700712080700501280340105103e1204601d4454560344a1143c04030080007030b0203024450403581425248ca03012209040f0034450b480c17110382118540944015800d13281a4010743c94088118142c1c1440c00490b401041c0c1078860350041240d11040740510754010002042e09228801c0c0061420000d006042d5468500d9018540310b280740c0e64443e20b03002000c26840d00c203038108030718028180d0700700710300c907412042c42d1408540140c0941000c03490081490781c001d400060000d6841600c41d85071380b241c0385100002280c8100000c1e0324550207400b40c007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 947430908 1250 947429658 947429671
    0x60c030501050f10031d0706090b09010c17040518150a03170903121b0f01060e15180f06041d061303020703050a1110050a020d051308190b060306 64
    0x6031221100f0203460942080021850b640c900031801c810014005091102049001012684001000e05c051900400040082e12040740b0140c180400f0000007400561500b40103010003070388080d10041c500100089034007604014010207088410703040c1e080c6a4200c2210000d010303d804084100e4245170880502c4100c80d008408040c00d107103c02c40c1c0303400c0d0b9401301131a05e0340f41c440c43c184c0a810003580344c09491185036940c0841404581c0c900110f050508041402019074500001031041c081c0407404190030060b5090303806248221b00000c901405040c0342101402c100b14001c001c4100742000080384250303c161802e018440124441c02d602034000c041c43c242c16048000095a02d1065003441801580644102c036040d5680b500c501d410404050030544507107041040d54400c608044c1c01001400400c0d1814514281c000d0034003d444011491044042040c00920220f81018201401001c0d001442c01d541416048100d56005104251400c50b41c185225001403098a004139041c0d11410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 947432158 1250 947430908 947430919
    0xb011203030e06071d0303040e0a1a12030a21050f0601091a0d0c090e1003020319030e150c0f03030604150b04121a0f0403110105100504050a02090409050a060c03050105 74
    0x1103070405c00e07081c0384415259a00343c4002c1c00005110070fa64100a4003510703c180d0005100104020302451402e0807021080c0208444003900e982010004102c440b0700c4003174608171004000c80000780c4001c0440b040c523845010f040c90f0a0261100034034100f18011b40d001d0300c4030540c042c1c0e0f800301c5911072040c07180034041944050190315a20b200301d400850901c041441c05c2410329031507401c5400c01d120f0580d05508036401105003032045080410100c003503400c0b07118003400401030300d40c0c0c0240403c40e1511900e00480c07504240c004488443d02c262400000a4015205902c544008680e0350750000c0324040c1c40340c1c3c00c00120104030701c060402041990380850b15903113000d090050a81441e0134006040300e0098400c068092010640440035000b91705420f81c004039070500d800d00900702ca9540c01907070b103564903020500a500c0c083c051411304486041c1d40c0854107544510f600c0000b03002350000103030400d051605480801c03001240a180a602c18002003010041d2075008504407103003405000d8000d03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 947433408 1250 947432158 947432177
    0x806011b030522060c030e011e05070f020603070c0201090e042a080a11011d0a121b080d08090c0f060f07050706180e0903030c070f0b011203030e0607 66
    0xa10400043c00400203414414100c11405100c603e00d101c01e0b54400c000099008803041c080540c000c2d4103800c0b02c0402d18048800e450200c2c054011894045160402c3c40701c006001404c101340c540e1840c00c0290001c0c60140c89207840756001e40b46031640d035000c030b0000e5041c030380100b100c86640060600a94110f140c2d919151034500300081c0c2c80c204074084030349050506000064000c02001101c1c0e00e248200b4607010302c01880320000d80304d5507155078000f030000c8a00513058841c1c0c4820414500300d0b0100d545808405002c0d0a0103101400d01d9060040a41410403000c074202d00009440000f00726980d881c1c1100760b8455060381d80301ea80e4440c0303003a03000f00e108011045615010015061001510b50910b2805901e507842c2458404240c1c8454040780d8076141110120050b04071010060980840295107440c20b003540d1030b280d00c00241144400701002c9507007000d00001d5211160015400075191501d941c46a01c00e20892880d0035007140000c0c240051005400780200d180c501462194403000c107407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 947434658 1250 947433408 947433413
    0x30903121f030c05041d15070e120721031e050d0539090d050c13020c101b120e031605010509120f0703021f0c0806011b 53
    0xc50405410822541d0015400240d601c49084000e80118881c00025400b18a04020300051358546030965054005034031000142c04004542e021114070703c4e401030f410076581e00348140c90010b80c1000d9640c1010fa6031802c54482c400004005083c4d4101010020400c82140540c00e1910260343c0020300180d040090440746100c088102c05030000306040003400c00900c020340f14111102215030440d206040c02da2842c0d00516101d031011890000344400b450303001102c00c20002c41c81690a401c3c003d000c0b1034801b500b481400d0000451080c801010036907809504004400a03400400359201180030b48001054980d0803445584982c0d00081d07030b240304c1c4106500080e00c20102ca244500030240d10703560f617400a114184014081000c4c00c0d1441c2b40b4030065801d0407403c5a0f002402d24800b82e014012000b4500205019200f04854007522599178502c00d10b02241401c04662440107007000d50200000784201c507421010f19800c8582e103e40c0595200c00045880741c0e9940003031120045c034a00010003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 947435908 1250 947434658 947434687
    0x603040807030c0f141c1115100f030f1b0f090b01030e01060602150a0c050f1602040504060204082b0516020a090e06010f0f2d080c010311030903 64
    0xa000d80550761101444c1c0c5140c4500a00070840416542d10760000c5159030b100d81010301407908810b68a00d0103e04007140c1440c0d1580c3c3d10340d80602030b082d00c458940080d04010b401e80e03030382024004d04841c10301e0140c0e603464486000d5007084011a0743c030680b004072500c08024950258121600020201c80c428035040d61030f0004c0c1b14000c5024101503c60906d645100c0c02401240c006000c03c1e030081c00352100c1d600900944050140085a8981c00d202800c04582d47c02025101c4040800030303c20381d00c0107000105055201041c00080d0028203040402c4207100c0c0960191040f0740e007d4054810a070804070b108495141c501200030b4440e01c8500450381e2241c81940a00401e84825008a10b1000e298000030400c0130144c6c0720900c02d503224184405101410302c5030324010700240c0f11002805041c11805600c22000f80141c3c64a80041e0a049010b8001110f500c05a88030410304c46900302d88494005d0344030030803d05000d0201f81400320310b044582030203080b070744030b000c1d04400b460424484001020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 947437158 1250 947435908 947435927
    0x15020c0d031401062006282a09030b150a27050c070501091202160315150504150312090501080f09120d0c031a0d030f020f030403060203090606060304080703 69
    0x104a4100660402c85d00381080040c1401406203640c00c420740c0c0c03045071404941c1c1788a8001c034200181410040b64400c0100d8071007072070480e010030303490000810003001243c0060180e4006000c00740101c09201040340510408040910300f03a640034040e5407298030300d01e4030850f6040382d40c0070b801e0011600b403000d800310b601680d0800011030545141c4862a00c1c0c1c0740c25140c03146401c1d603640f00d10510049a00d9010032140d401e144036444d01410381d6207941c4031182d05c0c000c6000c00c81d10881e118048085580c1c69000105d01804009208000007004a4500082c15a01b0701044982c1203ca604206441c0d004002d001c04480051b540d680c020794034100041c1d81c0000160107165188240020756500b580c21902400e0300c95110301000442d00e040560090030f407503699960800014024460b00000c0d10f40803103017140c40344c1600b04250f0313150030b80320b04074502000b200c1c950f0074902001c0f80100801280303030000c500500201c400c840141c1c94400401110307110948004000c10f00410004001034082c1d044603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 947438408 1250 947437158 947437187
    0xf22120e041122080a05030322060e06090f030c03090d051204030b100b0906220f08070603050a06050319050c0a0b2503020303150d15020c0d03140106 66
    0x200c0c4903820711526403441d4000c201200c030a0860b508059a0310f500c03c003450300003001c4130401040000e030385844e015106d1001411620082034204101407180c101003120b003400c1540321204001001411030794646802080e9104021070091800c00e00d15010004141c1700708540b2100038503e41078a180401c040e010745000122094000d0190603244030703580001500c015070068800c20140d11344a00c0082c0d80da5030310f0300402000c08c0c046c4541e05060b240c05046d03400041c40c1e0000a10b1f82031602c0454004140281d01a4000c218070050110b8090800308a540803070303c040c3c82c1445580c44d000b900c041a5400303030040540640c0440c6000d42d0000c7c8042203c0c50f99400b81d810f4335440d1350303400086964a812508250f41c01d040003d2030050314403d080344180702040368280300c40c03601e955503002500c1c0d00c006044a84110b61080c00341130a50f0301c4004460302594001c0d1030208489548070b100c0c2c060b41084000300d9a9015205c0300c078011602a001e1024181704212482010f41e0a01e24180c03650100d19102 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 947439658 1250 947438408 947438411
    0xc0409140123220506100507030f0804080c0609011d0109021513090501060315140f061b162409090c0e030d02250506091002030c060f22120e04 63
    0x9045403c800d01e028007440500f4620100d22440c010301401192150003800e9003c000c0e0030440c410210768001c143e01a0070b001454a00026201d605001150f07001e00b000d150741078018801802007818055000440c2d0031040c0c42048485220840243d080311f0b0b101d0400ba41180602130031501c1c3e0360549004095080c10084183c6030aa1611804030884409800c4100417075500c079000070007145c900001c40002c04142c03145c0a01c0d0004680850540181d1507071031405441701090742c0021100c01c2a030004800001411203038514665045002c20543c075204000e032810000c5282e00d00c1000c03504041c0351998140c1c072556000e0f413504000600900071811180100703c0341c6141030000c0e9030107110641a950b00c07079004102000b8054001902c8020b888491031448150f4403081205031614810b603022600f0890342e140e10782071094826800c0d80b151182605850003040108580219080750303080c01581d4a15060383c0048118440348606c40107403602403d00110591501111072162000c00c41c0700341c02510 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 947440908 1250 947439658 947439679
    0x40e040804030f050a06050a060803160501020409021809010f05010c0b280504030f030209030a110d020603100311030610030227010602100b0316052103030c0409140123 74
    0x1e4000d8680b1180004a03566041780040d01c091081a0045a8010400c1501040200e2074003513102d82e0303071141e0000603801d001030702031080610800f035042c2c4009100003c001e640c3d5095114007071034071a01b804910341c81880740000100e40d40e0490568003043e00c8043c1c50b4545c01190756229000d54000c02440c4d500503031004c40c4c48007520b402034402c02d20000c0031080c000c280c0b81424500906030303c5510b5408001c02d071040c06a034101d6900002d50f24103e0303030442c0640c00300d0070f00400480c0a00d4442140030350851000000d210314185c103030080804490080d0405514900290201900c0c1c6a080e01c0c00241040165000d101625000e005001400c2c1c046c01c10380f50000646465001c2c04209900039009a00040120390108010b405404a440021000307005508502c03c40005142900e00690b03015103d00a55070400d4901080a111503a00010031a600d0f072806a001d0401588203010381c001050800010100380c0d0300700d07020241a17808881e60406050b800914403604481c04102450f4040b05204 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 947442158 1250 947440908 947440913
    0xd0f0501021303140d030c0206011e05030d0c050609060714030a0209040905071d040812090f0304081b0f1f02030d05012c010e0601050a0c0b09070f0504020f040e04080403 75
    0x207a004015445000c07607800c08200800605c1c10040320600a000b814100145000010350204080e419503d0054001c0d05c540c4151000d40c11003015500000d40510500191740107540d00600c0c40c001241c881c004541690340e89601164030b41ca02a02c0381004540e00001750720340a85c09802941c0e0120f560f5000500701080c403000601510344000084d40e0340e42080806000c804542c45400107000e01007041800e05050903626602d41d84903c00c455000b40c00400046410070005002c1800d040c3c0014040381e441d9603c810780c0d00d03103a44903508400d002049460161b105814003c050402403000102401d0800705280d08090311613200303c0090302180010080706252130b84034030801c0d0107040c14074582c040b6900e4008c1c01081c900103181e2800942044031004101c0800c503a4049648400c003031a0060b1114113201c8162260080c503e03005160b025042d080200010001a424003107698242c0805516a942e8060004900c80c1040e00d0680304804c0006104d03000c043da86580c3c00c50b1141c4580380c5002c2d540d8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 947443408 1250 947442158 947442187
    0x170d030b06070b0a090b060d0b0f2203050a0221180f2e0e060423040f1b18091d0604080a02150f0103020d03031b02010b1e0d0f050102 59
    0xb180d084c0001640c6100c0c1c0e00900c07a42000e015408501660b01807030100854558000d0314500400d420407480350350000903049c1801d071003a82c0d5243e01959104004000600d4003030310641000c1044e500511034101d00c0b00983d00510701c81204880c00980481c0f900c080d25070010810360b040d80149410684018032847d4544405113400740010b6400e2890300101c500722103a4049070034808280d0300b009840a40741c69542c0d6841c0c1124101e840c01c181e41140101811800144581c26400c1590302900d01414400c180409030841e842e5464500c8840545005203001900e021014080c101c4243c8031380300007070201900d5035020320418a841c0d05112692440140402d1510b0011201100d100e6008120811002e03010411030440800080e21400d49290030340d15420620014440688104c00c0d1689900c00c2c1800381d441748018656070300d802c0041e6044044081d028010010071180948141d06201701c20181c22b9804442e102c0000f4146900300400f0340f58110030000405054800395401c012003511017503034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 947444658 1250 947443408 947443411
    0x5040b13080706020706030f050601091206060b1903150b030a020c0f1e060a0209062a0a0303050601020d022a1503040309060909090201090e180106031b170d030b06070b 74
    0x113540202001e40c200707040101501d207001e481b0180d01d4140070600807903071780159042099031a1040b04254240e0745040c42000b0342455888842002c8001604a02c1403140341818000543e464a0502c0300c8460100400310044603841000f04256041c8081400b45899030010016000540d048900450f00c80300304070304105040b990503600080072240b100c2c100e1010b005850380f0006442c021820141c81201003441f920030080c1000b41d120128412994100100e00f070411140c3c44c450440d400716a4520303000d00103202c19110940544145103e0b9545140700003480c84070f00d0541d0728002c0303080b13845011446001840684e1950300610307100110224103032220285226500944d00c4c204031030314200014042024680001508508140c01c440150340c01240242c03c8440c400e200f5a82039942202c4c0d2110154030384140b03000c070750070020000140300c80d0340c1e1104c1040d140507883d640010303a01c004100d00d42184100c0d081054000040c4404010b000e540203000c088009098545460030301d5840074050b180 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 947445908 1250 947444658 947444669
    0x170307090513090b07050a0e0f0a030b0a05190b031b180703050a0b060405030604020d020a0911070203011b17040302011b050a03060e011a0d0f0908120601080705040b130807 76
    0x550711091814040600710045d04580b590420740d20301641c002c1b00803c2e481c8000215809a500142e0710381c0540c0781c00b03544000a6410040d01401c6061844e42803001e003105403500389210004070410704510182c3e00c101c401600c4010000d1050601c404101081003100b4201154000604450040d50484280400c3d200304881d550000d640d02d0080d0301c0f20121400051024042c400a10040c40562400180241c00503011652050209402e1000568000054010000c2c0a04200f0f41c00741145010001d00840780c0f00314004d0001d004500d002d0616141603d072040001242c003032131240310706202c4085d190800d01902c000300302e0354407014030000c6202000b17819100044000a00d2220641e0610501000c0d161406d29103d09500d0011044180d620216419010401c00503038020740e10410743c0700071100e4556000c244040d1190b41170400050301f20340d036205100d50307601002070310641c402d01050b80300d2001c585505041a0130004445507070f0b0440d503440b6070113143e00712021031052010003541c0000c15 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 947447158 1250 947445908 947445911
    0x231603021e07050a03030503060d06020d061a190c05010902040221060d0b310c05190e011a090a1502160806070f141216020a170307090513 61
    0x91041c2410814429655209a0b90003500003071010390b4600243e14220b075094034240303840381c07982000103603000351001e40200740c10320020b0010489807085c0c101da003c90f800c421619003180c01c00d48654840d4428007010b10304070243c1d20070b2054003502542c460280319000d40000103000c6210f81c0400d0403603100540342d202d00921800c03c402106a0300c02802d034000010754030b0340c03000200b9680b400e801c0f000181c01340c540000c100c0c1c400f8101a0740d854070035a1410b120528040b5000d8030707040040031b00404d80100340c02540c504110300b00400000c40304404550204e486d1011b103038070709100c8110071980071804d40a00c400401007048a9034070018400042c003100c00307416045107240740c030123460b01064201454405809403001c018001c400305045a01528a0802446480443c00c1c1200d001840859a025586000c503c002001406022452103603012803407060000d0131030790702a03a0360645e04100030042540c0c540003a594240c541c0240d0741000b02400c2c07a036592030b00d540c00551010714580d1b11141b281d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 947448408 1250 947447158 947447173
    0x70302070b21160903062f0d150e0103030c0213051005030c0d0b01051c0c0b09030d0809060403120209060408010509061b0406030228050c070803040623160302 70
    0x1001c00401e416006007181c00700020500d4808805002c4c240304d44005800d50707a441001300151051204aa420040c03400500c03045401031700402c0c00550402c0898140441ca04208070a005903038101c074a05607405040d010155078619501220f00700c1d04550101d0300810443c000903101c00c11342c025075014241046880c400e00b424070080c1446d01886154403440b50303024420b5070700410055910035040d9107003a2110b040400501404481c00a0712240c020007803840000c00017244002d1001404c0341d81c10032030988102c0e801250341203910841c181c42021030b54005c8c40104002038010344203c20400300e04030000d41850004400204181c2090340849001d945a2040010210f4107224441c0d0040004502c08120311501c0e0914110b4041c9010360b82c2410b60000f840001042903484a40c071401d546004068051040c20000f0b1554000340300184452181400203d10304201006441c1034401595580100c108100342c01241c0c50300102982182075410080d6a010902b60190902c455002e80c00600c1003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 947449658 1250 947448408 947448457
    0xa140a02030d0e2d060310030c0f06080c0310090c051b0f03070308090705031902040c0e1c02010302120708180c0f123d091205070302070b 61
    0x10540c8416101c8208910400b00f8015581c84011400c0030a680648280315503840314122941079040449075940017101000700070850744400b200c031040c0c900c07615882038415607031840c80d4184c4106004040c0440c04500004980400c0320002d140d1107800300c441543c0a5a683c0f40311400c4684046481001980c0081d0806c1c00c46046100000c1300d03d0f100e00206a540c1420110f90b03100d00480301d0040410404001082041900700511009410b005080d02d0002c0300600d1103c40182c200030342280240d0900b0301c031490031400342180a444031006000106810807106159000741080c5204a0615a0074010020400c4030280c102d0b1103005152031300000b505204104506100c1c90b8400f040341644081c540011a80342c4800032070540f04c1c2601c080d885032910b1101c040c100742a0007030511603404400b0503a0443c0c0f0701c034440100710400309441440e940c1414249502034030000c04e03014001045218201803024130590040c1004c0703001c0e205641c1303407644400444055602140f0382006145602e4400340e035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 947450908 1250 947449658 947449663
    0x5060d02040f060603110f0405040b060c0d0903030314040b010501050313140105040627060b04060302180a051008030909070504170a0b060603220503041d04060e0a02030a140a140a0203 81
    0x703907844000205810050307c0b030a003441900c20750180c01c0c01903450b140b0b04280d40c1c0350b00040ea01c24124100640741c10f000f00000080c0400300d644419400a41460ad00382c0c200202d02210a001d10b40240682c1c070386a00741801503030700b60300141c0600d81c1d80c0c81c14044030300401c0e0800040444103010340e001040508103070130440c2c19195900c81e803618200c5800c104c1d0002040410350800255030000010030504000380000d4010f05066002a40000500c24620700140e040d03007001d40300e602c400340d08100d50744524412264800160141400301d0340104101c0a5074541000d80d03a40c0301140d490210319241e198480300c200300d4841403100c0684d42c403480717184003084111038915500c80b200f911036605500d0701440303104c80394440c01c00381410b1017121102d580500c2014001c0303901818200c4070742d000f681d001c059810307504981102d041d10190b151000e011007590001c41d02043c22a0028000c2c0781d601c040c0c0d151118084080d400070b81882c440c0c0070803900090f15103101075542c100f044003c0e01c14401280185070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 947452158 1250 947450908 947450921
    0x70b010e0c0f0a1404180902091605070609080417030304050607031a2103031e24010f021c0f1805130e1501030b0910050f0a05060d02040f060603 64
    0x1c940400a0110521180781841a102c03600c0039880d1030b4410b801e03a40a041da9605c20390b005000702202d0390900b04030201e51034000c43c0c6100d10a1301c180e141030760b4007029040050418002c203c0021410002c2401052042c7c100c044014001c2c043c0d40c1c1341c20764500222150700081100f07805550130100801080c80300500c40c2c0c2d030303100589003030501c6801d039007424851080c10340c1c044151085100740481d10f8603034208011345543c0b082e114100c039034a042110b800903c204443c44254103001c1c0d4034000034400501c044410010202007844950b640d0f003100c0041d5207800d04400c05200f1803141200c4185c46101394003521100c959240c8481d12110804a401007440d0007580c0d1809d5064540b002c1003009442d6200358017809948013030000b42c40c2c5091007090f410008803841c15086e03805080000300900425140c00e82c0100c3c03400d004c58030020001c0c100d241c1a200d08580c00f21140b1540000641d4500003508459032100c0010400b001d00b505507400a41110504081c40817030580e603030420320401d0741511421 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 947453408 1250 947452158 947452171
    0x302030406120f0203090127170f1902010203090d030608030d02210c1309050f07180905040510050f04030c020d15020a030e0d110601090b0a21050709050f161202070b010e 75
    0x5200c8e081c2502c81c002035840c0c2008222201c0000608414511500029503425031000203540e600f802030640020702035002502c190401e03001c0c0d4250103414900a00c584821140c042d03014504002d160b140e076500135001500900013200300c880358503592003201d14489104032600703407819441d0102001500005000c075000f0492080c81e18051000c03681074910b200754000950b1904041a40c80c4c01e0051000d111a5804040c0450520007404100310002c00d0000f2407035454401004550740e004452801500140c4001e000b040405080d90301500300710541c0722280e0b00a80390300222041c0140d0100890740149441700c0020340d20300f81504101428041e80e0380c20581441d2605003800c6036840c080e1140010701c12402d40b280d640c949050b40383c550f40d0020008080060100d81484050401980140c82007801100c160003155404201c140c00d07031150b00d000b4035064004407040c0e503404402c07031240403400801c0014040541080d1804803294001485a5480b800e0b08510651404c81504a0090094000d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 947454658 1250 947453408 947453471
    0xc1d064302060306040908090a030b04020907020c1005070309180e0f061b0d0b1002030309061605070210031d0c09060904081909030c09051603090302030406120f02030901 75
    0x4a000350b51044140c0f80c020000320350000f061000d0b4a01400b1a01c15138803066049a0300036000414090141e0703560b0300c80c41c000d5032071401c0c95907414412a140d5545604096010300c001c580c89206030700c100080c1040900ca410040152602c5001e01c1d14504000000c0070030184d01e07811810340030308090002c4040146418000c0000b820982550104040795010310b0300000300100e070315004101c403900070071980030002e00b09503088580240002d459a10841c2c0340c0c61240300b0040400c0032601028580020124556070301d1b0300b0541c0c15800c110061103511810f204160315282c24840354101c590300c0c10b0b01c0114a50060014a402c1e60500002c4039009010a100b403021108010100b44d03d28121081c85411459002c15201403079000e6400303041c03c3c1c201410450190002151102181d40301c94008d4075490150550f0840156007281502d041038001801030f0400d010400005015410400001018070302c04583c503001218000106d030801c0f1803d4402e0780d1a08181d4480301a034443e04680c1d115100b08 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 947455908 1250 947454658 947454787
    0x20a0206010312230a260705070609060606020a0c0f05090406050a0209041118031b040c09030b0717010806071d0d150b1804050606090a091211060601030c1d06 70
    0x4006d0221000810070002e014000841c0000c0055951014501e5940051b00300641a11000d000303590702c0390410112000b07078603100c0118600302e40d0001d00c0101c44006100d180030b0f03a02c076601e200103080c0103800010120b03001d00c5180850740e9280a00304102c540ca601d55925100c8a0300e0010000c01004c0e5428081d40001d03d0721020006418070307440040340309540104081041d540f080b5a28a01903001901e001001000d202080d6408800100d21740d55007003240303800f40d884481d03840d1540e07400d907050400706130f0500c010344820f500720001203066400180203140d0781c501750300d0312000d111a40e40c80590786641c0300c001c4000341c6040c8600111015051403c00e007185816601c00b6581c81000d0b100324441c0e1040000181c4810581e001204d0312948000c400328100240c0384080c04800c694000c6000b2806180009441c40d403207885600902c0c08141d43c1d01c2ca00c50128520310545500d2800b0494101d00100110b80c031182003035141102100b06814410722461511a1020900c0508005407c12002211 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 947457158 1250 947455908 947455967
    0xc0806100e0109090225030305040611090f090912072a06050403150914010b0a0b03100504050417040303050c07060509090c18030f0307030e04020a0206010312230a 72
    0x2048080e0b80145100590302d50810421b108a040d05103002c0b012003100400d80020140c0c9a0401d5016074841c031810b210000c0c51810488040c01b819503a00e40128006d00d08195510b0200e60f901d8028040a0a50f103880b400612105501d600c180e00544030105850b14038030007000c04140f03842e40868400540300701d19041910003070943c4501d10019100d0070040702001150503c2e5840441c85a6020341651030f50070300c1d60990b5000c1c002082901307102d100201c00000700e2140b078108807480f0309a20203241c0700302d03401c1104010041c80054415210000e000f84800c404490600061000e540262901d903100c103c513601c00e610b8800d042c2c10241c01c0080502030400141c8541c0c0c0c0440d040400c02180729100e02e110340a00b21070501c10364041d030b80341c402c2030003042009001000401c2c0c001c0c02556003c480c841500d0600c01a889600c1060005a00007001000443c42c44003600510113514a4251a03100883c400c8035882a2115100e240003200090003008035074001c8004004074451443c0620614001e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 947458408 1250 947457158 947457167
    0x3220e0115050a17010612050a0b06160809091512031315030f0609020d110c0d030c050c0102030411130903090b0903120d05010f170a080702010c05010c0806100e01 72
    0x80001c1041c0640403540407001d90003412074100d800070000380c5580543c2d60b81e00c0100f03444245418803010610b0301d0b001c82e4100e08180900400c1580180007240741002204401040c041d03032050a5405a000b403200c5c04003a5144402c1600802000728180e150307134910350400070f001c100e0340030300302d0a9803003044111100c0169034a03a504480811345400e82c802550031003134025080040d4900c160a01e031070004640f4001c1d95000d4121440f0102040200c004052142e0640f441042d000300c1c0a40e0040c2501074050f84250003c6c600c41c60a85005401c12902c0f514850aa0300141e40072154989560054505424000c0c0d0920524041000030310507401191400b51000e03401d0b00070480e0410000404401c9c0d52030030001ca11100f510000c1041d6912507811588005141c00c6c041d80ca501d8125090025080d200141d00e040a00d0104018020755465a90703034403040d60000070101d0601a51200d410003150081c4a010035612940d00c4903000ca00c0e105041001d60209040740b1000d2010042d05103e8a1340d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 947459658 1250 947458408 947458439
    0x100504060c051c09060b0d050d0207060f0203090402070f020904200904021e1c2402070512130308040801020a0806010513030b0c0c0d02030d14040b0703091403220e01 73
    0x690300c0001c8135102401c044018200401314143c00201c42003041c4104080080c50601e0000c00d0303070036070700250b0302c55004464000b082800c01c1c005a1091000403100e25207907000700a403600c0b1744000b00007400160f01141c0b0740041150103690311044000c0945019408a00e50b00e0058411900120141341980c0010000c03c0121210494407690400f403842e69190071480014040b80d000060500803141c0c50015200400d0302c08a680c10f00c0c2c03a4200c6410384040e80292080b00381d010b400b40c00c407001c0340c040a0341542c011042c961107940780503c0000100d0f802600800107403181038000b40e500c2d824228081e0030703824081c180b9810080304012045410501002401c181daa10030103e08098440f14001c15140c02946010303007840c000c010002e040c183c0c0000042606402034a8280041c40700b820a444250740115400740200d040d103000980198401d60015074010301c00c640c2d01c2c0360a00d028142610315042082e13003031055002416981c0c140030804131410020404000c214089605081003151407041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 947460908 1250 947459658 947459707
    0x16051504090b030a211407030507080d2004062c1311040f05120607020304060f1803030305011d060d060b0a150504090f0239100504060c05 61
    0x140c1d0b142803126a602030140014164016000c4c00d00e800d600c031000600001c00740c64240210700321294900c99036500341d003a1240290907854503801c1c0031942c0c4503400c0c00d034084402d00760100d64682820201d43d0004103607510040a40d042c541d160781c1041d41c0a0003841c8075440d0300c045210221010f201150351003c0c40243c0d11425280c280ca00c201d080c103250050150768141141e107000c0450082070451b0300381204422a00c049a0400070707000c03401e42d405d491703490550315080160810030090024a00032030b21000c2c1165285802c0c0a616024800c0e118807c84d1500304400007611a80108a0450000c400d004412081c0013504030300c1c2407420018036401031107400100300b1a1100e8880f0640c0d50344007265401000e0802d0081590140e020005203207a11900070300700e4032032070022124186102882038601c54100a580340d0381110309105a2140f524034500d184071179507525248801e101e40f040c0034172408090a92400b08181c00c041ca00f0300709036144030f000f83c0d00b00071040c8100024413441d01000e04c4041d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 947462158 1250 947460908 947460911
    0x330509011e020d0207022106070810060f09080610090b0f1806010c2102010c08092e020d0207050d020d0c08030a090209090c0307150522171605150409 66
    0x200a0066800603000e00c0d0801b030340c0807248180840d01020300a214104000c008401d4800c00c0d0345560083c3e9444005882c02840d00d00b15020500110340242554808040c40e4105440c02540d5102403601d072a0048500160329280c04074100b04091070383c0540ca1001c02e00f100c40d2241c904407600800c00b5280a494072445c92009032011500b075901907100c0240c00f075001030724039148041046181d511100d8031808400198a02002204440c0c0b042401c0b50081204a014108245091680703400d040e009c01c0000c41c06910004040c0c2020b4031510040c192861108000768480044e030514504000a102241d001c1d50044204604990340c40481440c8070b940c0f143c074898030794460701a1701e0028902040000d410071030000a006807400c0c0011440c021010480c111034541d03841d59640008a0030258000001c69410700003400040c0c130100801001c5105c80c2e40040300c2d15035560b00151003050710315100c465604162088544d0311a0901540c02510050312034050908400740414083c1c070682c843d0300c1c00305 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 947463408 1250 947462158 947462167
    0xf060609061b120a2724092102090a1113080f01020a020c01050304052109091003050d0c050309030a120f05040602030706020d02071209090605012a330509011e02 71
    0x1302281c0310400082d102d18110b606d40b0504a1304044221511580e040c004242040000038040510101d10402e00122031800b460303014040d401e2000003800a0507014440d074440740440b013200002809801c2304041c00811132906880c1128081c100b01c184510804240d0041100c1a070140d00040d80300c908038030a103059913480d5039a00b02141800110040420540300030034046a0802250025181c2400d08a41d00c030419282d08003040c25419843c40001c01540011000d10801801009825005402a01580c1c81e10102c0c0001070704003800060102c2c3c0c0e800b4000236400f001644480d4030b03091076060f410b1640c6440d0410802a40d80c2c0100b19004101580005112911a00035010740d0f20366035114500c1c5016800000019250010b07900603e007509190850005456109900c0184002a4070301401c02c00c04040030041404803501d9000e80c4c85014482d813220944682100c00c1103030100e5125044101048506224180c0380e0180a2807407ea041505400030039012184041c0900001c0e103005a84 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 947464658 1250 947463408 947463467
    0x5060a14250c051f0605010c111018090f0e4216030e070e18070803040e070f032d0b06180a0e0c030f060609061b120a 52
    0x201030540100510500641c015565107100200c540310303403580002800c0c172500d40c5540c01190b1030304000d40040c3c009000080e144001d0304241c0d40b04401e490062030040c80c1e00c601103440710a144c0e00c9070b202e40300c01340c0ea90302c5000c01c00100340300d0581103130001c10140c500c00342181d01c15503010009200d0b08283c1c00b10491190702020400c010f8a07050703154a0f1f00b0920918110402e400380e8440d400582000c070307003030248010100c01c000c83c00400303171401080210039907101d00b03410088041910f10745030391a00c0755140c081a941f0042028100405010301c600c0c0c02c0c5e181c1110024010240900008180f5092003200040441c619160b618050844848102c1000514020074040c0410001c0103400840005841d810420003030603811500d04150342480760241d84020368070501d881125100110001400801c520310000691240c0045008001030704100d0441c0010b00c85510807880e074181c40c0c49540388008060014406112140440c044007824000104406401032030740360054409807410600303500c0e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 947465908 1250 947464658 947464667
    0x14040b09010f0e060f0a020c12030c090405010312120c0f030c090e070207090e030f250813050301140105100e0102150403090f0f03030c120c0f05060a1425 68
    0x79400c146210510480d0300c08043c1545513882610800a11084c01000403041031150080785c64503400c1d80024540100d403a404400f080e040508050170f0180104039030641a900c40c051507000c1e500070030b42e409895043c010040d1401c025040d01c03003034290811204200164201003c2c0703040c400c4a00700400d1a40441000300c800b1055a08460b2680d00c00074240820158000b4206041d20403041d030405c40d10010764141660380c041c088030b0b100000c0c001c00040d030100301c90180041980c1c01080304a4000c1150b5a100e01d810f4100024038401c00307031156070401161a09014a03102001c07903540350000380d4180300208044401100d1000144a03001d541d50070164400c00c0074000d200030f0090481000e085c203103030041c0300740803d10603120064080100894511a4031450104403a13058a55102d14400c0395120910340c4500a0748034184150b85a0050119940c00c604076001c92190010304114500f85180f01d045407000510580385618140410a00340302d04190b6824003103042c240c203a04a184c0b001c0456 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 947467158 1250 947465908 947465921
    0x605010c0b1806010305070812090906010e0d0501053c0109240e15100504260a050f0601080109080d0b0a081f0c0806060703030c0201020f0a09030b010914040b0901 72
    0x342e0751245100010a110000c00c030241078507021025114440c0b1802e40c039050301e01400d08159482004c841c003142c0250b01034850f0703200412028200c00750b5603c0740e03101c80c0d085600c00c0724105102c88039846400e01900030700004440d080b551032490381d01100b51012440580005000c1c42c0610f03035031080d68003071301e010340c98003807126207000740ca10391606031182001440ca0200780d411043c1184203880401c52443c011110710340070030b01c1d40e03900c0341042d20301a081c0610222006c400342503000c40400211941006118850b80e640c0100010030741c0d01e80b203500b65464110705070302c00400c691400da50390380050482400c0b680529004000402d2135060000043c6e03262103940e110410a100b500c0c8140c0740c0d01c43c64002861501c51304281000050826001542c9505c000c45115900520400500c030019000ba80166900101c1d480010b081010910700b17258a94000807865001c00d191b90400c00400801b46980303805040780300702c03d0244604420850f89013050242000703000c055403c00141c00003000b5030064 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 947468408 1250 947467158 947467201
    0x7030b01110a08071106160609030e100f09150e0d0c08070e2a030703051317040f0801060303090501052b0507021e10090305120702010516030605010c0b 67
    0x4440c0b003150707482c0000d095800103008070b550910401c56810325103009826100310b0302104101c0361060750591340d00d100508542d03400314188619820002083d84880d0f854101e441e10f01e03100c1c10000703046400c02902d80c401950200ca243e420b0402000602503012401a25441e4160fa21604075005481c041c0300c4260381e41c1000c020b5100c3d002c0c1c00107800b90140340c1917000301221030241c1d000c11204680f0301001d030103140001c0200e40007000881c945620991000c0e5000b084402046054000ca550b903000782c06040c1408a0700c00c0c1d011600b031080740080340b281da0041407841d00030420035180d070345c020b4003101f52486140d06002d0042207400d0310107000044606c1114409101c140074100800c0f0010081005491000051240f6014419889100801d030300c01c2194040041c103080c5608103d0f6000381108100c110704100c81880902109001648641d01801c180d8001044030302d0618003080040d1408074400c0b0415041c0001040300b07076000300034007500079000100301617280d07600703c000d000b02100d11820 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 947469658 1250 947468408 947468413
    0xa05101202033402060126120a03140603060106140d02030907150302091806010201060308030907031a0420040e160608060a0b04090917040311030c01051207030b0111 73
    0x10040c004001104441160040311a200c0e462900d2460f4114500000d031810005640800700503c6030040c10000800c900303401d40d0850554000e45400c0c41e041030300001e6450901c5001090501032503800d4020074408480fa4008400140390240000360781e01070610810301400090466064100743c00002c9031140c0c43e912100399640c0c00e0011a484da110b45234480c0610a910245030104424800c0c021562003c0700106080c10769030010759100903075980904428190b40da100400000142d04a0295200300e111001906030301d442d41c1810201e2000d141c0400034004c00e600c0c00c000008d8207401e49000c0700001d103903415030788200000100e00107101a4451480c0d40c4101c1415816121010004006442e8650b459056603180c2605204415009000d80c40042c1001e000501212006500034401e0500441c1e03680c501780008460050f2680c07240d002612120240c1142d002681800c03c401c1818103030a02c0c0151911452507000164030300b018004408154507200c1d0040705a03c1201440c0e2030300c1c8010706 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 947470908 1250 947469658 947469661
    0x2030f061003120801051e040f0906060f06020102090d0b0403020a0c0b0a11010501051507080403080c24161b02211c0c020108182a0f0a0510120203 65
    0x480d060032166200407030303001410b00e0220321070724404d90f100d504072200a80084204031101e070304d104a10740c4031190280c006540340111491941c0c9070140410700360040303c0001e020743c100502803210584682191080d0380c010424040940ca40f41e030084030a41d0000d6240c102c50321036280c204d003400545000a42514401c007004a55410b5402c024452102603480708500540b84030a642d00b40c400c03d100e0950b00a081c201544049a1080024960284109191032a00d600c0f6681c000f841d400c007401c101515442424025103030001c24401a801080d0000b0f00041c1c3e01e4100c082010010400c00c141d4108100140ca46200030302c1030020420643d401411441d0005140590700e40d1020580200b54452107051140e10340314072140c200c0d1012140c9039036004800d62484e001541c20003c05044600e250407140e10244110324140328142e5181100700c109405041c0000703c0071005200da080c080c0c0b1a10000345800b015a461600110455800b9a521001161a200285c03844400b050100919500020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 947472158 1250 947470908 947470921
    0x1200c09010e06040e0a120c11030706030b0a0b070b010312110a050c030d09030c06032c0303011404020c070e060402090a03230703082a0f011e0915050402030f06 71
    0xc01244220300a5504116003d640310600b65a03048998020b0303c0791f040e1005807080c0ca8071071034a0f910716a001b065500d100034407510202e4078141c40f0364807010000390707110407022041c940000c2c810005d05000c6029401d011098613000c0300c1036010f00c0b000304101e08408481d0001d5000d071411641c181244010f43e0f40600443c105542c841c44d4500d0507a10900a0348820600342d80965050703000d0365000b0301071110f42420400142d0040c807010010040010003c800c0021303a6000d0002c1108045815010355120b501d41020000980d85e52050703640301c0d0b401030100403030602d0300180707800c00c85401413000ba08540b100c0001c20000d100f01d009442c0c0083c07001c603010050155200044e0305445641002291710b44851070550344030b65243c00000c10000040207a91900041460800366111541035004540300d501c11070246060346620b05010030380d4507030b540001d0000d0b880320b100042035640035061000000d40c1c0e031694a0401c040d241d80034800d07500c0000ca01503440c100805040b08404000302c0e1100e04214 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 947473408 1250 947472158 947472179
    0x17010b09040b151c05010b040315090f020a0906060207150e19050402070f0b07080f04031107230a0512120d06050307082b0905060c0a0611220501200c0901 68
    0x200900601c1c03410300307000188100c80c500c1148e0440350004500d600c0e81030340703002d8040034001020b03003613902803411180e200241ea80c1090510082040d03800025926150400190a0052542c0005040c1010001c01c4c007c00d600501d141d81c3c1a80c0842341d40c41144820701e00701241c1403e58101c2c80d0064408114841004000c4507100703401d5004030b01006a03984c80500480e001d8808603130401820b200c02003c80c0000740200000c1c2249064a4142c4d01403a454400e690f42d43c2ca501d01c05c03201c0944541c1c1a200c114103006490402030720003541c011581174200000642d4034603034183c00394281103001607a15101a03c541c42040174150084c1507590322039885125940c1c8410400100384030519074081d49108140b07086141c440b034019521900e9141e403414040011a400c4580d084441e0700030040600b00148444c42008994901380920948403601c20030555103a40000e81030101649101c4028042c41c0e0b00143e81000000c0080c42200d40480e001e07104a04101e400c070300d52904400b8480012443d40280c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 947474658 1250 947473408 947473447
    0x30311010e01020c01020a08102714070302040e060108091b0303040305030d1e271a040b2208040b090607050706030504200f19030203070e060117010b09040b15 70
    0x7c0390b0786c0c0c4400740c07920003245128080d00d10620360041e01d220701240f501000e2518045103621003500009000608001c5180d03c42012107019000135030004052040003500c0c1d07991070700f00c00c0a2030b08211a24001540c00d40e140409403c00c4009000100040b80941c0c04004030b801035039200c42981d8850400e420440042e2210100d0700e01c1410707580c0030001240240f44a0f41c0e944410b000007a0105680a0411002100b24a00162640c000845a610403860f1030402e45000f2445541c03041c4141c6082c210000000001e101c0c611050240c440c2c030b16000c43d104805803070507648004880c035030704c610410000c2c0300d9118161004060740034510000035802e81642c4454403640c010794900e03a100081840c468001d090390718045502034003822a544450400e60415003448000715000100683c0780d40010785055083c1e401050400b86c844208215941d001c40c2c409034890b840325043c00070354184004161a0b000e04180c3c54001c0e90340d034000c04500d40d40c804d1003596812940d40c459942d002c2d00340b28171800600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 947475908 1250 947474658 947474677
    0x2304030f020a030f0806010905061303050f03090a0504181505090c060f030a0b0111120309300a120c0509180c040605031f060215100f030311010e01020c0102 69
    0x1021400004507400400d803404260740c1a40e50903040301100e54182c43c1e0714405800d2604001e500c00002c00d2640b40d02008003014503459599014003031961810901c1c00d440c46654540580003400641e03210340fa20642d0b001542d4040f03e0100d03181c1031000c11482c080d03192010240138105018801014120180e012901628660382a03070b010340114000c0c880d06110302c01343d1010080080000640d040c00580c4004009081450400c680c1d80d82c141301c00749842d015404210a46000006016601404210760b24030f043d0070310509a540c1200001711555101442403040c001c030720005a08244603c1074017201e000000e811001c200306408076500074155002100c20a01900c0801c0500103402024500c903031065550951861410342045070880d026000500304081c00c40305600201c03801001d030118200905810342c010240014052a44480400060004c0c842b1006400e0107100b020080000241900d0300350a11541c2004602c4040d4010400750a0b24842c41d4408500d52402503010b40040c0f00051 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 947477158 1250 947475908 947475917
    0x7050c01150501050d0f09150209040b0f0d02010f0302190c11090c04050f03212505100e0c03010507120e1204060311040e040f020a0b0a21230403 64
    0x10700c0c041c96820300740e03107030261a0101d00b0600403002245025080074100c410000300101d444021a500e039081220140801e4240325008200034000307050511440c4101c510444185400851030390114808645490021f810032046c4207a1315091406501150740008102c0c4040301c0c01c00820342c00801e0002ca11800311803085003400c1d20201403800300486401040302054441c5014501b108119000101d42d54441d0140101042c00304803008824030021580180402d2030fa031a50000b0102090918000408105403c4240c0d2000803501c002052071300c1c41c0e0520380006004160741d100a2038000020b44c0194150300b0601005110b580c00074598021740500d0b01c00380050182025081d80784d203684602c0c0401500140401c0058500c60b40000d400c10100030714061a0684070342c01441d20130390444090307403681d02c1c903a41d410450400e06400c42c020150401d442d4100000b2000040c0080c0c801d1000440d102e0780b0031036241c2c00290b079600c610300d100385404c00c0c020003d40b103a041810703050003214140d0105 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 947478408 1250 947477158 947477171
    0x1b15011806061106011502071d15010f0e01050f04032f1e060306190605040f060e031506031c0e0405101a0d140108010e0f1204091805030307050c01 65
    0x154040c01c40851500b400f84081c0126a01b4158104164122103810030114401d6004c00900c00740c003c800706c00d524800781c500110900e0040e0300700a8950f4082c1d0018100703c0c1090aa00c0601c3e400031201c0c80100c42480e1441c0c6da8180d454040000307006981010b0f1542207140801c240000c0802041e503c03902c0060301c9005007030840d07400c100c001001c0f0130000b001c0a003d0401d2036181e2916200959000900610880c5111201e203400215030b000ca070451008108001014820a1280b1009000030074071481c1000155040c240481d4803200c2405000b0101035406003c05d086980610078a210142244200f20404c182114000c00000e41c002038280154501000f25551140340300c480350070380c0c445aa050115840b2020070071429070040c2c1c00c0103c80c070707038404207400400c2c102500c8500a0010b40d001044540c2ca40741c91504001e149058009142d009000301c821450071360302aa8200c0319043c00016040c40d82075000070301e81036007480042c010301000040280c4035401c00c014212140800d0000c0062 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 947479658 1250 947478408 947478419
    0x1106010902031e061309201009350102120c030f070c0614040c0e160e04020d06051005123103020a05070803041403121b15011806 57
    0x4a10090710b42020700010f043c00745071120903240c06a0342100c800b9001d2921a04980c0c07042045450b00a000c4414100c4a04c0500b80010070100d00144080c0844548106002c01d40015007105a50301ca00b890700d1505030301c0141038641d4800034a41128404030a030002c034a0b1841058001e40c4281400a02520481c0108451405010589104801e99911540300d903c60900695101c0d094034000c40700d0981310315058200d00c441d0761000f40103074400c030f40b41d590080c2450b4200090000c01401d004042c0000c48030703411450b50200d5691401d640c00e131001a43c1c0c10403011403d01428890700000d4108401d888405200c07584040201200042c0709080700450b01d61442e010740030100b00c56000200340502d5011400e071011541040400740c4079004503442c40c0344079a9010304150284d4002c4050343c0001c20108001080310740ba02c012000c08070b01070700c00b0100100c04540240681000c81c00641000c01140c030402c002080040603c44041040420960791989108845850035055807501c41c1041e100080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 947480908 1250 947479658 947479661
    0x11e17072f070902070c03050109030f0f1d10051b0d0f020a0b0606090f0913051009020108180309060f09193210050c060f0709090c091511060109 64
    0xc03054807080282400030310346000400650030801095864a8a2140c00400101c09201d031800051198540d000b40d4414000c001d4003800c000700240702413205800c0e4002e00c0c218403030784000c1500411140750031109100c0104480900806504072205a0320002212480c100042c060f256220981d40342040601248400c9840b00101c00380200500c000c14049101d80c60b0050261290f104082d00c4e900508801400003a50140c0135034110941041e0f5400744000d000e4140702e504184000b074a4148145130480d4002440c8680c0109000100b04444482c205144414802c5a4038070b04010000f540f2001509414a42ea0340502d24052051001030682c00019101c01440e0b01118100b0000e40c4803184180011800300520480001c19140341d907151000c00da403100c44460100d881030f50b03466125560200000e180c0003026060f20203055490040140150380200b0801c00e54048280c04280d2410200090790211030341d03080460b00c0c0200b1038000c03aa5a42c022040300d00d050790301080310322990782c2e403e4000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 947482014 1106 947480908 947480987
    0x9060a03050609010510050a2d05041e0b090f01030f02130302090f0c070201050a09030b16021e0d050703020703080f07031706011e1707 60
    0x68541043c400460242c03009035032100d0802c0180c02c01408034010213540f4030030800f000c0a928100d100341d050030042404007111488004141350000381568200b40200350380c011b110100d4049002da48403a1030201c691441a0610341540d400074000e00b9000e407842c041c141030b11480312100780c621910084c5100c1d000000002600d0781580704008450304041c14800d0600301c3d880174042e007441010105c502080e4242481a80e40751004000d03210100158005880e0308080c20030004ea4881400c41062a02c22640c00d580555800d05000880050311600c0700710507030300c08005885000d002d00001c1621a000780111803400d562691500c9480d8042031200d100c484021031144200b50b0028865042e190030030040c00791703615000000030721000c0d2800e444140003c140d240007040502801c080448814203c4000003a441c00c84005000d884800706000382c061122015521150704135170f20203 = true := by decide +kernel

theorem cover : BRFrame.Cov 947302158 947482014 := by
  have h0 := BRFrame.cov_init 947302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 947302158 ≤ n) (h2 : n < 947482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
