-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1606
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:49:58.191342+00:00
-- url     : https://prove2.me/submissions/db62565a-17d3-4628-910d-00397a863fe9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 288669064 ≤ n < 288848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 288670314 1250 288669064 288669091
    0x1b0604020109092a05040803070302011509020705060403030e0c040912030c0f020705130b0a0303120e01060302091f0b0d020a02011104050609010c030c1a0402012003090103110d0603210512 83
    0x88134412903172406550002a56800002104410f250741500017481a04181108040030b5079540510b0f0101e1042c01e1001300b40d03801610005002c00e000781d103c05c4e03e0400060554094444403400101150410344003111480503160281d184942e15100b40203001c02c039400c160301940d40031840603603200c10910401c0e210380d0543c5c004002904554101d04100240035010384203081c2c032843d0241004980c030300702c012072a15043c100d0118900c140121002c40c0d4002c2c02d0415291102042e800740e038400d142045100e101c7c403110005000326580c0080400c070303000c40401a01d844030180c000703003594900024005824006d02092000b41e451108403200081c090a007000d421055240580343c0c0040400064090f0b044010002c02050300d0000051246200346d8449480c08048011403030301c29400702040c0d000d90b0003800f1004040d4025840440200b081481a50030241c89000000a03107603503400c01c541c8101400e43c64241c40c607008080420081d40780c00d2907810010030020003504410002d01d0400300c0f045 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 288671564 1250 288670314 288670391
    0xc080919020310020d021e030f01060806030a0b07030c020c090103020a06030903020f100603120315050906011112210108060c0f0708070f0318030203060604020309031b060402010909 80
    0x20b007041440d001140841c0c0564a81d010158010002c0d0007003c2c54414000d030442144c0c0b081891003040782d104443c40784505a960b400e1200841302c444008000c0350701845095122000300d0150103400b403080d1f00300c5d5800f051210381c0070b10081c2413032611840036004240d4100184016659441c804040c3c514920300010080e1080c01c04924080484c14a1809401100d4017681c4002d00c03600f20b142528040c0c441c6a4110440c82400c40032194540c041c0c810f015901c210520007468001c88180c2c000c1c03030516009920b00c02c040186e80c240700c004101401040c20000f5160002c01c2d40d038591350003250004000702c81c15807400407030b5901e5800080192400b42400500c0d00107400e03000041d1080c507a00b003982651a48042e19181000080100341940865403030300401d40c01d18211504801600d034098007a01942e125501804041d420103804603031540030a001c07113112645071000c6131441d003203004000c00860419000150611000d9000349844500303001c02460140101c00340441e01c18000d490030030f080c40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 288672814 1250 288671564 288671569
    0xe0109030e0f01020c18040209070504080307030c030203040b120a0608030702030d121103090307060e07080d08060a0e0c0a03110f2a06090c0901140904021e0d080a030c08091902 78
    0x400040582c6d910550a032010041c100101c14500d1003144281e03002c07151070321a21401e0740d480c0201d20071440c980d40304010090009101d034bc000c41d1131a05c02d00460b4103264542c1c403070514a03000f0703507404000d903213841c41084200000f500a01005080b51800303180b8141c3d040e0003003605c1d001c00741500303800d201103011031115007015548041e5190200581803910781c140140b000f500c90b0f1041c83c056a0040c10f061000c4605034001c1090001c94100c140109019001d1080c00d8404100003050709a1180038540e000a0784006c1186852040039a100c00039030f50010f00201604a5803400c20548101d4800d02003400e11035808400c4035418211700404d956444460455082c5100c011146906640288000d00c40c4194001402140e804412940209a43c0e00d80d0b200701c030500001c0d01d000e40d0205209001c100907047c019844c080c13812071b10004449032898903001c1050320f590000200d505000000e2080e8145031301d403080000751800c2d45800f10041c14a24a01d564807031483c0304210300c0700301c034403807420455 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 288674064 1250 288672814 288672823
    0x310060e060603130c060c030e310b0415030c060c0f0602030c0913060f080f06010608100803040605070309050405040f1101030b040615020f0a0309151710090e0109030e0f0102 77
    0x7103510078602c004894903000d0007810907d05120403008603d003092002d0007890280e07000c0c4404028140c4650250289800f0602c11640101d003800c003503685e0300c0743c0c48110b403914069031445990703040007005410314528000c180c54039180d205004012081010000240c9900c528241e0585c2060000d40c498076203c1101655214101c00140e1040c2e417140d290f40e106c030940c2c028400316001d0300250b240303080d690100162100784040c40c1030107030f07003100c0014003809010301030242c0c0080c0f0141e026411540c5400396a0b2642d0303c250040008650301041c14030805034007c00c05005003205980034000e030b050a82d114410589100d40003480000c0640e024442c80e41b1030b0f4006201040001d0042c4546e507038608413001140c04803144200107004040258100c0d420001e00c0c0806581e040d40e031800000e01d0040140040e007007007518103080000050442d805841048001401051580a100d9480e482c0002c1c1c0c0c007c8840002c01d800d03281c2d040400713030800700703030007100b003040542c1c1c251880507055160b000102d0a1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 288675314 1250 288674064 288674101
    0x71418120a030c050f0a11040218060403080c011a0f130b0a03140f0c090a0c050702060c060a0b03010c1403040c0e01080615181f0e13020310060e060603 67
    0xd032207900c44010074980e1080006020707600400c00e442c07003030084620b56511080390041c05420305001c2c1c80b00092a0815900800b00c010803000004031414040d00021103a901940c000e0310300c1d880200d440b0000c41404c9c41510304100460009a100010110100d0403c4c200704040d2032007031070454803051a0329201d4200c4070910100034101c1801507103900d070010039121101d00116040c450003a08019180001410040d11000103281c10050781c1c511094501500a170491030040100c10303c81c080058403a0800b4010310120a8098416450301880d003004642d03d429201b8826810582505006500118a0f89501c1041d0035525502d5880303051040c03691038071b5030068842c1c0c0c1d804400003c402d04c0c086506402a505102a540e03418100010458580c03644015402075201040210340000a06580154240c4400550118403661880f021249503c100c510400d03107010031041104524060002901c4405140800c1084c6800d00342e55400c650001044240103100020125410036924210b1040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 288676564 1250 288675314 288675349
    0x21c120c02010b280509040b13060603021507200901090b0a03021804051911010c02040e0d020f070f0803030f0c040f030302010f060803030609040308070e03160e071418 74
    0x10030714041c802000c2500f0208a8644c80807466000c20300349000e401c000c0c02a42c00c4601840e00791034601e80d081c0000c88102e001c5409541c0c130900000143c6595074000840e045150916848a8840c2400b03055450303006030900c078940114080368201d5a68100540c19501d007d20001400d140c000003180c1295856000a58019040007070044195140802e03148030f184103c2c1583c180981000300f078201c6002181008201c0c424940070803820754401e010003880c5500041c00840c2c078200d2510501d0802d8100050440141c011030a0351491031020030410006007130310307124802402d103411182c1da202c1c04003400580d09491004003007240940d10005a4025000d480ea5810101c1c1d0759240c00380c000c010369000c2c210704500f880070004003d00c010041d01d20501000d070503440199900d5500311525100105000140034510041100f103490030032100f0b013055021032001e2030039403e1900c1d20a801000030011002c100310180355018003600381c81594089001e005403110901000383c006480c404c042001c034178 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 288677814 1250 288676564 288676579
    0x90c090a0603030e01020d05040510050708070b040326040618050d032f121b070c08060a0c09030f030c08270405010501020a0809060c060f0403021c120c02010b 70
    0x1084004a510007002c60340b1a40b03841c2c880e48502c0f0300580e1580c0b100c014007004503406003c10041411b20b40d409006554492500700d1509a03241d03680c44454004890580d00d001c00c0301c0401003013603000b80d850344401c0300b419000b840043e9036020740c01c1d80f844001c1c00200002d440d100290013001c981c0000f4908a540308054036103410a101c4018002c1012003224a044a10056058070841c00c0e5507890070408518030045240c46249646031018030005000e01048410007801c1d04003000510000d001d030b90748580d00c1c500d205454450700c1c500d403007005072007240360034602000445c2d0345810600a400f01e80d4404800304886680b424203032801601004003808490380018911503454810030040e10712840d00c01c060000689201c103103c21902d00340034044c0980c0c8141c4001707001c507084034042d05516800a00b1240b42c1400e08490b0b80c00c100301074400480b00005c04082c0420150180021a9200e140494002d094244544014804002d4640d0080b500d561000e8415086100b90061001c004c405000d08 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 288679064 1250 288677814 288677821
    0x7080d020c0312040c0b0a050d150528090209030703022404090504050f1606140c07031a090606060316020c120c030709200c100501180e0f0a0605090c09 67
    0x403e400d1200f1038040ba030821000c100450010440781c150b50741c0540599880f4208821860428000d00c00c40040c45413401d030b405000599540d036900003103a2610112468031420032a601c5000403500541c120b410b02c04e00501541e1a82d0b10000752010843c6e8045440b05d034240c2080e03085c162804203419410600001c0003601181e22a007a0f0022800b5500c1001118209500070720901d480da91411091032146161140402512b0312804039940742d10b00740300c0040d2400e070290151900e0401e042e0f1003291001b898819003551403071016107080d406241d2401400462a040700010030900c030003401d0710b050f03003018500140d0852080001300040d16002c1e2441e0442117550780405c2d034a03050b25581c00e01c02c1c8282540440c0c2c002490081d464000b000c5034180e081245507044814903900325112400081c890107015070190700b41409500e0013410250b14010080302400041000d03074401408649840c1e12801002288142c00100040e406801c49000505525000703860303170070010360748159540040c801052 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 288680314 1250 288679064 288679087
    0x904020a0c0611130501030e0709150506130501141603030203181605100905030a1707121d0607020f010c0c2c06030a080d091506060e04140c07080d020c03 68
    0x200341e07603411314800c20140740c0d68800440958190245400c201c2d00841c504022403121504504600742c0c14400346070545450b84040750003608181c0c580007007580111000c02c02541c2210542580b1600d4445091403d0241240708008a152590050030160700100040700f04030138620b003483d1800380300142e40d100200c04004488036046402442d114800440c0f100045900a811010480d000a0003a18242c541520745440a20381d90f040001e50000400100000400c40c41c3c09600d042043e403a004920854442406009907a54040070300070801000801d026a03034081c0c5610781f00c00c091900c406540c1e11460442e0000340103a02c510110140c448140d681072501119103003084001c03180ca0310060f0b81c0ca0701099920030a103070010304841c03002c00c111070441c85160040481d641c083e01c0c54440340c44001c03a8141c11140e95620140c0002c044860a0a80b4549030051104903480b001d2034402c0b501300385084150328855100010480400000e10300c92514454041d02c2009101606a035141e8902c03900 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 288681564 1250 288680314 288680317
    0x2151204031404030c081b0a140d05011104081f0614040c02071a09012a0201050c03090a120b1005030304151b030918020301031a060111060703020c0c01020606060904020a0c0611 78
    0x200340e48031405850200b6142000c00300d81003109c0340e038045842d000d003c00c41445481720348003209807a99501e8100382012a0481c1004100500d0314000a00e42d4001c8120400031520340404006022400d201c010010040d05d0401984c0a0301d007150300240700c004044090346400300e190b0114800010210484031054801d0000e021220000e1f00c0300c103400b6500c0410004c040d00020500d000f408818580b04016501c6a000f038144900d03803a0490380780c10300e40000984a80215803080e070022440b28901c20412085001458202c0024484003c00f64100300000b610790085010380300c036084518181d104240d2103450119500808400340c4100c5240d182002480503141780079070102490244402c0103080041c0c803c0b20b0490b40c10515580e01103076407000102490308040c08060422414000304110f8100c1848054000d21003500e0069440c0e444a100c1814540c0b4610418150340120301008280d40301d01d070449018020449005980b41c00d451801d481d05081c00714090140c1345011028070005407440c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 288682814 1250 288681564 288681583
    0x9030304330906020f030906030a050705070804090b0f0d0b1b1213062904110c012301060e09010b03090102130602030408101112060102010e03120402151204031404030c08 75
    0x40c05e98407200c040c54503c85e40c80c03145600098000c0020030002d0f0300203405a0156070800c14a290480c07610b4815200d60809402070b8200d001e5040d940c5080c907403030b894045032804403038100342c1b03d40b040105030b5242c6401d41080240001d540c8907104065a9000030801c0489240c5030b6000032a42650401000d020040c007010a400c0300c40d1440c00c42582d00c2401d08540a598030160340301d076510781412040c20b200240c007402c09040311401043c000e43d454031000b0300070840d090b5282c00c405c00003010b6010868800f80d0041c0e00c06030901102c03c0d10b8003000d071182c600315030540d030022450954035121a07086500a02c260381c4e6002154117000004121540e0110060013183d0420701150342002d0140c40c100300315841000340c030740b200400300300e083c86000101801c15841081400009004004080401d00396030160700010a072400c040c0810085103008001399540385040d01515082c140c088a00c094056000382024040c8141c6141074003298494000300c6015590001d0302c80b10b001d95480d28240d440440c0c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 288684064 1250 288682814 288682817
    0x31b040b0607031e0801080303010b0f040f0e06010905040501050a050630010801050702060105090a0f1e090b090106060c1b1503050f0a0c051803031605150c09030304330906 76
    0x11022000342d900c40c4039250705031f03000700c000f4500d180d01e070082001c040c1e80490000740516030700b4000001c108809069503030042071340c152042028540900010700d0302c4803a0300114442d518010041c4981e4850304407100640c0e074103545559a0328140c00c3e610a4525141045280b070144d1880c0721010090f20194290484075154000d000d5500c0e50101641ca8140900a003904001405e0018082c005070b60803011441041e1180054000759420340084d81000c07004008516a890b541020204050100c0c1c482e4000f0f1440700810080c1e040010040c40740d00b80d400301070b2949140001103512074a41c582480b0007040066800103003000c105502501502c170444500808414040c0010100d0000e070081d500014800da8425140021409160030f9030840d50b11046d4062105205220b65020091440c0e50384a000d4801400342c1380442c0c10001d031003c0c0052075003c0e100400d004903026503c0c000709075804d5914410112509100d40040c0c9052486184010003290f50000c0401807a0790b006030264040d03586c0c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 288685314 1250 288684064 288684107
    0x30f0304060f020d0e220e0c010e0901030f0809190e06041a0d030f090e04050a050f070e040602030414030a03051b0408060a0b0d080c0d030c0e031b040b060703 70
    0x82c0030281e0302d07040700c10051004545c8408140c141032405000c3da19207402c004450090301484c00509008035500c8a80c2c1c107106038013100e0310748943c5da040040510000341c03c0312072505941c11540c2d40f00303841544400060440001180e040745541d10383c10078120b0090608003041e4141c0c1e54140700b121824007942c025014900e03090401c50200c0b20b030028201c7d1080d02a01c0d4040c900803d07a000c84402102c0f6081c0c3d010421292004540c04040b1851907004074041d40040048800c44e0402d2410312348080401d44161740b00705400c10581c144038030a2036000750040740043e101d60326030038000c1d0702c00300301385081c44075010001d130709220b0b40d0301a03014600407119505071003142d610791f0b2a5284079110f20300808449030f01003000545c5043c02d90f04186080c150150804c0318602d0240c2e0f94007826044000d940301d140d0003044054003550307450301c607200800f403451403c012841a000d001c03903110300704e10003001d1901c0b107071014588242e00c80e80c0014943c2d990143c84180d4843c500d00300100100352102209400c50300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 288686564 1250 288685314 288685337
    0x9090c042012040204020d09140d050301061d0406032f060a120f0905061003110301020304020a03140120090405010b0c0c0120070b0301081603170901050405030f030406 74
    0x3420749409510445403061580340c025018401c0c080407400910480c0d00503001c1160714119801c90241e944283d115000d0804501502410780d810140038030307240400c1050a000402c0b5895201c422985101080511101d040744503c0c0820050085a000070b0003042102d40180800395034407021004c400807210350b2003c6407041d4020002144100d140301c1c800107a60001c40090b00312103900c03400c41e21030341e003400060a81c955030310302e400d0810449502d000082d0340c0a00300240102d44010b1851610300301c008514518080e400110f81d4501360002800c0408280140c580c03250095110700c00380d40c0421090194655865020f44130340e8000040d1a01a9007010000109550700005490501003420050241402900011a401340801051903861034594410007103405040c02a40054034102012a50343e60400f8221860000c1040aa030300d141d40d0b0300b50410100318240d0a42e00c2c40d010034200a50b03200400350040b1000e0180381c0000b40d050082000046050600200910032030701e9a40b2490f01c1281e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 288687814 1250 288686564 288686591
    0x16020a05060613060512010c0809010b01210b2107091e0504080409150e1608190f0e03040e01050613030204090f060c0906020f0f191109090c04 63
    0x902140005116900c51808602185094803082c010b00f4180e4000242890f45e03800045d1801104103032584043e507403044146406a4020b04a603440141c0d10002e1003021040d070002081d4000901c1c0c0e203150001c24075040407408007190000300305c1140c000d04074141c051102852910116141e002c4592a204003040041d031510039002d00b03070074080e90384400e4000c0000401510f014000080085030391900400003c6107150b0240300303030840407540e0844e02455900b000b030720400000d40031b040700361564004035100c0c1340c05a200c000d044d07100c600300c00b00840c1040f45541d403c014114410b00b03014028200b22a0110b007040c008054411035040085401c0316036038400600c0a00c0c03140284040f100601c41c0824405814507401c004203880c4164070810410003142c48280840c0c0002c504600002d00710b940400c0b001760b040101c5101519001d001d0842c040044051399607414507141c4c0d2034481400005800180b12103611610641c810107000c2e91000c2c5030200b1070a464451907040e20344038030300e040d45091101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 288689064 1250 288687814 288687823
    0x1a0408091f26060f0406030c0303080105040507050c0c100e0a1d0f040201020703030509030717030c0f1c080907120b010807150e01051305190311100f0809100c05031602 74
    0x342c40326039525465100d0724103020603002c2016200307400540b0360341c0000001c1c500c04c1e0680011806036031b034543e455050204110617100041c00c0082002018048160030410200d004c00103901c00f00c44159000e100303858261408000c0300e42c2c050348002217540c00516002581c2031800e5140300508518640e6450b40c20303407465a01c0594001c0d0044e44510b00034030000e4010401015200402012116030696070304072444184402502e041e4070b6000412400300048040015800c2d03454990054040d140e001d2480d40f01c200e090903102010828440c01065a6640600400018210101c0d0100d082e14131418000c3c40f0f00028429010640319030580002c0600900c407080c908010941d0303c880c520411030004441c0b40d0441c2000c0f481816141400190301d945034001880140ba621400b140e03410f01c1c6041281d10080106170507070080d4401250000c009078800c03001a85200c4070f04000d1490380300e006103646802445c41d6006482450681104001031304000038600c154461003c104c103052074000c1c202d03101e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 288690314 1250 288689064 288689117
    0x3060504062d090203102c1302060c03031006080711370318060e09040b0405031201090603120507110111150a02040f121a0408091f 58
    0x5440391000780381010300d41c0d070b010314a41c0a580600000d609855001200c1280e105580900d0000e0030070300c00700004100c01c0d02c0103000580f031030300d0490100136118080b050b250307008080010b198002c41122085654090a070790340306145000b120f40764a0503001108011006000b5036010640440004031414852843e031009070f02040d01501960501b480032504100c00c0d0190103508804050341c2d0070500340000c8002d841240a41c0d40c8862003000300c0b41814894825401c00001c00030f1400c421405074403008002c582251f44000884586c0d6168100307a419401103040700b6054079185e40000403180764903005041500e004100300054000c0360031080c0d8803489408002000a000c00703e40f0f1509601603ca00e044071824401034500e5140e0303084403001d0400c070482d45500310310780c0450140542c1a0145000d0060700320b4101c04204200c0c03645805081c01ca590035140c10300d43c04940000d00700315805003070714139000300074080116010045d020500d05070201c40c0c818001070740c106040f40d0158a00c8850004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 288691564 1250 288690314 288690329
    0xb1804050c0c0d03180b1e090f030f03060d0b0a05060102120304051903051c0f060614040e04080d06080a0308090715051b121806090a050609040b0a090c0306050406 72
    0x61015200c5013a80900a80750040001c145403c02c2c8401203100c1800e600c1c414094125102c1c1c080400070080c400c041805841003859030304c070b40d4488004401c0041128001f07071071999519240c2c2d4451001840312200041c00509451440c0c0038015400e032650446409410300344c0035140404002c0b803581d48540021100508240d20941c680b28100080c07a5850351540d009103005483d00e480d80d1b486100d4038071281c152810035a6504d07080217245910f072040b0000380541e032912111412146040e0b2400b401140075801a081032500800c04204503c02198051141441705012480e074915046031034010900c03066010590400004d86a080003140381010340c0c100310101c01d41e0329000c48044805030400d000341001501203c10b01c41070490200550000e0b4140da1000304d54489030424512a561844400c2c1c900a580c01e03c1145100e0ba91141c07814140c640540d00e454403548054005005412042c51403030b0007440012010500c211107420801041d1469101804410382d91014081110440c1c0315208 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 288692814 1250 288691564 288691573
    0x60501050a0c1428020910030305040e0901020c010c0c05190b071b0c151101020c030d180b09011514060703050310030c0b07022704110402040b1804050c0c 68
    0x1400181210103000a203c9100216000503e4901c403880860103002c1e402c4d6000482415541d04624012440951082d0740e6250000704916598000d0071038080c43c0640307101d104500002503501c3c03900354180e0b101501030200900810410403000340040341007100603145070003149002003c130901104c040c00604e0b80180782480c3c0d559407860407926540115070100d0b0495081c103c081c08a40c8407810380000d40102d1130944208203010740702420640c0824108131040e4014082d00414120110945804501aa4002c180c0043c115104051084d6001d0010b0410803600280100410154019070820109500c01132070181c9901c101c0e1090784140741503541c1320b1010003020300001d12030009150450030212002605585981c0d50f0140c520311178122817001c0300003003141003e514041c40750b00d16401491800d420800d4038007503403035403220005002521960844102c00e001c0c0c0c8581d41250000c000d00407041e42c13540fa61029070120762444020702889242080d010404a1034040d040b182004040c900a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 288694064 1250 288692814 288692837
    0x31503010c0c110d140d090509040515070516030207060e0105040503340306022125050c0f0a0c060311070b10090212060102010509060c07020d080409020c070801060501050a 76
    0x8425441c010f840007500f090307880001c00c4c00901d000040303130600180c00c03024044414900750001d0000b016540004e104801050070f200200b0400700b150003c004c000c08035200942d0380d0000070380b02c1c2d100d10f8141943c04049805004103040e4041480070550390075503603841d041010140115000d0065010303e41d8150081c0d0700010852048000a03484000040c003007400011031201710b00341000840c3d005440007600002c4880b0520703010307800460708001041050040341040404101c040701c400400d0340d94103005142003480680224251284a40700c1c2c0c08580250901c1103040381c48043d001005c6402d0040c500d404600c0034020702031000c400d07480182490030b120140c2c550040442000d020300c5806400035802207940d2030303d80020802030064244e00003407400d00a000a0031102c00400c0c01c842900700b0414400c1010940085817403c980482c0c0c046e1401001d42010380c0c140c440c95003d581800e100050340d0300644000b0548804541140c80208040c60341c0e00010b4480d8421981c100300001d803000d015 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 288695314 1250 288694064 288694073
    0x100501020d032c150a02070f0206070221330f100503010f0b131a0402130e0114030f0f1f090209070806030706050405090402010503040314070602031503010c0c 70
    0x692801c586030038101d40e08103424003440000c566024a05294012030803d0621103007202d0815007084d408441103160550940b04e031740788e41040800003485010000f40c0d1500b5542c1e01261aa1012080e4240c10b10106104504d80d68458404912301054020300418600000e00020a189030302c085141d031003080d58516030580e003403120041124100d0048848041900d490900c142c0b00c00030600c03000064128074100400400c08058510900c815041000c0c464a1a0508040c100b001030196005601c480182e1600c006640c1c5542080502c81754003c000500003000b5402d0341c00c41da40c140c041e50928802d00c400c583c0c54480200c05a52958080040c0380ca0207030744040d49805200500800149114250b0b00242e01c0c00740c242c0300e80001542c41014071041d490144a030100504060038854a414a002d0100707428000c02803020741030040210001d000d150250740400c4a55a901c1e40003aa18820340c035010000f5001950b0141460000c410303026050304051140c01c0c0d01c19100d4860f01e8595200356034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 288696564 1250 288695314 288695321
    0xc0307120206120406021206030a050703060506060705030309060a0b06040e04020105090d060f06031205120117031201031406100b12040c05040609020405030c10090e10230108100501020d03 83
    0x200d8016900304494a0f004000c2c01e08640141d202d41d50159640007696010031080704041d00d442d110b40c00c80301c59840082d800040100c1283d0380b0600110305559610002180c6009860000d03009c1c1c040001000842070000c01d40740e00c296100c060030403d000d807100c2441881d00850145e4502260000042800340d0f014a024203500717100180b00d004140390326a44c2009880b1320040326528aa114181481040f0b50070307a69040381985c900d05030f0304015210306100c0070301c641803042000c1042c00c092601e02c004000c4c41284c0c0c450f8100550b1145c02e5a41e850520140302649580500601862000c9000705019480000440344403411050070015088407604c200ca034081d0046401c04100c42c0f00042503180e900540008091100006860303030319140c249800e1504011041c1d205080d058007410b0007a130000c0c1c18800703a0344c0380c7c0104100c0740e0703a40d410414108582d81089a003003c9413004803242c980c4990303101e45065000e9a8215898503590142400030b40e1602450b03025810547e60700d95070b64460790 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 288697814 1250 288696564 288696599
    0x5040b041115070615290c0304030c0b030f01090207081903060e09070503100e0d0f02190c03020f03070b0a0e030a0f03020601210c03021018140f01020c0307 69
    0x10402c04460350070444500e95a404180c0484040d40c42e82c201c61105210401040001d1410b03800c0c1d903000040041d4001020f50103054604036504000c40d180300d90301400c0058501442d4401c2d484031880361070b600341902540040390010341003400d203800401d001d0740d1070080c1c0303005960001026090001d08640607401408542000f800c040d503420b80001c0c0c540036007403468040e00c1c0c0100036203501810041814100b4091f0001e2540d071505003c0700560b04540040c03841e07510301c0e0902c0d00102101240300101d041c010b0403102d125a800032400900c2c04e11415000c804200d9200b121032003221011401419150304291003142070b010814003442007218000c486844110300020107071004020709940d19003a54034101d00550040c0c1c81040140b04500c4a156008400040710b0003915140d01c00b44e03a105088030306400300900500440303000c0c9140328004c403040b10805807410003c50043d03403103c28410306000c40c41c0d1842c1c440d207070300781c0b00b0381e40b82d400031810b0540c0800203000b500c003050411034541d14213a4080c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 288699064 1250 288697814 288697819
    0x60c0a030e010903030c1101050919140105013203060403030209130204170601060c05030307121413050601050103020703080103120e03120405030724440a05040b0411 73
    0x3042403101c0007400388242440c0a210361400206640074030401001d810406000f070500303a1515041c0f090510b40026042245080813807170789940e00042ca003e0300700b000804d0002182d9801e103c000300380031000c44050b07810200b043c0c12180c540f41c940c403c5d5410103245401050380580001c00030401082c800c0c0c008040c04500900301000d05082c056462040f80c0c415842580d000c5401307603203680300d10010301c481c500400080c41c0030703840b0f1003890300c440f0745a12003c0c00003810312044440d0403007006101c0e0085010448580a0144c0038586a0100103c02801c09401c6805018a0002194541c02807090b80c1070310f03030903507260580c41c0c4c01c40ea20460010300b6003c08006021001c40a43c903565800c03c50303c113500192680403a21a880d01c3d06140c50102c041c2c2060704242100411180d140c00146540c081c0480035140011050514022803081c60801c80e00c49000c002480c1c55220140303187c40751880043c80b1a10b05010307165a06a1902c0c00c48100b40c800804001482e000700f004a09241c1422100d200d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 288700314 1250 288699064 288699071
    0x30e040e01180305041701051e07020106090c08040b010b04080a03030902130507120e01020403030806100e030708030a080109020a091e05041e050a09121107090e032802060c0a03 78
    0x10340c8048144009840b078110000755000905021560ba107600c0c42c3e440503450f40082c0320b2030402d811401040c01703903030b0f0511402068500004034600d06c00d4000200038182900d040108032080040101200411101074030410031643c00004c1141101e0101c50484010a0207052803010b20746c1d040340640807404c5c090340c0c40f45602a11550f1034890f84200c5009910701e0311150f401c0300d2120040313001e07204116074086d10b43c0d06c107000400100341c22410103030340840d089031400d100740080f500035100e4030846c03441715401d0321a8083c0483c85690000041c20400301e56168440140c0c5c1e1400028144d204a224000006041c001d00304102d12001141269494092a14802d650b403110013250403114050002c118450700103e0070910607003180701e5283c0006140c202405600510b0b00c90024000c0b010306c244e010084103404e14100760000707101600c043d01c1c10b01424840c0401900b552039490f00401090410211400300c00369208600000703c0300b113201030707401801090f40c0d405041940e5800083e4400149900d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 288701564 1250 288700314 288700331
    0x1905220e031303020109060c0b0a090204150801020912060103151517031b01090309050f030a05060a020304020a0501230922061a2a0c0306010e0708060904030e040e01 73
    0x2414005041c1103150b19500803505440c1d4000100040006d41c1710a081c810084c004c0c030007052840b2006036000000400100350801d00d440460014034072403052060134090014040349510040d00207000000080341c10341d100d44406c01c581e54440f003003072000a122030324440c0c000450f1081c64100001c080c0300d0303001030141241e4a1a00308006280030383c0b681526000010340d84001910710060101401c1075000030071103d655680c01030424040c6005441c424114840c0c54002d03958104010340307a5076801426101307142000294180a0340065404034824401002d001c22994844c03a885440700c10203d0401c0369410040e4140301c010f40c0b1658415412200510030241a0300a214552001e400c0e801c1c0d00240e664034000074850132b10307200e2a1217505400100030302e01c104615001070b02c00c00c40c005180d070b00c12410750900c1c103031600c0c00c00c0ca81c060b058010007000281c40c910001142c1e02c105403580340c510380d9544100402016000403035005002c40e000c1a8102c85a0070194041c1524000e10000000c5611 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 288702814 1250 288701564 288701591
    0x9010b1314011e1703040503010515060a1812062a080f06010309120c0c0902130e0c090405040b010812031e10032a0504020a0c0f0807120e190522 64
    0x340340d44804d00c060360001400308600d003000d1061a40c405120742e49a6481306000e80040d4440c0f2406d1010b400300154a046a490441400e240d200208105070340c1c41041c848614025026002c40401c2c00d800301d560480000c0080c441c00820038005030a40d44102075036440303a031600311983c0c010309524101555001c3d50400210170750360101081c80c40d0784030500c20b0403092803c45103498564003c412103500510002810619020741d010503030340c816901000c00d42e5520002100c5000d060101d44d48141130400380710038403e03094039031816118164245c03070805400c1e0351031001d82d110540b5101c140001c007338042c45407085d6141d404d0782c02c01014100941c0d82c690300d0b01d5008030311500150845d0301072502c00c03207000308040518401005160646056081c1075003030102804101c00c0c20006011201c002041f4410000002c003101d400590050040c12102d0000d4401004040c010482900503848502c030010340c00100e940e0388040f24002081c02d062101596140c0d035002907040d1400e615940c03284e00c45121034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 288704064 1250 288702814 288702839
    0x70b0a090b0f060915010f26070c1406060109180b03010905030307030e0a02090403030c260106030605060306090123060c010b0a1e060c020a0e09010b1314011e 70
    0xb5291401c40b04042d041070400c2060381000a40503c01e409004030b00e04c5074503604506070350030040c02030602c0b1030f99018a00c2250703807044207100301a501d0fa081c1020403d40642000c2d5110503d4010311381c2d0103034621010700c40d9030742e000c0656202d8080784400301c0400410341001c50031507146440f041d000c200d0425000c0480c0c02d44196044c00c5509070400f204200c84203a051081c680c010345000000c00412095030081050b10201800290030503444403000c0f140c0320b014091620340c00282403940340b18050f011001072200d040c28002c0400017420310348001440d1030800e060320300440c8011b0001c0c0c45079280458800310000075a941c1180c008003413813200c6490f42c8a0340503203034407400d520003c9004541e480c00c1026500050300500289004482c0d21080201507040300816038a460428001940e03280c000140b1220f6682d202c012110090f41c00c03c28580010340080da20b032641603600c0303903024501e50013040c162100504054000500c003030040124502c800d4100c060881407000c0301c1101600c0d1180403814 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 288705314 1250 288704064 288704071
    0x60b0310031e02060f07171303050601060815090a0b120c0f010c05100b06090a06020f0c06041508040807061803020c0102150118270213060b070b0a090b 67
    0x5203034110310400a1102d451580300710b89510382c0c8061180042d5900203241e9000d0542480c40c0410302250080030003403814552043d61604001040c0c640c0c2002412030391010042c001101d043c06100000210103004040e083e018940c20258100c6800303034031017442401180101905615a02c91694501584030090f18941c94a80f81c1c003e800401d440400703001c4902000c0c0700e42810019034070141c81c00b2500204660a440c00002c03400702e007d1540600040042c0680041540c0c406004035000038542d0300020a40f41c0220403070180d50389030094034108413a07800b0f148030b08928031401031060400c15124001c0c5950003032041411a08058079502d40c40106d4509409038214100d05004900926804204420f840382c0e09100404407403403070024130414040103205400048040c413848000700c0c5402e4000b00c20101d40384005812702d0070440804001d404840c0c000742c0c00380341410b40c0003455499500504044d103450307599161824807565284001c0e444014001c0f44219a5040204002809003007010300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 288706564 1250 288705314 288705331
    0x5060a0215010b040e10032414070f020c030c01050307110708010603062316110307020d0303061a12010509040201120203090102030f01080c10051b070803070506090f031804060b03 79
    0x45460800711945d450b08000707440f12003452a814010070028440c030944a4541e10480780c00a404440c444615001e0070034000d200040010050800140070b9000d0001c94600959034216801c901d0040f05058540040c490f1107400120708000040440d40181c544d807540380082c0e01200e105c20303604d4003c1030840f036164000711551a194410711a0a0b5003200b201c200b80e9401c40784040c90f0b400d107070000204801c1f004100c2c005124180000c039450321414415100c1280e0003a290322300a0002d483d00038000c22013030180e04400c0d4035074400d0200c8200c95130195041d01100010880d8280d081c1010400c5010000f0400ca041164400108038203c1c82c90015600602d40b1100140e1a814a440c0c00208113005802c03001c4181c2c81410b0010956940e01244108000235007009075a50012442c000a5200c8444911490388107200e00013072120700000c001c4c4040d43c040d0f010f403207003602d5002205480d0820111407181d541c0c818401c01400300075058200c05101d10042c00084c000ea901c814009003a002180c4042 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 288707814 1250 288706564 288706567
    0x80703050d08012301050405061902060106030e071a1e0d0609091e1106040b0702190f0b0c1e0a0c05030c01140d0f1107031806080105060a0215010b 65
    0x8204202080034440c44011420415801d604103c4400f020249100c2225500c16000b00c2d02d480c0c990103501141c02070800607044603a14101d24030b0f020400071020b42d0040040c8260000060f0700f6200b0b10468000552003805002e5607480c003c2410004241c028807507d140b0b00800800506080740d001a45000c0407100038107841d504495503040403900300764020604a400c1208510028034500b004a14102110408030910811410880c50440a200f50950844030015020030350100000c003a10003540b00f1038003004441000545c070046132580344500020074401c07007800c0c080310f0780300c10113840c0040140c022140c4200c01c15101510341101e40381c032b2180070780114101505001d2034003440e07009014240c0c0200002010040024240c404400c4542c9143d20301140420842216401c007610501140a080c0054601d600d4001c506a0103c4003ca01080f507a880c1100310420002600d002c83c0c1302501c602406a00c0d007400e1104c694064070400c0214040c20411a00710084807400300d01900031010441d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 288709064 1250 288707814 288707819
    0x70b030f0a0510030c0e07140a0c05100608070501140c0703030f02060601090602060a0e0c09012c010f0510050c120d060b0c030d1e050a09060605091308090a0305070807 74
    0x2035049410152040910f0b0549003401d001003040001c100d0101c03080c140034408075954040e4102d65800c1c2400c0098400a4000b071541092540b03c07a440342041d0043c01506c10308488000c11300708440c400d1240c5c01c00c1e41c218031420009507004221811141c0d1080c2102c91a004404e0650741c01d0229603001100865042c120985049074104100e40d4050028280850001d0410002940c1d4040040a903100180c0340d648440140e0018005d03ca1083d40c00381455010756111540110000090044000b0f040111a50189840d400b01302c00d0741225110b40b5449101030900702880700c030f402d0050044090013020000d90805040800440b04043e204c8400c03603071140e503a004503006a40280c3e014004c81d400c28071203c00c8454003c01180c00f0880b10900014410f02a0326601c0c040362008404020418544810005c020060360400d040c00ca10501c41001020b480f00208020704000340e034916000300160320000d0004000d0342c014860b12000a03c12111140d607540c440b480c1034156005450f00da000501704 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 288710314 1250 288709064 288709081
    0xd0906140906040317060a0f0e0105030d02031305040f090f0302070501020c040c171b18190b090d060b030f0c0a1403060c0a05091002010e0709180206030405070b030f 73
    0x210390018092400b500c414180381d1001045108052240414051403d0100b510307540c40304c000d0700c02006100421000c0c16964601600d520074240f00b114000c0c029110320800c8544040b00301e07038010f590442c0402400341004140001032802002d900c8007a40d0303400e0307010085641c0c0000002c0c228441e5000b0701100d820b007000282802c951040d8140680d00b065031481d100b0343c02094141100f150740340d403d06a03540d02d070050641841c0c035440780c0000d00d00000f518607640b0b802d56240062140e00781e400d50b43c241034002d00009400b000348030381d03101e40c0380030302c040c03085031602402c40c20b4214090400854100c01d503400003802e000404020b030b99554011030003280705051112401009140c41c4018041020b1180d01103620360900a2040d09903583c00205982158002c50540d00c0d43d041c040d188a04c24260444043c0c02000d018803425114442c55500056050740b078003440f02d00c050154500c1d00c0e86202c40d801c3c801c1942014000301d0f5a03005004c03010a1107600303100550701c10010f4400140403130416503403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 288711564 1250 288710314 288710351
    0xf060f1406130b0f091e06030d05030a0c02071e030b010b070809012610230a09021e030c03041406010812070201021e070612060323030d0906 62
    0x400c00306603480000c10a8550300e200500441442900c0d000c40d061000200060b015101110180d40c8000d500040c48040500e00e0685a103e5002000c100041d0b1601c0040640da801c21a8040c000650b0820008603030388a0f5801094155040b401203031480e076218011091858010b04048c0f5030725541400400900c26072030081d41c0146602580c5528116180c2c640035050b1048046042c14002c200c0769500000032054603021240e00c203400018041d04080c110f070202081c991081130442c0040092903d48814540c1d011080c0b0780740140240402450120f03680061b4024502c4005110300102413410003010720f90055118404c140515940d0b450300f4074144c0d54180c034103081c40541e41d02100042c0300840d8000741c4000c080c21040c001613102c00103440100e14111116116440c03481c16044010308041002909006585090b00c60703e1440c840100c1f84012150148006050024500c0d0402090340210060303106084006007501d18101c1c6000c030810079071f03a0101003281d415543c1d040c0000d003041080d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 288712814 1250 288711564 288711581
    0x17070810140d03080615040303020607031113140414010e07022104050105030c091c020f0301180b0411031213060f0518010302041509080c030a02060d0c05070f060f 72
    0x15800701d010040c800201d00c1c0051181c03401002c1c01000303408551107540304100341080300b281c9000c00c1d039101d0b181e00e13000707498000a6400e000464200404162004c028500750307200601008030410f0144e2900c44c2031074011810142c0d29400942c2c0e40105a40499029500c43c0038001d15004441c244c241a10001d141c400f0429124440c40746090501c1c06004408003124200d500908c2d10716101e031940706000069100b0380c50400c1d8891140390518076641288050f101c1c0c03031802182c01100401001d01814280c82c0c402c00000300707080701c1016403000a080f0310380a6070441c3c00750200d003582406460100b803034031500038802440c082001c0b8400380400c2c410041c00c0c002d80b407980740140040c0c1039400040d00b03600502c01c05400c0600c1000c1c3e81c43c0300740d00c240e0503640140110071071028480d099400c05070611410b070080520345c0c0501211502c007401e0001c2c62240b081d82c054004c034504000045000c00800c0c1601c2c825080003400c210701d4000c80d480000c5c01e502a4013489000880c02d04188441d400c81e030040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 288714064 1250 288712814 288712829
    0x4240e040516180207080d0204180b0402250807020406030819090b0304290a0609060b0c0307080325050c100603080a030b0406090e070815040f02010f17070810 70
    0x1a042442180d03004107000d114098080c1c801350700c50941e8035194041380034884074500c40501c00301d00010600c0c60f500d43d50a40e22140710080141e080c039601801f098ac8107517050007456040801006029007000c0d50386201c410302812459007071204079800541550802d80c01a1000000030609014441c0358945e01f195805aa00344003101901c1c000007000d89000060002d094560644e10314040420b030115800401e55004820151b00d2415080b448000c0c1300d00e000707002c001440e00501050801e28201151030b0003610100443c00c000d8165a903c110b41d200a02d00d444298282d00711048050825000185c40a11a2035694442c60410100c070f1402d15040244403400382410000c00c0850b41003070803110407002c1e612f030100d0700150030f034085030140a9951000c80a1403500c540008851000706428051301c58020a0740ca003a585080b03000d0400700d003a40c1c0034107441e0542e28004010741c01440b00b0000d0f0b82c69401d100c0f1144c803c94091806110303080794001c021600800c1000205a40d0009280203029079 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 288715314 1250 288714064 288714103
    0xf0516090f060f02210a030b0604030c0b070c2106050a1e0507030b0307090b09010b0f1204030c060f0902030606030a150b06090a170d051804240e0405 66
    0xc088004841010a1281d076060200c3c4043e00c030a6244248101c440c5400c101c030001840041d00c461244556002d40401c10005e454042c1d08200e074a001d4007203408803a040340000c524070b401e003000520903a10142084454154482c0000380d00c08070846d0881c1c2140c50b007078440a1112003030514000ba40c1008150350b558030301e0459045607903140c40007802540a0f0100000940c3c8d80c0e018800c1d4010401c100407030b9407520400200285901940d00f0a0203074180549107040c090340d039840350000501800304042d008000074440c406032511445100c603400f900a00d0080d680806a40358201100d09216040009030b49500c0200e05501b003c01005400880680050803035a040361500d04401710054443e08100da00c420510507180e80d494242c4000900007003100035800e50390b08500504420000b04108240130b444c0c0d00d5512540180300340c42e00e000480b16040d0b00781c200c2001f04002440c2801144c400300c0000c20300c040000b148a070009001c0d051a403049078440c186402c0841c039050a0344d40b5010254070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 288716564 1250 288715314 288715319
    0xa0801050a05150607060e031608130b0406081303090918200d2009090d021002090a06050706240f05030c0d0f140a06050a0c0e0a060f0e03010f051609 66
    0x44d88000c941074540c0000d0001082c1d00c2c403100c19401c510900703c601d202200005920000e011004004007046408410049007860f030307031400318a46004900c9400d000c03034644000500785801603d80381038110704c40c2c80d04030368150b100e002c15030454000c2d00e400c40710403000441036001c0200070109441510250748040c403070319640c0d000207010b0351407982c5c0c01041607940000d2200070040401340c03040300341030050071504a4034003840d0b1241e0f03a100101807a401132040180d4844814014070864890000180c076802141e41000c40940b01c43e4000c403811100a032703466841412070740c0202442c00342d0103000300e108041546041c010044078515504480e1084e086002500e000382c1d0342501000c1e159600480034030b41c1c00d6080c00c00c40e800d40841c4041487c9801403906150800516502c040d10807850108200701458201754200d8200345411000e036000074940105100c12030040b00c80701c031481628604100100300210119095400040350590915116001c0c00409128120641e039a031500f441c2a4190302d2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 288717814 1250 288716564 288716569
    0x6021b0901090b0d060207052505010c020d03051c0606110303100509060d140106060807020c0108150a050a0801090204061e03020603070c06020a0206100807061205090c0a0801050a0515 81
    0xd0188180c400da02c1c1c1c0c40600da41180c075002030340000950090000c54a843c2d80c0c1c10f00a4581444801141030f0352452601d4903c80d1908007181c00a84406940d526540310480c0d091040e5800b84510035010301c88140038030803600300010750485801c01c2e00351011602c2441d0610142070400d105501890507001402000800114200103100710f8104641c1201c0030b0316035201051800030150000380040050588a107220745054000f103045030069a00d14806035a94042203813116400f0303100c180019401400709280b0000c0f1005c2080c2034600a01c2904e03400d949200060b214419544240030031394460f80080290302e02446220018000212031241c069240c01c02c0301024919404001d210b03007004004601400e1250360314407440b55114a046640c0c06033410041e40c1d480d81220540010072441c5008554907001280300c00c00c03900b4585031601c1950117101d48001420b40108001e00900c54140140c256070f8815030058010f01e6030800002e10740c00c024000d5000e54000800c0b0300701d10107a1600c2c02040e42c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 288719064 1250 288717814 288717829
    0xc0909010c0e04021b0313080d050703080f04020103110c06191803033b0607020c0a0e090c1011010e03070206030708040624050910030c0302010c08040803040f06021b 73
    0x42d00100c50041c0d07034010420f0720170804d84980c0c0c0300307803014480425000e44042c80c1900510650303a40c807048581c01e90742c07001c041300c0074440c142c4000c00044105010565040413001c00c1504a07105040c0480c2d00360100c4411a031a8010241c141c1c00342d03000e031080c400300c66080c0401d00e0080d0602001405850302c07041c003442500e40e402d24020201603843c442d030b06440006054256a0858007118008541c03172030807203562028510352001c071a0707000304004245443d0000640400f10940076000741d039260716004141150a40007088030000e802a8440340d140c40d66095004240701140c1e481d04605400950301682c210341c4401a4000940d00c10030400d00569203034001e413a4001114981034038155130318500f001c06001521401c0b07840703442904003103107407460408482055503000e803206041ca540e040f49880d041003071403201808400440b071080c400b40d4461207162a07114010000e0924240c0d40340800d501d503a20940c02900e0407080c40c6824090154180040f500e0169000300c00301000c1245400113281 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 288720314 1250 288719064 288719087
    0x5161805030a0803090f031b010c0315090f0f050a020406140702033703020d020c0409020604030605071407060614120706050c0a02030a0804030b01080607051e0408010504050c0909010c 81
    0x4078440440005d080f80790401c50b0400c40c031200001d40ea1130f90410344201c0107415900744100600e5003024220802c081c42485104164501b880c7c20086441c5803904803801802c1032003600c079869840390300050342e044550117042d00900b202080180e80300d291860050810344603c12400806208103d03c0c0056500002da02411010352031144030f0f0f610020582921200d071803030070b000f0030700d00c421603c005164012a040034991034175001d40301e10205610030001100c86901e802036000209103c1030000c24034031b900017039200b40e482c20000d1100750002d00604a541260b90202e81041d01c8581c140440a20122060800075058401c0c0a2900f20031212549034020750103000304101e07006c01d80740c030598001c0164400780b90b00a420354000725003606110720298000c1c0410f81b00d0804072000061242c40c0020428800c050301e541d900e080544820681038103010943c02c5880040c0d080c00082044c110a101d024010391081c402440c4030500942030001c1001c0007003039025682d02d41104c1000075508081c8001d00c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 288721564 1250 288720314 288720323
    0x90c0906060c1110030b0909010e1603232d010b1507061e23010506070302030a141c0902030c010e0d030e0315090a2006121905161805030a 61
    0x8000c9003940d01100241b40b4061002d03481036544083c402145019131003004400044d6059a69500c0c00064291400341d140c0300c02440b0b594443c005072000b03040004507070710311010b000944101d9880341070344e0034048200410348241442240000c1075000c100344507000c111401078230004040d040780f10340794045004200c0c0140c00141c40e0032001c034580460381540c0c405d03c01c08039010415115008908220404000c00b08074001d58070300000305142c900f1038280e6441d550325074000c51403c24080d00482c5c40c0c2030550260103081c40c0c2030100010070700d607414914603403900302c030000a00060140100361030001e01000417418801c0c4032400000d2600e0743ea1106001d107030941001400c040c80d00b0040b07071900c1c4c148054002c1c0366684000f40180b0704004515205054000c001d5a07466003240354a85003204420a8540c0c0d01c034408008055500c40291240e5901240c13111a400408000c0700d4020140d8800f11060a42081009101d1190613001002c01e0343c150901e8600101d49824003000c640c1c2c52545060192 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 288722814 1250 288721564 288721579
    0x4030e061b03030c09011403010302060a11010902130f0506010e1309080d1406030708070f0e1f0b04061107050a1208071b09050106020609100b01050d090c0906060c11 73
    0x7011801164000541c04403000c2181e5491802009030304144d0000701da02400a150b0305600b2a40e4002d20040c0ea05a030340080503149448001d00090b00c5003103401c0d688181c2ca540b249230f00409641c0d1106400501603030200301140d035050080741c50080314002800b0605004840d03409005640754a400a0f16440a003100012002491f0502080034020f107000c4402a500f0705030400a51000c00405a01a0100364212034005440e00c16081d00c844d020702800b10a22500d41041040d03000c4c10007420741286001108040d40c40030b085400740070b094283c1001500750030000342040f02581c800c00c0b0f6075415884002030240c4605040018000d1062482141c030101c40300040316050142c04800c440c2c1d210750100424404191500f1444007100e1307103210300300915180c42c00001c0c415002181c003038824450071000d4a006c141c18950880102103001c407080c1000302c20321140f84c1c04a003a206e00d000041c00740413620540c030300d000011070032354a0641010003040501d00d4610b0000e00101024049400300301d681c071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 288724064 1250 288722814 288722827
    0x3030806030a060207081809040f060b150c06160e0d08030402010302090d05062401080412090f0608150d0c09180c09050402010315080706050c010209120304080106080604030e06 78
    0x78a0100b0b00480a040035100003500c408001b40e0070000c000c910112058003031580301c00010004080c0c001c940c0640260344080349600003c059511400c10f107240100715041c040c2140c4605040c0d60000b03400c2d440c1d294031403001c1c000741d03840304150814074403000d10b8143d9508000710086002e002e040c2e84001d200e1070001c000b103000c40e03000303405540c80210003411000c2c182e00755042583d86c80c001542d07180400e82c1c03840c003008903c2c400301d03559007040b90701030710390414946032a692449d1000c0c0c000c01020030408200c10128601c10004801001800203541c0c81519047c50240c441c2e24040100d0040c0c0708604040030701c0e0018421420b00401c9801c801308c0060107c4000c045403101c440800f20041c606c2c0720b0b0074070102d07203100d10307074851030186000ba6000c1004003001440404000340c58026034030294030000d410001a88240c00412a034400c1c8000941401d40d940e0106e00d2146400e0448086504049400d025542c02445000300800181c8014003103030500e61009001c03a0b814a603110b008500c000b400b03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 288725314 1250 288724064 288724069
    0x5060f10060513150c030801050103051312020115080a02011707080c07050a05060721050103030e0f040213030b0414011103072604150c0206060906010305100308160c05060c0703030806 81
    0x84000d088221303d00116021294000707041d80d640f0030049000c02c03802c8001254551081c45400d2040c4c4008c80040c1d201501758441050b0f161200d81e0130b10441d034940103070381008120308000304e00402c03800c4000d0403d002903100142848000c90010240d4660420420646e9903100340000c1e00541a41100c6a075040d0750b0400f903080440c030310b40240c4584039800601066030380c41a4801001e000e114880665030090302d942e102030700ca080c840500010305001d860340c903038500070840e40e09010008100514154031800f10344038800740d1b41d00989040c51804108018410f1440c031005405000d000204458420f02c200c0f115030b0300014094a04001c091400b400e5081b0324109486540c00d07050100d03142d2031806182c251071402d082c1c80c504c0703803880c14941e10b4450300f0700000e0f0240c01620001c0c03030100541c1d01c0e03000440090100504842514440e448000f0124403408011710080100d030050310001a0141405100465607920490003031074104082c8107801400303c1d10400740d81d41450101580e4807400700 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 288726564 1250 288725314 288725347
    0x9070b070b01060927050a0212040f020f030316030c060609020c0a03021c02031806070819081b03040f05120f090a0504020a05030a020d060b0a020a05060f100605 71
    0x4501060004003601480807010099040780c001c4c0c0e44040306583c03140048103ca62032864100d10b280380300341000780d82003c660401507001100748030040c18441410003030b26110790251000d0710302c0c03041802107805501301241441d0b040003040e0010340c5400c1044c0036130045500310100203400c02140c94032110420026800400080c40512415511282026540c07901c1e5100810210058440c00384503941007078040d0700c4a02142c44940145007000c00140100c000d40748201d2010741d01400401590002035409805404020014411000010f030070103009040d00c400a4814207940b106512103608801c0c00d0821264443d903c5030203082048020320b060740c40c111001d1034500c2410000300c2d89421700b80c0001301500c103101d030440d00000301c01e95410038002240700300419000000c00800009882a000c0d800901c1080441500020342590341c0350002d105030400b032101c00050f08641c01a40c24030004110168015200c440c0d50001c50034081c200c800c80502c107208ae03d05000e40890342140e450b21454 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 288727814 1250 288726564 288726569
    0xd0513062a141c0207090b040f02210108010506090c07050a0c120c21120e090a0203060301152d08070905090f0316023007050406060503090303010501080907 69
    0x31440ca01811850480b464060110b0720a440e4410040300d10b0b10001c41003400004200550040e1060fa8240144c0c6030182000400c0030303411507181e98000c01035079134a1000340841c40d141083c0d07102150142841e040c00d100d041e842040c25038140014024a41d4a08040981112900640e650740301d95500d0b247c0d09202c03882c54090900783c00c961740007821424105000030540d20035080490200d407110b02c0c551004841c000d00d800003426807020a00014025008011400c0c0c03c3c0c03e04010204c513034000100c80f0b64084031032004654001c014407040341001d000e00e695010420080d00c45a40c10100451038044410f40d0492040e11004100302e100c88005080002402c14402520003560f1540b01c030202804003036811185a1040a41c1c40d00c44a1011003692205c007070560302507000c804a6000c100c804840d032200c400c040341c641d07010080060881480c807000355070100003402c0380301d181c00c0c20031040b40c20582c41f02d800d01004008014400343e000c011681991024280304401e0f84a0f4840d075480c0114a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 288729064 1250 288727814 288727877
    0x705060a1d0a032105031303080403020a08030c04180207050c040506040b030a2d12260901060801060b070c0b13153207030e2404080d051306 62
    0x20780d001c4203203c60f10031503d900300c4a41403914a01220044c084800e48021a4a0049130100700c0031080024802c140c440d030054024812110080380985440607a5402034803090119000001c1c00c014140a89815110058410800b1030800155444450b04c83c1050001c65116603500e50018045541d61741c0508800203020f01180d20012262400c0c4d01507006203000d21050245900c400c01c180c8200126051110b41d2107184900305015562060300c0c000c004811154400703414814003901c0303182c0341d10b119200b649843d001040d0340d4038107031910f800c585998024000900d41040706602041c0c0e00019602211141d1112907521000d449d0100c444d0f00d042c0c4c0003181c00d6440c411005134007513480000310605c040440403000e410110780d1000541140c15001450101c03d09007c60000f00e40240f44c07140480340c01505001003441c0040f030303e9000581410b40040c0b4020701080a00014504004210f041005d5040c00b91905440901d6041e00c0c039500e104040810410801d44140417020000400807400321 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 288730314 1250 288729064 288729079
    0x30e01060801091403040605251205070b0702060601051b0102250606080d0806131509060e06030a020109050d1713090e0c0a05040c020c030708010c110705060a1d 71
    0xd03944040e001e00201e440a5030300320301c4d00308441003c0b4404012607044400c0e43c0c440c9490142c2d81600c80300307007015103050402030030001450030001c503804000607840c866444e030302c3d01c0d0703100322a150003840c0f40b00142c004401c546c042410898545d0300101210300d465881200c14030079070b0404a401d4068896908009004005035005800c440251010f001880303100700780501010780c480c2d030b0031559400081201c5c0001a1900040381081c00c0000010b89410031325800411000042e100c4056544450f41c072080078665141020443d91000700403840d04500220044c169500040d00003c0500c8001d01901307106681560940d802c21140c030b5451000c2c454010b103400c0d1110700094940f940c20b0901d00c1150030403814492031540c60070001c80c60501411008002c0b10790030f41007009000c0100540a090000e622482c02041d696580400c001e1000300300840000c50101035180d00180490f00400c40a0110303401244144220b560705400c0d544841094a0300e110101d40c00140380b07060b081d5090815400800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 288731564 1250 288730314 288730319
    0x1707150e0d0f18050105030406091205090319020a060315090c05040e1501091413020f0304050106150206011503020403080a0801090c0903050a08160b0901140105010c0b06040507030e0106 82
    0x214910814070550340740e6035240d1400440580d54aa548003594903103c0c803000b000c2c0001d600410103150007034014900064480c031079548864100340c980c4007450109501181070031051030200700544414665000c12440c580f11540425180c0320580152014141c440302c1980074030344001a403c004040c001300520040780d07428005413042d03026000348010380d50b5100009508045420700c243c001c0c1410394038084550b10b01144410411180d850741980180c401d4860100ca5520313001a00c07880503e80101541c80c00d1901c1e02900b150690341c006100c1c003084407200045280c0108066045410a84c055100358499090440003445540c100402e00b4602095440031554002c4210b0b05a6440400401c01000050400c2d10309200071f200080c4507900c11030100001401420161003845603c5a4490340c0c0c029640d07a10200c0c11048078241e1580c0c1d51801036140c20340268036044d004020a080242d840c1e0071940354100c0c640030040c0381134055925880450461032090b44080c1007842944002c0110341e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 288732814 1250 288731564 288731591
    0x50304150e1c0c09020307020d0e031204030b090c0312030a0e0a080f03040309060e031b0a0e04080a0215240d020306070e0a050a0632210a0504170715 66
    0x1c1d0030716403c1d948005076a001090000d403034802c0301e000f0700340c1d0f80050420307160040003124041010280e0641500440c44036546036881a0701034005144200d08040c4a8a013100c00d0134a080d041b510303002d120342d026507281001c50305000e0444e41c100c0c0451002141c40ca10f020046440c2088041005007480000942210b030b00c04014084d500031803096607054040340e07844004071114140030f030180d070f815040000385103402d400800c8441034848015091b80c6095960380004280302004030344c00d440100c0000b80d441500d0340e05200c100c0e404c0b050f6402380210760030f001090074075040c00301c4146800c65000391126002a541c6800c54204941d005040780c5181c60b058000a04044090ba8014000ea911039030220b542d18100c92043c0a030703036091b074034120700b00414003840e030313184a40c202c0031b4000041f004c581d003072031003e82d43c020440c00d485502492021428410502007600c001088101c503a071410040c0070029100f040da07072003403c0705001480d40b1048241041004844ca0460078610b442c03803e00c0105852 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 288734064 1250 288732814 288732859
    0x11d1e0109051608040512130504020f0418090c05040507020c0d05100b090c0f0a0516060b0a050f0d0201050c24040b01170c10030212070e040b0d050304150e 69
    0x12145580c00d0103014100300f9068079181e03025180141190001d0680f2010340b6442e0313001d4107442c55040c144403412a07403000400c0c22684408030391551000300140500c030054040107031b258000c4181d02c1c204192082504d40121058442c003960348a2510707000070940c007a20800030240c0d1800020485500b0a000d4904203507100f0150101c074032318506220549096160021283e0300c120b0100f0409880c2020714107110280380e109044600c00d0040610404070341700d107001c13407450b80d9034806c80001400604040400030410403560000384514015203020707e49443d41010740380c170300d030b42824210b494140903800380e410000c1441c0d800840c219401a00b208000100300094000d50080400100503629203000003801910a58400b8460b402041c034201c2d05e0404140414202c459450014149502040007074420f9201f030b500e020026203020482e00051030148174021a030002110000c524808a07035400e80c42c2d000300e201e0011030440700c4c0e14200b44a8000c3d0a80c400c2d0320b200414602528440c1c90401840 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 288735314 1250 288734064 288734071
    0xb0f031f0b0d0302031b0703120203030109050a0c050a030b060d0e01020315010c080a14070602041401020d110a0b13141b06090a210606060e01030e0105011d1e010905 73
    0x102030400c441e400260070890408208950581d0240d45040b903840c150080e08954070301d210855128000c0004040751200900c5005400258041d550300e5140c04915001e4510203845d5901c1280b030441c0101440d0381007021160000c4046c02c005c9200342d0000c00080d140d01400350901c2d84075042c2000c0412022040d40294407800c803401100910742400e0004441d00d003045503009160110400c10301c0740c00b5000e200400c44840c00c904220303150110f103a56010513600030342e00c1004c47c1404554800356560701402103403914940352030040d0156546031401a6154045c580260081501b00c0104132102045034007400076980003030290341403100110030070f84d03608140309c0c0c0d802040147c12046c41203464004200c2d610020000e11031303944182449240e101d01013024440e00d0082d6940b80c2c400001a40900824004000c0c0c0e4071100820940d04002406403906580c4a103110b9160200521241001c00410000307900d2007081c2800d0342e666111501074031b00030030085d2848940e8040c0001841c064940002e4070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 288736564 1250 288735314 288735373
    0x60501030509030928051906031d0601140a0b04060801061716080603190b01050a0605072a090501030b04020a050d05102418051e0106030b0f03 63
    0xd40e5403078074100d48038000e50390200c0e0f00015110140500742c103c3d800c00c0e68044035107807175180071031740c0c0d0b40c0024400c0c0030f0b103240e60880d9555420204021601403060031504000405610710800321065002e0b26410140101f0310154810a88403001e91284032854000e0710307526034035650352501c2d110080d0081e0024483c4000040501c481e010522100c00c1c01c083c025010445010290307a2001c2e0141c6020400805054141c0f0641d00c0041000a10b401007100d610b004907003000780e81d41450b0600c580740f44550050400c0c48410045140010112454141d403600304107400040061030b088051007005042d400002d11900300340c0080300303005041c0c58941c0100d1080703a94104c174a44c0c030424041c5a280c20003001e40030740c022140320000031403e41c000504a0b40d0400ca4003c654511707042c10210407620303030000c54016501c074100e440e680c40395108103030300001c4020160703403141d075210384100010307005000d01001c2544130654400d06444e0740c01142c031421001002e484114014087e5200302000c4e03004c060300c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 288737814 1250 288736564 288736571
    0x1b030b01090219020307030e0108042904021e0901120f0f0305030105100c08190908030412060c0305061e060d0e0a0c1e0b130510050d050a1e0c0905040f06050103 71
    0x840e43c4c0000100c036202549615661802d011650056030b501100802c180c45501481c1600c3c024030603140544542840080d6104030f00b07081c18010f000c2c0c0200703034040041d03080c40d1106248003542d5403016000d045440345803c12041110703903e402090900b4000300240b40c6800390213514109500301000c3d60603100e05569880000b56105000c58880c0c90400c000b51001004000302d2501c2a40003000166000f06c1c0d041203424103648140e011300d10780c01940158201c00440c1c41d40c43c204040c9004200f0301100919060029081c00b400003001c0f900f102c0d4912412250301502d641143c0c40d180103459540480410400000600200344c9807100390140003101c0210304c207c00412401e03501e07514000d801c0d11600b50240040c1c1069108010b5511841c3d12242001c0c0b00a4002070b5562607400782e000641403542c0b125201c07403400061006036400030b090105000d042044480c00742c1118101c2016041e6005004980c280c6504000c0e2110b02d45500084d82007401c0c0301e10a2001c8480741c00c2001129000c1c1e9041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 288739064 1250 288737814 288737857
    0x203030f10050a2610090201022109010804240e0610180906090b010b04030b0c09010203090906040e0a050d0f09050607021002070807030f0c05090609041b030b010902 73
    0x2441c50307180d40c1c000c0980c84401000e00b0310036400044024142825000c1591042d9081c40d0016460542540355103500e0702c6e1215005000c40d64103005817040c800c400c050100c02c2a040c468402510300400000b40d040140f04c100140501801d0802d9101124440300b12800000c0800901d00103041c0701d0036500340910400c07021466040082d00084120b5403c0910060b1180c51054540042c2080ba0f0081d1101c61312805280b02140004803203134000c0c40030405081c1d0b598034500e0080c4510340c0c000c002414000303040c8514109660013208a92904404a61105907552405d00040041002da24400301d603125507218034040207070000341001c006205880704196a03000a00881c6d441146001d990f421800904c400302c011308204011484005643c015101825150002d441c07810a882e4410ba034a95407107048001803040492040001e02026200c483e080d290080224110450241c40200f8a000019200c121100b2155840c400382d40d0101541800b940d50b102f0600203074106040305e540100300380c1c03141d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 288740314 1250 288739064 288739081
    0x304060e06040b010e10090f0e16080303040213060902031302011d030a0803070314161d0d02090c0906040e18011503030302180a12030906020304210515070203030f 72
    0x61481a640070940c80500c1c0e080855240c3d40e80c80103440034031b00215680c07010036200450701501014078107264001411a9000ea8418a02080402c902e01f41c1d0103401c005026107800842141e80c450f406840c917045450301134074200000e00040d0300070b84400d440803044c400400740351350524080b14003d9988020440510300c206000040124840354507511100150300041c00030b2002e158018000e0500041d90f80000c2900300c0c210f8421100641c0341441404c00706c400c140c00c10b00c110342c10414214450060554040882d0390101684000383c400d035080000980001d00800071034294081c0030340ba0b60344441e43d603206041016802da80d84440021140007040401d00c0522403406c7c0414054490681c15145441c1540294000400c4c0e01e1201081c4002c0d00042d1070710b5075808001e040903191060380619905005000000711f4000e0401c6400030042000b906001c646081031540415161403101c40b07c519049103090203902400388140d04260410006940100c00b80d8480c0030030307860038110365a0b007840 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 288741564 1250 288740314 288740323
    0x8150603010b31060807260f04150c0c0b0105090714030c04090501060f0f02010c0206010b0c03071217010e090d030527010519050118020a0917030304060e 68
    0x20289602014080c651030360152484221401d085059408425031105110108101060300403001054600f4180843d06034031108941f034106d032103610680300c0c031900c65015544a40160810441c8060000032505000d0700303c40c1c0a840100081c410452088526000f40c0340c28815070b42a0303100100c900000a06090070f020482c400c20081c0c0d220360a030605075a1000280d08007074001d018084082c48041100340c8a84101c0e4040c1041e615454140d14103031000a28503d0300f540b0345011a410448070102e40b40d00000c0c1c00d0f054581c031414242d2200035004072907256000d0f541003c0c2100150058584401c2d8100c24100d01808088490451036030301e400900308608070544a5102d02d5004034400349400303100307900481e08888003241c900c807802c0454001a840303084404485200b40d544500b80100c1e100000003071480c810782500281305640c90980d160050b00030000d03c5c1001c0c01d80008001075941e11452a0308050040a80e0050f040c0450411542c4d581d0411101198014540180071038004070016 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 288742814 1250 288741564 288741569
    0x110f06090d2a08030711100b091302010804022202130602010606020d0504050118090e010b100e09010306050901060b07081c090f14030d0f09020f011403070e06190815060301 76
    0x30011582e4003000d6071540004d5200405001c10030402001c4100c2081c4140f06440507070924400206413001004100a0301480240095502080580c042e80051342c04ca041541e0043d0110341c1c011409152800d603850b0014940c42c5c42140c1880007038261100290b0a141105581c55503008108264079000240d0341e50a4440801010075000d020800c017540c414034070410505803100c401c40b00a03540747c880c0000d58000c4c0a844000747d440300c2c1d88400f14101110f40c0002906280352105440d01e40c4d002080c00c80f00103000c081d000e16110340c001405040c003500000020400c1911007503070303241603080c5218241c100700b80818005162079244070b00c5000c01d004080c000758210303400c4044200c031a038071040d0390b0044070281c16250109221010603451300e48203c10702d82169000c046804121441000400248600c1c910f05000001c1200b00740001c0a40581c1c0d841255800c0c100a0103460f0400240d80e40070b20000003c40b4550b906005416a50003054203004601c0c81c007001120080000401845001c00d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 288744064 1250 288742814 288742877
    0x1b040e10050a1a070c0b0c0a0b060406150305060d170307020d03150b090409020a060e030f031204080a030e07090906051305250509010b0a09090b030d110f06090d 71
    0x101c2e400030000081d1401040c0b50b52080656800040d07441b401c00b68240c0262158100d16002003d04205000480c0e08090f03101604583c100959824066120004021040040e0405982d040000c42e02d480303444901d00c0c4076403c51113500d041003199004000641c81202c00c140140620700a0b03000300741c02030081000e0480c81e19501b481050900d1041406504400b40c40ea500686415400d80541c444691310409400b4507951140310040d114281132034019044007044c0180e0003044070310380035100414000d410560000d20a6505d4a910404901030406140c220006001c1c40800188800302c540c071010355548034800501059403840710602030404c14000103040741d04004400b041840c050408080040b5103c070400100c41c0e109c40100386042000d800500303250300c0000f0103a0040390445d01e8a001405810414041203000c000401d88449440f040b0500740403220350092101c080c180f1080c15001000001c40c0c0302807401c41516680d030102e1181010200e44451031070707804021076106608d90035405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 288745314 1250 288744064 288744089
    0x4170118110303190509040c1e0c0503040906150306090507020a030521040f020a0803160602090a030605070309170909010b0315030d020a030e1f081b040e10050a 71
    0x340c507460007036400d00088942c1030004000b262920100c540c0a108145125079901c0c0c0c8075500c0340244011255070464540130300c0220700c511035281d000c20b030301c0801d40c022074036100c2440c129503e0302c0d6243d07000d15040007039064246080442e061900c000b810b845014260b03403c1c000705649410000482c0c50984541c80103810800c0b02502080c0203600900e8200440700725254104150090020000720641301181d02c000415582015450b210203003d0282802401542c0b0300022503070086e41190018800501082d0081003000103036950189880003981c020340e080c40540b52502c0c00400a02c1031050440e64020340d0000c8400c444200410380380003000142c101c959990908410380b1464100400e00c4085c5044c2c0b8800d12180d840c00d0041a0840320140c004040f84409454058800e4001c020240d008240403610701c07203102001c40d1a031a550181c0d05100a203038035190070960f990b200d80ca65180d101480003c000800a0440d50418810342d659250085010386800c204032640f40203100d1150b24005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 288746564 1250 288745314 288745361
    0x9020d0b1512101d060711010906050403051b010b060d0b0a0302030f0307050c0d120305040f140c090604020f0922060b040501080603011b050d0e1002041701 69
    0x2149000c2030303000180004a40c41c9050303010002101500c692400c00c0c25604610454114644103008600890130040700361800c07401d001510342d41c3c03400003c2c040170810170310106600b207868081d405103041d150030050602c41883d09080141c20f680c03081009190304210f5141a144444040c030891418400080800d4a450005c1d0841005041e007010b01581c0b08a0b9103c000005983c10044020b040c050440911307111400f9080090800c181143e0460185181c0c10860340041c1d900304007200d412046060010742c5031035a08040100909000c0c00404c580c82e040e03002d1000100000b1809009102114698501d50340c00f800d110a0740506079204841308801d0101d40030030b2034a105803103050240c03824503002c0c2c0a0300022840603a030203030340044161503001a00303000d00d50307206880940c0400254001d10071181410042400d504403090044100003000c41d41c031840c0e58240c0c0140d200454520200c1d264000c0f01901c1000079030040c8644080184034412120360280b06009206400311900e060300a44131 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 288747814 1250 288746564 288746573
    0xc09071731051b03010f14045d200316020405090a08070305030a06240e0f0a08010605010306051219140307060e0f030f0d0c05040f030b0a0f09020d 65
    0x8100d6030a07691301d0f54984192044888240c402c0c55000d91032114405441c2c20507040030701d004001081d10600c1d10f40d0300c0494003600c1207403100312410041819403081206200c48400800303c5411002100d41e000a003a90184103540302c4002500000c3c07030902c107113840d17001c0000c1c1680c900c00c1d01a0b2544107044c0d91203c80240c0360a81c801035025039018184d60601d6180d42c0c80d6010b42d48404400c41c0030820100a1002d02a564401e0724041d2030b5181803070382c5000c4d4401c115001000f05060100c100040040140b81d55282c3c00162580400301030a90100a620b401849001c2d00c024000c1030300182c40d1100000d41172a008541c01c05110280340038200703030f0220a5030751007260240c080540317008070200d40c0b46d1005042040100005805548009200c2201d0351442c1e061800c940038501d4240e00038080300c0441580d0104075614030140d50800180100203032019107840c0100d40c8020b00f070340c84200c00001031041046031248229030b106404c0001441061a010031902005006904003004a2104c00080c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 288749064 1250 288747814 288747853
    0x1208010e160c17040e04030302030906060a081c09180501090f0506010f050901021e102901110f03040b0a080606070f02060307030b150a02011d0c0907173105 69
    0x40c3c81c00e07441280b401e525030340c0345000440252411000285d001040044481c424802a40c001100303c40c1103109030b18081540d5034031101511801c512110005915081c140601000300003030040a0700141013160f2524440c00829003403249405e21800c1c804010f001031031920526100303040584540122501c540301c01c4955402c82e12a150640c8229814012103504161014480704015001403086124240380702040d542c420b042c1038002c024440341203d800c2000c050007580c50b002841c003140d07000104820b1615214510010b540540000580031030f0010320328000344864006a00d82c1c0c1c0260f1503500502990744112507015022001c600101c0c2e005203490001990401340b43d01c1d0110f90142100700003985c111240d40c000d0f48000c00010424400342c0c0a00583c03408240380410b074401c0c40b2948904c26211160803010034410142c2800060304940102e031143d660f802415082e40e071525244a0415441c0c1075241d14820140400f90403034000403000749912080796206015220305600c000a1210b01d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 288750314 1250 288749064 288749093
    0x60c0302010608190302010b030109020619021f06030210020c0d03110a12230304020a050904020d0606060306030b01050306070906112505010315140f0d1208010e160c 73
    0x841d500c90b20002941c0e10200440040310b0741c401341d5101c11965601c1d0281c21a20030a00c020700036418a9070b41c0e001741e5588026a0401c1e0054100719411502c803283c12400d0004104109500115500e850f644028290b0f20503002d6034400e840090301d5007234020041e6551442c50395000e9110b03280324160400248250825100000350745c003169200030f201d0f600c040e0007168a644050000700350300c0d004101c5400400c2c044900c07442c1940c14518509294001c113600070b50a020b094061803042d00490701315158850300292140e0010300810480d915004003c000e00003034401a100091500d0010809280205640303020321810345560010324a40002900e500350a07041002041c054820341241c0307107103495801c0b100842858884400700f4104400034003110800d44205412140b100000d0044000c00107032018005c0085646000700410800015420100004000e106078000f80042e0b02881e044240c0e5410394040300b601209564030f400b9100300c0c648400e80a6000103050000050102c2c9134650013241 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 288751564 1250 288750314 288750317
    0x3010806130c0503030c0f010605010c022103040315020a1e020d030c051902012009010c0609080d0911010f0516020d0218091e06010e0708060f120d020c030109030504060c03 76
    0xb5980d503500000c0c01c58001003659501034100c3d0706030442062080c86003030090318007400c040000c0030207034000c600454450030301100720641c20185d06125160401c1913400455100d17101015044810740c0300d0b40a07422042d43c26000c5141149412081004481ca03003d60542c3c5a0007890f450424503811006420b0140800c002c0c448100f00b01c020142c08014810071540c0e20b42c00201d04030100100c440030fa000640780500c207a0300c0a100e8104a07a03808020848000d030030070008544030000342800c1c10144500001c90b17201c1c516001c55442003001d100f4054400304030988464030180350005c0159400d100d06c01200c014000c4001c0c681005140101c0602000d50001e0080303082e1078040091a00c98a400f49d030340040c0c0381e0000c5040c01b031b042c25145414404080341e5010741502d5141c6528686ca1a8001c1c1c0b6847c10710407040001400344d05c601000e06a40d039001408a00501070841456840d0b0720740c0c2d80300300014060322a0454040c1414042c06d1407c0b0b5140e0744844c541403801030b08994031048050101d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 288752814 1250 288751564 288751583
    0xa1211240d0b1306030b06030d05120a06090207032106030b13030c0b01060908071707060c02010c02190501110610060e01200d0f0305060d12050f0304140d050301080613 74
    0x2405078954001010844030803c200040032415130400141054008041c148203500403101c00044a6105007900c450f07980340d01c00703a1810b0f15654180b4000d44410341020b9605403000c680c5106042d0f01ca002485003100c8032103d07100010b030702c00c8248180c8003180030207010340c00c5004c04141000c000348103403884c0b075001c1d05d03084c28a03403050760b20700002c01c000b0380c480ca0001c0d203401400c0c004000103002450003010520164012a40c0c3e00042c262240350300c0c4641002c1c4113031800d031034095900880c1513010b581e0303009003079020203c00d03074035800926031480c021580011400324003c400c6100010790320380900e940040c815603003894a4011588010607114440c10484c41c0d891080811440030341441c08480c91001900c100e2540e120010040c400a44000f006c06090a090098640302c0c11186040d02d600a0204c1c4002c442404085d5468031520080e994501000000c100620800d10714045441e48a04160b8032481034092007290140420300881803c0d40048010031400b03150700c00c0d00c5003024441c2c01d800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 288754064 1250 288752814 288752831
    0xb03071d030102160c050a060206040f02150706091407060e0303161106030108101103010e04032708010203011a030103150209030a02040c0c0302060117031204050c0a1211240d 77
    0x90700113101440c049943d0b4030035480500041c540f210110b00a00340a1000704840d00e803d854885040c0c0701050041d00400380001c039551030040c408115826140c2103201032059001620f0f1000760019403c281c000300f4018031401186040c8074441c02046a04000e0045040ca0000d0118034003101c1480012120003d00d02101c0206450358409107000708020304c0035120700e0000c4a94801551114010f40603030083c100014003018008a4803590440c1e05841d08002840042c51240403001000d0b00b00301594042e043e0016006005400850694100c0300c901c11742c4441c1c59160b95a107000a00000702110442c00b072403444015149d01410100400408488a40742d064001c981190046240e20000a0903140700744189501004001c4c01032500c0900b841d68070f044590415181c0c011405101681b03079904003c681030140070400690108002400420b40035903890501d08030584e88801150700850b68114075040307182c010080c10740d200c2c105c500304504140c9007501d2503050307005030300030200107940f5000e2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 288755314 1250 288754064 288754087
    0x105150d0216080d2412030e031c12020712050a120203040b0609090d02030d020904060e010e180309010815010512042003070506120402010903051002070c0b03071d030102 75
    0x58003006030081c0e035441c0c4d80c2d410340448036056900c042c03412400c0c01411040c02500104000044003100c6492941d8504030310203281c1150700d02407902c00300c3ea0501c550300a48040702801c1c46c500d5a900743c59215048100c111258450590192200180c4116a41540109410302580c010400031070980b81c600c040c842d4882c1014100e80047e24242e41102c2104208100c074140012410340040030740f001440e078030003c004025a244195228030403540d80204859005480e40d030401c1c0c00ad09505404030441d5a107440c071280407400219400c07014003000110509203101c0100860340c5110042e96408030300d956501c1540c0c102e0300300a0000e4100882044040d444481e908860f80c0500c0c842d10b508405000400d034043c8828800c100800e102e41c10003002008280d580c1c038205c41c0300c102c100386072000a940d680016650202c00f940b020380280a070030100c100c441c2e0940c1c02000900c1c0b003221145111034507424031741da1a000031a604004202e005044e0701c09002c480c403404083e00d100800151414038001007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 288756564 1250 288755314 288755347
    0x140d0501080601050f01110c011b080706020304050607090609050906060c16060e0a0815091e0a0203100504150e0709090309080f03070c0b09030a02040207050c04060e0105150d02 78
    0x840751640001006201d54a407800e40309400d8a801d01e450722040060102c003545680c1c0307203141c09062013200382800030482c04814092464917002031201e911181d0354180745010390700407541201d05000e0000098000c3d4007401c03609003a9a8550340760000e8070300b00001d0164580d409040305500c1042031100d00e2150108010041c0f0030011800c070000c19902d0000d010304410304461a40d0310030140c0701400c0c03064102c000380e040300d030f540c032110202d801e911042202d500701000c100a0b281c54960042e0345944001001402c2c401c407610980c220b07031607120740c02c640004603141514000c00c14104c80340240407214080e00500103213510328050381d4500d0b58850907581100c5614000328041703044110104074070380c024444054844542806545410800c1e62010010801e6000348203480e000424180184d4070204914194258041e01c11592050030341005c0e82c3d80e02c004070034184924107018020400e450a80b448904842d0041e00a602012101080c45044e401c000115030100f03509100200c2105400071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 288757814 1250 288756564 288756569
    0x103050c01020c01141606090c06021f02030705040302040930080903090a05012d17061002280c0e010303080903040b16030c141b1e01140d0501 63
    0x402890510600c80c0064205555800381030305005d20020812075403000c00c0300301e481c1940d001c081e0381c6030744160f450028001c14032604090428a0000350105807942c002804070194042c8180c8807c802894400b000142d00c01251141c000a000380030810050034260400d102e070500c62402d44a54034655004058000e00300c242c0e1418403001120819209038200c207840d84c00003110b001540c0b40060500104480c03681511605040114400c0ca0407641d060305a401c502c2405240190401c41c2a0f42e580100400d10780c005090f00e5a14040c08030300f41d850020008500c4e001c15030050180c41d542003814050030140c60700c581c5030f40400004464005981c040c1140b000c1c2c000414028041e505500703000f0442d41c80200703090b00590003040306000200c0a141030701c050007100f03840700720b0005c0d0038a012a0020580035006210003094210080030740c001080b40c0c540c003c1000030842034095030380100071402074001101211540542c0301c40c812544101d042082e0780e440c62440340d1a05016450140c00c03201d00340e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 288759064 1250 288757814 288757823
    0x24040f020306161106040c05061c05100501091217131214060108120f0706020f0c0106060f0201060e0105060702041e02031005090106050a120b0d1109010509010e07050f070b0103 78
    0x40504107089400134020b0072894010002801c1618066a420f2000042401518401c100105074030400f540203074103c201d0422005800e01c03c9003001c032040c84202701e40703001d11400701c2c3c09643c0c049a4204000842c5c0019600441c450302e52400c07540c0d090320298082e1610440f03007480c0303c2c00070410802100403a99005d21801c43d0b504075090301c02301c0c5820002c06800c072254541126400c81c0b1058443d10549900b10b41032030351165242c0803850b0003030017846030300c500c05440040801c0d00d110100040d40210100d80312901c8018120b41070210880c05c87e41e10740038050010700840010301082c10b0581c09005103501c0540300245010302c980d2000101b070449100000100d400208111034511500c242200403c02982c070440340d5414030002030042d0080c0f40d8002e0401c154083d25070380c0002190403200ba0610042c0c003004082c82ca504102e51540394078816640034240b00d00000070310f81856083c590403101d0603010140302c0d49030707001d00301d41e140d21840049801800520044000c10080d190090007107108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 288760314 1250 288759064 288759091
    0xe04020f0f0d05010f0f0603020f1b100c08070c14010b040908180f0105250804080307030806090405030715110f04141807030908070503030f071124040f020306 70
    0x40015200343c1d01d058001c0700d004441d00008010300c030407a00d800c1c001d66495040c056110041c005003d8441d0140c0800c1c00d010302c0070b641542c0048880070452400d104515482440ba602d2807010a07580000141d61560006418000d102c0c0840c06010000d401c0f4a0584004100f04502500007810784041e008141c81002c40003501c2030300c200c807002036004c0042d4247c40d11490020204006829802244282140caa42440c603001c2401692045013040f88ea0020056480310707192050f803545d9030800c1004802165200d4045031807890003c01c19881345500a00131407410b115a0b8400258100300c80500b20345940350036001c0b07100f40e8414090082c0d00c0810707000c07070740b02d40c5081c0000c08207c08050185004030030403403880000480403040c050340181d2a09000c2800b00d040c0c50804100e2061035009070045c040481031240e120144420760b4000c4240795500c503000114a500a500c1d03024030107610b0040d640021900101c000143c15156100303000b8505041c100c101e540200c0e06200d02201d40d04000c810 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 288761564 1250 288760314 288760327
    0x2040e1c1106040c0e0406090210320706020708040b0307020a150507080a050702240901050f01151404080313030b010f030c0315021306110c040c050306010e04020f0f 73
    0x51065400304207400e10801042241419191203c0c83c0c1e81c0d0740142030144140c0c10004040c4111904800105a0f02030000311644140b44001040250703a084c0d041011a803400900728016060030f42005444000c0c04040d01d0030946a980b41c009601400089801e0002403000103100945d01014520414160700540030082240c9480744100f240c1800c03141c00750b41750605000090703a010b0310b4158081d0005900003140d8440c01c03800c0c0e1800c2c0100d0000712040d40080400c42940714000038450140320720070003c1c040d64503415040940c01009000710a001d2440d032149107e4184101c1b0449040d0f11041c0e5001c2c0f400740c0300c0b1030260940c2d00003e0300c4002400c40702c02c10020400d40300401801820300000075190b4501750b541c1c40390311124a2101a010110b00c41c04094900c076294115407035940d0280090300003130790700c84025014082040403040603005d4800c038150241002d02400c0c0400035240d80c1c041c69aa12000152040440e140c4065006a420311061201c000b00400802d140040c11201d191070b02d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 288762814 1250 288761564 288761567
    0xe070203040602060f0c19030b04020d0b040e0303010501021002030a06050d0f15111c021303051b15093102130503030a0503011a0c0616110a030e010c02040e1c 70
    0x3100039220103d0300e2095030402981c49000000d07074403003070901560340480d0251f2000c1140a03011084032581d000d403000031080d4401a05a212201e0304c1400d903000e114003542c0c0003580d130701c0f80000d01c00d60f800b5800c01d07842c20030905195401103604c010541000200c04da1541c1c080390700d1004031700048035920400d9641505121490f0030700c49207511021000d10140001d5006036055001300c0f0302d00000c0806400d107a00c0350000c6501618a10061210325550030343e44e9090140d038600603403080d070980382038101e54052641009058103604503410344080303240019013070900070242080c90710301c401035544121440c00c3c4190344c03140255a41900f0400351f19601e11000260300503285a122a210360700401418200d150043c05072411038200c04001003503a01032640c200700354412219051002e00810702002500b95580564118459040d40c500341c401418030b20b0300342d07540d6140c24003801151580b04c0515480d80300301d48a010892000d0300c00318111915440d42c4e450401c504000302c40d2086024501c0c02e005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 288764064 1250 288762814 288762823
    0x1050a030f080d050a09150c09060c0312020a0302070210080408120415050f061804020a09051b04150f03090b040b0603010207080304060507020f0715230706060515040803180102070e070203040602 86
    0x21f0164000400c03026107600ba0190000040e80305079030520128213918800c0c140a41841f40301004041c03803e40d66031210403802802540100c508a00c5003220f490b02c14490713442400076920070740d8131035000f902e482d01b604d5414022840045c004c45401d2a106540c2d000003c943c0a542d014103525410501c0c0d90034001c04000409520300e034031450803002441044050384c2c03507c910508440c91843c00140b66220841e030f14004140310031440743d48000000f00040e800581480e0307040000340c03e80e0340c001d01c01c1c0c4881048040d180b001002078120110900440e000c246015081e6030000d000900052400440c1c0e0385d50503007501304407425141c0c0c40c3d8550400201580600c841503040901c540501074aa041014451982c046090f410017080400f03000c0b03074101960480048015825805151b40303a501c03500d0140c5c060401030084600a448100034508030810380c00545003540c0031003020b14209603078011030120b81020855014114402e40c103001a4002ca02603001d401a199a0f0155940d6400c020010345071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 288765314 1250 288764064 288764093
    0x9230606010e03331003031b021e010504120602180103151505090d05341a040b04060909050f04030e12100213080f0601050a030f080d050a09 62
    0x6100d0300c0c102d00c141590300800d10414070801503034003425001c00101d488010208540340070764480340c100c052068002c04d90104000700c0348690b5800030f845900c804210000701c05410000d401c0010107030b42380c845805007460034a614030181750490629640e4840c0701c040b0301c494270080d0b4025038005001c4003008100c4001404e042c00a08003401824900d611011510742d8510408270700801c1007100d03040c800d2240046a9021100908009001c8070700d081c05600c83c0002c1c45402c5062a032030707003002c6a00900700b150780d45051082e41c1d02149a40341842c801d6070b9500300f2a00600c00601040081810200e103400340000d825181c0d40c0400203428841080c044420280c945640d01b9404410440020350190500e40c44a100b03a40304e802c0c0661034014185080c1641d01c103000507900206440d4122161042c1500803581e5040488101222214000f61100f000b80102c9420000e80d580504c040785500c4034040000d48501c140d9490249458101021079000741c80c5e1214954443d01654140031800310110507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 288766564 1250 288765314 288765317
    0xe03030f090a120209160504120b180c0105180f0a09150905010b0904180501140912030f0c070c09180c05100806090c1e0d05011a030106120923060601 66
    0x480d08800d40010381c548000a01030a20212514204c1b0000713031040040e1001004107003406a402142490700c1c3d401b82070b0480d10220000301c5202c4002c2c01000010b1350403039121060315a5841c00544c0706600307806c2c448080c003554008411011105613520b84a82c1807004048102002940041103150749000e40c41703903401400828100710041c0101e07694901114610742003101e00060f4403060726050074241c00a841c018105503c0d0102094901003005000c6c0c2c807612444003590580352101104082a02090300c0e400408a003501c0014504032501c002003041074061018030310510707036031621203040d18446400d1104010008940400300642c10341402c015000031284540d5501510000900a2200401691040f1090300100e80041d0059049900403072007862904050440c0b446450350603404103003035806c03051401c000000c3c100c0e003546245820802104902d4a1646403400840f4506240d00d250841c56a40300b248400040541c0710b005041c0f19031010206e00301c182e82d4076281c1011070080c000d60 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 288767814 1250 288766564 288766589
    0x9010f060b0c0d36050109051e040b2404080c0a120f0c0f0f03050607050403030f2d020a0303060801020901051e13030b041101030908190e03030f090a 66
    0x400c00e60040740c0c040a60321549024051130100060a22000c0414503040e00c0c0190b4202d880c428100000380c102060342c0c02070322004085035840741401800b800010041c2c1d00c0103081c10a205040c600380e0130210311140c0040c0000440d20300003421140c914a03203a01901203c074002401c010402d020b202a0049000c00c4400ea050719103401144046840d591a00030140020280e83c0020402d0160107840580b24540e090301c0625140c800402003041240401c1d102c0303209140c001000148518112401c0c0da41c140d88000490380207220a0703642c49143d580303004117418549441044e01c0d04c10100040c440c44a64010240c20f24981000b50032550240c100361041d9004104c2d55003166003000440780c0343c0d0905000383c965540950030840103800b54060001c48c11212180010a1100f1081d01e18000d5000d09004c600c404541d070f0054048801040b0010420744061040030355001402484a146039040d0900c56040c0224000180c04c55115600c0c00381c0e541c4020454814078180100442c02404800c40e000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 288769064 1250 288767814 288767827
    0xb0d203403050304062d0603150509030901110a0203010f06030b07020a0c1401020705060a020c18060a030807080705060f0a0e0303060d02060c07030b0103060209151c1a060309010f060b 81
    0x10000d1200030001740c12242c9614041100d6101c0240c11802c499002c8441401c0d86c1251021002610203440b0550b415071004071281104402480703160f0040301a00010351034109014010750f40790028202c0368402c0e002303048001c070140e1000c0c0185000b07104600c1001074034509500d0920910362000d841e0202f1540903090202c000342c19031317400710251028070802038051141c9000407441e00b05150015030b045003010401d00d01080e00042c000f013540e20222800114244200c0d0b01001c1c600c0116005a80100c41410420101da0a20028171200d8040c154107440c00d440c60f110740b45081c500741c07000098402e41030b00300111092a0322505502074815805586141440000640c14220158000c2e109000015000d001400304200c04402143d000000d05000e43e0f40c0c1c10040c1c0250080b14025016500340c15242051803da4011a207581c5a00d0f2250f1952091050502c0010f01c200c0c01c811401d035032190016801c1d40e5481c0085c61142513442c002107040e00c40c01c0200e000b0344600341d0100da50101c1c1030041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 288770314 1250 288769064 288769067
    0x3110c0f040506031006080c0405010617010e07031b090816050904020909011407020a020f04020304050a0609080f0c060613060605030109020307030b1e010807090b0d203403 76
    0x8202048030111004522510b0360b8000900f80703200300c0c01c40b210041c0340440004070031501158100e66000c003220701b08181d03a0f9802c8143e900c00000c00700302803030303809190040c4046280c40344d12542101d5070785000500390030340804100c9074599409024002c5982c016003000403c0382040703c10708034095488007540707640c641408604140d0002d00020b201c1c01065001440340c1c9000d40c44408007688640159096081144000e51200203000c001c0c2d000d2503154403a140242014000c582c01194440d0041c98400400d031507010052000301d1003191a040d00700141c41400b20007001501c1d00c115020042d00741c0c0d041250070400c200103c045001445824584100031194010056a04541800002682d203a031001411402080b12282d425801100c0c101020554111b880011207141000e81700d02c02245c59028060314004050b114072986081c003000034954035940c9810140c0301c1d00c02050b40d03501403030300c1400203100c5030004a501c00c0885449407001560f0a2900d0030b00c984207039101c0b007007041d03030300c2e291030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 288771564 1250 288770314 288770329
    0xa02040803090f060d140106020705030a1a0601140f0405090a060b070b09030c0706080f18030315010509030d050306130507020a0b130f050102040f06021207020f030a150903110c 78
    0x240e0511980f40341540100e60788841c012900388402c045420050b5002001c955044e1140a0080305d005100f95440800c480c02c00003100c10400780c00507486084401101240111560010002e60400c200b0010390101e01c00c10300050003145450003507064441c2d044c0302c28030aa01c64000c0c07801310342c503080c41d0041001415202c1103d0b503454000550380000d540302c1611030314600c2080813680c95407003522000511658400f105900468a01c41800100e0b101e0200200003914122100400d80d0810804201100c0007440e0b9030498001c10706207941014207400000307050210300c0045030081000041003064074a0b0400c00304112098102c000c1081e81040701c0c0c025541c0714403402c01805414203501142e100e065000320072080740e50000002c3c180e00e40d00e1610f10f020750800c2c030074218101c00803c1e021610a0012a100440089000c20142025425001c100047d00c010b8102034040c081d0000d40404184981d15001c0c02947c0b070382c1301203092042440c00401da259a24680f64464002042c019101d503150318 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 288772814 1250 288771564 288771577
    0xf0f1504020108132f010201092111010204080708010e030301120b0c0c010f0e060106020708210906070c030201120203190911060a02010603050c06130902220e0406050a02040803 78
    0x40c0100699075400c6900c44440c44da40741c00f0303100681d0144480d00044c481c64030140030951070700248261909100c0160300b62036181340c2c01469142c03c1d90300002c81c1076081c420555140443d00d4080c0500c00c01c001c815089a0141d0004401c0fa0049001406201824015510002c211400551071036141c0700070b03c5002e00c4089802490101c160b400314a41c440103109039100da02640300200101c03142400084010312602c0c12029a0380074050000580900124449040f9503180d8007401c0c403401c2503030005082c40c2c840400210604020304c4070105644481340504001842138030780d038039aa400c0d4000504601444042040210300400030020300e00000b2a92162900401034041010082841c084110908031801c0d65004000800c0207520b80394150030020440c0e0049060f61800d00400c42485514421001400c00186602da81040186000c0d401001d02402ca55134008100086070181c1e80721002590201403807203643c03018002840000c0c852150848000da0045182038902051240c980c000e80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 288774064 1250 288772814 288772817
    0x6360102070f0b0a02120a0201091103120901110109062310050d03030b0301090219090f1808160206030c0c010c080907181d0303010807060804080d0c0c0c03050f0f15040201 76
    0x41413035040719000300044143c03400c03107041c40d07504c0343c01ca800300034028800d100c4240c0d9540c81a04460b000d1b818049845801100c8a10345a0301d000d1030b400064030300c820300d03001c0e02d5050346da0780b5410004104503104052121409010b40710404140401030501850090030380085030544101c108a16a81c2d81406896140d040c10041007201b00e0b0400203004101644000c2c1d0065100f10340e90791401d0344002200c003074801c1c602003003100200b03081540003241e100d1030f404690030800a035403401080c1110042c0210071004404083c4a07445a80480c1c00d64205641004241901048280029000b802804000d24042c80e1514482c03038100a035984d1481e15210354010303255049a089075500392034201840001410494200700b0f82e100008983d031740d000740306420480c080c0c5400403844c076204110960003107410442d0f41d8101002c80701040c0007805110304100034030130034480c58000503c0d070030300101c015030052002d0541003108030303000c50500e18000d2441815800c140b03048403a0039141c0284541080e0203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 288775314 1250 288774064 288774067
    0x80708090307150f1503080403141905010b1e030a0204020f160c03031e05040e0c0c1b030708160308030c130308030a2a03050606360102070f0b 63
    0x500210505501c24088003508a08685103c80000c1c12a50040c00140f0b000b41800c10000c001c0720095041c141550100510814040004002141d000541030010043e03c2d4181d60801b0120248002584000711044807070b42d44610315541540350a07101e1070200364081100804101d080720011703484094080f4024881c41d404070b04d50000111900c180c41ca10080e9201400e625042c80c14201b240001c1c3d0703c000c03400510054030311156244006070782201c81c0b030705885907414181040c100c0100e0305c400500c40a0417903424450100f18081c1000095100c11088440d9002000308600b41420499142c0006400b644024076100c454402c6400c180110b9070000007580e10303031300d40502410b100c0c46410750650704000b003c0c0000c07040c441120001c42c0a004c084404001c44030108802c0590ba040d55002d50600081a60a584501d030198020507800413006000f980340c10301802d005841d00140240200d00c00805080104988110842d83c2c1d640031000d0004220507031508038518038038905030140c00e008050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 288776564 1250 288775314 288775321
    0x4061409180a0b0402040c0509210c06042c01050319050a12080a0606021903080a06180608100b030a020d030203040b0a050d050703062102060f13150e01080708 70
    0x72254846041d50030000181c409841d12401e000c1040d81e0203aa0030b0b4400d5107001c500e025554003507411030f1200b040c090003a0105100c2d074802d1160441d0340d0484851503014425080c40749640d0b84c40180040e01103003080045002c0c0700034401c1054001c3c0501c001051058000511190313400050352801d820001c0440c1818502503d0843d09081280100600c41c001c49080e200805400c0301c00e5900c1006022801c0001c0c5a640030200d0751110810803140740d0954800011002ca4130507110305512002102001c100780e5030300c09860140281c80020f40c05020383d540801c2c06400304c1409240d40c2c410103544140700e074225400c0040c0d12078850081c024482c200d1100c040007014000e000396002400e0f90050302d0b40b5450554005007440d481000668203142c603140011b2945800391150000340d6141020042c1c2c8039100c03400c0000b040304000b806980c08141030059100c2a100c100040150708648404440d00c40c0c6030098250301100c0210117402440552024030901e82d91005140f94440c45510b0489810f44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 288777814 1250 288776564 288776581
    0x60f0904020d0908091207120308090120130603051e0711031810051201090b01031d010e010c0c0506040803070e060703270f12060e0304030302010605040b04061409 72
    0x120b5104200030050a0420400c10302c4640c8014050b58182581c82081c0c3c10808804e45441c0c000c4d50190a99000f08400c811010074402c42c4035a503c00322490001944104110b442107840c00b2031008a04403803800103141c5400403480b50320701c0003420181030030b001e241005c4000c00744100d06058450352000340301c800941c09e00d104600300080b20340580c0a4a590f00d100c082d0014058554000741406807040c0003580008601c00d1040310202d66100100d08050b9080030315001c003803e04642c000d4105a02e4982164540f901920b2100140216000000301c48441c0d4070000e003036030002c20102007404020514030002c15404a281c5901a511600840d0399580b0100152400702c88640c10340d401203000708002c010035030032100c04034201503520402d2480c18140b410f500c0c42c00d1654040e40800340000c850402090040c2012030910521565021071a83e0a0b010503a1464026a0003600141c1d11408100140c0c1071511541075544c0c01610300b40016820b1888540100c01c405240382d004011a800050405 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 288779064 1250 288777814 288777817
    0x703090b1803120c0c01030b01020f100204030b090d050f0a0516080909010806070e010e1c0b010e0105150f160212010c080907060e210607080103031d060f090402 71
    0x200040340909840344644207040040c108003804060003845000c041100360074100e0240e8a80c0385004c40180000c3e074030b403030044018182c0c071100076040d03106150303070b41031420014041070300104040400144ca070392542c00d00b2500140b000d03082c01c1c03040e008114600c1206a000045030b0915100c0d6100781e41c3c515032010201d070240f04400e121852000365003810020491004002c141081c400c0b40c2c60462a621a40240d4450606071001804900081d0500800d94000c0701c1483c0461401010689455480d48070708040c4080000d080741c50b041014014800c080d0102b04c081c0c098042921000442c42403141600000d2203042000c00c4141c0700401c3c40c0c403558011030504007056502600d540c0d90900304c071846902804001d980c0001042c40700f000110407030000a40d160884203d940c03418981c10388102070018020a001c00c1c0100340d48498008002900104500d901802b203e582d20919036140d07090040c41c0d680980e05480e40702e190360700480c1c815035484041e1603100509014039560350300540b0000e8000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 288780314 1250 288779064 288779069
    0x8010c080a052e15030e1522030c050f030415020c0607110d050f0d09140d0609020d0515040b0703020a09140a0815100503070e04080f0903010515040606030c05030a02070309 76
    0x151401c0c500ca49030b2a60640086190f150546d00711015801e2060000010a80823107070040d0b031022034400c0e07440d681c00135044108514001e080c0028005950703100e8606020302024068600c0d41300003020003040740f10036080c4103040c0c7c5500c00f6201810100000a12503c2030f0309020303051101a0841c03e100b581d03003509501d001039210b412280402030100c182c90700c4106c00102c600110f264a100040c98200c10808050100304c0103003c1d04440e41503542da6030040c42103100c16608a6066001c00d0001b0304100001c14203120111180d2400e03182c50b00e003002c041103004005100b01030041c483c3c24203c68000341c220b815039095801003810305030340c1e5001c02c0302d4255540c040c07003642c40b60446521a5881c49000b243c0680411003512009940342c0017410340d10310f014495841600340603030014000c9080030010749004d02e03d0445092410501000083c20744405441b940c01041d41c100240c0342c02c0ca4248100c00050503d030030300b1702c181c4840a501401a000042c44080503d40003e01103040602c5980d64102 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 288781564 1250 288780314 288780329
    0x9060f0d0309060807140702060c07050901120507060c0b0609070234090c0225030c091a0a060e011815050c070e1b0903150108010c080a052e 62
    0x911120500700104104000d00c1250041966079010407503442c8211810401c060740c0c00ca070f40d89030001c84c0c1c2c01c0c03040d40d0b0300402e1586018007072000702003201d0b90350084a074000d0901d0240c0d40c902070340d00c0c00e219080003039a500071010300c13144800e10000a00750740207145d8020700c01c551018944d030710b0f480e060341420381c0e404e00080284480111010b9200e803030240040312001d44804448016102e2182d48111441c8241c0100582c0c00154410110030300d07550300070007900c55140c3c0a00c1d02d558980d44c803699051b0942128403c00e494204ca513591082031026425140c130111485419185000781c090948043c0320307280b90410401c40014440810300ca00280001d003814130f818001c19400b640020100e0300310000744509401100f0000801c1844d1540f16400f60341501c10210740b8141d25507119200d584000b2030150136014000d403417411031010061a9000f801c1484c00031901680c0008014134030340c401400325030b0b5240b6000a004561a03d201c91200c401c21001c2000104d1814060100354205141e1003081d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 288782814 1250 288781564 288781579
    0x150e030a180b090d2d06050402040c0c0210121517060106030e0c060702011704030305150a1d0c1207020c18060904080d06030f11030d0507030c0209060f 67
    0x1250962018150708845112501c140100ba200c0080819603ca03030540b80e03034400c2151a011021070034881d0a08440022a51500040c907500b4140c01d00302141c100080d55225501c0b4200415820640038410301160350346000c44101402d54005209885060b00e03a00c10096816104111506140c0c80100034615810003000e5076503031031400340c5130300044504000d240d0080d90700010350305000f0300405169070300783e102402d845583e08050002035045560241d041015018860700c03d0608070009034001e80c06558041140d103401e054006c80c485c0480c550a00403010b0b400100490780d441034410456504007008500d480c1c039a903400144500441300b0800c842d2828900340700e0465000501d80b220403405466800680d038072090f42d01c10b40340f000c558054015501100060002d012007008050904800c2d40000e5071648a440c0c01c0e02080e044074040320100b031509a002003c1c641041117a1090700d80f450300b5450b003c89903600520000700400000c0c05100901c01050309552032031142c01e1900300160211 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 288784064 1250 288782814 288782827
    0x2d0703020a08030d06051207030209060109030f061b110303060d0c030b0117010b0d020f09070201021b1f0603020d030e06040e0a021b010c05040e040c0b0c0d080604020405090103150e03 81
    0x65840303900540005004a1071704070000b400d41842c8940340d005ca2071782d0000c3c0500130300c0d5400380003a424008101034100002010040b0000d846000c0070580d0501408000035a800c846520040e8001d860f006002804500d441c042d0207070f5030020071258086c20a40d401410624903190440d017244094000a0510707402000200300710352401405111846480020b02094034030b402404007503154030300e000e500321601034000429402c18130f09003a002061840010700d4029071901c4103040e0402840f80c4d26168000d81e000451141085084900c0301421850403c030306c5145a00040381c010300144010140400300401c0c072415604c80342034178000e08141c10301003d20300d8958524802544500d0040c0c00c00900c08078291030510701446022256019a1203407454281004401914550010811104910b42486c08907605846001034800d6152100050040c0f544d45100a400c90b140206218080c610601c8104040d40d5108001070449421140d6880000c10100f04800900304091f1140f0701d610001802 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 288785314 1250 288784064 288784079
    0x40b0307080604140403080414071403060a0627060315050402120106030c170703050a0503131a0406140c010504030801081e0604020f0a0f0e182d0703020a 68
    0x214850000c0d41e590708041c0d900c20b0300b000304032105881c1028007410301070700180000e4051824990041e0003a141c42100c442401015880c042d181d8101001090341c020f5010b4060504000780c54205240e508284405402c0c51514800304074101900c042c4114506081d4513040500d0340b010000d0f542102141071060415025040940001d540403401032090000c1241c120300d0600c56082030300d51043c0c000064901c0d241c2d001204244e010201042401007420000009104010900500b881200038540318280c00d0044442042594020a00c10007401e2280b404065840120b4064076998200348060001c0555490400e01400304030411039841d02040c00b060503040242103048450180c01c40309031104d189040c0c0c05080b60543c0441d03030303980140042801490115a0416070410283c0007a007003a5490b401030130f09034002d5100c0450300c00050300b8000c411205002c4500512082c0d0010040c1c0c505058814141145d17195500c40482160500d500f6241c2d4203025500046400401c000041500c9001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 288786564 1250 288785314 288785317
    0x8060a030f0506010e0a090b06060306040204090e0c1513060f1e0309060f020f040909020411030a0c08130224040f030c2409090902030c040203130303062720040b 71
    0x440380702085d030307000107103400c2c2490041600451380540c078a5020b840701801d0019640000d800603500c548c003400701144400592003907e0b104244000180030380303039911b0140180314030200c0344451465010451407000741c081840d0a811103109140c01c9500d4100f071841262961103101c031100c0f00b808010413403000158103400602c0800d026a030100003a0b1102c0c00c00508074482c00c2c8003a032100174140000c000c9440c0b540c2c00395105900190001c81c5c1026407007240c0c1d18030380c402c50303890000c2e50361020308040d441c2e84003030380c1a40120b070820740082e01c003550340008481c07891017031051628030300c00070205031a2080721003614010240308146021103a12850000d41d005290b001e01900054400e1441841d00481e2508001c0c00d0010384a0303089260421079820043c0442210698252040e50107401c3c0e142c490b4070095110b41c03044180301400b103200c1d02c1d00405841481c1d00c4600c40b8403c1c80c0170a413200494500d0b4103424181404001100c001030400c0b0700c0d080c90804440e0050070004580004d00f10701100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 288787814 1250 288786564 288786569
    0x30c0209182b05070c32060a0c06020310030606060e01030e0d080105100309050d080103020907020607050f07050c06030406061707080307110414180d0804110108060a030f050601 78
    0xc082c0c541d18900c50000402d50044000240804964041c490340024001c20003019920b0107400d545a8a540f00c0034049910120094034003009280314000c2c00c90100c225201b60020070045070264035140300340300010001c0011000140c0741c00c0d8000045901c0c0c40312282c5041c015503000788180180c1d0354445000e0414003d112026000c03900340b00451000c1003011034440c20b584515140d050051342004244401c0e50654a00442416981c0e48003902142042103140300c02c0549a403803060660451041c8075844030080d0008056601040c1131220080e08202900c1340c56400002c41134603004641046880c00c51903034051034200307000005010030f1001c560444030944821107480e103546050510007603603d0480340300b42d40e0150400c0c085100002c00303141c5018100c0c40b0090010480e0020300f4035185e420441034800c170340d14054100441444010512110326150001e040c4190380b0302e010f444400315441d06010090400c04a040041c40968441252034055504407105d030081c0003051406030764640007130 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 288789064 1250 288787814 288787861
    0x51b120106180b1804081606110306120109030e0603091f0218090114090c0904050a0b24090f0a0b0d060303020c0d050a120504051206150405090a0f030c0209 69
    0xf00441c0c0040c2040092040c0502d4000034454a82d5141e032100e206c140c11680041c001454000925004541c0304d0040c041c0d1040c420248aa0f00e05000c0d0800c050411401c1018003517034100900c90003ca90440703541000c2c03100076a21a41d5a60b00c0d944d4441c14040e0800c240c003040c0030a882001e04142443d400391842d4069070b45100c0c00c80c1d00c20070400c25204c0003441640544020440040d0607400d1030401c03250881607800805051901c100c0015054840890303081c004d40da680c070140949483c005072044103541a0052140011003078148545451140811761030282010058800e0161504a0628003d15103160402e46400500034080080d01407071100b40d00603c5098509151b0b03241000e00e00069039801402400824190b40d907152050406007944010b2080c14000015a9200e9801000d4401643d00c040c1c410780c50b121801c0143d02880c0360101c0c0c001c40c509020041e04020010321070200f01d81003512481c0300031940c074080703d8061194200940081000050200a01c040004000c001000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 288790314 1250 288789064 288789071
    0x50109060f0807090f0f110705010c1e05090f0316030506061c062301120606090c050421021c0209160e10050915040e01060903051b12010618 62
    0x7203480c40300e5108503500500b8100d42000070104180a00c0398032074410070b0030180002c61001d0303003003421500302c2c0d152106000d101c03040002d450301040400c0c4100d01e039040b96410300150b100b01c1d0f003a605152034000710409080c8100012045d110f41d549420180043c0e000600311600002103021280d00c80c441b62004540e0f5224000100d00a8078104018007107281c01d0000c443c40c04070072503c1d0000900300d681d49183c450000ba840d03007020f0b41e00c00c5807094060590230150840a403402c0ca451411151281e010480d000e01e400c555009140e0b01100b11030032609040440f028100c41100c295a001000000007540144405c250724040782200d440404510300884519a180d6150040c030100c40c18031180d0940024020714903140c1c80c0c82d00c00b0280d0382d0380f1080d1408504020303040c4042110050f54860682000030080740400c10038502c5075400d40506154030f00900703414030b1552031594440140560307003c02014251010358540b901c880100d00840724030001e02240d50b940c50032401c0d40c0c2c104204800110705 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 288791564 1250 288790314 288790319
    0x5070309151815050909150a091b09080a0b0403140a0f090e04260403151508030a082406071104061a030f1512010507090611030313060b030f0105010906 67
    0x8600c549540c0c4041191130b400c0c545500d0348204082c02400402581d0744403a561000b040940300d880001000d04034820000404942c0509600c1c1811050b14007c010400040c1d814000d080c0b020075800c0c110796012252100d03e03143c0c1d1805440d008a40c405040095078007055010109501c03940c4010001c00d1501d0340340b4215107540070b01c00d04480444e0041c0004106030b0044003170403a9400a6460308010064442c10942c4035984d00018071440c80b00046c1c40c0c1d03143c401d0b49400e03070b68541c4d1000040030703490b006501d0709240060190079810010110411003100d1882201b08200c06110749120000c010500b075078807842860b00f800c00d01021003c00f07010303510300b60000c10031140c825406a007900300c07048081d0841d61509690642001c00904244001c0d07145046216541c941408480110441200218440c03400002c0200b00b40c1d0294000010030101d210b206a283e0404001c6070b40203500c841e43d00384040b0860400d074024091000c201e68061084a154a41d141c0043d88640d0589407523600c144040f56 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 288792814 1250 288791564 288791579
    0xa060f0608070c0311030406080402040e0c2101090f0f0b0604050c12090a0605180105090a08040512150106031d1506090a140709061707020d050703091518 68
    0x5824000d240118015001088002c2d008403142d00b81d82d8400c1c6441e034000e40000c1d51007821030704503920510100d00201c007400110b103440e0081040e0050360760000d0000e183c07020001010b4803900650040e10700c02821045a00c0c540a40101508541081e171010b00841780d45403c03540010401c40039209415400042006450280210b9000b4a220601170341004420b441804860501510508891060b8241c07000010018002d0a206020707214124899051f02d803981d41c02e490b0000d1428000ba0014548800007038958416a000e0b00c40c03d1306c1281e1010f038002021454681440502d0841540c4280001a016031540203158100742c0c240300988a400c501507030940d0703549000303116844000141c0020b1101e041c400c64541d88034055103400319166803507030320015500030241c410500040c0b010070140300580e00116400c500359420b01c602c407601e2901c900700a4540d16007001c502d04000e000a00d190130705204400d1600034150703007001c00310700305101800a0f01544401151502c06e6012500004072003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 288794064 1250 288792814 288792839
    0x103050f0105010f0e09010801020a021c120908090405090102181f0807050f07060234060e121803060f0c0306090721050105041503030212030a140c030a06 68
    0x5145000a0a01603420000103441100d01c02c0d124104005c0c203c5022011951111a91402043d520000594510403c4e030001c1c01d0116508501e0b2088155001d00174916a01101c901d034410300c1d0040000ea5000769180040c0c02d88074407054075600c2410901402280362044d8002c008002e100311518005041e40000e010012015810042400d209507990b01c50182c0200d8410754030901398908203140c5060450702c030a10350801782050740d00c00e5000c9103600065501418001650540c40c109120010b40c0200080412488213030040000d034030740009182e1403004010200e2003c1014080b2610794003140004040c91091422852203482154007081000b10144400d0f4041c6500e910f40314a190345203c1400110840605041d040001c0d0705404100d0318071440001403000d070400c5020819500d481d0404c000d6071861420b40f40004000c1d0403c10000340c001611201340200d40241c9600c940d500071b03001000381103800d0311000440c4d901d0704200211800100451040c040403604008054882c00304504a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 288795314 1250 288794064 288794071
    0xd09051e030a0620070303020d0b040b100e01020c04060305010f0f0c050304030e0f120d030b030c01050403171204050607030c020d090506070606090e161a0a05030c070b010b0d0b010305 81
    0xd50400082c080205100350001102c0c0460740244900b041d2a0010a000c40d03407000340103a0010b030740442d00351800c2c5e80e64082c10880403800c94082c44001d050b0000105842d460704085130030b2141c00135030303170503d130b4001d00ca4245d03101402131017003010907501c0c10204d001e4014044c0c5081c00510303207100903581030745501c5810a8500c4556030503045964580e8180c425510001e83c181c0d00414907072000703115648907015103400c03401031809002401c201c008041d040c1e68442c0c0c403c5110790006c001403031090742d11205840c12241c000741002248200300345010601e02ca00e426a03000d0302c00e10350401040c4840021080e0161b07100740c0d801c20155060200407a150f01441c90b006002a51060303040040e490424050700c003990051701c0c0003030915501c0281c1411070b500c40b90f8640040c1c108680740e1303c0c800b00401c1c5250003032220349180440c0003540c0121401034880c06404205010010002c5103600d0040c4013503940c0f051744481295078950710b47d501602c160f04903803040590b49040c11044605540701c1c2c00740c07600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 288796564 1250 288795314 288795319
    0x18060f0405060c07050303070311010b01082404090f08030f0c120408030712060303021f0203090312191811190501030b030102120c07051e060c0f0c0d09051e 69
    0x10300381890200031180d4086029005103114812020031a503400340002c00480340b0036103134a1074000c400b2030b90b5829591034100704d41c14006860200582105c403140481800848030000090110404000600503d1101e8020b402600104004010461481d0045001d89402c024881040d07588124002c25442085c0c002a450a10f180100d80058803160185800c0820381c03c1503103480d00781c480c42404982c0e46500036001032307000080060410200b10441c81d80a00d5411055165242440e44a44d80b407041c0c442401025840340d0009240d24032408071424408900d560904c401d0030303403000300c3e10001e140c2c207000d8441c0b50784815030040c2c1e450b0a0006c0c0c8804a1103000c4405c103a454200107500034450829910f800d55000c0001000c41d05055004610070540d050b2007544910a50501074903059031120000e0710700c60380100c0a0030030580001d029a10801020440c3d03a04c0c0040b1000702e406011388602a20140305140100862079005985901940e101780c4049551841c2c0400c000a1100000700168 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 288797814 1250 288796564 288796567
    0xc0606060f07030e0f0405190608030c1b060c16090c17190b0d030314060904051e01020f0c010b010f092108040308041509150801050603250518060f 65
    0x70009002c1c0c0300c05108132000500302543e2542c4c24010809448088410a052102c03e11440c0c40d81d4566114060180000c1c0d0011801d00240c100c125680d03040a04034020802103440002e9400d503504801c0b12602070503001942c0348080329010720302000c40d05000c0c100815082030300703006003144924008210b0601c6201c41c0021521041500034214482c102c0022505880b200c003d00c00c1c1d00c81481800e00301e03102c0d58000a0344030610888a44030f01300038000600c100803d078140004101d000130500c4581010880003415443d414441d0b40c028419040403210050300410000c50484042d4015410800c080c0c0354040c070681100b104860100c064001c4c07039548401c94510500302c1540c1120896030307078401c003651442c10f80c582d151910a43c0280d81312840003400c03807001c141e20b5680400906c0c02070601c105522032040400c0ba000d0100c0d00e050090b11f00230540031001960111000001d5443e408090222140031641e04000405039030010005510b22040501d8502e0700c1e080000489113030000240402c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 288799064 1250 288797814 288797827
    0x14030f040902130305010606050a0206010905040c2c040b0f0a15060e0f0d1b0b0304050d0c060f0509030306030106140f0f060408070e1504090222090b0c0c0606060f 72
    0x31000f034001005050340c8410580c0e0110015000b4480c0e480513080d940c07911521a19040d038002c1c80e041058011080d00340c202360501000849003000f1400342ea66000420380b81c10300340000c02c9402d540c500002154018400140b00500440c110014050500b1a6142d0b00556445641d1070564000c0e6035a001c00208120081004e2849043c80404840d13000307084c50401068100050b94446442e0020b031030003c0c1c00003800800c200c0759088000100762805030903082d86880d499203030726840c0120711402070003181884441041441d81c8010001050b40ca8100890705107035000c1d0741c2e41d8100f1070b40350f40258a041c90118590f1038014500e243c00d040200841c0040c000007040c410070b00384007a05280c20480603c400304642c03105101800180c0b005803e040f12358500102c68190760301d13411828500951400c28a1030160700d4845501e000d0111210301d545206450a418100400301311001402100c5400306200030f00d60118000c2210000c414101c5034030b80ca603041003180c0342c0b0603610000e2a02a080246 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 288800314 1250 288799064 288799079
    0xc010305070c050709060801060501020a030926010c0c12020c0901050609030f100c0201060510081308130e040b061005041a0d090614070206070c08070204020405040c050714030f04 79
    0x103a5000c1c031a4540380341c0311501ea541d514940407080e000307468800c4d1a02c83c00e006144007482140d0013004244002c08001c00191070142010501c2d0141400084070301001c550035038024080465080070300700c000c0000c1d40450500510290b0800e0048503004586420b0340ca101d4030006001c25001001840400564609400c100c1c85a00510281e07070140140b000c200d15a0f0000e0141400c2019040000316a5a961500003401c41e2002c1c0c000c03074450700e0a8941c0d003584a501c1103080b584034801d10401e0880e00c8a07414002440e02440038444810a8665404529030020500380c40c0a0f61040c26209540e40710f1008108500c0d088080020000320140000c05c40d40c8074135100c010090300e440c0c618603d0f041000c1c580006032058804190b60441e280c0c0e9090103041802c41c0c8081c3c0c01000c2e032000c1d01c007506003a9802468171011410181018901050343e00940da915412180100720040081061072020359000d00160040c190030b5491180200941a9803000401103035400780c0c90100ea2484d25040940b07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 288801564 1250 288800314 288800321
    0xf010914120f071d0606071502031008070f03030315050306070c0c03060c08091c0e010c08040504151802030103120804060b0325080724140403151107050c0103 70
    0x4541d0151080781241c10741e01100b4407014002e0301c0c0d0030043d0090304413010041300d885a0041c0655001c0c0804100100102e4641200840d184030040d0300980d9079251504584a40741d1507800849181c000c0e96030018125103030140440840f4820303107003804140340c038542406040040d032080300d03055080300c4009000e940c843e9175103410f607500c5038040004040d1280c603018103c80d001840750340031950506c20720030354100c100800302003142950781164800f12241b60060010412400f541e040c003c07a11001da04010840003510090180078004120094550301c1d001c4406040c1d00c100000340e048224000031600460080340c1c160307070700105d880300358441c1c0c0c11088504601c0100b05450701c0d40d841c20755000940e81031100e0741c481d0b504040300c00c080203441905d0a00c2c140c00d984c0030074403d91180300c0c20464210134503004c0604190007045a409940c01030301c1075900c98459810004444d60000b800700410600b00c1009103101184881001411002580710700c080c0305888010b015540700c0101e10340e183d8406d41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 288802814 1250 288801564 288801589
    0x9091005031b090a0213090c0801090515180a09050f0304050a1d0f04020d0b040b0a1a0a050d03030b280608040807110f1320030103080409020f0f0c03090f010914 71
    0x2964001041d585020020423940c05200050001d4010001041001e5803030086039008007207583c1e80c3c2c540381c80001c0090f481c000051402c00110301d0040c0040c07040c130000e82c488480725811030700b0b8503c0801c0f0006070139280d5110b4007545104904d80035000c106031032030310409507036407040c0c80c1d100000ba10b480000040300721008000f241d20018146801e00054442140c10f8000d070b00c42d40c07100d1018102410b030b100c00d8a01c108201901900503155010380d40c0c1d5121a854100d0394155092480f1b2001400c044000c4c1c030344109003503040b280c840382102d4418074681c8144a280b0304503000381c1803a40c423150102e170151130640c1c02810b0300ca418402040031444942201c640300c10001c0c1030181040040c800700d0902050f582c081081181c1d60302c1c0e0008580b000078011302c1541c0c3c84c010558615811a070f2210f1141c0598041d00c10456408580c48400703610139022558441c441c0388140d9204c141c942c1c0d410396258003e413001400307902500e807403281c0d550060401c3c0b800d075403403041010030304481007092065840810 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 288804064 1250 288802814 288802837
    0x90b0d02043b0c040303030504111c03030c0f090501030b1f0c0b0c030906041203090c0b04080c030115170a020613030201020d0203030f011a09091005031b090a02 71
    0x810000400000c4082108100348401c5001c00000381c0b280410344401000300e040000020418003006510300ea0002201d050b01d6041c140040c5984607030519007140c08000030541c5c0c1044203045c50042511400a500e00c9443c480e41d8188802da852032400c403110403001e04800d0200750406828043d640c041d822050001c0c1c4003074241c01d011600041e00701480c10945140c1d501242c81200110240010309407115070024040e0015403a5080c40d03600e42c1e648680081002c0d000201c20044028070900c81d804c481407090b00820400c51441d110000c030240f0f5070192195001601c903170b130b40f10415410103001c0c001d4001500007610a08500d0008010b610b28083c070302c01c0c4110302070100d41d540140d89030b40c060044060608100072200381035200180c9465850301c110000d40d4014010410401100500c113410b69003008021040d806940034070f90303203038000d02ca04d81d680040d04ca410011100e040c1d1003010100e0f4800c80817548841c0c140d030400440d00d54591100350300b00d107140b00002d00744240d0781c009010403001c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 288805314 1250 288804064 288804067
    0x807080c1c0f0207080709020f070507141e0f01050a0e1c06050105150414040605270c040602300a0305010302011713020409060b0a0f08060f07090b0d02 67
    0x1405040c1d05040c0040c088500001d080c84803201155403201c0151118405400108906410034103907550700c2c285403180c821030310780015031452860340c4001940c92031030344102100c00154841019090500301c03251054090540400405814500f220068908010141c07241c1d00c11444080116007603071202d0020000d00550104881d8623840303c0e42840b240d41c90500c100c0740072118910f4488180d4106911040c881c50b0300324a814000070544048504407052808000402480500441e0180138103a20059001c866600313404100307050381200011b2200707030000380d100d1503407510342c40181c5000324041e8500513440380e02c0000b89818055800c0c4900302d860f5072420a50000400c82c0b2006512030139a000000713842d070004108650f000785a4030604001841c1c80040b601d41001b00c12100b42506001034840e5441d46100410300c5041e511a07401a24050840d0401c6600c90048000304c04040c401e20100b8400c240004801840020026010b07400e66078442180c1450b0040d00720154000c41100e00340c0560 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 288806564 1250 288805314 288805327
    0x403051204110d030801080607020102040503100911060304060902090108030c03090105093601061e0e04060e0a091106090a0302120c190513420603050f0901021204080708 75
    0xa460610f032280a110756524052903040500950500da006080b0405680c01400140800d43e40424041c0c45404019400140c0040301e0401c0d842e1200346284660b0069000020311003803040d5a00300c03414250090341c04062a903a5240741c0c85c0e0740d01c6541d03002c03000d9410030300c1503c0d4990711401c02040c401c02c004240761248254110150f00c5030700124403400031555610072501942c0d0505550a0042886d4104480c075500700342c034440b6828030004030340c0c800c0250a081044051b907565004001070308002c003801056241809098004203000903060f54000340e2509440098074054040300c60313002d0050aa0450749145a091010240281e0301f4241c89000d4040c41c4800da464803401038070000103400d605080303d0300c1c1c5070600c809200d58480002c005401c2180e44030540d140000c0c0000c0a04843c440c0507081013a010481d0820b1030f44581c0d04006082841c40025015450342045004590030840c0304400c4c0c654405440c04c13881684103083c40721900b00d00040218000101521555004084191900341e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 288807814 1250 288806564 288806569
    0x180f091909150e0d180e0403030f0e06040c06030b040b0d02090c270a1401020d050c0708100c020d0c05060a0518030d091502120a0f0b0a03050105041a040305120411 72
    0x52001000a99960280340300c9003055601c48003c0080d040745c41e0500d540b03507081100c4c948500500810140c103141e2a40070380110031420798007000038890b0017402c2e14a5814545004050701000d4410400082d003008100c6019113001d11031410601c07802084109400f946a0a0004900d001040003540c0070701440035648000241c1e103500814005803040c0d01b01d80c058201045203044c2d45420203500c2840190b041c44c03d5076000205141e00c04010304007182c480559042c0246001071301e070400301c1280074000704100c65402c913800100d0380d104290251001c41680325000c030b50f0b0380b299050242055102030081112000c00350300840d0095118070098030341c002c0d0400e44d6442e5611460030495015a91035942d0203011078140c0e0408015500d100561521450351a1f4a804102c0517108051a5565140074024492698003403035940300003620324510309030f803814014024041100d00f41c0d0f40f0498122444d00b05035025180300c0c42950315031200e07420010b01004200c01d5810061045032060701d903011441017a13 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 288809064 1250 288807814 288807821
    0x90503030f090405010608091005220303020403050c030109210201110f090a06020309010509011d09010f1a0a0503041506080304081e0a210201020708180f09190915 72
    0x3240806944503402d00030311045a20503482102046151400d0042c442d0011440141c0140545008030b40d5440300302500f904117041411b103101c1039001440150406801d5005481201d00500076141030150b1182458280c540444000b441b1006140c503c0030401582c1d40b0042c00e1110910000400c62007080700345501c0d5020244620043c078001c280b01855107000ba6180c07000d00080c0c40514101424200040d01500031203400d14184015110040d407a2078607981c81007840c01c0700a04200f41542e5030b014840d8035403814040d500c0da102c1d100e1801e540c0c1140d44030888001c101d06a58040c510355543e15007000301004601c0c00c042003a201c0400044018041001c1c10217840c0c040302401e105800300d0102641c6035100c5a84040981041ea4980c0200e00c8541600d443c00f040f0320a2460701d02100e2000f03c1c024800c01100802c500c00126004284695181c2c00c0c68070407006441d00c2c00c551049004214840600b180c2031000a142a14201005800758020303a00c5a8480c061a50900c1e000d035072150183e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 288810314 1250 288809064 288809077
    0x5030102070c0519030c0b16060504030512150907110102070c030525031205030903160f12021b10050f04030818090c070303091415180c060403110109050303 69
    0xc161a0b6014040340c500400c141035034035111501c07513043c545140c2e1440110a994400c0607094000416244603524541c5295115994060400c00040c40c00d860098066004221020441c0030340b18001000580c981250314141343c4024440d07030b8950790b001c43c01c0302e100b0341c072803000540340d5002c2c0504e10001d0303000621200a14412009009184200603030580d180c00c02004402194840e01c800300007040600710f0000540905240c0541d0700e980c0c6030056451881544100100000641e02c0c02061103100381410701201e1286068080380700d02e91004907920400710041e0b030601c03141c04040e0011032501c042c8101055034107083c00c5041c0250300300c0c0e9450541043c1d0060b40c11410004401240040000f031070300b5044411101c0786058100000e428509000e0b200c3c00a051540d6880503500b8030640c814007005280341c1204540302c10060400d4010505000d607012658525200d03042c161013000801c0c209107880d00070304003a0405245484060484440c521400e0501c26169000b15458900384028003c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 288811564 1250 288810314 288810323
    0x30812040c0e18010c020304050609040e03090a090c02060a0c0f030b031c090f15050a0f17161d01212711010c030f0e040f050a0902011b02100f0201060503010207 71
    0x42034108014182c29a0398172505e03c0115042008184500d540f81b1094072096203041da000036408815a907c546035101c0c08000c503610004143d0001024100e0b03030030003640c00702c86600303070340c0241c41c0d800c041401d45610200402c04120400d90030a880b0b4443d50158a0341c10001f4100e071490020140c840b54401a80700c0c050000a00c254010301401c4c00740c0502074001c0540042c4105070401d100f00040960050f9402e2030700b0001d180030b4a1045622400080f04000601d922228030760400301c0c1507210b0601080c6502003c100e142e220300c80c03005e41c070815000e52220b040e11130202c038202841d03d070500891500400c0c1d4101d41e68048850360841092441c00c038003400300b1000c60ba20003082c103002c07500407000d0802d24100451a40c200c2d000036800341d1410001c07511410004103d0b12200d0029000d402c81020844007035103070108104003a062604550348140c002c1c0c0711906aa038234140121103140c51080069000042888000c103410302c100c480c8507455110f8800002c4464540000a09980c000d86003500c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 288812814 1250 288811564 288811591
    0x50d0807060924060806040b04141c030219210c03090b2a19050a020c09071d06040e04030e01021509030307030c020105070806010509010e031005010305070f030812040c0e 75
    0x240200f6a41c440c6002070319142e03009110a1400f0f603964030b00e0100090005007a0310a001d2584c0c00440200a8109040501ea900c80c444851500e8010000d41203821001a481e8800010700c074058040c2d94040551110274141c60070600e20500450050030b245041030b410107a90b0410395001c43d9203001002d01511101c800312115400340603038100781040c06085070490b1503082054014920850000141c0f00c030550800075100c0780110401d909180d4441c400720b0f0000c1c08030341000f00c1140d009048514400720780d086694280410014400c1c02d00450046980600e01400441c001c2030051402000d150014811501d5510235010268411002502c000d401948040705018626030940141911100d007440200014503011000512000b4054100c5050200005123203005034890709a8003e6088080d08840303042800e010881d00801003440260ba0030f018524003c100003c2ca0680c0c00300322074000c0c006608080c0d400c8494030074001c01510494204840302e80004801a024286a00c510480010b80 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 288814064 1250 288812814 288812873
    0x606080c0f100c031b050f070819030206131115070b06060712081906260f0604140712050318090108070603020310050415090b0a050d08070609 63
    0x48181607501a8040c030810200c128510083d60199592000b10341500d0440c10300c03c0d8010008101d00c40c0301d00041c06600a120190b00180000903901044a041c1c0d02101c05034002075440c841000f03814180200160000000300b0b12a41000101d440c00e5402129840c3c0c0111640c40050040100c1e458801c00c1c2502c041401c0090200009400ba8022800d85000b8a0920b40703988400c003142000341c80e00705006408000c502140b281625050203503040441c100b003926221f000901d6201c02c1031600c140810040880d00540900c04501c031070300c90040c40c1c01000e40b51100c0d615800f1201d0b1402c2c1c000c405200300b010002c0c5240d10750000c6041d00b40500c01842c0e5a0305800080135003207003403040c02030152800310010044000c0010f803410413905103160068503926901c00b494051041a0700095009007000c5002d0300d03602d400804070b070440720011020000200d00900b40701c03002640e4450701d603001c0381c1caa01d9400031641c0e010007802d4142c0b003910000f8050009550304e50000c10b500c841d4400081104820 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 288815314 1250 288814064 288814069
    0xd0e06010f0b070c03030809010f02130e0c070b01170f070308040326040b1803070312080106030b03030901212c0307081909080703051b06071104050c070606080c 71
    0x1c0024100340c8401c1c0d8030303200316511603d000030840e100003000c202c040000910340d55000e42c4014071000c45940255034440c40c0300c4184042e0415402400c60008034007001c108521407001c02c440401d94843c0507e0701c603a00c1c101142c10400700b40380304030503940a126524989950709000060107948210322407030300c5a066080070002d2041ca400300000309409088682c0c41c1200c100159002c4403030750000d10b0b80e50381d2880385c1000b86011124155800d071080306d0010003040f40c00d54031141111a55940d50043d40c0c0c0e00c5c0011001d80d90400e001e180c054004110080507544525034905603690089000c103004120f40230481c04942d40f110300b0b002d41006580c03a400c0006420742d261740240084030b00450512a85846004240c8103410068964098040f00da40006000b80c169000030007955090380c081550768142141c40d074940010403820039004800500d02c9141c02c03400e0310f50058022000c00c0b020f1009905100c01050080c0440e2a068814090703100010100d000391809400b00d0001362407110500300a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 288816564 1250 288815314 288815339
    0x1209030301140d0201020a121701090501060f090608010302010c0f080333090a09060b0a08010507020c100e040e0f0d0e090f010308160c0e040f0c05010e060d110d0e0601 74
    0x14511481600f00c0c10710240c1c0c1c0c0000ca00c40210f40000e1040d101442501c02600c032038175060004505101d9000000900c0136640d03020300d049403200d88501c0b4120302000e004a07403040700c0f8081c100108202a0045c40954400d61070502594407a4611945449041e2550011500304407a10766401c280013080c2040e0340340c40a01061111450840c280081c1c0075840044c00210005000f2045142e444031400e060082e00e8029100c5248080d0804050b41d4688055078040c040455000015200348210815030b410700306904110800560ba403005107881117010800030b4841c14010380a5031041e02c0c003910084000f0b014500c0141c49503242c1010814410081c080c41ca01c0003070840b03010854450041001c2a10201201c0882440d1032011401104a03d40928046103d81040242000741410003007081450400c0c004194040c2c400c400c0c8855542c0b0046401c1c0d03181c01c0c01d2681007901030100e0340c0c41940c0fa41215424464000140341000c150218000444038200c035900301031381c01000104400d640004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 288817814 1250 288816564 288816599
    0xf04021807090905040f120c1406060916021c05040501080a0204140d1a0f0109050901050402150d0b12070323030913022205010207120506070809031209030301 70
    0x40c0c802400745003a04000d8001d04051050b80c920350b444400040c1081000000d4211940e404040e041100003404002030030602c00000440b442e40d104503020340704150003d5030300c5c42008000c1a01c0304580c0c2c2c1141d051030000000e180d500c154861510304100200409080e0101d201643d5070740c5482d90700e0f0800040c031580700030701040c0f401c0f84108400e01160045040b400410041030b120a0b5100c00a8070f0f019121444c100200c400d00c14018050192281d40b4401c81c5040f5040b10350184083d4a41c402054201d40c2c00b550300944c4955083e201c7c440103034141000c0e18201c940d000380001d02c00c05103c003141d00661f51401c17094840c0c20500c41481008600e21011100e021991403880100750308220503980ca1048a035401d1155002e10850703074207c0c07a83d804070351000340c0100c83d241081284d1620039040c2c402034041e281c0940111580450400801c1c403042040c1504080102029224510240ca00e608003620100850004004444081204001042c0105a8100119541d40c50714000046c0d10325200e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 288819064 1250 288817814 288817849
    0x50a0602091c020a1e03080d050a0b03010b01080103020f060f180405091504240207060b0a14060d150302030604050c0901060f02061f05180a0c0318290f0402 69
    0x2420b81c0150702c9000021060341c002d0300420326469614600d5804600103940001c10201c0005142a140f1240e0b4100318000c0500c80c44c1401042907541c1010b099600400d00d6074005100280104003500d410080c10f05180005080c15150405000d080d60041d80080001054500d03046040b481d503041a00c169030b801101c1d58007600c039006082c01c004000711009000540a0305528400404400c4c2d480a41d06050600040840d6649580d02e40400070340381a103074091180c1d01100c000241c0007998030001c004800300405841ca01100d51061400420300301c40c44210002c2904808030040c0ca003004000d008501410051115080080c100700d48d50005810075420403c1a81c001103602d500080c0854229074a030000c00d2640c00402160740f03c3e41d01641c005584601d0101600c103500b8000008503016440c11501400440d000003000d80603544400743c400303070b4184c00e44030b44000f1506150304034202ca811003d240210310b411034050072407a082521180e081e41c1c8408140400c51810314000e64100109 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 288820314 1250 288819064 288819109
    0x6180c012f0114100803031303090e010e0a0c050a090512030d05010f0f0902090f0607030309051212010b070203030405060a0306030b0c032d0a0908040308120f070905030a02040b0409050a060209 85
    0x5e02210540b6400301400d01b80340884070307106800426029000e44c9018006260180e000c40d03070344a200c070b01d4180e0b09841d0112000e1801000e216090701c00d40890b1441c1c56161208441103140c1400e012900c2c1407408142d60034002404031104003055805003d0080c000940140c915508200062810907000c0e0b0003124402c0c4100003100310380d2900e07500545101821104161207a030203080c00d030301515038810014014090034482e58030300103c00e400b4200b04840302402c40420381e202e0b03050a040c5c0c0b068010103903155009106c00c110b5450712034024044d1400c00d02c2e01080c65942ca50b182007484000740c8044004000100030854010301035000d45401e0300e40d80412002c001380ca0038001c0741000002e048500d03426200d411000a01601400326002181d1181140d660f030000d440d04a107450b4000d540341941014103c01150300709204071010002c4e24001006000344860550800000301002480b007034101c0e03100d085100c04104140030910b41540100350160365010303218200690ba8810300360b041c0f0303800d40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 288821564 1250 288820314 288820319
    0x50310020c070303031a0301060b030709080a0209010e0414030408030a03051e0109050702010b2808060103150506012703050c010306120b0402030a0807030e0306180c012f011410 78
    0x110320b4122500360800240400e610068038030304415880b1501d4041d800c00e840066410003240055118901d20b60312414107a8540114507190002c101001c0e6100e102c040c01440000c0442048541013403203a04c150101501c954001400d64115a001d00301c1030700701091009141e9014050a5440100e0b044008410011041e4019010b4818021181d01d955200d0004460320300035402040c000000030b282408110140ba10000c01d04518200d10707100c2c0d01c04240009004100041003810790b03510103400c900924081107c4401480010541c9040014403070300c591903100328401a00301c03850b041a60203402c5003581011842e100d06200d81c541054030f45042004103021404d86a106554415503c509a849900004e40350002c0344038041e14400b0005490720815810800c1e0595000042c1c0c150f401d2a65855822141c1200d901c403224030a4002c0900c102d000e40c4211030110301c003d0f64040240464411504207140e036441c111410307038240e5403000c1070600010b002158990200c0380a054001e00d60 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 288822814 1250 288821564 288821587
    0x1003030206010e190903050c0304032f03030a0302070611210c1309050606070b090307110d150c110106060215011a0a080a091a010303120b100e04020c100605031002 72
    0xd04582c405a00d144c0d150b03c5c3e141014130840c101c03104001e0040440740c03a42d4690802c2c0003101c2c20304144c0c2502e00b4000d030329884540307071000720b6030044940180550304190f40d84000b43c01030b41c00464125220340d0784e0b242c0c0c1811002044090030b001030340c40c0c0d4101e002c4c958003600b100f280d05024140509020007404180c810700000003090054078040d402c00301e0951600000320300e40303000b50040108024500c0c030420164004c004041c2140c6401201d4040c034a9030081d0908c000240448005400c03a504040048065101d50304040540360740c600e0b1442c071120801c40e07100d0031588590004001604241c0724001c0b8500348090290141c82190011400d18070032004010245c07150b03850a2052050b840b0006d4600d24040d4040e08450382c00801d240d06c00885000d1a0b20800824001100822840e0383c03011000000d5108500d06050042e261302c00882c202242540e60311968043e60358440d400700b110300d010400901840140c140034040c081440b40c100130400d400c0c9042c814100145901c188007021289 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 288824064 1250 288822814 288822841
    0x209040507032403170f040f031407060306060c060c0c050f010b030c060301080307060b01050705010c09090c050c150a0f0207060c0f1d04020304020607120f2327091003030206010e 79
    0x1540c02a43e45d6507603200520311080d079000f81d600082c590000000c00000380b080002100c2030f2810440c0c141c4030381c50b44846090f0308a0710507000d00000903045615140000e02c3c00e0740300c00c2e0b50f501141410082640c2135075455250078282ca02d544800e94441501c2da0140c10100114070b08a04101e4000341590305107100582d89018008015242c541c81d5040b03180030b6406603048a00c0550080d00034406132010040c003422860051040c101990311f401c0f010007031144610305540c2e40b0345136000600000402402d000010020107010254483d5807568820b0720400e4910080000034031502d004100c0803003150b8083e08051020101c801440202d03840000c011510b4101b0314070b441011140162251039500204999016140000303201c04401000c05440075045a2442c28504030f50b9150a50210324192800c142d00703854550f9680c0020901c1840c2101e000c0c40000310b92030000b424030713030003013070b80a400121034201c01d44110300d110460200502c140360b81880a80d024120f0f0b00325258250074208003c0d20503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 288825314 1250 288824064 288824093
    0x5090f1f381c06021e0a09150305010803070303050403051b0708010b010f0f0f02120a020f010b15040605030a0b060406050c0c010201061a0306210d11010c050702010804060209040507032403 83
    0x28a40c1c0000d001545d0703124913444410402c100520b05844080307480010b0102202d40c0107581d101c110401c00c45060794424018281a20b8000d00514208542e903503003603018010240040f01800740911418006c040380ca11a41900e000400c000e0580c039150404407401c480700d440380c42e41005446008840407503009102003641406a1130701c200103828601c8101d0604068881c04201540e00180109100382e0000304080c00c00301c200c0c000c00c8802241c0c3c0401450000e80085099035202c24030003002043d0080c0040c2d076000361310050200c0c881e255040000e00540c0550003020108502240c06010030740100070b00100c0e82c0c800e0000f0000307641045443e49402c8283c807000c161841300040055507544480084441e80304401da0041c01e00c20110503050303200d10130b1780910000a00c24030f0380d28655900501034500002510b85905150071025001141e01044c024001c0e02c2007a001c2000c00496101c07441506d100f444281da00040315002c10000000261001c500d860f100042c0030380600114410f14801d020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 288826564 1250 288825314 288825323
    0x806100518041a040c050301022a07062f010e060106090b040803030109020c0a060524041a0f0102070e0f04140a0b190b040509030a020105090f1f381c 66
    0x711303a41d92074401d0031050035030803941d015400820b08011500c0d010444d9228000301781103180c035904407150300070b5444596114050001d0300203101c10000d2185040f040c135210311120b804080d484510b211031800d5940b00c0024600c5a4040e0004000a80d801107980c005841030441052619140c0600c1641e40d02040c06500c401c2c55001074500450042000740d84441c582c404028001c0b4582400b208120700134103c43c90004855242d1820f04500d0103104040141003c10300303040381049030a0074460703100b0103130181c0b6056204110010845a1201e030104d4861180303a000c000030f500e01403501c220b26030320810491000e680403506420015000c0700e10075038481c01034041e001d03201c0c00045141010740700c1d03041c60503046845d18042c09008200400100303011a001d030001d0003991219045c8a680f080c03940810861900000200460580d11254002601a81345008100304030202d000d01004592040c03910a5500c020441c00303c1c085002d130101d41428401c03141d41b0450641043e402d0034504455600a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 288827814 1250 288826564 288826613
    0x70c020613050414010f090b090f06120303150109060f0c0b0a0f1a0315011a0a031b0e1002030307020a0803090f010905030a02010f0504020109050415080610051804 72
    0x100403580c0801180040100910611298110444040c9004e80030b00602c3e03170001030303064042179444450240c0031000002404401d16981c03100001c0b48680c0000c0e00140d8851200203610603d0007040020b1809250340003a580c040903815030016102c444503922130000e0101c00d40c004c2c002103800100c3d03410410782102840314290749010000d4001d2400c582c142c0300d81032814150040020305a0300014640310700360100c1c2c4050b41000c600c54864007003442008001d44004407440d5541e03540101420484480b800d0110f010310319031030501c0b0f106280b06108000600000c201e2103080c40c0000a002240784140040d62a60070b041d42c0c020748803000d01c03102502401c000801324035014801c00651440c0c1b0390200003000904400d181c090346036401076090034015030804901d42d09903083d034032405004950584512015601d00710901c4080e00c0c8509080688000581000500c21024050540310f95117180c0d0307640e01d80d410841000b2299420007200181c1a104000700320001e01da40441c14007401c200e00620 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 288829064 1250 288827814 288827827
    0x180602120d1a0a06020a05010b1509061606020301120b06010c0c0b070311010501121406010f060e010203070203060108060a11090a09270b040b06031f0213030b0405070303020d08070c0206 82
    0x582c261240322540d80c124114140008100d41c0c007255400c04144110001c1c0207100c6540c04000d8404415000d4240c00901004000c0030340c076108000b1305100c044080081c1c1415039a44852007207070801d0340040040c906030071140f0f00700410f00600c5070b8800310900302200c151000303480d13410f99451076010b41e084241d030006410b01490b0042c0305251450b03c20708005d1000d50b03101e80300c4204150500c44121080200c2e420b01494080020aa481c1030365034400b01a88090305c5c28108540e00307141c0e9091307141076020030841c02000d62020311032a8040c008440003003290b41400310503241158903440805041100c1802003001d40c1e0f803615592400ca5000410101d6030070b0b070700c60f46d01c06213591100001842d80c1c1c4a0710814100400c0620320361240e4044e12407000c2e560f485d002815205d49076410590406801c0c6075275200d9401e82c66010340724032120001220300080d02c90b90341c0301728000c05680594070303030340412030400c201541042480c06562503480d00303600300d044c00c0002404001c180c1c030700240b0424010441 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 288830314 1250 288829064 288829091
    0xd0506091e1609050d06020a140408030922090308090c0d0b04170f03010816090507050901180801060603290121110739050d06090b0403180602120d 65
    0x20030060704c0300401d030304920400791800400a50051040380d010500c05c280e141c00010080c419078013112001070195280902a000f002180c2c1c2503c080003001302e0850b030101c5c0190304144280303041c0e40e100e40c8604070309040844c1064908646800114490444100e103000054142403640303800070391028141110041c840d842d400d40780a101041c8400d0b1101200029009800092203000314000040c01d64002c3d84030064441038480480b402c20106d241007102c407550754400c2d0a83c818806040300001d0304070f600c88031144d0948019a0001c000282c561820203082150401d0340c5010240d007000c1c001d04a06c000780007804020794019408903400d034540320303003000c2c0410b80c00411200141c0004030ba5980010701c1c2031185000030201da103000e46601c13500d2045c800030440c50300107440c07004040d580c001442c1204006d10016a144121703001511906050300040f00c1c910241d02841c841d4a91071511543c0201200c1ca030384640c2e011703000310350003115459449107926040b030310f0907440d4a40c04105110032204 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 288831564 1250 288830314 288830327
    0x70b031e13050a200301090305040e0402130c02010f0b040605030a030f0210090c03050d032711040c0302032406090d050c030a030206221a070903080d0506091e16 71
    0x4000e062401000320304030802401c62800c00d001400d04040d07001043d03204c4203141c04c89010880060210390100702c00e010210003600d075070358840d1004021100c40078107110307684c1c152b4060011600150391034065440d4a07901d00e0045c12901413094404001c0b8500c0c01000a40d0752182002c081c0600c001461f01501c090310900480307050f1018400180044904d601d01b41440388003034401030b0f92500032480c40c4c138185403090244081031100e115600243c4031240e03860000c0700341990401c0b40d00c05000f100d191001c1d02d80b4001c8500e1811036807401a00d0340390003402c18800c0c0b81e602da8013107003138890320f00b280c01c0b1907035610700b40c4035000f00c140d0301c110651580340380c5686042c050f6a4500d5241c4245400c940030140e0000f0010300c075013404100c9140421340403603251100e55000b18002c00808100241c8045000006a03283d031041c1c440c685001c4583d0340b600c2d03220195010001c1168103540350f03802c22401d41410858550040a090001007203c48803252080c8202c0014090808440c00c1c0313801104a14071481 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 288832814 1250 288831564 288831601
    0x1b010315090911040e061b090103230a060503160e180102181c020321120108010f0b01050a170604021902030304051204050607240c0809070b031e 64
    0x600410801c2d140e4108100304103419540244035500384901c00b10810700104a4030b02426501d001c2120728078a01d440030116130418030480d0b042541e501c40f01d050231140050050144e0903007051340700940c24600c0c101d03002d56449422543c080d0f8080c03100c1014200c00110749804a031b009581c00545510340c440604040c04207030b840c2c119250b0021641c42d984000382d51241d0011030701207800b05030180c0180c1c11207074010711401010358540c11808090490a90451540d99442082c1340c0d883e01d41880c0e541c01c800702c600280c00c01700083c1c1d5140c1c00051002c070144180c110148003420514205500104001d0801c0008400d58014261f0b030804a4665152901500c11016010410141c2481500d400079030341d40003260306441c207124071184230840034528070440e0150b40000d80079034945410345d21800082418065029816040b038002c0c0c0841350001d2040303812004044c6d0b02c0a00505011419a1030b142d03141d04601b4240b0001c1003480580c40703040c0402c1d0b1018815041480c0203555a40315144042c5005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 288834064 1250 288832814 288832829
    0x60e0a0504050a0b2407110d020d0b04140606130e0a051221060d1e0f080406120b06090d0302150a02030f0a0506030706030e0c030d0305060109081b010315 68
    0x241c107200ca102e4554000782c0c0358107810f03504410415200396001000d417170400b00c002c02c1c600e010000c0c000440d400801c4100f0a0501500450581003154013190559001002c1545c45140c07a609000c100010041c1e800008046000244182d0610760005004415100758000f801759070744000ca41e401205000c032801160308a03056541c02180c0000c2681550f1181c4118164101d50210608007090301d030081c140a00c1002e0220300d50321407540d4510410002011b501800018120003140000d80360003142c0b0110f41c85008400c1d100c61074544003034141080d0003c2d07034040d0b0741032254220054075000251840f80038111200010b001850034168200440300c0c40784801341c0346050401600c0f07401030300210b000c0d0400148252042d614842a0012654103070303a4950b1580101504010080c4a40c00580c2e80750608010342e4080d4140200092130504448420b50200b500c0700c01b000301940c1c009204c030006001c044090070b0001d00110b2094116040300c908141856075600c582c2109007245221440034100f203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 288835314 1250 288834064 288834071
    0x60609030f0f010609060602070f03170d06121a04020102060f100b0309030c0634121410050f01022d0307030c0605070306030803040b1b0403062a02030301060e0a0504 73
    0x2c100110340030740304a00078030420604044001402910001d5a14107c548000c9007408850860340c0d110b2042185010050760b00f0000e200f41c0c400c1030340c0340c0304a0005181e500003902e0010420300d07211840422680304010209445420800940d030080350713031a130164100301140800d13078840c2e99480d00f42c61542c201e40f250100110811451000001c0100090349812081354150764414590300c9040c0300034800d421416180000019004d00382401b4012025603904005001140103004c00c03041f10460405107803401068414015003102d54104c0384044c02e03080d10400115044c0d00c001031359422144003540c1280000d1440101004002007032a00c01811050550341e450310141801000c02400c4172060321000e1424000c902098020310500045035408a201e608584e200d440745900c2c030100505072506598040120102c5a51220080020f9031041100061000c2ca070300300741586002e81d03203d1002d81d00d22107a003090300503000019079044442a00e095500d4420341c01c0484c40c2c0040315808640c01c21306 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 288836564 1250 288835314 288835333
    0x180f110102011b022d1002090312030403120b03030f0a0c0f020919050c0a0c0210170a0905010b040c0e1009091109011b0c050d030c1704080f0601030b060609030f 71
    0x1340401c42c82802d0441252160840900d024900b8000344842842c0145501410060120840e1900a80500711000b41511025000034024800b29401145c0440018114400400840d8458403400c80c1000d02a0011400c1c040961041c2d07480340f094064800134401d988105c4010012041203551020b54081d0030200709051041041008040145201c2c600908080014032144c01043c00c0d00c0103d03480340d03103120540019400303000001854240c11001c0004185110310030f60313182141039001c1c3c074a5900c0050140c0355818020f0842b0000c968052069081c09400102103920400030010a141129035249182180a0507203991400358014800b85051041c410010304210001e481140001c4c3c03205e03a1800750205102d8040c003c000700080c1600d07005101406242800c1c04400d02081c030030f082c00c034a04981e98846c45441c00303509a1425580c40d00041c18040144248044504144000020071540d419503444914004004207902e02130780c400710340c00c940c0341e0701080600d40c0c140300341c001d0312030441 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 288837814 1250 288836564 288836567
    0x5150121081b010c08011e0b0c010f0c020c0102010e070b0921100204170303070906051303020303040e04051603050a020108070c0602031608011a03181c05070303180f110102011b 78
    0x103000010308000c501003600000c0c3c0c00131030745070f00c105001d60503c03d47e044070304207140030340c541d000b40d01840c81c19940e80d0081907654000c0d01c0340c009102a150000c0a2440265000900b5540700c501c4900d80c5400c00e90040003500e00120a03280e544100701c4034600c03d004181e00008180c42515481c410b2445031000c01007100c2440ea0051007030f2030302030317400d441d50701032503881503649210944010f400209c0c0980d041102038411006801505048800703425001e076a5000030780703541c100b83c100c050300c0803810041c8020840100103018100c40300944629419203944c803141e4440f5191174000e07060040030301c00245001c0c8924034104005511800c115201e0a1071300b51101c15404000000010a92400c008100805e011468000864142044034516510500500f0711121000300d008200d00c40d4003814241e0303c085d01c40c1040313281050b03658240c982d440c6080c002c0690703482c032444502c0c0400d8074640030041000740121000c850382080968a0f90424200101e0040003410001810030070240d40c48102c09 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 288839064 1250 288837814 288837821
    0x1c020c01150f0305070e06210715050301090506100c030e03031201030602070204050903131406090a0b1201060c15050601120f020711100f11160b0705150121081b01 72
    0x20781c0513000b1182d0341d03510740d0f01403c1c0d0303041d060f00d036564013800d40756501d8050000345c038401e03000044810075111043e43d82c10401d5a00f628840020002c20000720062007048004d109d042d91006c412608440c019105030005020b00c0040840a020449071922920309070f1000c20450311041c0b881c0562420719a52410120020741007050200e20490500d000f06440d4980001a908034a048013076000c1030301d10b080769040346074421001190300144c05100140580e0b803400100e02c020700d558412581d45150000c15031b00311120580008060002c02140280843e540c03850f90101c04070525000500c03929242d0040c0c0e4100d8102605050311418404044111210b036000703440700904c075407104a5901d210308100402e5026450009000511101c10400c90b00c0c03146004e500c112001c032040c2d9440d4410345080702d0320545503822174548103800003921070403c4000c00c000200410b0903091040f06504107c084600e2420820081c05840070514907038040c441100c089945c00841c40c131402070304062141050f40607 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 288840314 1250 288839064 288839069
    0x1d100908010b0130090602030403030c0f0503041a13060e01061503060506030a0c110d080709060503150609040e03070c062304050904030e03011d121c020c01150f 71
    0x650801124000c82c1d40038000958030015042008100b10300035140c2210412520f0f40060070b0251945d003844082001c0344011741c0541d0180c1d030040f410040c8140f0140011144140b101c0402404004020200c0c40c03c01800b4044101c0b5468080e03036849050f81031185601c400c03006003c02c3d1601104080180056000c00122011528851110b0304a814280d0490341248030345034000204000054202519501c6010208420f00340140301c2581081490315080800c40c1a80202e90348800b8032000e1500481d40500502c2286892803a514250785515401140c000d0654050a00482e1000c1140d56907040714903990303030240c2100c0d21203a107410001c0181ca00d922070040424541c0c101c41401c041c03c000450007003e401075007985006e03d0501805800d190080c070540c1004482802c000c0d65640a01444008105c64590b03404d034803400e030760214104943c0001c540c4281c0001c1103440310a003503012103009500002000140c8501d1010740407030140a00c0d1a1301082c2c032003250f8021031401c80c000e0200c002d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 288841564 1250 288840314 288840329
    0x6040908220918141e0c0a09090515042301021201080a0215030a0f0c03290102211905030a0c050313020603041a01080a1b1202011d1009 60
    0x1c032036031040400116042d248000058581000c0c040000c10003203401400801490401c982c0745445980a00f0701103868100191050381010410086515000301c0e040701802c115402080100d40703540d030f03403582d0721601192a500b402c1048001014041e2a051610300302c0e0300185803801c1f8650f1100d84900030341c000d440b8242403481150000c10b076000e0004080784202c1e409004012640000144007641d50001840e00a2164803103020302d00e0075001e40078040c203110154402042c0c00e8400d07101d5121b08000203210007100d80540081c061035a90006002078010014000064170f1803001c2c02c2050503100e0000900b100400d00c1c000041700d0743d40880214469005001e0820007a00321404c01c69280c4029108a0b16500400c2551400f510b440802141c21a101d2007035404e000e02588140c8140b08001d03484110142c01c04004a02403040442c0d49015600305224428100380c1444403208241c2c42620000c0e04018058075085a400400300005a007014010005200180d1008009090311054041c0d0740 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 288842814 1250 288841564 288841627
    0x304080610030b01170c0406090506090618070c030302070501020406201605060a05120c0a030e210322050a0c06030c090303030c09030b010b04170607020c060306040908 74
    0x144040001400041030301e81c40480900280d19102c00d2110441140c40700740611300408110b503203143c7c0d4070b228071002011208408642072030b0110070054400b00c020710080c012007541c10403119000c40001455881101800c00040c823001a00b0124024000d2610040041d0703c0003a000c10900e8101903d12103182c1000e80d081000e0605401c0c0c90340326058058115038843ca00316052000f8074061000d00107000403440d1560401070503980c4540e45480a07500b4480c5000006002075030154103000d00c60750b080200c0018801460302d41c410310145024080c035504074880200204030383c105243e81d265402080d5000483c1c00601a0400c0c40d103501b4000f00440e121440110000b03000d40c02030107054006441c13a00c410401d945162004d8000d003903c1d00d2024104804404048001202000054040d01c1d5980c4c91544a1b07040c4540441d0074101c040310b400c03603613005604201a0a500284c0c1955141c802d6595075100e885681c007103409040c080c2001011001e001c600100845040c00705112020806007900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 288844064 1250 288842814 288842821
    0xc03160501050a06150503040f0201140328271a33030c13020f0c030c0c01020105100920040305010b010e120d2d11060c090612070e030d0203040806 65
    0x1e0650149500a14007080c0240006401703d04081c001c01001401810036240a04440342124103d52041312053b801c192007210303604070400e4591300c00e151402c01c88410040e070002806941c0c01ca0700c0d003c0036802000c8a2003244000c00400c1d504e8128040e22903c0a1003d50070008c0140001c103854035000441004800001c61019200728844c180008003e006070080d00080c2050144c4181d41425548505030200280c048440c080d00040a02d4103486015545605200c3c2e41070781820a46040c0074110380c1043c09200324041ca075610714088a008100000e01c1d0880000e414004030402c00091083d102c0202d000003d01c0010741000d45045000d9a440c0b01c214071200c01c1081c0c03002c41d40780d10b403015800802d8568140f80078107040b13081100811000c0081d041c1c080d08401b9511405100e881c0040d00b582c45401022804000300c3e9080780c03c8208240c01c2008140200b00240075040300b011203001480041010f5900400c3d00740140d01c2c0240c181ca007081c80c0c1c404080e54030742c454410fa030a10310448002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 288845314 1250 288844064 288844079
    0x50a0e0117070c060902030708010b190803041e030b1905130506060f01020109020913050706020118170705150105030708010207080d051b03010609060e01020d140c03160501050a06 79
    0x301e0203501d00200d1044055100c9050407600c50210b294201c0302c541da02c841e0321000d41d03404c000c0794000b803581d6000031415204200502c40c006041080d0113444841c150001d01c00080d020040d2170a40c1d840c1e0340d41d442e200180801c0e91000da01d941d44050400c002c05014030155460041d00c01030307404080750341442240c9070000d40c003c1e00350b505003000d442504800e01041f9689400702200c441030005200100324041150000364021405450264420918844110030024103004000050200380000c1209040a0350041006581c031440103014904106040c2c031640603801c15296003030740050803070b030500c0035018000300003080a00a03107101e4402d040c8005800e21050007241c060746d500007a81410701c01440910400b4080182402c81e43d140400388454944d075251020b507000b090180d581c0c00b455403900c40042d04c015800107400d4110740000d50032250454210144009400c00d007003a1640d1242001d03800750450282c0000c0220350380140000c031050080540240d4000d040700c1604201c100e6480782c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 288846564 1250 288845314 288845327
    0x804090b061306140c01140a1410050603060402071506061b110607140a0b06040b0d0305070b040302030405030106080715050405091503030702120f16271506050a0e01 73
    0x1107040c0210b51201400f885204c1c4403100e0019918006940c01c00d4160301c180360175528140100020311141d00200408460f02d4003418216041c240340b4a25242400f600001c4000d5580c003616020320000400f26030191202c0c4e048881c89a00700c0d940c2d41d07140d504c441c0303103201400c014850000050344140c10b004c0c40b084d2081e110080154412007043e403240b6100c003030118940200e2030a50762151198100714a80310705102c3c1720301b81c920411441c4000d1411500304012540e200401301d00a04441000c1c0000130b4001080700c64161300070700740d510260b0b560300d0124594030a07030304400d07019424151f0000e103840b400240d80c816580f201054901840007814222203d02561044a6000c0340b0400403d5004100c40e150004425010301030381d0ad03085154000ca04116400b079007490644d480585102505c0340d05000b110800041011021030311403800c00301c0c890109608203d2000d0300800b500388002c0d03c03020382c00504044080d240c2c01044541e16040038015411008404001c01c4000d144210550b01c18803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 288847814 1250 288846564 288846577
    0x90d030e030d0302030c1204050f0a08030f10030201080105130624080f090705130906090305040e13020907030c03180f0302060c03070f050f13030506150303130303030e070b04030804090b06 83
    0x81d2040c100000c47c0188003201c1400382c020307034080c0101e003034403140300c40c042c0507102285008902c1a9a64207201d03201e01c0302920000c00c6c1d650162140e030001d1005030ba0100607030f4115a030032a004044001052020b800400c1c19031b1119164048601c28a0a09003041541101461181e2604a80e0b55204520000000000c030b640340b80c1038119030800c0c002e078a0200c6030281c50fa00b1100d40001d000300ca07030f1380b080c0031a41c4081080d000b052022408104201441d11051341c1b14420380c40e0000284981d40c0071440a04016281100b8180c480780341c3c40f0558420b40c03009011184c01103030590119560f060a14150704c80c034405030010f024007400100b003203920788110b07401224942d5900000c1030a1540848964002d2610095054420000d2500300b80c1840d0965020310f001d00e010701218200380000a0900c0c000e42c08060290708180402c0801030b180002e040200d0b44c050034049a10822000003c1c180030403a080300105800101d400320510103042c018009031607000c28208001804001081400e02400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 288848920 1106 288847814 288847831
    0x4140708060f01030c1d0c031302060d02070506070f080106200307110901060207060507121407030806040506061c0c03020f0703020303090c0f03070614090d030e030d030203 76
    0x56140005001010301000c03480c50910310311100d070f1b50080c0040014180071002031100f440030348004130201d42c01450955903949103400c0070000d410a02c1c09480d20b100340d90014400034000d026010780b1400c1c50701c0b03c9200303038a000c2d400c6442d030035490301c80310103144015560415030104101400d9164810003640709070030000000c3c480040c9050b0b2041e01154059003042120581090444580540040c0050803556402d2800d07034528122240f003114425001030ba030424154007503001c034041c9000715014040c94480030f00700030b102d0107003020700c101030b481000302c01c0440c1a0560020007001103070700307016090002c05d400d01142500110001c0d000350b000081000101081481302000011003150000c1d44000a0b40100f41e41c0c00b074600441c01071100d00121520540c00707400944d0014400249240c1b0034800724600100403000361040c0d82c3c0a48504550359100c1400ba0081d01c0c03003039042 = true := by decide +kernel

theorem cover : BRFrame.Cov 288669064 288848920 := by
  have h0 := BRFrame.cov_init 288669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 288669064 ≤ n) (h2 : n < 288848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
