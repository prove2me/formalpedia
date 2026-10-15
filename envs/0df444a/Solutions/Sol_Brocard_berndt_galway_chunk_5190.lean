-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5190
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:02:41.851641+00:00
-- url     : https://prove2.me/submissions/e9e2bdda-0b45-4e93-a3fc-aac96af3a9f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 933273381 ≤ n < 933453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 933274631 1250 933273381 933273403
    0x705090708011a09090711011410060905060405030a030305220656060d02130b1206010c030908011401090b041404080703021f0c0e0603070f08100b0c0a05 68
    0x1441000841c02c1602c8042182d61b1040c220308040068004030658203004018480c0c01080450f592010b020114607101700003011150203a851000784c0d41c86a041200300c3c480e511800d6490b51003d04c080c400280030341c00095001980034491281503040002071045000c00c85000ca40b5541c0c1c42c04000c111180207500d59003520681c84240110010340201c0c600608000f0303810808141e08100360100c0e011911012083e800005803d00303856495494015020b5041407040c5030045180315008103012203020141d4100c42c0c01100c9203040e40d10f40300015139031042c0c402c41c140c0802141c92000302d483d085c240501c1100e01060340c07000c1d506616160b42e1004550043c07803131602c114144086200300c950038100e8260865000104507a4451551809038034003891003c682011a4003100040c1c8030310b00030380c846070300612180c48800c0d44c03140c04000c010305484226035880c003180d66404060b584910800d00c8a501403c3d042d50541181d0300d43e00e1940d13254010f046207034401d9000d00784079404c100382407064400c40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 933275881 1250 933274631 933274679
    0x20307090506012705180103020a0e28020d020f071a09030d020913050720011506030902010306050603192009060c0a0609111206060901120302070509070801 69
    0x2e040000000b441c0c0d452008410219800d044440e040e5a12480c41200c010311004060b01c0340d040c800d026001207800e0910003a8801c0b014880006050284001014411400c454428101803640c45d0a141705401550040c15403c4d42070210503010f0745d1360b100501d00f200c0d865414a4a4142e80c0c41e10042c04151a4840512100e0b1241404030180300003050b9480003502100160b1589040400314030a0754a200480c200305080c1002e00011640004a8500341000d441000b4180c02289103d00e080e12010880382c100200205c0d810040e4500c03c2d4440029244149400302d2442d0b51440000c443e500207455400c41001101c08500c4010543e20400b803101c4404103805d80707500d02048400109004200031503000e55000580f20202c11410304c0000146a44580c04001d0b40000e824803100c1c52501d04141c5014030003006c00160840000581c80e403203104010001c5038182e08002c410b035400c80d400c1c00e08600303602c50307e0b0b808986642d40c006c00070b00c2000c03581da40c0801507142c642c001c00e58501d4004040d401c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 933277131 1250 933275881 933275891
    0x31e06160207090b03120304060c2303042411040510020c03070909031b0309050906010c0f03120905070803030604060b030709033017060f030a26040902040302030709 73
    0xc1a41c001c0303910800c030f9102080000e041603107403020a0414002c18146114883c0000800040110690003c81150929a0b03409403240c1c41c41d2846030040310380f0a03541ca0f1100180000f60002c0d02440000b10841a40724042c0d0145814405240c20703505542078521030010042014480c41c20708004106820381544002d098146507031020945541d1070f0f018013484107403501001c8040c140100306e44a00d01300003031442d403190b00e082d0500800c2c81003a07001d00c0c1d100c1c104007408101958881ea0442807000d4005a00f4800c0c800c41d0f54040c0c1d03070444112000d580117600d0b070741c0030008501c0c2030103180014014007000e0b554a107440020081100c43c0d0760807001110300c0c14410301c18032950001141d01a01d07070040c0e0300248105d542040f0f44504881c24510342a002c0703008070240d0181e61005c54004841001440d121240d2203000402c00410f1484050700c0d01a802500400701042c59101c84d280e40e02d00201c1d0040c1d040c2401c080d03a0f6001d40c802d4002000302500014104110f040401064006203100841084 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 933278381 1250 933277131 933277171
    0xf07081927030b0c07050d0806010305070519080403030b0a1e0e091e1204140901050f0d060b040b090c040609080102040e1302150406091a04060c0210020c031e06 71
    0x42109600020f00385015100004201559440813100040e8000c0c0071170314000100380d0010001c550884546002904005c08641c4250140c07064079405251130781591204030810404031109100180164100b5449440a840340c0d00c9641e03c4c0c10181030020801d070a91040440280d0119500c1c0e4806100401aa010850051004641d03550025001c40003032580004085d01d1501d0104c04100c0c2c0c030000240090b001070001c14000d0301e00f49410094805001c0c4e6a80c8404000d440740000d0300305038210400004007400210315600c400754000b0000c000086c00907a08020440c1520201d4083c84181c60008082c0200c0c0d4018400400070700400d0029441d00b814410aa0701081c0d014102c1c3c01c0c2d18840c0c000100465075039859142c0442616664941c80d00c2d640e11000b025107080c0e02c40d012451201d203550907814084181141c0550f00161a01106400e00c0e50a105420b95070203054130442c0105000020295410f02c02071052520070403414140d2510300013800d0a290000c0c140704e02e09640b540d0506 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 933279631 1250 933278381 933278447
    0xb040e0f0a021009240210110a140d020705060414010504020328140102040f05030c030c0f190905040b130b01090507140d1a060315060f070819 63
    0xd00107a81c16100c001e107602c40b80700140d900c04d0098000191007020900c00840862210200d80303d821032680c21550024016000f0504450500c4030002440340c08002111749c07d0701900701c2090022140c01103615200c59003503200c0891300003039003c45075500b0000c14030041c0205511241c1c50000000000c2089040544c0000d6a03041541c488405a001100d41c50b03003502c001050010302203070000d89165210341516101e034001d42c018002c010000c00b2048020829050019000c60b01c80300c040c0003444107495036030810003180d500030052540200c841a114490b20984000300340180700c00d40010a041c2024608100e181c0380040c00440310b1017920900e130002c560001c040c50f0440e0348c008400281034a030800116a140b81c5c4403201e44c400398000580c000c4282440e80b00c24000c903510800b1450207580d0001700012803000703403405ca0440e0340400c04850a0720340f20380101000c008070050f1718070700107003595043c0310354200185602d44090070385d0300c444455400125000130281211690300b60f49050b20004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 933280881 1250 933279631 933279643
    0x61409010e0f190623030109150302190f090c0c02091008010c082d01090c05090a030312110a141e13090e0109030504171e010b040e0f 59
    0x290400041055886040d00d504503840c0701000082c0520503a40c8880d0010660079045120300c50004030441c0c183c00080100740600302801c20b40850241c03459181c0f810140180c04180700542c403c4400582c00030040c0d80e0005840d003042c822410b00c802c9507180c00100e0718010b625922a01005051115202000f540302c202d80c1401c640c1200c168540d40c80700074200d40481000d4206114030b41c40c1400c441c2d0b1080e0841e100f2845072102154244100061000b2601c0d04040400b501090701010b100512103104143c0100d51140c24510301507040c01a800c00184041301954002e8010806504e514100303107110f030098210948244148600c1c3c1406540300400a0105d912082c24012000c58846807001e40e110420068054614000344c8504100b010781d40c40101e40d2248483c0b4526180014107014018041c0c2c2660075019103a0074205440c050407040c01906410f0a1049806000c00311131801c203000600c00d03901000c980001411415080c18442100c13080e40000f0001e6104040c1000b40d01000144 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 933282131 1250 933280881 933280897
    0x1c021c0e0d06090f080a03020705010b040b150d0912090302010e0111030d090c090c03020c150112081804111902060420030f010903020105061f080403050c0a0503120a05010614 77
    0x4009403d10f00380c00c00242c055040c80d80102411000103045054651640141841038045c100800c40802c1d01010801100c4100d0130003600034a00c0450b10866a045001801c0b2980c03458001188608065589601034905c001c001d07400b160b280c1d4818015540d0045a04120351001e0030030b165610724440350b0750b90302c0c000d400880504944030549141004009074010009080b10301d4244203410340c8440c044d0203034100300c1003409a8421440e400410308184e9030340c28121040c01c845420411703070644401d0b00b19804014400c0589a000b01c003601ca0392030394407404403980381000850351140483d5456000100000c06072004652000c2d06000119080401000c019081070000b820702c8030401d40406d04101010310000125403071f0000c40c500345a0103401c4648034100459200b001e40c020103031055003110a000c1080c001038200000200040d0050000744488000001207844110069071040d1442d030107861038825101900342404000b00c003500482e03014056078201003911090800d00d1000c2402034010f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 933283381 1250 933282131 933282143
    0x4082410182702040509030a050f0d06051c060f0608060a0903020a050a1b0b07030806041d03040b13060801030305160f06061d0106020d0504050108091c021c0e0d 71
    0x1a402001c1d4481c1ea021400b00c08000d8400c0d4021400240490341000412606a000340e040100090380070002200725018100b8540318681080d0314014080026006006410860780d40c641c001308a55450b1442c140c4004905008080c541c403162400c3c0055840341100f200170327076003002003d0200722400301314164054407604000074003050500b0704a00e005940d9601629074004c3d102c0100030300212201a045000c0c0035070f60006403550360200100d0501c00e00c24080c00145940c00070660f03900c1d194025480c00c0210b2541041d51107000800070313046601a50114400982c000b8500d10000002d5400c01c000b054203080c1214a58503588015100303100d41100c00144442e400c804d9010024199a010304058000703008200203915125680301107003099004020380107000000103001c0e480000c0b5003201030440e80e201810a0b1400e030040d1110305001e07054062a004070603092141c856002500c0d910503a20b540100102800c0c0c41018622020549074207040180c10488401d0f203441e0913001181a55002c8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 933284631 1250 933283381 933283409
    0x5100311032401080c010906080f0405100612060b040908040b0c160315050a0c1215031b0e1005030a080a020a050f0c0a09050108100c02100204082410 66
    0x34103004506052041c810440c2da8414030310301001c400241030703942100448415070366840054510720700600c507650000c4c2104000070f00c040c0c0c1518913503030070902c201d04490304caa45000b01c01e0161001500f00151a0074110307600c60501c60030740036400003414251010060a00591607806540c0310301d000b00c0741070060004040c00801d10070806505040b0413201034000c1c05459140010580740c000c2542241c103810100490a004500d00c00c041e540200d649910801701051802403000d80082907a00402440c03078079002000c2014800c1a5407103d40300010b071403003141402d614005014014103070103501c1850043c1400343d41c80c005011114150440318594071503200b090101e2030500103410081160007200d494074484003000800143c450030464072904803540360002d640c11503a0910601030715034025442024200b60070b500c841d034944010f2042d02c8044070301c1600c0c002079a005901c00d2030607a000c0039148103600000003402c8039030381e81000c508080b4181540d06c1885c02215018808201c0d40113 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 933285881 1250 933284631 933284663
    0x5030606120319020c120105060f150d020d09020909120a0503060d121e1103070b06030a02090f070e0907050714192a0302090f04020f0d200301051003 66
    0x3042903c0400000742c2c0c20118000782c4440081d140d072050321003203008200348202c0a03101501801020303c00c5001800400341043c5003000c01114025440e1034130291a0100003c1c24031103168002425071215008001c0340201031071040c03151500006016030440d0300704411310145900c560b422603c0c0380d5454504182c41342c0740d0600160025842d010000e1030254102101a112900894015228101100f840c00d609000c4030b030981d8603002d07513501c01d80150010090580059000e0030380640049019003200c880500f00d40c0418450002900c015088200080800020a03070220f6400c480c0035040d034074080541407940c8090414080e002005028602e92441844048410070290710548440d203110341150348103007810700c00000041c000f4440052018030710100a18503e003000708a076809022130300380d65543c1c20f040d4041c4001800881c0c0c4021002600c1e0419030740c01000c1c02226000300c8046a14010f000c02d000090103060084602a90401c0304102c507801148500508032078200281d01500c00b40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 933287131 1250 933285881 933285883
    0x6030e10020d0c030501060906020d0825110601060504035019020a1a0d0c0e03061e070e0409150b090108031e16170a09050405010503060612 62
    0xa4506480d81034408100c007400d40701d154000c030b003a24609131420059640c03603440403901d0070f8240c001c1e240507902079404001c9503803103010b690350b04c04e500a2401d5040001e90142e1480615207c03031600c009034034080002e003600d105101c20b5004000710b0a2603454245981d0303a1400781c000c3c80021988404003100850080c6032903110700005c903075400c0d0fe12403014000e403038084c407400590500c000f01c0c2e10a24075244030722660801c9502d81d9540003400f804003a85005041c2042c040340044031540b01d0f2092001080e1440039014151304030f41300391940d00c06c8000120a161a00c840244288046940b0f08410140c44245059454010409182840c0001c03d41400705002d02200382c402001c3c10801002481c6604035503203d038145c6842150300e00c60599850040580d2401a0015050741c0502650300055020f40030000300701d16210030f03040c10400c8840752038542d001d40e09200c2e5003551071400668210000c1c0e1085007500501801c407010015541000046686e0b202c0040c0301d28011441d20740400d140c0c41c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 933288381 1250 933287131 933287143
    0xf080606071a0c03100f1202040207030c05031903180f06050601090e0c090f060307020304061d1003050a050a0212040813171b0d020108060d08040b0c010501030507090905060106030e 80
    0x1000000e00b2030141000282da61a980c0104c4a44001050850000c1170030001e01c000704080724503004980c4910506034007004000d50003a074044003440080c048100c0011170600c00b8100c2124001d00785a02c205410f100501036030380310170301c0007441c41580e003401000500303030942c0d41c980580241c4000b4a580d984d4006940701185a0046848103035a00100041600c00b40c00500e107a8805413928142e0300511014003140e1701058403004096002403100b88580c0c1c0c85000c40d01e56690072a400038172030810710008105030043d044441c60010f03440f44100152900c49000700c0340c0040089030214075007803415140b00c0c040c0034007502c002c0261100103803582c0405060b850f6a00903260341803100000c1c0840310f03002c665596000702c1c10300c09090152000991486c011480d80d18450701a10ac0003203595510041050300000010111070400707051101083c81e0321641c020340958544000001802e50660421a2905500340d10940c0318a0600e40500f000802c041030305411036005080204a584640d0f00a5085c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 933289631 1250 933288381 933288413
    0x7021e070f1e05010207031a0618091510082d030c150a02130603021e0c010e1c05090d0f061103060103140c16020f090403020c0a060f08060607 63
    0x140e0410350128100c450382810000b0a003074400980034403640d440c01aa1103120703610018082d20f40c07050000e51926102e444456002d60300030100d4102042ca4010a44103201c20340d03d04602d9448500030300c1c0da08501c110155004542c404160000b20301d0300d11603d5544682114124180c125840c1e016580c800c5900c0546218103001e045d2602d602e40020310701e540d010354900600c6444003220104211900d98400c803480364280306140203c007030074a181640a540448448a401000c028500c4071540c10f4401a101d5081614004918034050704405441c00003180c041d480080c44280403500c5103034000040f01d2301240c050b01c00c05501e91044c1804000c2903802d40340a840d035410f01030400380c24040310740107620a00b0300f6281000680f515050100691004554005025401b0411031900010205e01e41c1d080324401003485064030002ca010441228095070100c015900c8084000317103030f2404840c008040e061902d001445c000480000070710078100074110600554001070341006021281c50300d40413817 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 933290881 1250 933289631 933289649
    0x303060d060b090c1c090309090209210f150f010608100308390a02040f02090a0e01090c02160612271106041208030a1509051e07021e07 60
    0x5458524041c02d420340c403007540c4903105c10000540b10b031190400d10618601907011b90303507a2006410b0441c400000c1d40000840340d8020940700c42ca0040701081c40011144040d008050308407000c01b149280c0c900452000501d2440d4400d2013080461801003111314112405890003c1032601e504070030010038900345e08082c00340e100c00100e440c001d2030702902000b140020141c10b82074800700d1750b1542014070740c0045070140b150010982d0201600d810b412180503010381c101c005141403814800110209120341c84076031030f40d028400400c042001c0d44664002201a800648403100c1c506031001a003a20360f00881061200c192100543d20200782e210910005012510011110950094000c080245082252606d6602e210540b581c1041d0080d03030200c0d500d0140c40c58102ca00da5641030040d405c02030042c805155140303e199168088034103848018040c07060001810704001c900c20701400c4c42d0000c00140003e8200074001031a070b00250110710640f00038511030111006146e0f1500f05403065020441d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 933292131 1250 933290881 933290899
    0x601050f07030914010804020d0b0a020c030a03050604060915150e060a0c111005340b04060e010908041e0f0807091a010905060f040f0308030f0601020a050303060d060b 74
    0x30941c10520300340a964414840e84204c4c40c21100440da545421138000f5000150101c6410010740f9082505400542e4110050300344901488503501c2d64100c2d0240c200042e40301c2c8248407488c1028401c1c40090726801d0310601407000c0e07984255034044607510880040c5105502ca10340c034240310761810602c07081c00406103560740a88030401009614039060544045c0c81c03001582c011860041c4802441880b0b9460b41030030b102d034101501c4984000d03071003001c3c0d10100c0c0f42103005481d950110132a08945c465540005d06041c607052190480314291680020b41e03143c4180c40e8041003000041e2030444190301d01080000708681068940050315501418145841e0000850311140c041545000e4035a625810007800341500c00d40c240c900540880c0a020960a000a220701c2c01c292004180c0f50b03480c54041490b0503681d00144c010404658000d0ba000700c804003c1c081c400c03070000c00d015044182440200f94002c6035842d200e03224400078100900c51840c8001c480100302c1e5070740100580f05001841160 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 933293381 1250 933292131 933292133
    0xc011101020f161a0403020706031d0d032a051e090d08030115020307170c0f0d1809050601270e090c091b0909071403070c051006060509090601050f07 66
    0x2200e10f8010104460100e915030725800100c0e03248400030b1103690150300902d1203034034140702640100300e1400b850311b286190721926480420300300080c0240b1141980c0000d0380c1c50381100025246150311148503e4589012a04200700d503000040c7c90062541d000c4204030b0a8040444070319910030030b41c1042c0c109069a81840c280200d00c80510304070380070208d92244182c203122040740c40b885032243c024001a040f0001d090301c040014040e14000720b80d10101c0c1c04c1e0754400c4140d285800c28a031131440001d6844100c1d401058207001030a401010b14100622841c1040400600030400c041d00c003822270320036a4140b0848944983d000f400a0105442c5031030709041c410f003800e840384040e4003154018a031a030041450082c29810f00b40d01001880a140c0c00d21081e05c040204801d4094010400c10404039a440e82650b480381c02540a100740d5181c0c646605d100d0716045042c400d0710076000055034903100f000c010035034101c01100e55804088807c0d20540d41ea0100582d0729019801e80d40d040a6000318101c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 933294631 1250 933293381 933293407
    0xf0308060310090803150d0209101401050703020309040506010e0a081e030a054503070e090703060902240c0106241b0b1603060b0c0c011101020f 64
    0x16015803000c0d8140c1d0912000d20240509550380340c42c005001100400c0060310510a040d01260720302c1c5e0082248103e80041d40006880e040152240c4540448c80c541c00c026440500310030702420344003820702c0c0f828540d103524003941b00d0280060050140d9211030000f2040d0388070300740c00c00198900900242d0300d203803a811120b81d501290f15001543c50303010840c9403143c02000058510018041da01c092074025401d81c541c107002450038400d00060b40c00c0d140f252504003000120a4981004106d8604140310102010314203101c039884800b094800c00288808894081412401d40e5000b0b100840c0f481140d102003020364042100303158404017400f190010825038078000344000c01c0c404000b40866a190011035802000074005402c1d01008045c01183c19030051f001c000d25005a01520360f64080940c035540e02441086681d1001400480e001c6d240030358151099a001d001c101005605212083c06140d0703a41a0003030815050140d036645c038420b691406d40484840d00614104140c40d16155a205 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 933295881 1250 933294631 933294647
    0x1b0b0402130221060307050a26010f0935210109021c14060405041e0501050604150e07030207080c161503090312151a0c06010f0e010303030510030f03 66
    0x81c40c00104071400700318a445d0000c1c1c21000d40e0801088201c0151408000c42c6075600004d81d001c480321000210f881d001ca0003841041c0da4141c80c5000410b4998403031238200d40241c2c2110343e040380403101c040c2e56100c0001000110500700c440134101c0e40d483c1508c010340c0540400d0b900110522003142000881ca0301c6d11900604110390340d090001c01e006030b00022401c1a28400203521065029890000700285440e8002c1d540041c018a20210a0030060a94100d48146104140e545130f4580702840fa840c00e00e80710300240c804507404200c1c00103040283c20402240c0c0a03005e43c04068000c00c110301801103000859904150b50390890380e403e009200228449040d6108800f10040794404500016001c0c0c0901d10b2042c0d41580c40c00a410440c1c00c6020040c6103c0750f0001188040c1b49000c46e0b01c00100030400c00442584d840c2903114900c40c07124605d80030050304258402002d103a0104115240c40500d41d0640b0b0b41400c02261a80c1e6039204a135514202d40d2000c1c040070f4001e5540c0003415009520 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 933297131 1250 933295881 933295927
    0x2120103050a11030303010e0601080705040b030a060e090a03050306040c09080d0207060f0306061b03020c041401081b030a060c0c120f02061b1b01061d01151b0b04021302 75
    0x41880c1401180c0f08042c0c89000900c07a25100111082c0050760a41c4a8840c0581c490a9400d05504054594800c0c1c3c10075001107030050300c000d0b55440140041401d000c240b5030700c0b030182002802110b0a5a4000b00240405001e81c0c0c050b85d107800b226035540780a0794840020f450910304855103003150003002540c0b20a240300e403c0100e0040264085c7c0b10388a8007034002034500340d44401c1200ac002d04403e01d14070b40e0f080c1080e81180212240740b903242d0703240e025181821a0b4550003c00300e504000f0030a00300213134900c0b2041020541d0064205035100450080345c04d5401c9072000540001d01c1c6819101008050b10007001041d0710f5070400c1c8119000201c217a071072403c560888074240d68000c4001c52141c0e2410392005190030074844c581842905010340f4203000c6005002080a59072004400c161410001a40b948070107000d005211080c642c50381f443c03400c0c01e18039042e05a441c0c1c8070210001ca1190407009889200804d000509544840b54501301101c601a8210741d00d002c0301448070160300200b51 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 933298381 1250 933297131 933297143
    0x504030215090a0b01290a0c02120a0b0c0708130e0a0b01171f0902191d0607020603040204140a050702010b01180e10080f01021c150603020d02120103050a 68
    0x1010400c1031500240d4043c0140d80445101c144da400e10345542ca401c26048140d21911070300c04154a904082030000d800f951081f9103401d006445148100401d50040d030190010682c000c081a901090411180c590440350300c03100d0503541d9000d8144100948201c4090000200d6800700028403120302c0c0c03c0151244507000805c0100146620044031200d0050360041404d60204010400701d10141528040001074941150020380d0381c5d859003410303a0040f01d0080d0200d03582c071074503840e000e800202c20048158140c114000300e100d0540010f400d030207030380710180c0102e070080001011501d81e90701440100d580100422014503004403650301a0200720388a00055080074a020041d5014000301080780000000610041d4100406081c44100040c450010f010604600144100d41400000e074800301210025a464040300b14104001100b800185d00052403e0b00403594008050600401c3e240f651801581d500c1c04211000040d0181221001440c071121b0000401c2000020b144441d080c8590 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 933299631 1250 933298381 933298423
    0x50405060402090a051207050301050c030105010f08070c030c152c0c1e0f090f070206010b07080910030b0a0e04020a0902160b060105070b0403020d0809071401081905040302 76
    0x4801c0c40142d02410202c0c1d40c0018601c001030100e0304c0e15142041c44281e40346c003201c2d00c2659400010b8250380b800c0d02e0041e00313903200000521543d68407003140800b00d20242011105807d08080041101404990140403c00342c181048200849807004604642c40203400380010140190006000c070511903107900a2180381803040c0e1211000b0994001d4040c0c001d1031021842c40b0f180c5ca5070306056445901c25809015080c07164070a95aa11519000d184007059000180c603010b07001034a440810b8002c2201840c007030160301c001841d06012110041d800362403003203000b0120b1034160050300308200d903541d00a911040115102e1801c8040c11b10032030088800c65285551158440220f10526502102e52a8850302c514041404112520303000801850907a04d070003010b44540c4aa214142d50840040c1c1008240031101ca03800501c0381e030807289000141c07050600c0c2550f915003480b00d2000310ba040c007405400098000ca0036030f000c0c031800411075009010700d1505250003510707004044042c40d9200e00c05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 933300881 1250 933299631 933299641
    0x203100e07050a050d06030c0308130f0b07080703230d110403030804083702060f0c0301140604030609061b08011401081807060908070b21040f0c0807050405 69
    0x180c4509004440d20b448452500d101601c0803030711a44901000300704940c5a840000004010188a60082d1b005010590310b03141400d010030595800e950100b203041c85a81401d1022220483c200e81d065680105166640c20740c5240560311454001000d0403960745003a0780b00240c0c842400280080d510b010400c024510000c4007041380ea0041780005800921020300050001e00720000402c00340c1c00d0400c400c018001c0900044212a52142e90380201800c10f01ca400c141c50340400a0ba03400c8003203030324005560714084407140c01d5030205100b544d010003100b1030343d441e16844e00400c80700903641100050108000a082032406001c0d40580407001055081e50000514400c489040c140c9001d1498440c18244190044842c0ca9001e028a102e24070580083d80c2e107142c04108034001400c1d40e031500718030385140084a83c100741a591001d600c50504003c0c0c803c8035400030610055051100f0805500d640f52420301013600c0b0382d0764400415644404401040c071140014110342141da049405002c42d90b90 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 933302131 1250 933300881 933300899
    0x31b070341031c050c1e041206020415020c10030c140c01020703111b060d0f02030f010302031908070b180709050912091f1809050405010b04020702010819060308040603020310 77
    0x1c0300d03220085082845941803080582031034410500306c0203d207904080d161600101d0094042c003084402a80c00101001032660310f40c64008102ca403800680b091000c0c410103c4c1c2003600b52030b00f000c10183d4a050501402e400344100d09082921101890348480d0100318a41c002e42c0803243c1500456003801c03d641c40d0b00c2d400104001d2940c1d40058500d40c0303291034420710440ba008140003200003525404205003000c03451004c1c500c50401c240d41080c20794914018507041600a42c0c84405441d09001f034000032840c520112101d45501c110a411181e8420700c1400790350720380811000c02801410800a5150300b07a030815402492010103842c0d480001014145ea00c1c4607c044264005980510000010030500d205030b40f10074460070840c8860b44509580c0b01407261942010509554901c28403081c07081c2440740d101500407e4070700310301d401d8540e000a420b07458020103c011050000c48c0e440e600107c1504000700560b80048259100d60303c0c5e40000d4040d4004443c2c3c1044200c0d00e07640003800b00c0c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 933303381 1250 933302131 933302141
    0x405090c030a0b1510020d03110328110f0c07060e0a18200d0b060403020a0302060a03090f03080118050403140702030c0d05031b070341031c 62
    0x10001e000704256502940c4512211500801202d150811105480e400d911400c0351030380e610102c2d5024281c0d02000343c0003d4201c0700308401e1907005010a00030040e007c00d4461400c02c0f1003042102441c004d070180b80729080985003080c10310041d07440214183c07170808005c02c0600079101e852340030f8624950f125034080344c03656402d13900580c2c400d240a00400889103141414281549a003401040c4403400c8520305d58031443e60071035034510368000204150700c001648100740d05030720100c0b000f918003480c1d500001d00ca007031117010191080b4000a00310100e180254020f629580d800011214607009a003400380c80d0140901c2085007601c019005007400305590f104030f03445a98585c480742c410244a0000100c15084000c04036050f03c00c149201c4420307940c8031200c512051003480115614500140900d44140c0c1800a190b400d520400c801e0001410300741110303441c1c81030903540808410400a42c0040c166034100d50101c2e5060440c500030904002000404072460440402400000b0303205e05a000c582d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 933304631 1250 933303381 933303403
    0xc0f140a06170a02070201030b100f12050603070e09031e0409140609180f10050105190602062202041b14040807030f290604140906040219080a060b040509 68
    0x203925100098122203484d8042d040c20360040c900000c52110080203e00e01c4100448240007013503414124403032081d4010324a510710011440f01340024181100860b941e00168000c803c1c4214040d00010641c00d0200155007081009800c05c02d556001130348489410b074858003071035038000d060544125000107400342040c0140302c090211000c90355a498603909424440e400c29030076005110b40d003814507108010090540085003c0020079524100410005030000e4221144c0303190f40f440c1c10003049401040442e4000c010324614141e00c11502c6034400c0c806941751000758001d00d010029400c01c62401c2e410241e2143c41c2d01c808002410030704104109028512800c2055800745030144005444642d202c01410310500030080d400041440c02c1d00c07055a0404102c404520403010490304d0f2900b4001c001120044114690792401c0c0070341c50a031900802040a8010f481082107038100b0080340303040c00300518280c42035901103042c1c1c1c5054405000d90844141c0700d6030410005c00e40b003100c00710f8004204 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 933305881 1250 933304631 933304667
    0x1050d0f060e030415031b0908060f0c0f070f031808071403030c060403080f0f0c0f03061f0c02091015110c0306010e0f0f0c03010b070c0f140a06 64
    0x850340366624000903001888030a0101d02050000181040007203000c410010900d48001c1026001210300e0000100386244c03200c20080c40000c20401d01030b0102c0c0b141d4000181c01540c01c0246d070342c0d1600c00000e104c2e80c2c1d40300c1c00e07240d0000f4081c4d0034098115128030000c0d210380c1e1244524400f400c0c4510301d81915004454580d0064842041140700741d0808884456024068034104035507401905d080c80320403503003500401c1700241000880007080114641c859070003481d074407050411a6003500c8038001e0000815200c4000404a05141e845902400c812440c3c540d2950704004c401c0c0e0001d0800c00c0c0da000480c0581d139154003003030100308005020030642d40c081c6900200300403542c1044444c5d8842d104c41e02d016020321031814801e500c0c18019540030f00242807288580381071202c1c1c2c0e0301c19010011300442c1801c1c00745042c040b90545079800c4904403503429400c5900c03a425820030100040041d849001c05030070140740080d10361101c2105552a0400b20b580600580c0d039a40144c8812a10380c00700205 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 933307131 1250 933305881 933305903
    0x5010e011b030b010309060f090c0618060f0e030f100605151e0c060c03042a0612021314010201060806070903061a1c0b0105031501181806021201050d 66
    0x881ea120364031122100301c05160216859100352940c508890700380c10000c003859102d00195040c000e480482600500070380c5030441240346068185515031085000d1902000300001d0882c083e40d1241c50a48078080303000b0166280f1070040604540e0380d05030160034070200ca0078900b001070303d40340c50b0482c0d803090001e00e45641c2c50302011040c1840c008660a60450030003a0a00070801d2500042144a100d9205911003540c0e900709410907003148110414401060002e0300c41d03604190070740050590441d5440e0511601c440420083d4402034003840017202102c07241075100040c441030b080c5d403903194004203800800010342c49210b615241c11040700d00c00b000c908150340401c001a0700c0ea105201003041910003c1c58a404a00080c02e1b40191072001d001e00c4420000502c00d1003001030308140188400c030010001020054940700c661070051091010407200320b8a2003e22010030b41044003075200e100500e07a11104103284c000002e40200c040505481e202c00004106814420300c61a24680c000740c00380e40c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 933308381 1250 933307131 933307181
    0xf1c0801030b06030a170703021920011e030615170711010f0504030c02090f070f030b1306150909200706140a2f121018060305010e01 59
    0x40b6040c030240c40150103110703211031100030944143c01480079025130f0112030f40d144031900300240340511201d190200b1203156950100061424900b40300000f050054080011503220016111500340c07500e981103602042154400302d81c1c0c142e1215054582c04095502c01c854920720403112581004405180201540b0204484900800300001d1401c00300d4000f0a00c2c84a502100c0144d0314290340840c0420000705801c0210702d00b09054540c8059900d1070070109142c20000180140300003030391003061580c1c81e44096015191440e48003a100801d207010301c0001d0341c80444d103082094400410300064900800481c0c0f0003d540100e4160103420100b50009903540d08200c18075074080042143c8044d80c840307580c24800c21044103688280e0413440c0001d80303080301840101141d4805100288400c500d490f000c0e00b2400201c0c25107240401c1c9400f4140e807130341c1d1020300b410302100350780100740003c00412580d0380184040e0000400e5a2041000b80240c03030308111060300713031244158815402044098044e0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 933309631 1250 933308381 933308393
    0x306090c09062b0602030a0b030111040621050f090d11120c01140702011a0303090a0b090604030b250c030f1103040b0301231507060207030e120f1c080103 68
    0x164400f080700708a603805800700700d1009843c2c0072404003118025000300c02c102c001115231003124000c0384260024003007807034042140c1149100f01d0055405018025a50030803820b40452403608903000c1c0c80c4100303d5410043c202c441c84032000c403820585481085c60b510320241c41241c0e40c990b80070b2024000c191000407800000510303002540701603d03d66940d0300b100c00e281c041000441c01140c41d40c00015580c44120210740000000e20038690103030380108100c89060721061054000c43d00c10540b05034480c603107100001d02c0341c81154806041460044244906040d5540c2000d0900e41200d0341d14440080c183c00030b48280201120150110302c802003407005045c0074451160f0a400000156441e1036115020408241c0007a00441200700800d021403201d2041000c1c076414445044465022040b054001d8407071601c92610b00520750b03030700814540f04240c0160081e080035280146000c003c01c07541c2c1c924994405080c0e012445074030036070102040d09140d03107903e0710f0b4044580e529078070700c0c0c2c2c00d5440785 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 933310881 1250 933309631 933309649
    0xc040902010c02030a121404030c150e03031801080f13060504080c1b0301050c0c030d47042c0f060106090e0709140108062d0306090c0906 61
    0x99040c41010644100113035818004001e245120351812010080300700d200800503c183c1d1000110b0000c10002400810140020300003201c0304108144900c2c0103046044881350401811a505488045140210780f18210300251034180c0a03650803c495840095030140b80c502507a1204080d45481448404140c10340c0240340d000307019403507441c40e1049810300d1626045003210003100241241801c515146428018182c201c1c0d00094080d013020341550700741c3d8591060556509405a868444e030705203242c1c0d4500d001c03003501c500c3c041200b03500c005085406441c0e030f8889266910840c2801c2504246031a1081d240a41900040304540c04a030804181ca03003030805020155900ca040c0440d090084c0c10803a40c0c0c00b929a995039045103a103810781c3c0000d007070702c00391500d024410740300f13814070152141042240c1d200400b46003441c1d01c0d81312200466130303488446030104031081020848075400d10101c500302d00405420350480b44590384890980e40c680e0b480c54403030355006220380042002c174a84a40c0b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 933312131 1250 933310881 933310883
    0x60d03030e0f03090108101d130501110d0c0336050a08070201170f160e031618180f0309090218010314100b0d11040801060e10080c0409 60
    0xc4906001401600d020302080340b116103a40b00080040165074001001600131200021381c1600da4117010a80c80d11410100304c0c000004440c2d80000c180d00c0380102c0305000c20350042c000300003101d607245050b0042e074425011900355905203d24082c1c10744c4a8030440c5041c40b808460400d800c1100c4082d4101403040101043c7c14a0501c03050b503011030810f11078044c003a44540c0400360350300046e10000d03005c1307900054681c02d042ca0200c10012180b003144080e039844000030403010004802c0340002d4840b082d95104450b01813050001040207003001602c480d00391840c410140a2124512030508282d81e240411040781201c81c0031a0307000140e0b06252410f485110342000c4c0141d985980619003260803915041c1c4907800c0c1107003002401e503050300c03503000e03441c00034120103949142261048800158502c14040c80300b400044900703034500270b80d20a2800e80c1d20000700c60703641d039501d4200d18040c0495029002690384040041030041801102000c100ca40d40390243c9085034540b003c010007400d072894 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 933313381 1250 933312131 933312137
    0x50105120610030f060e040c0b03150402030a091b0e1b070f0c03050a08190503130b04060b101d01030c0903140a15020a0f0305090c09100e070206011a0a08060d03 71
    0xb044201c4d14615015000190a040b40440b0951820341489100320102c0d85c0302212204040003801a400f01d80d81020103a5541a5000759498490403114002000d4088010305001d200310031241901d01502078200c200e03030700518502142d842e503c01d0303031101956051005003803080c00c1000f400007134650f001503000240a188000740c841c0e580e4580d00e080c00030a4500322010400040ea51000c0280d03010358100d81174007481d00350306528010303d01d0415404411400741c060304c020400074040002d250010141e00c9070160103142c1d5104101000703490920807034413060701d1101c3c095541200b944070b440303841c590080550344c0c046294030750b48034a019109007005040580c0a04202032010600c0d4072801d0164029a100040c0d490340e0b0000e009011942d0000c0d1481011705200030721074103590000720804195011159180c1c00c0d01c0d03020703c03918603414941c0600800d4205404001c80c8680229880e41200c94001c08843d610742c8018030a03240744504503402307000c1242d41001c181d05091a807503006040f44241 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 933314631 1250 933313381 933313391
    0x901140d0807080a020303071101050412111c050a0305010504050903120c0f04060f031406091807050907030504020a08120d51120f2102070f05010512061003 69
    0x41c0307402c183d5a019205040160f8800410300440c0381e80322803c101c200d81454000c00c030700d003081d94450701d12845020700c03c420458040d0700a86c0b041d0051090b01d43c050000f0001c88103010200c00f0107096a0020218100407034030704000003074a410302d4000c480c800c0e00300a0203107113040c81103100c0e1903c111001d0f002600406060101c4034140702204014005007950780c60380000e445070311000505544e040601c25041d0b501c0041440380d1519485102904a1603050812a08020b4000d10310301e0018168401984040700d1818069150f8055010394016402690501e41c004e072280166a50340b42c00c44801300c0c4828040082607500750080d40491101c0a5041034609000d003040003040f0b000e4071030001856001c2c403010044509400310880400c40700602c1e501c000600c1c0c1742a01e611031031011480050580c0d0030281150042000295044482c0100b42104034821405010000c0d500d005501884c104885031103000300745903005509444030201c0b078140218a036542d1f0024040c4080400a0b100141910f40d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 933315881 1250 933314631 933314633
    0x6080c0717040f170d0e19030c091104030506060d11060a08070207050409170a030b060c0102030103020406090506060d0c091214060c07120e010e120d08060901140d0807 74
    0x8003109107403444460905885908110500d41840080d500090040c111501c2c0c1c4c4090020200b80315100d41500d0802500313044984000c12110201e0300e2400000d1081200c01004000da4682058141c80c00008200469880421002e070300d44a1030102400552010000500034980081c3c211020340c41011601c202e4000c03180403071780c9074201e0b14002021500b15401c004a080e410094000144411034003480b00d0b41d00d60701c50b003000e82103c59a150020100080c9100c0f07040c01703504110300c0782d640685410b984640c52000b45000303410a01080b48918145540042c2c20241c90062500031a401080307180b508a5100d80700d0020400312100c81c0a00160301c00019106c2c0403100c1010352640103107061070007054210000750030302c8802007505011035014048200890740c01c4980000145003070a191080100c02c0300182c60707000c400b43c0d07226403124041002c203885440208005070900c0407034458419a45500d0304011140c1c00034099841e802150341d5010880b8a0101c44030750301c145c01414511b103440d140b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 933317131 1250 933315881 933315893
    0xd14031606240609090e150414010e0705010915090b0d0c02120313030f2715030b030c04020f07060203040c083912070609170a050706080c07 62
    0x41814103444040e503030a00b80d00c0c8441003203070007503800c0c0c0c0c2c015040c40d403030b414054003800030182c034001c02c420aa03540781098080582008200549990314a949803180343c00d1502c45134414051100b0001542000101282c0d4030000800344103942050f103810508504021030031803030303071b1400380900300700003a04d00005254080c20005018031100000b01140010f0442c00c040d2070006414010074280604100308256911007801d00040d0690500c3c2004407460355800440d02a11140e00300041240350443d082c0c803050803680c40008072190058040a80507040c0011f07002c50305842c205c150582c001417401b210520b03007a4010042050b1054116041240c180c175000109d07002120b0071110248185018080b4001c200980018600c1e6414105140b540301507140d202039400089882c1d25040103403c840e055521900107000d07002c240ca04844500d80d07668002010349400380728090514546824204000102154032007459400c28000c0891500e071000846050000800c03044083c4003e010110000e58 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 933318381 1250 933317131 933317167
    0xd0602070c180b120c01230d0207061a1809120c03030106080c0f040e131b050f01020c15090414010e04060b040c020c10020106091e0f0203060d1403 65
    0x16104203001e1652070b008034001c08a40c001c14420303114118080541c080040002812890340e40d080c60005600030000c624010700360200300040400b01c0e40490442010f01866000d0481640596014000e40c10b50b0030710800d404502e8a50700c2d4110901c41260202d181010f050320341c002d040101210b21000702c1d001701c41203e411102c80324940350000001000707078035130011b01c6603000710540706943d18041401c61070b99818851407240c00448021000000c2c0480302c10f421640322070b81c200342c1c46206203d01d00c15201c03842c0a0b40c041d480c4034480e1200c0d0f41d0602e503c00550540460030182240300d120321060030001c0240c102005e0964000d890b14500b04044020a040c01e00034448844d00c840c041c2094034016080c1c80c1001c26890090385041001132041c0d6002400c11411a0305440c08800c3c0201c400342280035000982041000314140b1000d000303403945034000e015040030842420071210391104070b86400e07880260b4420390b1004d040c0d044070021a0802c82e0910401400c4011246040405020a000c0d08 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 933319631 1250 933318381 933318389
    0x2708010204090b0a1406070f0203071215060b310f030804090612020a030807140601080f0709020a0e0910030b0c1c0519090807231e030304020d0602070c 67
    0x9a2100300c0d000385810000046005003460171070300d5641d0301c400000303e00705010341640079101c11503011480056440900400c1c01610400d201e00e542a15541441618505000b403400c0055240850005401c0544410754400b2601c102c4079444003001d4100f440340c1d428009000c1c41035000d210000160200703c0004042c000d45c451580c2035240c42c036040d4810b040b1440d9600002c1080d1200c00f000d001603490400840a8a900c0520349446045078144008014100d1884030700c14401d40001107580c003000250201c078070310514200c2da07442d51543c14210030380c040d03004000042600c2e00784407020707840c00810296010b000c100c0440d143c96565210f8840c5160b080d207084481860001b8032070205039a10003002c0080400480a202c00e0030400011220180001c0c40d804600340d580041d802044281c030102c032031464100400e0f941c81100a503101100c085454844821446500502c0c891190b0500b24040c1d202d0324500614199a00ca801740450288010021a0f07041c0d400c00103100001c00d00c030040c00c060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 933320881 1250 933319631 933319649
    0x60301030b01081b150a0201021608040f05030c1008091f0212130f0b062107150f08011a04081006050f06071106070206160b090d0903032708010204 65
    0x2a5240001d11818408002071013550005240d4020000351161080030f10300e4500e13820503541d18041688204d0090080030308802e995540c4501940a025042c8051320549004100720305002c0e42d01c10401d699201100c0d28941c000d013000300f820000c0d90040103a82d50042c03016054503040b5000c00046402c2701c0544000c116216804110325103010b4119040c0c0b98000d80241d0403240105450300e51550040042c04001e24013030b4040002101d90301c1c0c1c20076070f90042c2084082806c4541030300b07004540740d0383c69010313059070000e1940741c91802500c2804a00c0312465217440d4003a060b400c0c1003c2400410b024221050601e90412002528a2040050001030f0415600c001500d50520040040380303100150344500c0740c002070103003030b000c102c00d40d00303460b08094103c0d81d86946010038808078400780140d85020411013208000d1205000c00312100e0382c402d12030300b0306413821120045004d8980e0314440c04082c4c0007918486079140c0740c480e032940e850700c4a400b00442030b10140d655401c0909990060b0091580 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 933322131 1250 933320881 933320903
    0x5090403020f060702210a021f0b060c01021206010912060c0201090c120c0801050106020d030b1f020d0e1e0d0c150207081b06072901090506030c0d05100e070506030103 74
    0x54030386800301d20002901d1b030405c085c5041d000303400c000c5d61090112000f58840c50002c0760030b4a080d410f40e1110005003005000c003502da101d41c00900e4002d40121001104001880001801c0c561180700a0020740e0b130f40d6452403d000c101303600c07404000d1050b984904295943e54121101051600042034014525036014140e940142d1421402c88030300d51703201d070102d0b0f07041c58014404113801141100140c0050701e400150741c0b1070a0000707209000000c4c2990010380080c451401c0e203580c040340304042481c1c4c0340c5408003001c405009001502c90031981054980b0b40c4807100c9045860f20b4411041e290703000f25407135103c80b9100d500c004000000c0711004001b6034840001088401014441d0b02c050f02107a880001081904c0303070206029204084d4001e1400800f002038034480185000c009040308080e20340b98580d0368644900c1b10081070141d80452080c440c5030900045403a00d8240700381d400703500c003001e03002c2e1044c07083d130003005024005955642c0340640c080c003041c02e80315400a14000c501032001514 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 933323381 1250 933322131 933322153
    0x10051e0301090504050c031615090314030306100f0801030803060d0204050a020315010513060f0c201201150b160206070602031f1202220c0309050c010f0905090403020f060702 77
    0x11400403540340c80345c000c2c0c00c444000c9601d0540540100109c1701e907650140e01501c29880708444200c5a600024284090002c40b078110200000195110718020b490600b40303401640c2c1c003994084c3c036000c0a400012038401c014800114070f070000e150001e40140c03100c0c101d420b01e5400942958821503407013400507030100030482c0c104140c4030109641c0e0301c282080c0b482c1c801484503603016000c0e0350042d2030501003000840ba04442c80399001480050304283c0d00c1681c0740001003081c281007228501d592003070743c00c2080d600f030750350303043c446d0418078046d0340c5920700c18614050b17000040381c00025092a0440d400c52811015840301c1009040983c0319503c01692443c000703001902400303901c185e0306102c00100c4001e0049250942d010030002c3d8040b291300301c8840910300101c8100d400e80d81010380a506000c01d12990707079010b801400c1407038459810794510249040c011a2201c003030300c1041c400201c0c00d140c100b2140c1082003034145c01034080d1065800582e40c0c40c00b0285444400e41c0c0c21710050b4400300c0020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 933324631 1250 933323381 933323383
    0x30b030d031401030204020c0c0d030c02030610231504080303040b010b040518060d120e010207090203150f0a0305030a081603020f0703050c0c3c10051e030109050405 73
    0xd8404925030404000b200d046440e07810410320305000c0203008942c0003c9807000080c0400100300021801271280407400c04c14540103115000c50b410880c004d119100115812038010300c0407105540015080f198410343c0b007412454094840d600349504100c403946250304580400000300041d045000040d50359003060300c0d1000d04854140d100b50000c400c1400300344220b80c1c420310301003803c501004038203074642c49003000160340964044009200b141c10b0000d00c00c900c6d40007400c8c41103102c0f0980aa134075070380c1d0350004035090f031100711012030a1090440201009107002c40207084a20760241581e8005a201d6803030038176540c1b11015142c0806c40ba1000c00440466005080103160010324041d1300380502030510030382e43d00400c100102481404511605900c10400400911803002800c2c030002281101c043d40407207201054403245103881c2e6200d00080500001c600034481c402038070030804043d0803401261542c0140103106800300b22003900f000f246622101039400b0700f00740000024a805c2910703241d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 933325881 1250 933324631 933324643
    0x5031b03070b09180a060e24030f0c061c060e01031203020406210f06090203150f030706080712020a020709231b07050303090d080105032b0c0f03030b03 67
    0x684401a08001c843c0c1c2a403501344005094090008000c00c1540b5205080340103000c151700409204116202000f1800c581880140340d640f40030725500f045410200c080c50b0720785400d4058064103500070101042203041078002016010405001d0540d840d0b4040e052000791a81a8070820031141039500500a2007800c4180d403100341c089080442c6480d180180c0581030110030800340d0186c0d250726401084921098001d0a01ca4071001020041c0c0b58640594800039002540c2ca2886030f286c20301e01c0c030803605100c1500008088010018503503180b4080c01282c26410007084c0000300201720144004040c002e00140c640d00e92990042c009182c1040c1c800c008880d45420f00303a1043c9032440704d0b9030f440500c6c0c404840d0404e19540004000946d0b04a1042e041d00c1004001400b510001041040d1b82d4400706504011500c03c0d80d0382d840340c0c0d82e0b40f020141e07520044054605104400c100c0e120710748090f600a40b24286207420f10704182601c40d1212080c1d01c2c0c9180d419800700707448020f03044041c0340c14410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 933327131 1250 933325881 933325889
    0x70611060f0129130f050402070201081501021627060e04060c090b072001090302030d050d11030a021e040b180409210e010503151905031b0307 63
    0x30310441c90300c40c59490120038188511030b060300a10b001040b01c0c0c82e40e0680c624444060042c041d98031100c220243d10a10014441c9100c0341803440e0012406140a0003240d120035016514444c040c0c8911880c1c0030085801c4051a0641c880c005900052481005440c401008c152500c4009003000c1c1c12a00030000032440b01004040c40c1440c00d02202d9070070000250440d42100001549680644007521f8440007070304140c80b01d08012500386e0401c100510084c142c44006190010313104d010000640700340305240402503040c2c01488464601030310680207070940310781401c0c005c161003030384a40b04101a882690100c840c0303034000940503080d00204610140155000d048640740c10314040311448203016440780301c0788004600c10340000540e20303030300f000791025081002c100070144a0040714004142419844000c10b1907030014010542c041c200b50391040180f001100000c4c0380580c100803003580d00b03410000d080320700d4100118940d281001074130821903010013100c01510b58002007601e45629944 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 933328381 1250 933327131 933327133
    0x608010e2a0a06080703060305070f080f03092209211715041a0307090b190609030b18060c0a0207241119030e010306060518011b0f05070611 62
    0x11682450b9100c0b800182e003101c0030740c6018612034850360703012006001c02e40e0001d881c0344244100070888c2411046664116013020b002c0310200c40b01c2c40d4a003a10f90044150856112000782c05669921551201c07520b0380680000000a202d001da540d480d0090a0520b91030a0070500040070400141d0862104103680341d406800304074074134120390003408100d8030300070441c01030751203144000309540030107a00355620f0b10060070340d40d2542e11740c82c4100081c0789048c0898814143e4007410881e441014144009030303000c5d43d5960043c9800c6480c4c0401c0014050b211840c006508890003503040000e00c5150301078440c41c3c40b4155100307807081009180050582000c2101c0d2100d81814940b0a01d40a42401480c102d081c0f080d11210b03900f4500b8200785140241400419400907110708150341318604014125090b2400c100c3d640d29290202e41a000780e60b5040500c00740200f80e8450b540c06542c0303401c1e40300300159000d189145550354a11086031046021200c82d0302c0800c0034403590f0782251100c0c0d00303200000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 933329631 1250 933328381 933328453
    0xa1103160209013305040f03050a020301060614031b07121d010509061c09020d0605071209021012020904140901061d0103060e210306011119020609040608010e 70
    0x1142000c0c0b92140510004d4801001d0724400c08030501540c243c0d4020440d0a11b8203960701d5890800c00c0d210402224124441d5203000f00c08120f25001e0341d102583d1400241c44541950389240818120700005001c4150303100e0103206050026251402040500700c00d503542e80e40e042a62076400340300b440c0c4271500605000c0e051020406544501c1e0681c0d00e42c41400c08913122200d1303e80710306c0005101d41f1502030740182c801e016540c18001d807074100a0142e2074540d62600000c0e60384421400711104488004d61041c0341d034404880f214450302c90500001401c82c001480d02c0302100c00034044501200c0d01103513201c202020098006001c0c400c001c000d001c000702004440390180740035000c2b1101400000c140d2036a500c1c00044a0b40d003004440d8104c081602030020b0303880d5020312141c65800c1103503094002140254144039441000c81e0402440c090100360f0761000402d5800c10460760003425445822a946550005582109002d5141101803a1014054081c20038050450b41f210b61000190522000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 933330881 1250 933329631 933329669
    0x30c0f0102040b0d09020d06090807121e030e1e010c080112020105040e0a02070807140c10050d0b06090303040605031e0f010e0c09120616090f0b0a110316020901 71
    0xc10700715050f00700c035004e000501c0207a510000712032482c0b0660203803480d4078054409003000341c2100200212802410300320075840c240b042c2100c85078100c2050b4a100078070013140d405418025044105125280e400f69500b441070030f01d06544081c0117455070f0006079103030510306000c0c5810040c00c0b0701400c80c2041c54441031009400183c514441c0c1e102d20034218502d40c0c00544070491a80c10368520541c49081e1641ea185603041103103285005500104060042d90740f910020b140003904000b5010481c1ca4407410007001150302d80042031410310750354020310100942d0030140d9051000b030011b040642c50303440e10307418410003121003201145050701d62442241c0501405960032420705e41143c1c58480d0500165940800c201c84030300659900680001102400d1032600b04042040d40c030071498070070b0071040321842030400c940c41c4a01c0e101c0d20030b2100300720106100c4040010b004007144030032802c14404840c40c04c00b440789194001a100d0302c00c1c0303102c0c88240c000c52503c03a0460340140b5102d08c2c1b000e0300002c9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 933332131 1250 933330881 933330899
    0xe0d0e01090b13032a090615050306090f071b060e0f0a0c12020a09090b09010f18060c0905090108070e072105060118080102040824010b03100314030c0f010204 70
    0x7070001400310079507100d10145400400d26000200008545c540c40101c1d611640d41e800b4160500828000140d160301e1003144c0740c0301c1ca054a204200003028522152180c0100e010300a5014119004200c0a1110340780003105030900c0441c0c00303214640000c0c1d402c00840b4207070300f40510b48646200540260718a0b10100c0e0b918180c210a81c0c0402503001c42d030340c00350b10005170441800e520620f41a4181a218411322490b01781882c03085c04000c009000d1031b0001a00d1804039841040030b08500ca00f0680c004c400b1408a51140c010b188090809000301c90701c034000034074a803a00b40c0c00300e0b07001c1d44000401d01c20503883d40b0304150405c00500346003900a1070301034402d03151001e0314502404541d9910000b0300d941e04c01d6509100003a4071141040c009611040f649010354401d0144104504c60f602c03405461a041100307910303c5581d4078068204507428040784041c3c0b640301400d00d006107100d60001101040c1522600c0d40c5d0006101d008540d07030aa05030348a402c040056980c402c0c030780d02c140420490400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 933333381 1250 933332131 933332167
    0x1208090306091c0f0909050a020705060606092d1f2619110f0a03050c030c1213060216020f0411030610090b0c2506120902040e0d0e01090b 61
    0x1500b0040070b54107842004a0f17500441d41d2160301100d0404051211807607c030780c01001c0340350060041d10040d42e6481c05200035442503440c1f00e81c002c942d801c002200400c000c848034442051258031050707001c0310440010713042c0c00d20100010005080700e0720209141d403c65001200d2203825503502d070000144003100088004024410300580d402d6006a4450344041c2d17000d1048584844d8265480381e80488002603540c121074100c4000c2441d110205003c0b41d5250203076071181d0f04c101442854440d0b0407400c0c10b030042020b40000802d001c0900b216001401d01e0016111180701064440280720f52401084414a0040b410b103000701e143c8800c08400c2010710301203951008080c2da00c60342503640f80404540c0c41301a98400a0840404a40b00c42194030203e02c4800001401141c00180b100d508820811010140304007004035200300740c2844022000d4100f20340b00c60005100058007002e03c480c03542030400340440c0701e00140102c05803051568120030644080c00e08240a40d0407d4408a00800088 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 933334631 1250 933333381 933333433
    0x60e13050613050612070314070614093c1008070903030305090a0b0f16171f030b04110907090f0b0310031208042303030a090c120809030609 62
    0x3940b2000090465110880e61417034580c00c940444140c1036680c10952207800f88546815094010b40c680040c605110f0150f410400100200803403a21665104205400c500b4061031f0741003c11303a224580e40d6254a0790381900c0b004425003949100d1007404100040d2014464168082c05403041c1440304130341d40420052b064940c5410002000d40701c4400c071515001d100d1300020f1440d0480400c210340503c3c0a54454010340d40301c2030f0000000c0d06504103551103040100d0f4011403280d00c00004c1c0748080001403c04268105064911035240c49417604842d001044038261005c90080360001c00905044e00601d6110720a440c003641c9042c10301c0383c2c00f21800f840344100200c909010002c0b9a6094402600c44021648840c003071141803814000a4001030307003160f080c0c444c121120180252080201035559000d204d507005146155a4440d40078000e004001c019540b85d0610000403485044c181c01c9007000500034680d440d120030b9500b00f00741c50034800404c41c0b5196001140e82640080702841e80e44215 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 933335881 1250 933334631 933334669
    0x504150314040210211d0a1205180406081f38101d090705120a0e061f080307031b050312010e0403030507090e0a020c0307060501060e130506 62
    0x1506841c42c219046045051081d12803a2203105c240031200d1168041c500d8584c44155030203004e101203c04d2a01c0d0807480c08050441014a103c090360380782300f000100012400e401291194001c1d01010504175000c0790003407004ea910440c050813640100914401c50b002500b041840b05802e002c8040000000b20341c5540c0414101040c901070589902c0304480241401400f03503038010341c14580060002c6180d40f11301c0c90068401504002c1810161090b40c0700c0d02d415200d01b40750220140d1410792280c0000e01d194a2940d58924078001d5510901200740900700c41c01d2071440400007000306007400b2071264020740c81d9920400c80035001035003106190803265681c00e40c40a4401042c10303c6e0381184901200c0c0b80c4080d600400205030480d00c008907074002d6000c0d9034100500d6039020b0003603610380381a000d941c80d02000100092041c2005030010728110031994156820403c42e80d03110300560f08207801c8440456070061400c03245003040344107604410629034007030106050110100c1c2d503203082c2c02000009 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 933337131 1250 933335881 933335899
    0x705060a03020d0e06180604031b140a05011b02031806070309080106030501052d061309061104050102010b090415050637050d05060a09050c1005041503140402 70
    0x103014007980c10780c0c001a80c0303084140000540001c845880355012519801340e4181038001c0440c2142c000b4807a031145034191034005003408075030809840c1703031028041107440c20040c0703400340b00802043c031490600d180315000204044184820814103514071070b6545045520902028400c1000e5090715005a1015034081b551040303103050455030700c021a00440032070360078800c9c0041005015800b141c894441710b4400318042c0f031070400042c0e4400c0c0421029880c0e404501c00724540346444800344c803c40d140c040340000c1119031991803405403007c1202d54107110714089002c000c039580a005a4040807801c6410389820305c0c041d51040940340c030034161f1342d1046a03600c0000e41700340c03079950103288000d44043d00c4040f4041c419070440129030204070001e8051803000d030002100d0603c0c15050020580c090003a01e0340e9651015071000800090205580e90b00c03c402101c401501c9503c11002500e0aa0396810368981c1030007104800c04415100714010035203010010107220320000034164010341e0407108001c3d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 933338381 1250 933337131 933337147
    0x100c030210111b150c12040b331504060503070c05150a0c032922060b0309161211010c08040b070506010e152e0903110a08070506 57
    0x9403c1c015500f0541d1840030540358903031207610004050a040c100607250b81d80c19601c044a180c41c6014040c0249500500f80f00803400140402c00341950001c2d011a00070301c0071907007042801c410200106402c00b03040000310302c01034034202010030164043c28481010307d09403a0010040441c0700060001041020751001d03282084402d1040c1c40852104039007031074850802101a100030700150a9450109180c0844682003c01891800440d0f40c5a60001d5030071519580c1031140c3c010101d6500045940000c40d01a18503801d8803860b40942041c0d80060340740d10b404003450340f03880c2811508100340c00100f10304001c4000e2107288500750a5008009928000c0c41c03a00690708580817120003445000040f402082129511000d40310840c015811925030b80d9a851401012010554940104429a1b0b05000443c109084110501c100c5500c0884901051081c85100500382040c0c034000180c2301802042807050003450044640d90445481162510303100c03080b42d46803c54404d41e0301420020039120 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 933339631 1250 933338381 933338411
    0x40f0e011d160e040c030518010903120c11060a02122a09130501080c011805030a0b0c07051c0809010c020705010809030c01050a1d061b0904020c0102130302100c030210 74
    0x103e071914000e00180038590001c10090064801143d0400a0101c2e4103184140c610b0140640d28060740c0545903071505500001c92000501085003404080c01640f140e4021076800402005229810503c00117850700f4142420130340c11940070740401074400f00382d0002140080806c0b48000d04a950859440c0e8070210400880c41c0c0444c030400090300d03245402c000242ea440c010484950441003640d40d4241150180011003001c0914003946d5095030000402c200010380b54510281c0140440e40c009003840108e42d1514603100000e8004140240960248420320350060b00c2d190700003e03040d001380712603401034030000e5890959108560400c42d41c0c0c07000c288444024012105011607950080c0300c64507202503c170003d01a00c241d50000104250404e4141c50008240507006003070000cad00d01d07a55000f0001c1948590003641140758410b90070484111044024401044001d0341144a20107291840c010030600d010440400780c103000701c6500380d1001a5010504010045d002080083d0f9106169021 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 933340881 1250 933339631 933339647
    0x90c030f19020703082d06061b0f0c01090f05030c0906010e041d0d05090a090902062104050c04111c090210210204180504060b06040f0e011d16 63
    0x1a403510b8800500360043c140e000c80b540c0d215519251907011400d220640c41e9458030300081310b10181c40c5400000c56503e05d0407030700900002041507007000400e070300500c0013410442d14411000581c1d202181c90700c50307543c11500307480c0100000c10250f5030a610b0312000c240c48800c0d002550780b0685000c0000744d201da0150b403800074032480141c010005a01d5500f8041c401441c4c171614044184038a40d00b101d506c520402c2103609071100a401c401d00790b498600000003406101004a81c040c6050040581907140a12100c2084110f80c038034900034107150400d541444500c2d230010b802241001752035035500d004403044518078950720b0311400000007041160b0004141c4848000e6100d0202c95150085681c054040007030703054050131901c2c4140e0ba242c402d604a1141d4881c041e100903100b152100e00d80b582d80d0003150701c0340c0542000b25024030702d4400501d89074403070780082d032082d00e070000f052010315000c0502502400c01c0c0f40718500700d60b42c0c4200c5010314502c020900360800c0032840080041034411500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 933342131 1250 933340881 933340921
    0xb0a15030906110a0906111b01080702010212070804020111120a050f04091a030d0207140103050c2a010e0a08180310020f18011809020c0304210201020c090c030f 71
    0x41d85480348420b9200605e9143e4912913880041c078181110340d4126804a03121038000d13641000f8414a03412078006441c00c510003040b03002035550078007000c220554a011180d01c13030101507544800b503113418800985250720540790392059500070a808009540103000700c2d1050219414000d44851016120114903c51a00058019401c4c181803846480d59420f04a4100604a095403c48245004100d0340c84100b8400c0b039101540c200500d0781c09500a90086801040184105141c0000f241146814001c0b80743c00e8901d0031406407000c2406030f07080c4030b51112105008040c10204c1d1032901e410345039010311404601c003003503441072206180d6000c008900e0f1301c0c26880410364484100d0490301540f50068101d85002035040801e00e041507100d031600111a01c24481445c902d182810803040094100303003044141c621040001040384c03900305884240325200c0800c1c51140262520009050400da031100501422002040c41010714a00058070750090510b0f0080519a84403254180c0d09500318003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 933343381 1250 933342131 933342161
    0x90b0a0e130b1203040e16020a0f020a090e060f010b09031f02090d06090c1d15040b0a120c080105011d04020103060509010801050f180a1712010611010b0a15030906 72
    0x8000110728001c8094011101c1507400c031106d03a130f500c08040c104045603813a400c005800040100740025403480209458a001500c007a500c10b0711341d102402103903080c038507610265000d40d0030845002d6092200c503015050102c1881d080450b04004666603200e80f1030070b0004030040d0a0461004100e55050303900e8440c0c001c15108007040030381171110062180002c141c0b02a0440f98000c6442c660700301280c01117840154203441c1c955105c400718800c1920f035491881c0e01c103840b41070244950b0799400960014100040f0500c50f1000ca0b4a00795003540c40302e038000441d6906105c010415058180c4404180d00f29402254500c2e64440c8012802007460703400059010084a002295002d01540a5803017070b1071107004580942c0f80c1350b548105840500d0081d2203140d000388446400105500d281c0c0f1a040d0b0303440302c054103010b002c03000c500f500c841c00d82108001030380031080148003e10902441c4848041a100010201d0504e16121070301d40380a004803080c95210600442001f40e580d0141120031500c0c1c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 933344631 1250 933343381 933343399
    0xb270c070501110a020706090501050405010309020d0203010f1a09010605040510020f031b0f011103180f0d1112070f06020f090406030b150a08030d0e15090d090b0a0e130b 75
    0xf415080d50f0b500080400e600501c2041e2010907a580200340c19030554205859081c2818a400d00440c06814448800c82e040302c0301780c01c14001a1024000c03020080012400032850a032260600c088480790260b1a40c45840306800401045402c4411102070380e0042d2041040000703581400d9240840c40d041140441c44001f41c01c0e01c04107444d100718000400c0c0101542d02c0ba40882038018280c3d140c0032220421040e080012030708000b6440d121100d01c81085003a2a40c11240d4104981041140f9601d940801e00c80d104602e0304000a0204152400c1480401070400e03034941c0f250b01c4950b4004000030031a560025804034444800025111000760082c41072140e0f94136440c185421501c240d65006200d4510300c1541084c0c540a508c11003030b110144015400c002c1060803070b00103002c0c1102d260307110f4094000003080c00c02c40903415512901c070f203500401050704280700003846032201d94000551100117200c85844142e10081e20704403003104a03050000780c02c082034604010302184030b41e035520106c54 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 933345881 1250 933344631 933344651
    0xe01090b011e120308010608180c0f040e011107020405070f020a08070f120f0212040617100f0b1c0c050915360103091203050a02040e1305010b270c070501 68
    0x8095036040e648665203a02d910f0301e4440e4074103039007040c0d203980c030381e068001d102c00d02101d04046081c1c103414a0000ccc4045401c03160642c146084642c03490b90103040c0140041e011045d414030340292900000940390030390b490078500c00000c0d2105c800340c000070009540002c8517414401c00c0a4070003c0715401070880703213003c0c2d00c2170000303840304100c2d0a498000d8011062030303000e428841e400b69000c03101141c6500d940140325440a002e0400000c00800c00744015a07000f15100c8500440c20b0080c1881d180b1956030f030084000c0c4007030a068200304007248141024451404039610200f40c40041c0c1d03064440250103081c410349a1254011f058110032800c44540300d02e41c00c081000340d03001f9030400c020032000c000400100118142d0b000004087c04142c0115080c0030070601c030b030b03120395400804040014100741e1a01174820701c0302c4058542c8421f00802c6800b101c14043c0030300c80d000b281481180c440d5803460148000b513200c07421110140302c08000150025030368090480441d00d04aa109000300007500308 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 933347131 1250 933345881 933345887
    0x3060a1e020c0f0d081303030509030f030c071b14060d0f050915010509160f090504090308011401030516050c010f0203070c0c0806071d010215040303050a0e01090b011e1203 76
    0xa030f84076001d200e00c070301841d00d9138043c005190107501c80404102d000001510198090003001c1c144092510041154901d000e0719400a50b004d1195180c1e0140e072107402d4240b60101c02c441455540c540d11001c5401c20452139102010050020709481c100e44032201e603410500108080705549061034184010807905200210310600b030184030311040140790b42c0380c005200700d101c400c40d0041d01580c4039000e4030400c140034204580b440e44052401043e1580c41e1000704099440920045000c560a08010b10400e4500c3d10052025082843c003003000303241002e40742082e6511007101006005000a0f1b0142c1240290044440f4685070070080d5520708090f42c00030109420840165a1207002090202d807008021804030700900b4141d5070b00440f80445081d000c1d0295007040780c6415842190880340010b00301c0801203101c1c5000f80c0b400502803818641c00020303180f8000801c4026490600b580000400c201d201e181580c45c0c070000720348500948501c100c680817040e00703ca810460402805410194 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 933348381 1250 933347131 933347143
    0x8030403062708041a072d0515190902130c030f140603070501050310030215220509011403072d080d140a08130c15020a050c010c0203060a1e020c 64
    0x541d8401c00030f681706030103600200901482c28000c010700303502d543c0e503e011900d544020900758004e154001c1ea000c0c05544035480e010958803070561208030b11081250048103d0b08480c4c071a18440c034107102420a69002883c41802c00d44088022540d51040f2058a446544404000031400c50100000381211403035050b550021580d90388a88100308000c00e04d544034a0071341c3d00481d5421a250f804034103540c00c00040c00c640308d40c0161440418003280b02c1000d5051070740b1507064140080080c60303c3c240410700000c0b10058102c400480062035401006450014036002250000d014036a4080c025000300180a5124880c41040103425800411108404540e9035005142074039048403501d80420710304000e001d8030307206001107007100c00011801c10980c0200305200303200d10320000365242c07600181d803900c40e09480c820300141d1040c82600200201080785030f09104090800698042e1607a0019075140c03002403403c0034103a2200c0c4400c40211440c035100040d00c413010340030364a801d000c60b40c040e40c4407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 933349631 1250 933348381 933348389
    0x2010120506010c080706020703020109020411030402040b010219081e0c1c0c1203020309010902060a0e15040b04050d06020904060303032a020d0c0201180e04150203010803040306270804 81
    0xa40303800c0c0480c0d200d600409054128a6001e0841ca041a0700d50312001c4c025042441c094003955210b0325524010382d56840b42a00600074802406d4a90070240103000032a460480494159449610080920701c2180c6114171080d6002812603074448050400c0c0d110071403c141814500780d00810f03080d0102d040466200c0507161860b600400703800030340c1c00840762a090304a0140280094031f401d0303408188a6001142c0c0911150000710b20310326203501140103030b80444107450000e203011211482a1604a409070b95404040d06411308007414030700e44001c01c8c840d600c28503101d080e400d07603410100040c94050398541d800060007003090760780c3da090150140c500320007a003e00c03040340e40d5114000003641e10150740c100c078140d000300381100001c20155828806442c0581c1030000400c050040b4500c3e003641c04000d0110305217220030034189071078000010711003010340e80079050060006020401c400819078088035000040821603a44020045c0c280004d0000001051b0460080030828441c01c880100122 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 933350881 1250 933349631 933349667
    0x110c07031203020702060a03090809090c09030f0a020f120a0f06050f01120312020904060b031003060c0f0c020d0201050c06090a0309061b080705010209060406170609010803072010 79
    0xa480701400c100c0891080100003035101c40c0030722850701c002d07201c5d920040503113108010311417405280c070001685103642100c4051900000181d031f00d8603414180401104070f14058004c00c03a806c030301d9001401d039086c42c600141c0111880d17045d464404c0c00800c030b4154010303001001840080d00c01d00740325002c4d05080308c1210502041c07800000c0e421500b42581114150107641d00200c01c0030031078404000e54070440c2010751042e1103c0e008982825550015409201b605000103040c0d032861414400b503600b10540c000c20711014002d00300007070340c100342c43e902e20660403101300301002210310050f1101e000e5010342c1c140c244568070400000880000304064104d0094441020300c59807600c08079900144144500c050b0424551131030b00140c81c1501a1000e6885a400981402d20b400040f0b105504a03902000002c0e81e81d40050310110364940503107030014429070b2244140c2d0304101110356684100d4000074886107038118843d91214950021402c00c80008000c0e481070161100c000b0302c103074160701804042c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 933352131 1250 933350881 933350903
    0xe0705030105011b0803041106040b0f09040606230c01020d1803021e2a0415030c0f05090403121d070503071409071b1703182e110c0703 60
    0x510600d04c11440c0d03203654002c0b041d901c0c43d580c56990208040e00760344040c0e04404107010104070301810101070034884007180d407090b1b1241a04001c10064480c80c1d4840d40601074421303030801040750841c80301a04000150030003a900c03940220014024803a1842e0f0903100d13403505c3ca05042c040c0303038501030300c818502075030840b17000100c0010500c1a84076455860b80141d8020301881895961107a900d81d1f8540030000707400300c00a86880032409449201581c071042800382c1400f841004400350802d4090860014481200c0b4100300204000d90301c040c00180a024040e10480080885038204500710310240c80855000d80c00003418039990070303160040c14402c2c05060750200c0d001c02101010340f0407100c01000815141c403802002e40302042000400d076040c1c0c0c0800c0c009000310f0200f04c54140302e41600c5814954078501001c280c000c14071114400201508000301c100c0004030041c0b1544200c0c1500d0303484c1c41d045803071940c9080041050000d04124140042080c0c0051080490004200da00503400440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 933353381 1250 933352131 933352157
    0x901030e011407110304080601061709010912031802300303151002160f03060606050901090302040e0102120a0905010b0a15081503010e1605100905090c040e070503010501 75
    0x2081c0c0303140e01468440a0700c2c5074000340c82103200e040d07a442c014000b041540c1c9059100c602440c10001e0980069002c00e002e0800700e0310a8016085450f4485204402002005119940d14003024502d404960400d5202c0b00414604148000215040b5600800d400c0384140c1c1c5051101040d68403041100000c0c2000424030f0403034030f01008403880307080702c4858800385240903000c00c10303003d20040c0114214801e07011440c442c3d0000c2c50071a07000c3c200411103e110345140d89031a03829035001c1e82103070080080a0140c03203a941d030004c41680540758111400b14101009036616070090040620f203035458921070003480403240c00e17544500c0100340600001e0052100310424000449500d10840c3c4401d61311040403441d00d4403c00c00150005511031208035005111070000e402e546520134030130700350b0300401d000b01c4400b0010701d03084c4e00404064864000d4120b00d150003504400c51482102c0c0618088800105074203c09012280075004c400300092290a0030980148960000d018031400310b4141084c02c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 933354631 1250 933353381 933353383
    0xe0c0f0a0506071509050a110f1203030f09210706150b1e0702090108060601030c0e06091509060301060c0b01080a0f140a150e0118021c031205010b0901030e 69
    0x4030588002419031481c080140d510458200a400f607015101555440c25000044052000c0184503004800e803007130300d404030390030030038030400c50416688030b820400d00583c0901c801000380d0350310030034480e40c0001d99a00c810328241481b1240104003801c0355401c244059031034180c00074080f694000d40b0104250307082192641c5a0f45294080d403920031405201c2801b50201541101c214090a02466801c05203950302040741600282c02210941e01320b607042000d02e59142c8580042d1101354541280c030341e608000440c4043c410603801c01d00800d4014100001442d0311030845152410180400f5603c1da510340000f4000244d100d4100c9079191204c0000070f54140000d40000843d4012506040c408400d41d44c228912091028403181401414420000304d81c0b801c907140c090100e01c0101003000f400f4441a00c4c21224124450340010340300310b0700303980943c5445003545991403ea4070749144980b01d0342010b03140c00e02100c01e10b14841d802d000021402040d040080c05000310b00b0f88003401062250240e203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 933355881 1250 933354631 933354649
    0x12060301060e0408160c0e0103050d09051e031f0504050708031306052a011d01201b0a05031309020313060b0d06050a020c071e0620010e0c0f 62
    0x41280c001000086001329003508010107443c030171000075040d401c08607925a125051580d00084118442000420a0203030620a82141002e14504108a103041000080b5006142d4002601c0c0361011a03041c2010781301001400c42000d00801c0a43c4281007202c3c410003e041c0844007221345000d12223000803004000410b45000c0261054045141d50514200303d540f0380082e0801d90900709204009402e01c0350b82c1d040a1000100e0b0700020a030850f07017038041d0442c10610120325030160314121411078034000c25604c48511240d2040315030381d1855020880c82c1e0150211643c1300880c060f10860204014002000b044444403142c900d40c0c989a542502104a0108450100b42d081151409000144c030301d905c0343c280050014001c1c41b0081c1640c595a0446004031104000c40303a00168140038441d040040000515040e001510f60030b0b454910507823108000d11601c414408a0091151940f00c41c40240c0c80c4820240008c225522000417010740d21012180828042e000c0306041c2c0714207081c50900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 933357131 1250 933355881 933355889
    0x31f170309010f140307020d03150518040201031515030507050f030402040f0e0118020a080309010c0615211704140d15020f030a0b0334080f031206030106 68
    0xa1810505070000548549003c00c105804000305072070359005810500b0069800b4030580d90003007100c02c2114038043c0845089040c0b8400f8509400001c0156603038000e41c02032826003007101d0f1481e40d11030f480140d0140c09031500129135030015000106070082d0203505c502d5503e042c0d60701849252120030090303407984160200145941410800078001d41400c1d0024044d0340b0440800140c140d012036038050850702c041b0386103c1400c11114842c82075103003501200015000d00c2c4003641c644103140c000a01031510280c8010300c0c003510745d000740710400c085040100040c04d0b0300484c900a900702c941c48115003131003043c04940200403401c01d0b5000f0b105110546090b43c8001001e0103152041008105192090017030858140ac8074040c01d40e0b1807070b000d0002d040401c2c0b4182ca0940c0341c2c10000d0840d0251000800114080d0780034009040034007242075007070002640c0b00d4645000f400754903c0e4280422000381c000c4481c501c5141d001281400307000000f030000d06011070040425803030305000c06003a20800c0c42 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 933358381 1250 933357131 933357133
    0x60702101a0d140d0c060e01020c071a090306040305032202030c0105071407120b01080102070b130303021b07051c0506150d17070b010b030420030f03031f17 69
    0x203408030507410010640d584180c0100034400303103e8400702100e450300704d0003080740d8002041e002c0d11404110b25801112040c8440078001d6042c064849807555441c2c80910440c11204011818444401c50203411211074a40140607134030140f070f25007805019584140d591170440100d20a0f0802c106904134031100c04658028054440b0307685032801103801b500508002d80c0c000e10341030030440d0004030402c480c1c1c0041ca405010301d41c42c01800e0800811901b0141c4c80700c2c5542c1d004101500020305d910306016800220013a40c03401032012400d0481c0207005076540d60102581500c0c1906102c280050390100702e560840d00c1045020005501e0282c0281c400801006984480003284d1566800c06090200a070003500c00c00b0400440e84508429525114002c0404ea0000031343c0418800c8841d50749025100c0013103030500e1824560b030b80620401585c1c04c0110311642c0540c400e49940c2d0113120518010000e00c080707136140c3c00d20702e41c40302810403a00c0c641800b11000c1800064042502031604501c22a104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 933359631 1250 933358381 933358421
    0x60d0309030602090a050a0312020f030f0403081309050708090f030705030304062f0c01060906030203031b03040b040f05091b0a210914010b040b0604060c020a030204090506070210 79
    0x380d600d0010350404982d560388410910f1001c00c1c247c940741d88150041d8015240071320302402202002e42003141f000210043c5070401c00055071120030340000c071000c50754000070440e0744138000e455a8003000c0c002d4000e811498140f0307080c04159540048242d01130600303a0207071340e0090b0440c0a85a900e204209008000c1c2c0c000b440042e01082c2282d01903022139081c800b040044210950b950306240000748225000c0c044045682c2c02084401d03c503034006881d1581d81041004c1c15900000e03034a002d41800ca840350b405204404040ac0c80c02d200f9600100710710010107840c0c940701c2643c0c0108542c680505070191404a002480300c50300c4108501803240c0d401c44940ca41281c070b150031030b0600c0a0340c01446140205001c0d034000c5201512402510368000c2c5410000d89030100009420354103016444bd00c01e80c24429220750707603540d040c12542140d815007030070f1440b098684007169401301c0561010f07522520341154a81402400b180b407a200307140035401d03103013400ca006110fa0215201903001251200400e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 933360881 1250 933359631 933359633
    0x70c082109100810081510050d1505090c0901260304051507051c080603150f01060e03010f06060f17220201200c01020d1707030c120f05010e060d030903 67
    0x2d098800e42001ca1041070b4540d09480344041486d00209401e0800c0f420003000030000401081c07141000904400c841c480d511456540312900e070080c420208006265407400812a4920200f0040b40c0000c000307000410a0342c0e481500340250110149203000c0300200c180480c6110f40e001c0304480642e41c0045c0078040149041112b40c4054010502c03c031864440c44500d00c009440000d1200c1c103160a81d030b40d09070720340790800900d400c090030040d46404501404040c840c40c15030705800350341134600e0391400d2003100241c14002030152499141e01d005541c03501e40c012440c2c40d030060b180d154802c20380c0c560301c104c0054010300c613542d80401c81e8504010106000d4400c9004002c8920304441703401494000364801883c1c000b0325000c6110340c950010b03940420062003055805020071224006617040141c6440c0900b0000510008010b000108140d660382c04060340c680180180d0a003c01400300400c6590680140400244420301075002c02e0035105000400c1c502c5e10854401c00594142e4890b0445869 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 933362131 1250 933360881 933360887
    0x50d031110020409020301090e010207031403281d060411090604020d0e0703290a05040323030f060d03020312151c020f010201020313080f070c08210910 67
    0x18210310165015020024840141a001074000b0340f0410030010380c3ca500d0008075504030f071a0412916000d0f4018000c40c404250854400404005200411030b40c0395141a000b06400c103a60b02c02c4887c824800c000c040001e09036900009105000b92010307450320209841c615650708044400622480400d480700e00c0741c1c240380740d034650080e05c040e0001d800d0003540c1a05e07009440420044801030780c000c010400900106404680c00708004041c8e815118181c0c102d2410b1103c80100b0415003980c40b01e0103c1d081520820030384609610303460621480c0c0650310701054460f40141c41c08180212010003040711440d04550f0507500b1030340b5400031031a003081340d1000075500b10010b010705071090b00ca410300c00213a15842c0714184401b4540a90007903520580c4100710746031030745415860446e0f10600402501c40005000d0300002a08159102d80b1440d00d0300240b0319510420b42d0041c1041c104200c00a40e0000c00a5800100b07921b40244407400360380361b481070030303c0e0040c1ea0070f55074010701c504154942030380 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 933363381 1250 933362131 933362147
    0xc0e04050f1b0706021204050a060f05100b28021507020d051b0a14030403031b0528020d11010206091209010f11120726030103081819050307090204050d03 68
    0x480744c4070140c20060b8110384440b98000440e070070717141c40c1c0099200204000c07852041c5240e10100301c1e03042100b410304d00100d4040202d40d024140c5261000140e03200b507690700c0c41c500ca4645585c0b090503d20650f22000c0203454221003020891130808030004030b061039001080300c50120005641e101d04211258581c001c9601c0c2d203404c10a49402840d0106010480e600440c242040380c070401543e5407031662500810398015680070300201030b0042403d90002d540400e420880c483c0460100e0058010225003090480004ca0b000b940104002c0d5403c08120384c0040e1800150000d8083d50026542c070513520740c8400c290f150b00310f0000c038104031203882c41d80189090407241c08a0724019050807052607107685406215405001d91400c0482c0d071100b0002c8030030340608421115201c1d0700700941d0b80c0010003507038081808018020480407520f805203c0207101051040d9600034950700c4207120f02d0000288602540c01510300074040e101d40803408020500031101198030190404001c804103840c103d520030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 933364631 1250 933363381 933363383
    0x20702010c050601080105070f021f05040c0b28032f070b04150c2d0e0d030818010b0d021002030c060a0203070f080423030d0c0e04050f1b07 62
    0x22450a18600200302c080190300e020b400d44000004050400c6807014211815810a010440d03011068800340d80200c2e407550444203500a20114154a4520703011007500401d401c01e030b003450808074610311180d140030323a800451a80d224034140c1100d107100d4114280c0e142040c6815031080140c504c0c49482c07012440d803141010070a072000e1b082400c681d6903000228000d0340d0598284407a00a200b000046a100f500c2140e00c1ca401c0c0b40800500403480390f102c0484200d4600c1464564800300083c0c140100035100c00000020680c210804403881d01401e501e40699005810300c0840d108418034810501c00d5001da8180100b602c020358140744d0810003600109807842c0304501040c0078030280d046003041124010010712001680341e28104a00130806030305200c00c030040041c1030090002041a40c201c50981c4408101300c60101c2c0790a40b4041d103144902c5071144003030b501d071607400d160702640324084910710701003224180016100d6a44880f007582c030584078070084041040c60b059000307503414010007050f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 933365881 1250 933364631 933364637
    0x71b031a090106120302150f040506011421030a02060a060518041a070c050c010c03080f061516020f09090304180e01090c06031b020c04021b0105010f0e13050c010302070201 76
    0x80303900ca981580c6407013030003a001c07009030f8440e17141c02c1c0c188000354450f290300c200e00181c0500249841d0b02c4460341c400040c420800c524074407651104458484201c000c24004514000040c0035000d500d10701c0c3d40e91b0041d151032005016040c00302d00150030b140950703011503000415143c100c0b580344c3c1d00440c54100152089904001001108107400410000075101e044582c4650305400c0250030080d0030700c1c5400254a04008940c84882c0010b40c00860b481c1e04041d9162040440359074070300115400c01206030140e42d41010205400c11001d02410344030081c0e41c8281c941e01380c42e108410070300c15003800998074170001d038000388800e1140004040240601183c101c0300803c104c0350984449084a036441000e55001041071020b0082a4241c040d0001d000d000455045c0c4890101500a44a00ea45842e00d8800ea80018080b2031203d80d025008400b4442c0400030410395950781460728030351005105030a1031010240000d1141c0c1c2c201c9526031100c90304500548584c500c141e00440096110304022414 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 933367131 1250 933365881 933365891
    0xc0409120f2003130b070b04061a030114010807090b1c030903061103060f09130b06010c050f060601020c090c03010b030a1e090309080c060717120903071b031a0901 72
    0xc2150644401e03071507034000c0c4000c0d42e84e40c150000f454000b901e06800c807107441d100802500e800120302144503a48182c100b000064403138102030942c001c02c0c0e01043d1080c1e066090801e01c80744030200032081c0d03040704c1d8001c0c00c54074140c0e03680e11900f013940c40c9602ca09900c001c068030986c0801200d0310750340ca06980310f890803e81c65a01c03541d810702211440300c540d64107140040304100490801c006204403480d0b0448039113003c1c0c03800320f1a80d1800100444020074600d1104003051981e4015160200170540c481c0a0b594035502c4100403550b94941110154014460071141c0b945504044450030702503400c0e104601e2560382041c19460203540301a26101c5500da403001c2c0c1c90b1a10194052101c40c82403100d00215440d1660704008000d401e85400c2104107410138505c0d040d00350341d50411610f03035a50065031440c8965462002d0f820740d00030f0b003407007003c9042580108000080088010054a07205400415066018148500c5c46041b40e01000f4690303203085448110035444080c5480d800425400007280d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 933368381 1250 933367131 933367157
    0x1508041103011e0b0f06040503030316051917070504031a1914070306080304180908091903060e030307080403050912030a1112090904020607050c090106110c0409120f 73
    0x3d100d03511403003840c01590b41c1d14141502d45007200f041400c401c0d00310380243c100f41c101400030307840f440301811405044030303040f245240380c174094419241039035810680c031050000c80c1c0ca400b03401c0040c0f00749070841345040c0e20001041c1500440c00e45007529040030072403000e540038403180c0e181c1080c054100074038680c8c00c000340e54442400e40100d0340202075240c00c010382400c110101606507031494121181c01e0700244001c0c000450504000410040c1021010522082c0c5041001c01c520175001616003000b17014412060b105c182601280481c0d202d09400c00c20030500441454803404107640e060000313840100401c2c0032038803800240c00009402000c081044280310140e40c5154824103201b004190aa012490000f9003401050001c200c0003043d64507003003c0e140040c004480040000b481b0340c1c0d001c07501205112042180100020b0064582c11040d41c68036005440203040a01c0494070f8865444c6285103420580100072056600c9010f00302c0300001024203403045000e0203100745c10040b84410798030b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 933369631 1250 933368381 933368411
    0xd05061903032133060e0105070303022101031208100e09032106031626070f0e06120a0308041511042c010f1208042409150804110301 59
    0x440c030380901400c2110301821000c0150094021280500301404181042125002046c042c880c041c00d06e00342e0b0b03482c801843d0903030007401041d105203000000b81c12160f003038034032821405058a01030030381741001c6e0701704540031500e60300b044400800d4810210410011090030700204ca80000d800401e40341400e251804500c4107000c00c1010300c80348920b443c02e101483c1000d108180f411180208a0381c0328038141086164907030022400c00398213030307040e22002e80f0b1700c6800d2080c4000740c030ba40e070a4650a5a9218a90404807a05680f054402c1000950703143c2a81000203648c0fa03010340c5915618050307901d81e100e484c611002e41803e240c9180d141c44100c4981122800103001078400d180012208041c28071150002a00800d0410f0b9800644001803002840102048049504450001581042f07501d420344090145902075089032107840000c940a40301d0a41e50030111940307985014949507180040c100d00080b400700d440c003042420b00031a02280031a00300b059041c5001d000480c004c1517141e190 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 933370881 1250 933369631 933369641
    0x312041a25050d1811010203040b09060a110a030c02010e09010e0402130b0a0618140a0b0c010b0a060c12021b1c05070803030a050a0b0109050d0c050a09020d050619030321 75
    0x3002d810307101c4c40c14000420407a00440e0502440a10085003014185585501c55206281c0d80728494040414200700181c4159071411041c181101038481c110032518000d40810400d5008a011520700c494800007424601c020038101c1d001c0400c1c046064469400b8000e18140e00031494000949444c800030b1551203580c0c014000f08030540c0d860381007207903164401c0510100d5401401510035000341761a2195141c0c404841070350043c1c91420703510428507004500512607905a40c0d08407450220010f600d0b904540da0300f416030701a0b40751601020b01007030201d807076144d146000f04030414a81d01021640c00d01e0420070218880c007a0100301d80001c2a140c0604c2c020155001c0c101a600000c200150001117000d4560415824401401340300f003070400181001d0310310700034540540d00c2100b8107000e200080007240300404002d00040315135034440c80c04d08082d40c0814040ba440c0c1d03092a0114040382095065091824004000040c0041c2195411078401010b1024a0101c3c48000300d00184941c08c0d10030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 933372131 1250 933370881 933370901
    0xd060902030c0414040b030c130609060e0601030b010c05071e030507270905030a140d05040809041a06040902090604150e100203130e0703020c0312041a25050d 70
    0x100a03140c0303203004964184e00d5107001d000b90040342001c0c0781d02c109450001d11402c20031000c07150346603901d1107960140010001ca900c0070001500341040019104a810f800c1c1380500c40c2a03070103103c20306850340123403000d640c003860090099101010800032054120004880303e6032100c0311068a0b039030398443c00c0c03034452203401c00c07403540c0c06000d05003040510134403185400310414030381401280115181c06441303001d11514042800701c01e0342c1a4690711016000c650704603401c1c000070009400c190802c04429000702c00414000e40c50162460440715850f625501905001032440d480c0a0820a40300081c1d04030a5825811030301c28400840d00f0010007484920b50041036442c03154110150041120740342404500c1001d5400070001c19092610b104040001e035102460010000d0701e84a000b01d00074452009050000c0c003020a550454004c04c518241c091802440000c509a25180801d1240c0c2c00a0751511a421651591481c05081c2500d681010034041d081c0f807406c0519400c14070041c0d4100c0c41c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 933373381 1250 933372131 933372151
    0xf0705010c03150e0601052a1c0e220b030607030e011d0618120f030a110901090e04030314090102071709030a061e090c08010605060f0f0d06090203 65
    0x10707007044090b9042c400d19003008800c1c0701c0551074915003402c0c01342c19000034012504104c00042c003480d0411181c0a280550100d0b021221401c0191014880e25150000c200180031035045414203407991266502c0084030340010109141e580018010003004580004040c000584031724409038150b0381884818440c4155071408150b400304285c4080c2100c0841d13141c00f00c210007104256503c4a0001035659015294482c800c00d01c6801681640ca01f040340741383c1c487c4410001411018040703402014600880314040280082a04407500514502940c42e001b40050318410f01001000c551010343c42d0090b000b400c0004068200303030b8042c2038403801190380704104d81d000a54402004480d1040e6074100388240b04040c203214500d40020344900c4405000340800307072540034051040359903420300d4181074032940080002c940d9526001c241410144241510765282c408005003508001c41118088022100c5583c6880c40000c03041510760010130080c1102a80d414001c03a8850301480110f0059030307022 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 933374631 1250 933373381 933373391
    0x4140601150306061d0103020c0705031e150c070219180204060206130c090b0f04180215070b0703181202011a0103020c0601090e0f06070f121a06030603030f070501 72
    0x9070024003030b82c50550160040109600160b042c2d1407480c2d0039200701769001d18000d6a82c00402410a15140040d0850399060003000c44400c0031002044843d08240c0c105010380744a042842000c4918680446d004034003520108030940c01481c080001e40c20700c205101000340001d880e280b81c0c2d9280348010401c004841e1b0b0000d8280f11890701084110390100201055942a02c401e03a00c40c0c903c40c41078420742c0ca4150300c6808402180d51440445101d0b80341c06481081103501020441c1c11110102109030f00800510051701c40e0314000d4000c441c48550400c0440d01161200c4500b01c000701105905d4020f0381400515420002d0070441e01007445c1d040d19400810000611580c0794070100b420328a20703041c140b0420150045040100f07000c1d04443d08104000790b42c2035401302160800e4840f145192480c003901d400c00030502c0d0441c3d6010201c2442e5551400f44280d050409021030340c00078038040e100218001c800f10a40381900045a0002d00034007901d0074040015090511601300840c111007070b035142c2c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 933375881 1250 933374631 933374669
    0x41707141c030e0d090501030c231207050a1710030503070b01030c1e05040b01021f020409050c070b1513020f040918200a0308041d070e01090e04140601 67
    0x140645010f5201c00000750240c64400b610284c40c100300340c400c2e41c0c1810f44442c400700800c1d00850b0341044200c1e2440b052446034000c20181c50072544070398001d5038503c6070b80011a414a100d5810f441820f8004e4132242071041c1c0c90600441c012200074044000c0e108032074030210004500388081c00070248500b102c004e9039411803422907610000c5805c02c2102a0b102407240001c4400c00500408035942a240006d0780319801d40100e042080041c441022581001d8840d00991460fa000b403040b280c110300208029200c03101004070750b100780a0007600312114040172410030b640004040c031900000400c2c0140400a0f52400030698000140340141e010020a08214031100d500648800484000040558030003582d91651041800caa15002848141c2021003854480140400243d904080300a880e036642c3c10b4aa0849400c2c00940340b1050000c07808220348901030400c1c0b24074034105840f4000c0e100d007414054020030400401c140c072101c1c2c09441c01301c007682003800194042c0610000818000d010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 933377131 1250 933375881 933375887
    0x8060402040f0e2104121214040f090b010c06050a02040e0f06010c1227031a090c0f040b09150a0f0b0405090a0f0c0216050405041707141c 61
    0xe0082c4032a01c1c50500d982c007506002c020842c4801c100b02003a03809000800b50202c20500e00694001c20b05403002c0403842820700103d000302e40d1103001150b07500002828080301c1c5281c40c1c001da10603183c50213507007075042c441420725811100c116a01031411f401400b03080d031201c0d415110282c0352940010343c0000c0500288008002c555070000c00040d01e54124149a40000c01110794800c0c044c100c2858194120b00d514400e010840d83d001d8180c22500203c0d0100c150880a6000340c07108449850b100c0c2080802c100078040e09505c10240880a1720b40707444118140f2072112241c44210b0307401680c0b03031480b9125966900903c0d00490304086554102600c9009024104080740c006420000481c00b0411420311400101d0b020342d00152900000b50700c8540b9044060848182e8040f201070418200500540c0d0015030b008401e010584180486940c2d0b8050004440d0241d80241c498038041c0c5079030b01381a075000b000f492214400d00500c444000c03601c04a030304000e60554040d420520300400072101c0340d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 933378381 1250 933377131 933377141
    0x10f1404020c032d0c01060f0e0405070303081902070b0403030506031207060c0e09090d022e02031803030703240608070c1b0915060804051510030c0806040204 70
    0x80d1000c61411038200d24042e62070049500e0000260341c0f51a500c0c4146001c2d03543d111035000f501204686401090307041d04c0c00b80256014120b40d241400c00c00090000c40c240c1c4c0c0364000c54100000e01240303801c5032000c0341d03403100041240400f2172001e100c02e940d40c04144002d01c10749000310000c50032402d061400406550000e4040380c4258030100e6110169103049046980e03690340b0100001d10907002d0b0340150f40c454032808190751702040610070440c4141020408005600984d400d03140c0fa40b41392000d1041d881c0c20030b1040083d030750b140b030041e60303800300710394021a001b202900e039024006040055003440e40d402262040d00103600c3e07040c0304100803a50003804141f80002c010a000550a2101c0100004030081000e010001d80e480c1050602440b082c41e81d09045401c0280c0020580f40ca0220001d040b004000c148161030005001800c1c91040f41c0081c05140c0c880007030520182c1c0548401d00c0004050801e20701c1070490f4800200141c1038030801d500a1060f28081d004a29241c010001115 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 933379631 1250 933378381 933378419
    0x4061e0e100b15070f021c11030304260115030503070308150d0803060d1b0609150807051e0319051003030e040e21090a23060703020c030105010f 64
    0x50304002900c042c550341d141c181c00070203140d0f0348503d4652455040c010800841c120010b03400c03c07003451507102d8403888003081c0515140100e000d08241c2c0700c460103155981c03240d4800c521000b00c0480e02c3c1035941503402d01520414001e6000807550341400c003060918980581c0c0100c91035880041d00c0d00030140c109901a0740301a20020140c003042d0510f0104202e19400440145812800000100143c0d60640c1464585070803101a0211030441c42040500403040d008241c08500503c10000303410411719009003a6109030b0307490610710b84450005440c8c0380c105c000845001e02e00b1109007100c917410f8001540c45660011004240c1000d10600c00040343d4014101c102c00000400c0e05202080d00b14094100320700781510002041c20000c0700c0b060601c1803004008070201101c108119143e030142c0082c1c10200b400715417500181da42c80360840e0120625400c0c02074204001400007034185007101c042c004480c044d00603103104038611800242164803d80290110b402c01e0202403248007103902d1b604080d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 933380881 1250 933379631 933379663
    0x816080f2a0102030d0926090f0111030f0f030a0c030209010c021c0615051f0f050d0e16090c090b12130c09021c051302010804061e0e 59
    0x110384071511000101980010044111201c1a007400243d20030070131141c010302040010803440d0800e00d00250303000c0d400c3c2d4189024100500100e60040c544001302c6045080c0100341c1030003802940c005407030526407040d107849107000c2808060400391501d0014030f01ca900722100156285401c4440c401151081c18540c0101407043c00f04060076600300c04000b40781c940480d204482c440869801000408000030010b1846040150311860074410422070000c0c2c403c00c5440340c1120038614202c60a0400d414506130000b48110036050165005500801d80041d075031101280503841b1001c01c6150002c0c05980380f10800041a040005200c0c0c1d20a500b449900e1345811851306d442e2a0124034030307000d14071411680036080700c040781d5021510207000c0c10481c3c1c800e16100c002581c5602d420000d4004d440e041045200585021010781d18a20035684140354a9042030f5008180380c0045807a40390040c42140d5082e40c4401c10380c4114114001e011040d0702006002c0341d0741c5200d99070b10381001403004501000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 933382131 1250 933380881 933380893
    0x40e01060c020904170c01090c05040b04141602120301060216060521090102090a061d0a030f0b060f090c0a14120628030b04140a020f01030b0a0816080f 67
    0x503543c2d40c2c9100c0e007064105050001d4102d041285040c68407641d0741c00180780d0701e480d401c07804100c800240d0804072802118200503070a10202070100b80d4051425a440c90413208001032905d00038440f12508142d1303584100c030780a050341c00280e90182e00c02c4e0401009688442b60700100c88200d2108440601402c1c41d0140c2442c0003210b11181a4a0843c10201c0810301c640c0000c40200c000d40c19224450b038001d080c004115900c0401801711a502a03040028010103035031a2450705101145d8030403654410307082d06903030f1481d86800e20029800f6111952080007520740030140c3e88c43c4500a801070402c1003900340d5a42030244080c010104800508044480500c201c0f5001c2215461190344075005440c04007044140f1041541c5140300b19501e90751090740d0440c00301c1403249038413149110718420014403450700d40d80c1c00800d03a40c0c030205038020340c000d0050407401c039103512a400c1140c8514001d004801400d80701c083d01401c1c190305c0965100395002e2910204200841040344102d504030a10103800703 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 933383381 1250 933382131 933382133
    0x30d06180f0e30040b121b0d1a15030105100c0c05060c0703060501080c0f0d17090301020c0a05010c0806011d01141b010c111203130602070f03020102040e01060c 71
    0x9110a280e071618494480081203d40406146880c1c00c507203a82c01d0b28409039143e0316026010107613002203079081041c410b14030000b80c00010343c98541000c00b8848502c00e090016040c0d115018181440398070a111295012040c900e4031010540700d50041108602601c81d8185014000f1500034101c0c001c0810452203d25400700b48920305003000d45405072511613a91051903480c80c513000407940001d25540c41d16000107a01e07200810304a010074000c80302d608415041e50100120140040c8000d0036000c81c88183d1036007400703203030000d01440704098005410600e0440549083c1000d01c1810f032001d944030364412240d1540030000650040d003d007000050018200000e2821410003c611810300a100c0c8002c2c41560100b0165801c0203005607540d01c940020820703542c00307403640c69015408140407078161a113081c40840c0c2004003a414003006421640e40542e81c804c610342d1074100b542c865a0801485003c100c1001d203540304a0b01a800160f901c03807400d903a1090000059110720100a44000040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 933384631 1250 933383381 933383383
    0x30807020d0212030a030501050a0509011d07200703060506180406111b1c050a020c060f040b0a0809100903211103070c1112031605030d06180f0e 64
    0x150109405072038041c010300851000c140a040c501003001050300c004500e45450380c2c0d05801550581e40141c4c4c3d0094860394030403c0c082c45c102d081c000d10380c103c902c1c000d00804550720402d00562111240ca003d00c03544402c040200f0550001c6082c2c82c501d50045501403060103114010640c1007032054505400340124007a00c1d905c0311b00e010704010139090b245d084040d0440034510644400c0581d00141e8031030345045035401a90303006245400c0160305894040650039a0040094407081252a0003078452103100c1c10070000203a200d00228a07a00c101800b0108038820408082c166490b007640b03500040d030606d00d6100c4d10b000c640d400008207207400c0035001c03070000380e11240700c8c20030401c0c0d0003046c0203504494000001070416180c00c900800404802c00000e01d5000040c8800c0383c0c000d004c051480340c0c154083c8980c000c034404a28100d43d204014142404000d04880b00c0458087e02c25a030078040040508400d48155900c0754240f400342c0900000c5584483c81544145621503030104054902c5100a07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 933385881 1250 933384631 933384637
    0x62203020c0613090e1917070812090c0a050a05061c0608070816050d080306030a140607030b4002070303020d05150d150b0409060c02010b09010e0a050a02090d030c0611040308 77
    0x100000030007c11000113101c0e20f4151200a648003038801d485105001882050210032101380481d84a4000491040e00741801d019040c1c80700900a01310701800d002c244001d60740404401000a0504038204500380c0444c854072000e4480d40001d081410302e000307501450140e295400070850404030354204010769908010000e105c2d4450300300c2c0d49a513200d10000e400c0416400ac007034021302032190013100500f800b088192165941e5142005021080e400f8805501b68800b040501c0e0b00c0014046c044130000c054156208103400d000810000c0c01022440e4140e0f003109404070f000c20740108080045c0245802102da000d803400a0402c0c0c050000030014804200d04800a000c900c0c003030040708610328454110564510000e0018070089030b45103040310080041d012840e0065280a000302e400f450400210f904864100f29103c01544401100d80c00809014094646c010341c200440700c040d48444031103600c01802602c8008460f04582804c0007a10005212900d040c1e100b0801440017800c2d080603 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 933387131 1250 933385881 933385883
    0x16080a05040609020603092118091329150102060a1d0106030b060307090b060f0c160e1602010e1005060409140703060608062203020c0613090e19 64
    0x10905454504154008080c1c00b1006074201c50700008000341588001102c11081d00d80541c011810034808035000814010071400c0c65040c0040100f00c9d402d8608a003069401c070150104c1d07a13114102c2c40e62813880100070005005007955080c0c8003000b11094118841d03512503800b842c6000c040d42110300003900c03802e00500030010655250700031068400c0c40e481d244a1004401d000f040f5098403428841c481d1202120720340e00c039208640c1c01050440540c00f03100c6161318040d01e00c0b0b00b03040d003e0130180040d41104c511500603119404985e86180c0c1030b006042e00502890403040b841d41441604403c0302101d00301c0d10303815a0f040c000e583c00038480c00288201d4090408400190320740740c1100050241113041c0010300350300c110a09641542c8030114035102240d200c2d4004212260342c40031155128942103450104c1fa16252044c40f04c903080d2803007200d202620900c1075074103104091001521745e410440b941051403000d1a424060004240f01d08040000c0b110000c2c50320720046d00b64401c2c03082c11000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 933388381 1250 933387131 933387151
    0xb1c141b070f05030309030904060902191b120c0201020f0d020705060a020f010c050c0d030515150d0f060f050a030503040b0f0706090609030e090f0402281d1608 71
    0x40c00100380481c2400b4008200d07403110a50b44d490038a842240c0d9241c00812929205034031384400010f501c4424401c031641c036070041036480c0409040141c1076035060080a49100384030401404480042c41c401c0c6a001443d605441c0d5101039030042c00020728050141d80c20a4455000b0741c090b4012a8000440c802111001c039100340c0c0d2504050030403030074000c80008141d4070703600f07286203a017070180c110024142002c20041120110707005e88070102e058503401e580e80000220784443c40b8100d400c151406515610200321414a011000c003d814101c50726403000000d031507512030051001d90300b480c4081000f00402c903011f64005081d03483d103580324443c3d07108280f40d000e000911082003144070010b0b14551600700ea4104241c810500700b400c003070140c005084000807801403c0703510030714050f501140038802c10a640c3e0496602c90782031011b01400c0d44a9000c5607641500c15000fa0004148a0b0015051901454182c503011b41009088840083c00c145209904c0c0202c60031200e610000039a80614544 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 933389631 1250 933388381 933388387
    0x100b03060f10020a1e032a0f0204020708030a0501090e0114060909070302030601181103093004031a0f1306050402010c0206070602120105030d050702190b1c141b 71
    0x9505a103494020207000700150103454117210b8103041c3e1441161450701070344481c80c03c07102441c88111260001c98500440c9000c0c05440008a01d244038400c1e00944040c200500c0d00b80c5a849100c00c9070822140c3c4580b03103440d80011703c00710501e0701814024000d814000d0280306d0041c1824032b48032900501d194091502140001c0d10b80008014180045030081c2c19503d107940c54042c0c1500411040401031a806d003041d0b0031608044900041b0703131142040c2c90280c00c6409940c0e401c02c1c0d40d0801a100b083d1030000103041c00d07100300300c04002040107600c00d40300c0020f403100401110501c600c0040c5008070030200380c01003000340b007041c076900c101e10340d44114000baa969030b502c0181c1d4801000d40010750405008640c5600b008a10b03801403495403140300d40d4003403503a80c5004150361507200c50740d54070000318207109030401814000d4900f40308180c05070300180c0c01500c0703100a440c40d4100500941300071500340700010384543d20340309207401d00e6034902000c0e801b85007070103118102c040e2001d01004a6030b000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 933390881 1250 933389631 933389659
    0x7030201030f021e07110d02090c0a02010e100e01200304020919090605041a101a040302120a020a09020c1c0c06050403020d11011a060304051f05100b03060f 69
    0x80d50464400c4d80181d00b00d160b500f030719001600200e400401080b203100d4030032020f2007054a0400840e040280e40140002d2490307654620004550700320031000800e640d03c5e5020500307e00418000807100d14905000040d90840c401207680c00d45666810801c1c0f21007000f2841041201e103041200d90042d01500c0002c40c541768503013800c0f080c4004000b030f1a101440c1c110548104140b0b42c0010f40603078041c5000503e0340380c0300725004c5080c032405d0b0341c43d07070715141d0031001002610304070510f62485003c01c20449042035520b401007295aa40c6103030300c03599900000c0c410821440d1880c100e0000d802007403403c506040c1c9007400555038030141042e150744c1a4404100384042840745600551651b40810140014209441d01a5a40c8005d20450021410b80c0e801703e03001d000144116841003050042614850740c20030240030f06644040c0007541c944c066001003080b00c0c0001c0402c4000c00d14080400601c0b46408407040b14004c1650b000300c8880c1c0410400d0004641d14030048a0350100c080341d61141440c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 933392131 1250 933390881 933390911
    0x60e1b0715090c140303031e060d050322080a030f03020f22030b07180e0702430e070e060415091802070209072616110f0703020103 58
    0x4004a4a181c10700703244901080143c81c041201c111102d600c46110b44401e12000c254880c04206ea0348007003007074914038402c06000d400009940180020342080c03026901030700d034281141e100080d9020700b01e251240f4882240000d61500b8010001c260103402c03541d4856070014440f400310b032245420541c020450b1420030041108640d50000c04c1e035801c03080428000041015a512440180c03400c0c1100b00000b03a14602030f40702126082844c8450070403070fa051400c1425031040c003808101c01c6108010801c884401d240d243d10702082400c86103070390070445c1c1400700e03e400c08003100f40389506220040d08000e1840c00000007500840703141441c001c1100c006000c02d03885d00860b80715422540c812640b04005503007003045c0c40c094802032000c010355406488210f605078880c1440003504031214800090f00540704401d49018010000c5811030420001a482d01c40f524040e01c2c80613243c4ca64850b24540940c000780d0344120300d000c0c00040e020101262201c252500c1c0c1c01d10010307040c10b0302c450040f541c0c408 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 933393381 1250 933392131 933392153
    0x30f020909011401090b030c041a092805010c030903110d061a04200a0c060f022802070605180f030d021f0513030e0f090c0904060e1b07 60
    0x4030280005405694991000360039000c00d560290118409000208108800303408170b0f441814080080c03854107140c01030f0040100074044800b94004010f001c0c0c1c05499540300d40460901c02e0110007410181c0750500800000300c07680d400241881400e0b0b04560000750803a2649044940040b01d48015400e0200070070441001e1102c0113041c1c0b440c0080c41440030300300117506002400c080d9020403e141c2004c14038440a4201c0108182d122418001d05648521501003811107910489000c5034010803452a1400e0341c100c1c034580300340729034074446405c0300c4141c0541c0d1310004030707080c0700030a035403403800701c01603c0c621646da441c0400750110155084161107803010128498005000ca811516003482c00035241c2600141703103500e00081c0101c522107040b042c06074078051502c0220b000c60018440e13a080c0d8140307070f0500c405a0407000042000c0c007959180829a84036000110445503504400b0041000325100b5070003840c09000d180e0140000c00008040900c034210801c1c148a41c0c0d80c5e403500308002c3c840 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 933394631 1250 933393381 933393397
    0x108070e041d1e012007020117010b07021302030630060406061e350d0c020f010507030206270610030c090515190f060206041202060f0403030f02 64
    0x21003012019140c0780800200c202182460318000020401411200f509a0316055101e91541081d84164100c09881e04000c203103103881414580411700c0342c81001340aa060982c030145172004040340640940c01c0000040485400300c00d4114a5490320400181c00c1c14900c40350203941011a148840c0208280705904214190030b40c1160002d2915251500c068081c50252008480714a280002140c03001c0c11860203071030200c0d4503410351381f50541104240707d50220003040c4044080b10341c80c10610b42030020041e00c0b440c03651408000742e154014880006003c100150400c5420000300700440c2e0301042c0142c0000c60303040c015241765582220102c010500040b103008500a40c1c00303008400304040e04400449200e4900c0382b540c1595103c5a10440c1c074100d80e168508000352040514515044903804101c41150762091000358503200c40c0301298030070390088809a4803a2080c0424003445044c03140f0b0004042c8028031591030030300789584090740054070082c00d154461451914140040c0c05541c058 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 933395881 1250 933394631 933394661
    0x102040b0f3f0601090504020a0e0901140a090b06071a010311370f0b0405040b030613030f050717030f0f060f0d0206070b100302120304050108070e04 66
    0x1a44200d80c140d520b5485038846800b200c900140700120003003100d406000350141c034070354445440718a12801091180090005040215890011415039107503c0901140c41150741c4032004620001c017402452030060300502e130490410184041141d0303030a484079094548504c80031466011340800b080d01c50090f8407000f40306040d42040d52020102654860303040720b0003030602c241c4090080d814481a6071010b1280350450086c142140d101c641b020f460a5540c83c0144440700040c0d664031100c041024054210303058220340018100311a180034080c20000c0207080f400740c01d150400200c1c002040d180c00e1402424826003541520a06015400f602c8031541c10000c200800e60000ca602d900585c000c540f02c00c01300d082000031408980030180580c2c4942d60240003c43c1c1141182c041181500b00d4000c102e07401032040101e0400a0040c8441a0080c070440070080c00c02c5080d48100440101c01c800420140d60091004004a80c1c1c04800d554000425040020414400a0100d0042c0002e480c0344810 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 933397131 1250 933395881 933395887
    0xc0109021e0907030c0f08181f0b06040e01060c0c080601060903030318030c02013903020f0318240304030f030614030307080a031d1011070b180102040b 67
    0x4140d851405584003102100d010b0060364484800740c00f05c8200e683c41c400051610782444081c10301403404039420013034500082e00e4480d80320700301c68540a100300084584c503141c0b440d40f00c41d403034441c040c10106c4101100c2040c102800d1221b40c0f24800014819242040800e810305801d01581e450604040d0040c40c064403201d41e16800003801c0c1c1d0400744802c4000900c0c5c0078038241510b40592080000a07416950f0781880c1c4419001119030f41405c6144c600a4481450404651404008081d88000850014816107892410043c0c01d10284518089060b04100600c00f41c900b02c00004907891001140c55050411003403003550480c0e003000074034040041c0004284800e25400000d803207103148031580d0030b010003510380b00114881d0750002d898a4050384248801000038400d10b01a1402200501c0c0000391000e114842081840e980a4100401d8001107a480034548007401003a44e1401180616403625029070b403102c41d10341000f45540ea0700132024071100d81c400170a404840090060042051f2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 933398381 1250 933397131 933397159
    0x2205101503090203060711030327010207030201090b0a05010f0e1906090b04050604020c03250b10060f03020906031501120f0f0b0904030e13110a092105030f0c010902 73
    0x1c02400429416071080c443c034400550258030400701c40b034010a1000242d81144c542c24991220050200d200c058101d4000342e41c800105e00034800340c030100c2e00070780c00070803020b4850500c0c1c6d200d5400601101409418140107002c0324944100c1c03130007101c82207402035003150707a4118800155040008100301c0c45040110000e40349005802c00781d03401ca0304440030009926104200300480c0b041987c06021034205006c40824951072140201c00d20f01044019404455584da035580000e80031a240c0a00b162510410700580350302c02e070201507a207200d080843c540006840022201d001c000e116001d0545200301e51903850740b1500c1c0350066084c110106100785001c912240c40038150400c41030a5003441c00000041c41e01e45000668007843e01a150080d40118810511403d00c41840c1c1d00316000340c0b6494407058207031440b0010000061709a0340c010000d410413081c1c010b0000914005807445110703001d4140400c001000302c4645042c0c1c8070139113640d40005110940580160f0300301942c03190000740112 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 933399631 1250 933398381 933398387
    0x80708130b1905070e100e0f1005041e03020f0f030f010507051801020c1c1a1609140906040e0f011109010e0d080f07080403020d030309050c22051015 66
    0x1100b100d00000500c559a00d5400444100c0c038240c1580b03170701c01c0d265800c0030f02c214010400b0b0801401d016103112000100c9030045440d040501e003030400000d00029040001801c510b60700c120403c9503112024059145400103081d00e03000340340c85d0344130310904228880142e8041220001120100d402440759240c699409403150704090309000c0704400c3c42c0401001c941c40410040682003004242c0c3c6e10141400d80000a0302c12066821038407070710303840c20340308812204c0b50650b48a48090104681580c1c02007500608402c41503004180b0203400340181c403c9a51124801d5034801001d07100010001c43e0720001c0c915200501d01001344c2940f0349459810003c3c40d5034020041510207884100300d102070306050200b030111081c6c015100401c103000b404282e44d0064024244c842c010101c89040c03540700e130001031030140a10030803004039907202103140401c00184018625007008451070320441c0c0c240a24409030314000c02c041707000030b580c0754001003d17100464440c4014100620010026076010b80000e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 933400881 1250 933399631 933399661
    0xc20120609010615020304030312050406090503191706031005040206090406030c050a08030a020706050901170c120c090d1401060803120901180f080d0908270301020a080708130b 78
    0x504901d100130003281c02d045c1c0000102c40450b0b600d543ca001000d40518450001031402820440300103842d03010345030200724208041d25816031021282c0040000440028220a0304050074080c5086030000300311066602103100501d0282c100c0d0302103059903d510000d0b0030751003049019a886458000b020051040a030103031001c0e00e20585600c5446511000425070340d018080d41c110040c0c1c071a0341b0502406105001810340b081040c10401ea10403103071401400c4403d000c48086a40e41c0000c24200030064945100381d40002511082d540b42101c41000b080c102000c0b004040c010070441c0e004101c03484025800140141030f5003041c0c90b01e418500e40d0a41105500b9108441d4542c20504024401045180882841e0b940104a00d0300100c0998030b68a16800c9002401495542d900300740c00458400b4008040d070081c0c0844a002c0c07021030b05541c0914117a0130a086020741e105026a0050315004080207800101c50305000c0103665440c600302c80300c0c07907488600501a11702c1c5820320920205020b02c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 933402131 1250 933400881 933400889
    0x31a03062809051e460b070315030f08091815040507031401080c0a06030612020d050307120215160f0f0311070b0402100c201206090106 60
    0x414810124a80401c42034a19204018041d50000322000c1c01000c0e200b10035400c81000c100654031401c14611004c1c5400444002c0d02110000c0404002c490f11010a180c04d030440c10202c11010520094941d42c140d500014000b5090595911074940c100201e58540c4000311745c0219207d9007480c541c5032605a94100e0090140590002000c810f42c1401c0c0c00e80c25413041022849102c0c080380c01108000290601400e01070a040e03440040c03d074a500d0419002c2c1c040e1040400500008080505000f07484025900c800100b500e030103020300c4021005041d420900d60101c07642224066207040c858110f00c20500300500b43c4920b07014100006401042015129008410b4603001e1340e40d128182840c0006465050000384180000c00e00c0d4600503900d14400308040d160024030310001c07541080580d030122170241c80300d0780420104001c52400c41c22985200746180b81040d22081142c0e55900f13418059560341c0150040d800c03200c0e003e51100304181200031940c604444075400c1514407075000b002e184c05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 933403381 1250 933402131 933402181
    0x1b07110a0b03010605030a1d0a050c100e03060412031e090210030902011b11030304030b1005030f1b1309060e0106140d06090f0c03120807170403031a0306 68
    0x4001a02040807068074102c0380b464440c40d00c0e650352070189500511038203000b04102c1c4920001c9030115801000402c42441c411402044981c0083c810002e0704820000c02c1002c01c044103116000c1c0e500c01040ca5900a507010700a203201105d10f42e4207030080d040360581c0080d1020a200303248064803c54001c0e00c1200d0081c0d86507440400c0342c60044080d200070b0540039021800b1359403506400c25085c030b41000714a0044880c03003400d01140700041c0c2564403961003a16062a503070306105401e142c04030501c00800741180140103c140c581e40840e240c1d000001424070080a0010700940d85c1c5520508407044004000100007600d224580f1800400da030900c401d0196180c080042a810011407a212038040300820003681c500481d640e1001a101c00807084500700e4ac420341310000145203a4811020318802d4205800d900b14221008200030401014001004013100b081628446050034558206400d450040b40050880440080403055418050382621035041000b5050404600321600150542 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 933404631 1250 933403381 933403399
    0x70528030311040e010e0415020c0a020a080f0706051305030a1a10032102030c1912050f071403130b131707060c0f1208010e070203070b010b031b0711 66
    0x500b8015071405140204444050200c0050110304150b080495002d032184400c80a101e501c4082c6209980100500b652950b01258009003140b52400004000d011a0001840441c00020525a030744e090b521641042c4080000d006802082c81801031016203400340c101c03503040f46189080c03000c14609a5840754140c1c0ca440c0031a0110110940140460f600300d180150f091b2100c8080325440c00d0041c01100a44c8410403100a0010040c00f1000f2640e510024412060b00e9504000a0301d800b0200d1120030001c040000e4442043c07480c0a43d0740350360308000d88420a401d0700c1801c601d9803281140b090040048a000001c40d00c580701c00500f03107600088850405196119a603c10701600d1100e84c13100e54108840c280071180c03149904204040c0500340100c0055032540302d61032141c2c907143c03281001403107a1006200041110a049422800700d00c010b40c5170100c1a2a0110b1107a41030203000489407001004c40c000d2450900007043ca040c0108805545604a00d801002e498207280e01d24003440202c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 933405881 1250 933404631 933404651
    0x813060206100504110c07140f0a03050d0e040b1809070f05010e0f0117010b130e070c03080705041a03161115190603031101050a0507090501050705280303 68
    0x71828a0140002d03141200c0300c0c1d42080c0411000e03102c900d190a400c0ca10034040540d96501c03c00951000b411101540c4480402c4601406417200343c0310701e0700e8043c1003050820000901b002920050340c41c1e0610b80140da0341c440d1800200a400b80c04480d40c1d1101c14054601c8075080e69600b0f02e03000d00d14000440b8551503540380546046507061042d9400303d60b4281c2d40c200300f400c02c0ca210700201c0307005140818a40740c904580c01c540a07030a8100540102002c604130b0011080c503040080a0035507440c0c56a483d160a09004002c81d007460402420007808002184401d40200203690280a84268900c1c1580044142c170201d5001101c82e564140b08907071041030502c1c05284010503c5451001402d61408219000c50103180081c0019441844020161445080500c15600a54807179a1101e480302045400c0300d0130754001801c40049245440c00b0701110903000103603c01180e000382005620760041d42001820407000114000e00380089480e020841d2919001080400d071013500c04010440712 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 933407131 1250 933405881 933405883
    0x80a0507020c030a080f0f0a090e280209040617160b0f040b1b01060303080f072f010e030a030903020d0c0c1701020702040603030909060504090b070c030c0f08130602 73
    0x80d800c0c2940541010650b0300218178208010003039102058036843c80c0000072100f440740b42e0f02524910303002a02c03160041c031400c0c28440740c8540203013040018240c12200c2c061100e841c1503c801001009907030002d510080c0e5111078010000a181f41403103841c03010b960b80d2110352150b0194001c502c802c0d00000f00403175000e03001400c0d6560182112140350615080007941d04c42c0e82d2025200080080e01d00d00400c504010900554001d54031039524100c4038185081001c08200014140c001403182581400100341a58036110030120045402040e02c8209520441c1c0100380d001ca22401c0780c00300180f205012500340d0800f07070f0b0b00b51282c0c0c2292a04059404101c0d50030510390b034001c00074001844108031a405c0b0303005116108070020001403810b400d0303500140440390707940d008a011a00040040080010a201d031000a00e0b060b9024803a08060307544021745880e0003454030080c81010307400f46052500c15000b551078641c1c44401844118154186841203802102c04041e07000c100700800328000388 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 933408381 1250 933407131 933407143
    0x302030108010e0f0d080601020a08030c0a030f0b03120313080304260c03090d030e1f030e01020901020a0f03110307080304061d061303051c05150a03150b04020f0a080a050702 77
    0x4d9200050811241d2842c2d00320f0703110401400c1d66045200e02d40307000b4081190f4100840c06040e082c10340b40d59880c0c0b01030007d0b00352886c440074628220b03d007600c0040d4075200403078868014090103596036925520100399050748940c40b074015207140004001c2104010a100c2c2691071003c0c903402d01d030801100e00e80e5550644c82580c46444e0190800d0080721b00b50304000c011000340d40e20a042c0701c0d40e0340c40080045910003440b00945510300d1130030800110179030340510448170100d803140c00941c589081c050010755180704119008003643c500e108924107061055410100e10b1404101f0707269202c8040c2404062a00141c9082d01e01c20701d400000700b401e08164028107120b440b48405000e0036039070042c030b503043c0592104050f8288441005080642c401c00074561b284121045000504d03410304207801328644942d103c156009043c84041072000c80c5015500c141105a60b01c0046415018200440e029005d18074000302c1039203011400710992500468028418109510100081e5036440002c0b40d50741 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 933409631 1250 933408381 933408403
    0x412230d0b03061e19020d0525141812030307020115030b010501050c0a0b0a09050f0a170a020a0803011202130b1f0c020a061707141b01090f030302030108010e 70
    0x3600135104054500d4200d1a5141d0100c490004410300400031859a82640d220303107103e0f00a65030310410052001240003401c0c40c000c145002c803520440034410068040524a413201c030040102045c0220070548a0003164882c00d40a451428085c0560701d4407030740d03900f050303403c0b00141d400e14103001c03d6001701340590030840350807035090305580e40b90500544041e8000703800d541250242041c440e01040682d2035090081225070000118003400b03080541c105804400006180d800c800411804076680d4041d612140c0c003003280c490354808081805034038024090000070411003010000244aa4894002203880350003514603a156081c0304800008a03145e456003a58410240a030f000c004180c017485401c44540c1604040340c032408103400007400c0204c3c40e440100015540e00c0c042d0103504480f10b403550803070081d003880304030f480075029121400e00032107000d00c001840d01181248030542c02d400032450f09400c452542aa03200a044c020044e41c000d0007252443d40c2482004c1018100c00154802c484c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 933410881 1250 933409631 933409651
    0x21903050a080c070f050c010f03020c0322030c03120305060f0d200306252a080f0a0e10050a09050d170d1401050d0302060412230d0b0306 61
    0x1c1000c00c0300c107480602024100000c2e401003804194000340d5102c000c05070550003800181003c407040c000041c40c0c0b0101407000350400d4010301100c00c040e10300005680317020000807103840c125030080008603148441a4000b03840010285c1c000024402e146090042070300580e5410701c5030359214800c3c01482c00b603241045030403152018401e000f0031200010429150850140c072003042c14003600003882c0000980340e15810a44203000030b400080050303d042d50a081da41001c60451246090052200c05e81710f9030440718580701d84002c070411101c0d00845840341d46614206440b103450be54020070642c4501d6905005248158015803624020410f6400c040e1442c4c2d01c1130005401e16080c4804c01c45800030403181c1d80840c0b4000030107029001c01030000d042c0f0034180003030a15000c82c451180d40a0690003103005001110550300465808030300c403070344980c12084a0001c0403200008135100d9010b040d810700c0b00d008103500240d890480e28010704cc0d4110000050080701c00c614100740e1110000e880500386 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 933412131 1250 933410881 933410887
    0x509010510030e0f071824030b22051e0f0c040b0f04020f031b0301180507021501080a020a0801020a1e020f16090c080601080a020702120706020105040302190305 71
    0x6007403007a0000b400c10100042a00c00620002c90002d1403d00c00c0d8000d086d40480d0710308016500c152910820404100400f401030380d20409001070b41c01c1d0f54203408007400d03241020000590764101e40c4a4161030140007200707800c101c459820440c0d00c401448003400c0841701c8864160780244000a0b80e10508082140502aa10300c02c80c100401450400420340d048010f501c101c4d50107944903c09800e4000101203010f6480c0742c100792107120104130a044211000e0180010b119110420070804080c00e00c0d1280007855441c0d4000a030301e84020f110640c0ca42026040000c00d0300c801c00f060003a4601d01c2518030b41e000c0c0d48c440741242c4c240d00451881100040800b0012001d00442040c0d40c03081641034010b40703020310070000c1c10300c0c28900000ca007121502000e402c104545032491084261400181c07a1030241800d107030000901e502006403258560b50303008551801996a4851440218401b903411120b20b06c0c0d4514010340a031000b00d07426405401201e03041c0d0900380d4000403a5150552594590349 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 933413381 1250 933412131 933412159
    0x105090708160c050c0901081e0a030507020607030519030b13061d0c04181a03030703120509010605120f010e0a0b0105061b0d180503070501080f250801050a05090105 73
    0x2511207011481a540c500c05c41c50203c0e415250908000d01800c441800381c0200a407009042d4080c5417221081c40c1c0a600245003040443d51040c01e6075200c40d130480b049a65414242011100340c022103440041025007011407000d0583c05074407a45500800b50f4843d1300307070108425a1422544944140002c0403c0d081300440307040070304a551580b114140c0c483d0350030140c0324183c02100021400b0140419540c81c001d00912001d0411050300c105012001946041a41d507002000460104101101d0701d403200c0c00f08030010020f4100d80040c0001401c4200101281481150380e6628a441d01d501ca510704051a0903c241c0407070014405500310545540303a900c1c19044c04015840500344a8001c51640c000001c040018010700310500081d54480302034011284e40c110014035141d0020740700354041d5a04000e9039810401040e0b0082003021000816031b64514207031011000000f00410703d5006038050070a1070307005604107040e288166044241d09072030f0f0301031002546080c05801e0b8461400030080c6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 933414631 1250 933413381 933413387
    0xf0d29030c0d060e0609010507080609010b1209011803030212010b161401021303030c0b09010c120e0a050304180605030c1302130e010f0306050604151e05060f03010509070816 77
    0xb51000744501c800042c08481c4030030903414050155440303041030751914107101c03545502081d405c0e00000100d40d40c800701c1d4544030003081d07039204003d00d0403e0101900c0004081d50710030350000742c1740c480a44c040700800045242c000c0003544444410326109804c2e00020921450706410741c1d0b0320f013180b00c125011644030743c0ca5000c5042685046111259002c000b8844c026035402d903804002c40c4030b502c03604480d000b2840d0501c04c500000b0055419a0b141120740700419070701c64410503000c0b003031460000f0711120304850320f070a12090784000382052000040c0081e11204400c03c488801c90030000c01c000540d240c00415440300ea4801100e039001020900d500a000c1040e4014011540000c42c4a8a43c90380c41a09614800003603215500140200e2010801d10600b8028103500002c02c5404100240c01c00d0010700d1008620300450929034156094883c07400d0524405d01d0142200070901512101120118003483e03000f40600781c003c070a01000b051485014045482c000c810744840580a000145411 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 933415881 1250 933414631 933414649
    0x30c0b07142b0e24040305010203070905120105070206010b0c0f250503060f010317120405100605010309031710030807050606120303042001050f0d29030c 68
    0xc1d01c4400065407030041c00c141c1080188442c01002801c0c0707262207500e02000c281e40d41c00e06444014040740404800d0a80d0310300003244100d102c5a485520416290700716041d490240b0f4000904035031001040c00080c90700819044111641100e00800103d541031403a800d0322000d4944501503070000c001880031103a911301508100069404035140303002c48501251400c0b294245080b8007103034130003110030b10198449280000e00000d0b002000b00e800e15680c041541c0c50b0510002d00711218049084a04090807811295458819928840c1d0380c01d2a081c51600d8560205440014524201e4009155402801002c821a8258980864403941c040240c07403411001424024501c0c41001d0120004503850007508003140a01c1c014982072030124144100070000080401c07140c0c1c4180204000213030301c00c1d00008410703003004062500c168404011f0310b250082420161009030041010207444420b80d00c290300c40103a40458070001e102013a80155100075040c2240d4242d000b002400e0b0a0341040d00728 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 933417131 1250 933415881 933415883
    0x40215210414010903030f1a03210c070f0e0f070c021306051005070b0906090616020712060e0c10050706090218090307030906030c170601110f03040f0f030c0b07 71
    0x151a0032400b00309040d42110750603007080340031030303903c036580e8600140f2442500e1122001c0ca0442000e000310000003544c41402d890b05040a0224440003d8410541810f86040e00c1c6008115500c1c0740e201c03103441018105034001d0480e5101d0303010000d654008501d04541c000c0100da22590b43d6614144c0034000080b84801c10b0782d0b0b4203622540005182e403640200484410714583d1941d0300e5040524080043c03481c06000040c403030f80400180805002c000c41c140e90000c075090001400816a05416428140b80354000c0840c103000405102c01d02100b50040d564101c819429242844020402c00086c0740900c0490000188140b10000019251341c3c40344a0300e9000030003802034844904c03000285680300b150744880c0c0750004a03200042503000825840540b03c1030806000c101d00c0c90348010312460441c503080d0064a04200415400c2c0d008040c40c0400a09403000c2e10401142280000c2d031b20780c0544200440b01c65151400220050602c0c481020380c0c2c0e0081504074018507003050109207401400c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 933418381 1250 933417131 933417143
    0x10603080408161203050307110c150a0e04140601110c040f09031202041a0706090219140108061305430305041214090901030b0402152104 61
    0x10110204403020003070001801c1842c0100700034140c078039011010900540c050240400c1e07000304800040c3c1c2080549500440901d4001c0688004100c25480e04450981a50304213507440100d540b0460810300a050415541d01c440300d00c1c4121078107000445188072050305181c0c43c4100420310130341c41031011030036400b803101c00c40d601c41d80c62400060480c1e40312280d412000359076425110030550402d54401c0e14840c02c2e03008505007482c06a40c0c42c070015503c91102d20312030000a9140030410b29600c0307880b199801400c61040b92112030820f050a400d5070048001c03041c1002240035566100e103040c1c0b0b04c07a4801400b0103104040100d000302c00b620307003e070940031135009104109440700304002034050250080e140d01c1420250607413650401d08000c0c00580700700742c18541040040740c036400c2e40362225a041d00c0d00c0d00c00451503804074130a034080e0b600030560000c0e231800004180a100c0440bc2e009034000c50320415107811300400c03101988034020f5096243e0501004061103842000c0340e03070fa4058040c00c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 933419631 1250 933418381 933418391
    0x3020f0d1709031c1b020d05060a1514010527100203040906090c05310b09131401140f090127020a05090d0c03060c0f110102030f13020301 61
    0x256828540c40d1010034a80358000021402c0c0000340340c2004005000c50b0400012075024030f6600f0000c2a590300f030040c010b08a00203650407030440d200c40e140e003800203821000755000c508040c510180601b0920458243d0004051808901e150f1440c3d4110103070708050712100d00d0070016800c2070701d20040c5160a460111040c03901d078403158480d00180b6290100b950302643d0b456041c010088222909900004035003454040c00c132000d990040c0480d25590b040442c000280300395400c00e80d0000380034002c0b103803031044418000034951fa01540076041c0716008070381000d00b406210b0748604c1100c01500d00001d10700c5d10f100c010001c000c07101c0b41d18812800c010303000c1405030311280081169001d080e40710f192590b108082480070300f0a2810810300007405004194942030700e4010040407401501100c6119082c800c2c0b2500400200701106030041d64401028089004d0040000d00454110010100454403682c0720104202061084070301c02c1c00c24030000a415140c0000b44035400d070b07514108176055940d072 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 933420881 1250 933419631 933419633
    0x2070e0a0b09130605130c0b030405010b060c0a050f150f041a240a06050a110f1203040317091002030603033612100b210d091e03020f0d 60
    0x8036a5440c840c032410724060060f00200e1030190102c0b000102100410021420402c1c005921490036030304807846580e5007a03d9403550b080c014010f0609820303d80c0e011400050f200f0340d9101c04150907152601440a0311400900806400d0315001d000319401114010400003440a0450140d101e4009015070130505648108444425182c0d8055841003011402e9119900c142c000c060200303440c03440c0550720511880d25290001e0314074080e649884080c001681e80b62034000c001042500d04060840080340d1007041003400b010ba180e80251012340018030310016819000c035400510764041c11905004000700c56254441800a41014094030707410b0108002c04030000701444094142c1c4561108e82d03012500c4810590081001c544103030900940f000e42030001c2c01540402d003840454040304012500c9210b0b42c000032103540600c0810409003509503820700141000084c0c0800c0741519071500f0b5001502c03503c40d00c0d00c49201954120600040000c01e100504040c0c204c199074641c0581206485101c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 933422131 1250 933420881 933420889
    0x9012d03030c06050106050c0a110117040c090507050f04030609030c080d0c0909090f0f020102030405030d0207141f030c033908010f1a04170f0d0206060102070e0a0b 73
    0x205a000760001102c000d800340a1122a100b141c0c01403105041c61850415880d82107a161219200060800201540c0c001220707402081850a68881724045101d94a09860000c01e8000ca07402100303055842c10001800d1103005100300d828414005400d14241845c50351140060b0483c01c1045042000c05041789001513449006030450b541c0c4000c000c501d407144100700034484049a0320186d60141040880710210f1008403184c0c0449400102081c4074044d0350006070328503c03455200a0701403140c0203540010f0303640400e4440070b8130305040030401206034060400010503052142010078460036000980068080e900021090061b0301303001c11b802444c24100c0e1002c03550420414083d540ca16141c0d6004100221610080503040c18507110f903504210030051200f400d40a1403018040150111902d0b001c0b250603540103040020b017950303010a101c1c180c0c980701c2c040ba045560b06440303501d01408645001140c164460710040e4002c02c5001d1030014003030001000906100100c6a85080740941511 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 933423381 1250 933422131 933422219
    0x6050616050c12010c08090313090f02040806040b070e030a120e0d051b190b040303080714041424180d140102070213020708090622080d0207060305060901 68
    0x41e480000081c45d0900c0c20020b04514002891003c00d50002c000010f020300b2010020020b4421210000954050a80500000744543c0d0040401442010204000c00943d070900c60b2254100340c1c0c6518011401d01c0a0680c5c50081040c0140107894070206014414800d601d0f500c0030804c0189002002c00003030f1695401d03c20310000b84441513110b05046601400d1801c0c018000c0143d200c4501c0f4034a04c4c0c122607146030300840c08001e040006000200c1e0b0703014821080480d40602d120076403551a83d4035444a010085200601c900078408042000c80980014002c922000c240007400c51601c000d0741c0400c800a8924441b0542c40406041c29101003441100b22000303c000c101c00060b51000c0f1401006048100400c00300d40243c01003205400080c4218285c403400042070b96204d40381c8016030000940c10617141800b0010810b0000001003480d00000c0410b200031458080c2c07604203465280c11029900d084910b51303007001d0240010405c226407aa4045820950061076421040b0005c00c0345550342 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 933424631 1250 933423381 933423409
    0x1116081c081501030b090405011b18060e0102210304021e030a140f01050406060614040f0501050904020c1501090b0301020414130e030c010c0f08090604141606110606010306050616050c 81
    0x81c0d0744582d60b600300cad65982c16000d001d035914204004888004008103220754001d014031003c214200702d031841d05900030440005c0d51601c4550b9449000190364169055030000c43e010391046925079503031070380c00c120b0300e10b000180e81002d07024060001c00c94694000c1c00250340c291440e02e2041000c0350001c484207204185c0982d224520114200e4a0b01b200184600b0400d03c0c0741c054003104100c200041189100000200e84081c28035645a005100c00500240a815400901405210070841000b00040200c42c140e031280c0c0340c10080182010b091608030700580c014001009008003251800d860446000e0b96120200d41001c0385500b000e0031181d0640d00545943e0880c3da44174840303000710b543c0054410940f00214500341c9441d1030500912592610040d10281c50700c800c1d00180c0c0714409042c810b1407501060750a902c2c0249a4a44000380b032600010440d500038081c10780401c4856209016440031510010162410100c039001c068071001c25203082201c140c42441142c010700d072292241e2848403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 933425881 1250 933424631 933424633
    0x114010f050907050307080a020f0712080a05010b070605271b01082203030b0909030a090b0301030308041b050904080c010c03061a0a1116081c081501030b090405 71
    0x5549040038680c1200303010707004244a0607a038001c004100b0b6000f0280c0e503000f4490b15103034400380c60303100006009216003042140d00b2200001c00105004400c0ea10445003071031030380c1b000440c1d90380f0385e00681100c00a0081082480b000c10000300030404036041070b50005160880490050f15030041c0070076004003524921007540101d901010514108007004840ca44207080c43c80d2a4030b0020300030b165851a0408032604070401200e5902418030036403199040510280c43d0300d0300e80c100012000e0707594114002440000364000c101080d04991041580d040700da06403550010780e111a0340c1c05046c6441412072080120b004100000c0554442e10064000d5000311005561114070380d0209007900d160102600901d4107080c1c081012040c284e40321041003203a0124a520341d1103048049504129013840501c552081224500403041d0350b4066100700c41902040f603110103210100c51040c0c00e0148030010104003080b000458107001c1d4407600c00b818105240000d121444c0000103400403105980543e02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 933427131 1250 933425881 933425921
    0x20f040509040609140a1208150a06020f01061728052a03161401050c1e160612050c0706091208100302030a0219080712030305010f0b09150c01 63
    0xa0203150380700c58178519500c1d0058128004030f034480000c40c02c0c2e5580b0000402c020b2500185069020b8101d030118814024240c0c0b500d2555080700a40d24643c00d1402c4c566940b8000300014102001e01d152440585800c0141c030070014440c4041300c0000070100486000400401d004000590511680111508201580711900038081d42c0b40c1c0c0c40740c03885603964001e40c8000c0b26105241c0b0840e200504503168011882900d1010500403101e6010300c00d8101241d110f9802c01e01440348105c04014030505800c13048a10105c4007040740300b9420203912074040450001801c201d981c85041d008180c0c801c0703800d0700c10b5251040aa6610b412211008000d0341e52401752100009125400045c1c0d540040240c0868010a400d5400007a01c13081104002485411601c1079400c00880031b9191200506c0003d05a80885031b882c2038280d0b00700d220721030803400240b41c000040340c0c494842d14a0300640f0488008036080c9811403040c054002c10000000860345802c0c4000c0d6040c030000d02520940450120710080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 933428381 1250 933427131 933427133
    0xa09020a1211122d030a030b1014030c0c01182019050405101a040602010e0d080c0a031113050f030102040e0f13050d050c0c0919020f040509040609 65
    0xe15222020b1120710a624003845104026070000d401d20064115101e4070704820030981c0031121400c82007800d9400317070001041e065603c2e60554406041c0070b40a407401070900c0303000501162020070700d100b2108065414404034140d403010401501414001e04000242a4800351407003060110b905021541400514845400749024050820b032a0405541d10303c8043c90082d0340e03414030a424000c2901580c0e807040041d5169443c0141440102400d48076802c00c45600c0340300b569280c0c464001c000166007030030f0112a00c010002003401503110076681d607031842e407a03165002c0507591140074000109621110031161000c05580208045406d200c05080128504400d001388401c2c004038284c826403041c80704114078803502e8982ca41c843c0d00c0840c01d4205945081c14002d400159200c040c000c0d218607035402021a4003c00182a900d502074116084002034800b000106c082c11103010341071140010070410051499006004000c1c0141207485c1060340312004202c1c0f043c412242984c01c03d48580c0e080c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 933429631 1250 933428381 933428393
    0x60d0507020f1506040209190f05030d0e0f0d06333c12050102030a0e011e020a1101020d0f0c0801030309050906040207020603070201090b1008060c030a09020a12 71
    0x21502c14110301501072a40040c08940c0351100040c8214000c80d00090340d883d07607541d181c02c14240780910b440e8011115481e420750840c20009401214000c1c400c10b081404070300d00070000d04114102c01414250b6200003d001e202d9200c11068040f40c0f00d94a4824408031110b842c110340e00c10444541c1020403580d1400407049020031203620500c83d01d4620b10300f10811520005a1030400a135040c80c00d08621824131100c2543d007916071003005a580814005400c0100640040d40510b00c021400d0184807528080182210b41194070078107203010f802030030748102684e60058001c1544a040c80c1d40c51204c0613400c1c41c00d9038011640e5000d41a40c0d086820080359462064610036407162611418941c1942e401401450311800b5040c030420320200025055992501104c0740c0f141d015200c581c1707900b04060701074041c02d41210b049840e001c10000049450508500c1102200c02c580020402c40d1560b03803004c40380740e00c09400403000c1c0c0d44452562000d40c0740d0f12a80c000800f045c41c900703050040a0b090030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 933430881 1250 933429631 933429643
    0x16060219090b18150405150d1b0f12020910050c1c09090e070f0608090c010f0e06032208040806070503060f12152a071e05070302060d050702 62
    0x74100d000c018060301c140d541c40c0002400b007010b400d46001c000310584c0303000b814142c002e660086078030a190295480c41305960b00040c1c040c41000104c14450040424a2002d980382035072042000244542c503819156840303848000003155000c00c00501d030040401c0406d400f0446d20442c40040390740051250100c040c00c02000c0400d14044041500150b000032009100f214984900650203031299801074035000148030520040c940041070594650743e0f50006030111030100c944e01001c3c000c241700c13a031082d4003a013400b0820460590340c401800c0e4035072081201540010307141d00050710b004800007988038031940c0700782d144502070f0b0100c1b80c0f500d242c031422610700070b4014031030000c02c40c0070310501a07580c59452040c6103440d01201c80205006034414200c1c54035403071060011910100b070061110042c0c485c01680585175401840f8410048207114101c414400c00d02d0003041421006001c98002e80909070350004144614203480d041d036030f00e0300003448981003007144040b56940c910030f00680c680c041040f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 933432131 1250 933430881 933430889
    0x703060e130f0b0c0d060f0315110301260a0506180f0a080a030b0301060b0931020318060903030f0108060403020a060b1302040f05011b080901051606021909 69
    0x140001029a079850b1124480032000401e201c00b4040490414629401035030712441c41d886041050a5440c1c2c84c61301c00c1e10151006950801c200c0c9d00b100c001e0700f058014200e111085100342032542c0d1810202e42d20344013076604408519124a40c40c244505400d0003c000d8190040f0005d110030704210070048000280c1102500301c40d030100e40501c0240305e01040b20b007071468006d04030076103c50340314400358090a07141c4a0140c0c15481d004002c5480103d4001030444ea040694280301060540000c14500112000c90840c0861a018680220180035001150720842818480d08103508a003d21440d0240c192400025074101104010044404805140c0100195001400c480c100317500d0280d180e0b18041c2024001d25150041842e060704c0e00040c410050401c820215501ca6a8001d038000030703060b50040314000f4030080d419032a039100150318001481e8200e81c2e0185002600c100640c3d060340405501d040255100109001095481c4094184001c4030306121186040e8820020040081508 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 933433381 1250 933432131 933432151
    0x60607151d0d1710030f152016030509090103060f0c05031e07020106050d150e0106030203190221010f110c030a0309050a02060f0d1506080403081b030703060e 70
    0x1e0700c000c1e440d80710302181c0610319a100d0082d840e840703130f44c9501290310750f90704060201051039034010104070030100e000c003d460901404106000c0482c2c0d1411000d05e421078181404141807100103400005c2001d2010050f02c40c3c14a54a000143c0c0c0c046121700c0c41c264400d82d8401e5035610843c511158a0044110401c81c1e0710340702d8614a0300300f407010300c03d466030100900e541103440c0010f41c0d454001d600540c0a020024500021084a454103540c2400c0d6500385501c0d0314242a46140030100500440c02601d5008010303240d5030440543d519904204124281e0b4485c240d8450346c1c4605043d000320795401c884040010500120242070b5005032259007082500840081011421460000c402c3c0c1d2207510852a000c40e403d2541c3c1020391511400c0140030790b0000340059910403001032000245004142200180315610515181c400c3c90845882a0343c042014940003500091050003034a500a48003c0400ca1070f00480303804c900740c0c1c0c200300d850a001ca581c0b080b0501c003204680c0740440d032050044c9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 933434631 1250 933433381 933433393
    0xb190e0102040f0603020d0603020406080c030c03060403050301060c150f020c160302010905040e011d0d0f110709050711070806100909150203070c120e09071107050108060607151d 79
    0x10316091283c404a00c9041e04041e07000c0b0722442c4034010b60b00700302c2c000c2d0b80081c0b041c40a141c444130005d4545418000c01d0b80700c0e1280c000f0b050000d04004c00c0c9a4400d40c3c058450b1b030309681ca001401c0e82c540300d441c001141e1440d0750000b0859194018172903066443c210950058441300110b200600d814000309041281d54640101000141e900c00020416940152404500c0140740b00d00035004d800301c100b2000300900300040301011180c00143d56001c03000c2981d21a28900c002040c00c0c0d415080e80401c103020340d007014000344030200302c2d0341009401c11000d00c0c00e071281c030010451850506c1a15086040c07560081000d202007100c01e24141409044458410850003403150b030384440741c5203003c0c1c0f88690310750048001003055020f89031500040b604000081da26549800d401000100c008018038410111179000ca2840b130300c14142c8010020b581d00041218900300401903c85c4d0304024105907004808010040001c0d01c1040300003c0180e50074004a0350700c0f00c000020120300c040d403266041d00c0e4809 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 933435881 1250 933434631 933434639
    0x602030c060a0b060d110c06010608041e1e0c030b151c11090414071a030a0b0609030a030503010e0a110403061e02040b0307030509030309070302090a02070b190e010204 74
    0x32491680118030031100103180203e00300810350502810b8017500401b46049282c1050b00407500003448501c55640944036607a807030315002d6800311000c0d00c0140401480450440e03440403c4820b01e860f107070007107440604000301f04a24801c0f225140c4c4044500c1000540c003001003149000225400800c1034815004581102020540078010503109403184042c009021091101326021643e5004001d01000e54a10b09070410380403940d22044400c000c5d1161600000380c1060f8103501c68024030681600e00e14580340d01070f401018003c0070752180e51299003048a044290f034100601d4000a22a80b1910f0300e0b03600d0700010b107440e008000c0040d030b41c460505035045403002c6160201e505880e801540021550b0141581c801c2100700c01290100e858400280802e00d400c00070050351041c0c441ea81c3c240225030303a0910054413808150b80750011079001c408240014541000c82aa104140032001403c052480e01e60b4082d800c420354110548503090880c110510840740940c80c80101000025440d152038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 933437131 1250 933435881 933435883
    0x3070504020a030b1908030a180f0605130909030543290f0a02070215300106120f0612050706080c250f0c090b0f060307110708070e040c0602030c 64
    0x41c0030602c41001040d00083d40d00b0355009c403101018000041d14144001d494020250040c1d000b9181603081503811a00042c1703a09890280300c69041e850756445003410640b035103200240740f2a100c40c0c4140f548603000d20ba481c0585261400707454040c41d140c10080c1500e4103040c060703c0e11a0306801c1845001d070480761001000000229040403000407141c599948900f10381009020710031000350701c10140c00d0b420074141e10080107844044041003000414520041e1401d0441000740e01050071520580b0040050502801100d840c180032044003051040200c001c1c0320480305680c1014007600002c10410040c01403c000240c05400c0a003050081d038145540480e1150144c41a450020982d00480c0f1440081c00c002404074070b944030190800000f003c0c80c0801180340c0341e004050701c0350700c3e000d0340c03011078509414030078018075002c1d00c05440c40c0c41ea80000c86030380252004203031061040d40c1300002c9180c410031100d03000f041d1070204044542003a20341107810301e003568403020442d4000d0004404c1414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 933438381 1250 933437131 933437137
    0xa0c09140d031115010f050603040314090307090609090c15050d0b060c0f0c09090c010c080f040512010b030d0903050c09060a0f140a0509040503030403050903070504020a030b190803 80
    0x2204031000282900e45103070482e01068403c112012502a80280c5003203400c11075040c034140c5101b800c9105210f0303202c0301403142c01c2c00101c43c0640010301f01c03003000500c11150b43c0200701604010b4251100951a1500780d000d07101141c1c4110003041d658844281402840c24030310021f0041030003075114002d00c840c0010194003c840c4603807009551010003000d81e03610003007103c82464800e41078810015030516100c0e1580386080c10280105e40006c0014a40c10000c6142400ca0b0416107400940750340c545c031240d802d41c21070001c1c1101211704010106090760745d010200b800c0764150340040303600d04095090600f401c074401080300c00d01c00c41000910004001080300714540100381c40f495400c0d515100010b440000075405035102541c41d00d00465031809402e0406141d000c00d4641d104841d0b40c1e58248141000126000351030341d0030130310120780003a21850003041905030040c2210030450b00c410004040360300115501000c295107240384841420081c0702c0e0b203454080d51040c03221003841d1801164481c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 933439631 1250 933438381 933438419
    0x12020904060f0212131103060c0703211d010b04090818010315080d080105060c0316030c02060d060302011e050f07020102070306090b0405120f09101b08030a0c09 71
    0x2916080d0400b040021981a1070b513501c00020411242d0400409000241c4201103080e02c0220091815190718100081c1103409100c444034101e15058190f241202d101540ea48800011112010600310340103a40c010102c0c003104849050500da5071903600182155a01c0404900232802c012025000c10f41c0c460a0301e42e6a030b0760381d0000d441d00d485140120010014015a45505601c002011501c6040050301c0340c84461a9154404d01e42d881c0c40400c0002d004031541020258410002400c078124900344801d6160320a003004034401c91141c0c00a00300c0c0c4c000ca6084104e166403a4410010b41d030317101501c0803040c03044104c03880d8002c894182c01840d510502d030120304626000100c140459100b000540011074220800300007814051800004400099905407020310640c2001d0003030340c905404442c0c4002e90b000080d480d05000c00144035050b01a101600e0911800c2c0c5042050a0000204500c81a110b540c400d0381c0e030b01c2c0c030091250485281c0f202640400c401001d0511000414200404800b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 933440881 1250 933439631 933439643
    0x302070303110a0c290705061614041e172817071a070c150603120306060201061205030d050c040f030b0a06051008130305091210050112020904 63
    0x1c106642e0072403401c020804018035000c0840e1000550a80b011070b990090b40071034840707140340c101d1900340c005035000d148009483c50f00128040b4103886604c01207400c080303403c0c4c10b003046881d0010407110601e4005a002504070f519800c0226441003103d0000e102804542c0c1c0702100303101140c4032081d56104441c05070140e25985014203400d50103c00348420743c10f40e220745070041003031202c2000032403030f00244001c44880c000c40300b183d091042804c000034860003282c0d40d400040b00b0191034030842c100b188410341c1070940c1e83d81d070040302060080900d054172a100341c0340411080d24080c4020f0844d1a5640040e400134140701c40440024004811180b0144c200c8001146646440390200c031503200d07940c40b982d40590040400030030801c1055105100c0c0c8036030582005025074920500100b512090f00001c000751781c6d2800144580071100d8200303d0140246001c6061580000102d035401801c40c0e10268aa1300080400c41019183d0180c1405030950420001841d185540811244074018000500d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 933442131 1250 933440881 933440897
    0xb0904030801050a2c1005030a0302010e190f15021201030302061b04140402130f15030510030b04140c15091201200c03090a030b0402031011030601050d0e0307051c0207030302070303 80
    0x401c0306d4480e00c400f400c4018141c500c2d203900b91401a000b4000c10060b04054002c1e107408280da21284145003d07199006080e0004040c859030b1204180107008000d201e00543c240601e140c2114501d4205018512a400400c100c2c00e02074a80500415004052000c0d1a402c1000380200c01a07040301031542c010945001d40c0790301c81f200741d00c040c43ca2550080041615103980000d240f00c80700c0303203810301c0b0511764808000c2a02c8a104600d44d14140e030001405074110300c0d001c140044d80c84070440d921003003007905640468031880300082c002d011600034207420f1000800c01c0d2100340760041d070b50825445000c3c000c129070400f9403c1d402086081110030380c0c000c030300800c801c01452014401c1b075a204000914000960b6100e01d4024000c100c103031400d900920450806521040320b502c134441d0004010500c0da400d699403030740112003561111145400061321074203046103054041010b0003286100300082e290320200700c0f0a00c490106140700c1e510440d4031a220400100e034001c24010305403901442c10600c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 933443381 1250 933442131 933442141
    0x316200d11030c06040606050910030305030c09120d090602010c0503040f17040b1c140402031b06040e0108030903010b0a1d0a060e18010e030901080a0209040b0904030801050a2c 78
    0xc02c0d4024012004003c0c084c950401080001d607a00500966008031030810654a503409150304c00040c0b4040100030640410100b0324140745140038051094006101107003035134080a1041c10443c1045804e800b00f041004107009840e02801424841000340c80c140c0d083d450151901c6000ca00d50b20301c0500019032191010008010601c112409405071900855442007410701608440c85c401030888201032515040d900b0600c81c05149600507a0020000e2034058800c9001c14848041c0da40016802032007000001900c1851014080c024803988024544500303e590a00d0b00b5501d0f60320040d0b1190840a406000c3d5202c4404401c50056004498060355904c0307845941c014980341c1c11560340310408408102d140800356a030080490000f00080c890a1101050790f0703680e0103003e1441380890b1010740050801803e503809030a140f04002d20204841b04554042696820251002c0d00003030f8041300140f202d4107110b8015001060304016820404500000c04409120041c15500250b501800417403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 933444631 1250 933443381 933443383
    0x2030a09050a0507060e01080708070f020c03070f05040b12060103080904060e160906050a0905010c0c0b0f03180703030e0609041b1d0409050705150f0316200d11 71
    0x41155000301103819805850800035590f500324441e05e000203040c160a0120341d485654554011441521044043d8032008001d5400403030300d1440070b046209460112059980410070f00000384003403001400c20500300024002a50701402503a0300854607950502c0c0701d00c80006020341160f4001180340d0f2100307001c100050103000d80e548070b110401601401d03c51141d211024200503507a40d510350540c0c00303550322016983d6000c0c4c48408800b10340d828a041007a035000e8403864503030302d21821400c6030f540d4560b0440075040d0040035054250000c08030030000c004009030488110701380c0300d01c01840d64900d5560010440302e03208007a00c0c001c0300042000d0685171225041516042200d041c681182825150000c000d054081d00139581a030812110555900703043c8215841150000090142d581c03c002c10310030400721844011104490030051100040b8006000e907000381e02d200529440c039004490000c144250b040c1c41c907800c100142d07100f20400c044c00100100d00301c40724141031001c207400e41241 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 933445881 1250 933444631 933444641
    0xc01080112060e07060504051e01091203200618160909081c0c0e0d083a0603060b04180b1302090405010e010c08040c06140d0c030c020120030a02030a 66
    0x240c040b403150030800f0541710f0b0050058420f5403000d43d002c20000b10240103440080c2851810940800d80c8881c2c18860381400c1544820b445001b070034441d0351003600400e51110102c0032940842240c0080c810f0020340e910b0032441460194000300141242141c11514800c4004140704400c00190b031000e40c1e1040104250a80e9603940c07540b00411440c02c800c43e4004003400c00001614002a50304485107064a401100c0912054010780c0c440d0404003020800d1640c0783d40351488079498545501c09201004900c7c01c5c03542c1c80400c043d00410814038503d0080255103180921922030781c2000c59000318500403030504030000c0d40114280306507440e03240fa0a4804030b00ca050294000400d003003000103210054200f4408070002c04001c2200d15201c03030049900703201c00e4500801550405004000c49407107101030305070314224140307a145040c0c0c8440380c510440c2d03142034000c0c0229490b460300f03289c20354080c0710f200080591103980600d00654a059038001d4031004001d01d03400c81c0d020001c65000803c035441 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 933447131 1250 933445881 933445901
    0x709020a03142a0f0d090f0209040c090501090606081311190f06090509070309050114250306050a060521180c060f070b060d02130b030f0c0108011206 66
    0x15560407814044248210000709201c01c490400d540c0e43c05403d00e003040000c55030102c43c1c102009060021700900c11000d00400242a600744076400440e00150f40c4400b819801207224240341d0421911304160a820ba44050307028050b8585080750400141c0e8101d044a40d000341e4403001c10002c4c000c1c5142c03205121040400c500d820001020200ca180700095206600f551560074103181420340d5844211180c14590080c00d030084c0364140860b0a440c0290083c0300424416400880c99050a40c4450200c450480b0990001c00304a03078260300421007591801040485854184212800e00b000314a00c0d140d14440c980070010000750110703c9046601c4001c10384010b600502d4100d003460380103844407006000298406e4004e14820004a160408c04c60b00341d4031003601c0d41e80c103014190325002c10704a4020700c03039078121803501d100703c00590f03901840e02503451620600261608011003030500e0310003d40c103451015400034424652a03038101402d28115500500300001265691501e0406064a034034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 933448381 1250 933447131 933447161
    0xa14070f0209360f03160206030a09060c170a0506010206062715100905010e150d09060f0c11300d02030402010e010e0a0e0601050c03071b05030601080709020a03 71
    0x340700c1200c100720a450245010543d0445000e410a0f0b86016203e00c6010002030200307651024042c01400d045014690280c551200060b111509840d0142503d402030300c5000082c0e00c00d202030303045a9107031a6a1350001e0f944001013000d03140200020b941d80b400600043c1c071032010f0002820302200309102c0001142d2020601c000d49041021b005101e58080c0301c030702c503c5a0b08000f0849c0c6454401e00501c021500160750b02108031039001d00380a50302c07111a211526003002001001c0c04000b041c043c0344803051191600240c0c00b013085803881e0449035407592540402880c2d908002c00e074403000030b503145641f10341d0850b20008490420401c4110b1000c05032001051008600d01c0e41c2c19943c0e50103144110f0003038075513428801164004440b41009459142d622440342e000c02c1c414412000d85050340b0403418188113207011411340805195800800c000c81d02403c10840701d9050312048003514000388401c1d4024003007035061117500c5031201c60724012a10819401700b00f1180303140c440c2d04142c2c206d001000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 933449631 1250 933448381 933448441
    0x200a150221010e0c1206010e041b0c05010605040c02030912070e0103060501140603160c02010201021c0905010614010f031107020a0e0f060a06020a110d0c06050a14070f0209 76
    0x11407800400c0c0403d00c105144101c54500049001c0e80d41000c840c3c0c0003801c4520110181c2c0d88070015965850708100c001e070810b503122081740c00084400b1403000700341241e4a55080c1001640303003043c00c0d0780c0c1d1a0000c50155080220740004680c00000b41c8020141c101d60b0804101e00400241e0f160605a42c0300a100805000000085c042c05a00c00c0741a0340042c1400b160040007081403205500c1309881e000e64403000e070080b41d060349114482c0c00c2c40b260320504c0054644278006000a464007005480070038550380d42c0b004041041424441c0c1d200900c03012840c1094400d2460010b440300480844c1107061588880005111104040840c0da41642c010b105914440c3c8800080025117400c5440001c824015400302e4814a00051044200d420980c0200170755102992200030710383d003400d142c54001c000c0c0d4114600090000c250880074140c20340d59140c1301c50404d000203051010750151101e40d82402c0000b00c021900d501002120f071038059074221001e48071840c81e061002400349140c0306d840160 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 933450881 1250 933449631 933449677
    0x714030a050324010e1e04020f04061209170705071805040204051f15030603140a0308251d03010504031d2209021309060b01200a1502 59
    0x700145024030245040b20045560b02200c02070303000040c00d4014080343d00c80700c2026a51508550045040c45101101e50020a8600102d03080c0e8202d131982c1150140080b8007030107299400707240c04483c11641d036000d2085240c107840e03503035034004900005140000c0002d030310814080104450f900420440e000820305910100b248401440190717000ca100701c2c14000811682c0e401006100041040c0c10f601c0c4008a1801003440116401141c1400500d030721144000082074000007202c03210305504c0d0251804909600e402000440c000303181103001290144049240507510f00c014130744100e5824010718441140c0700141d000200e107003480ba0b05600301010001003503409080440700300c0c0c805031901d083c06a2711080011110707404413841c222121a140c50517090703560341c00000c0032a001030400e03c24505040410300540f0400c000c1174a0b0a500d0f076030307032000030350380300600e0720b50b01c2d0000c107291001c6800342e00c41981743c1d4600301d0082e0103809120310010200d4401d504440400541d140c0050f803160704 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 933452131 1250 933450881 933450887
    0x1f080a030305060f060705122d13060c1a10171e0a03080609130506070809061b1801140a031d01052205010f0614030f0f0c060714030a 59
    0x204440b01c0d4040c0c5100d080d0701c04d030b500b403800070b840041da400000380c0300003440040c4d0121540c1180b000515148489104806941c0304d50580c03c01201003184102e50340c4400d5010b1160b004c00c00d5000c3e00030000c054245002044d0308450b00039441c50701c24403011a58481c40c01248040c4070031341200c51404140114144400d50005640740b002540600e0000d003280c44001f030365141e4410190180c0401c0120780020341a25100d41c000f0307840000c00009201051180e1078061400ba01110108041081d14060250741a010000c0c642e00038070700c42800c000700811507000541c500800b440800100042c40100c8443e85c058aa45243c0702001c03d1003a48940800720010b000d0000c2007680c0e1034000c01000051450441800342901c80c1e83e030400c032544406400c07640130721044001441914955611241044111058080c81000b4a0510390304c5144800c960101800e00550050240e043e40c40004ca00341401c40c04034505604800c00c0307034055100c8105092265039030440250010017800000340c4c420103960 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 933453237 1106 933452131 933452141
    0xb0c060114130f18050607030501050316030b0702100f020d050c0705030415050c03030a09050c18010b070609020d0f0318050901090504031e0806031002030f1f080a0303 74
    0x30310083d0204c10003640d05030840d419084a0144000907605000301800341038201c01618120410740d1107075020a03190f00c802800039002c81e0000d41418000e01280302c1d00c20300c1500a10003c0408000310009601ca454450000380c034240110306200120301c00d031a119540170001350b14007800d03d456501c00c20445410300040141c02c00801c110701205002950003800b0700200411a1107840c0351003400e02e0300c2001018041d50040801c2c80004d000d901040d0704407400c1d5145180c1d075261300e04012001c2c10307800074065000400c42d05180c0030404001819440c6502070340c1c681070001c03110410300c0c4210340e45100c0c999100c01c1d03d400502106285500c0141c03ca8402d09081100c40443c031200c80c00e41d14001f40c2100410078a20811540742014813044020b03418189003103203180340c440a44045010041c200540307109045d400e24250101180214001c1c0c40320380201c3e1140811481d0040c0980 = true := by decide +kernel

theorem cover : BRFrame.Cov 933273381 933453237 := by
  have h0 := BRFrame.cov_init 933273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 933273381 ≤ n) (h2 : n < 933453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
