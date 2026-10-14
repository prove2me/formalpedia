-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0451
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:52:54.661611+00:00
-- url     : https://prove2.me/submissions/6b87f498-49e8-4bb0-97c6-f2c3cf56099b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 80935253 ≤ n < 81115109 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 80936503 1250 80935253 80935273
    0x70513030b010f0b041a030a020702100e01030509190615050405041203050c12131a1f0f0e0c130b0307030501060f020609070504090602070c030609051c0c0f0f02030a06060503 77
    0xb070300701d201790700420600049000e10340c44691181401144c0c0085c0650780581456256408110030829036a03800d0007141d40d54040d00007035641449034139446802d0304001c00758030031031501100c0400031001300906001d03102e507041c408115111000e10002c00020b0420003507441e02d030402c40c0300800042e80c1100004e0600d008658404000016034000368100516103185849054072a0072042e40c01004840c000c05007400e8a0360409030b003050754842e10b41c01500220094007548032510000f495040443c0c44030440105014903285103444592107400d0f0101c00c2c3c0d4654000e2080d503a0780019030f20280e24001c001040060701e81d49908114106c0d9190b484481203212141c6041e40c4030801200e600c1c600c1e030300c0300c40704104038070b0190080f040a50081d140146441800e4540c1003034201103400036103405072901d903000c0810000f003100f94409401c084800b0103110000000900c150304205d0080c0200796806140c0c02071003030140142804903802412160540100d140c0b410141510f0303c1640e100380a4004e02c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 80937753 1250 80936503 80936519
    0x91203050115210509030309070902270a0e150405090105130303020a0e12010e0f190807020a0801020a03090201030c021207060507030b030a0605090106121a070513030b010f 76
    0x868141c90003100c41e03003030000304008119804108802481c03811003d4201d40400030840784200c90040c52108040d5603a80380c010321700c901e80800780d030087d103001e481001228a580002c1444403500080c3d00c4191982443e55800112a403115401c030b40700228100042c0300000204d504002c001200070b98090015603900d00c0d03542e00b00c62049a4050044903010700c1c080000b4800d900401c600c1d9824248134000c0c1c0c8103500891040d48040c0b080e41043d079905c134412034280b8400c104480004040900070301e904c0c0b141d50802011203612150003001c5042c0032407000d0440d91000c08110160040400071034842100d89001009005118000e90109240c9190501c5191002c078075649134001d07038103903c1e2030628a070303032040000c0100500420403d540e403004544d142ea001d00c0084052070150360003040a0030281c11050031100d01d94007030600380006070301d000006040b040754544c4108440b8048c220555562400b034640b4810f21581341e07a40c444680700070040000861a20781071b03c006459004140b074590140c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 80939003 1250 80937753 80937761
    0x50a050606030f0603030409090507240c110f060f09040c03020a0c0f0f050a0302060414060411010807090506040f0e01050621150618040e010911010e01030b0604060201091203 77
    0x11080c1c000008000140c03225002c41095504128050112481c1c1561501494102c8100d07800441c0c25070040d040c1000368440c807580028102d0f84090050341d00c001c0003480500003407c00000141052101040559a0b075a910540c5640f44005005503903103480303601d01d00380700740d000059043c42145811001d11101c1d03c07a1003a10810466034841004100d42a00c5a4950614681c02210748c80018840880051800e00c040c02c50789210340c00900e12402c05280c41903214140c00d00400380c6a01c1401008003040d02d495420311024828204410b5540f8ad011088030003204c6900601d8201c1d000240001e40510008204005c4490071180c01907540d0700d4004003c81d81c8604d54200010300800008404113120005400b60000001229010b904200c500424030b00d0b0040303002c5000c40c0443e206422184c0c1007074000c249541104600130405811030f075076032401e450403c428207810085161202c17903440c3d0003076000113010318008001c6a211651030318024040c11071a002101e443e095403040c2d065113802405 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 80940253 1250 80939003 80939011
    0x9020408160503061b070f141b010504060507110d0507090b0a0b0712090815040b06010c030804061509060f03031407050a060f1e0b091e060603070509130f050a05 71
    0x701920390340d100c80c803a00c044018006010030b0251304c1042081c00003480c1407c010100d500c6035440781d04150140741180c1c1800f503103210808021042c04001c04040ea8440c080f03c1c00da40790380c104680c80e130301e0904080141103c1802c051b5040140ca008400a10000080180c100c03003143e1410b120800c9488280a1440c4440c85881540e40081c0101030001c2d960360302c241c0a2031101e00e03210b03211f0342d40c550740503203000340b00c00b030f0105400032030070500c010720460182c021790156080c02c00052200d0256401001104000c10240a82d540c03039107100c1045c003402c002030b00142a6a0303801cbc041245c549029a080000d6840110081461480e030051002100e9040d110143c1c3c1000c003400400304652280000390800241b0021150780d00c0317103000041002030441071440d11503140c00184803400138051240103800500030b000546190201c1640d01106062247c0d8000020786146132039032241042614180160001075510412110f100682021503a0000c0d00c101400702c3c0c24805512213a01c84421504196 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 80941503 1250 80940253 80940259
    0x40b060a170c04020f090307090f14040302030703030504031e02030c0613020612042f100206060a030615030f03020f010c03140f10090606200d0207030f05011104090204081605 77
    0x3458581c0342e45440e902424804402e0382c00303a45000ca9100010707042685c1031300000c840c00c0e070320740780c0240508103031041e421200310f50384041c04941015203002c0d54034069810000c0c00c2548030070007d000c05101d0ba8901240c8030f000040450143c0f0080d60180d226041424138041d41e105040024010b8150011588811500035044038904410542d40700c5030810000c2c010b40701d07110784009011a41c440026090a00030380011021040780e001c9007080403032040c1000820455100ca4144905c40e907485600c0021a80c0c0a100010a007151141b41c032100e000640c400b41510000ba4110030600d50041035100d82c103414900200000d881e20303d410b80c104c90b0141d14440714031004000003210b55803c20740c0180c1011900c658420340c0c85d90352030713410152031582d0080300001d1105408610f00d65102280200c1008a41010b040141d191440080d83c890382c51002800104041810001380322003913000e40502d1a504050b6952261142c01a070040c0d0b02510501c181e0380309411085560001900d00e03041914001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 80942753 1250 80941503 80941513
    0x14090d0807051e0304080c010b0d080405120c0603090102030106090e0405070b0c0c0307061d0607051504170a08100e15060a02331305060615040905040b060a17 70
    0x244401c40301c0780c10840500d041d140f940040c01d1118a10f860203948a6131050002e070f5a01c0d00c9000c860f5094440c2003254038000d131612500100040c10101c00d850a680c0d05640301c600c0b40340d19045c164908272144800c80d400c40000810720a01e844190002c6041e25420f40701c041c01295135091181c181030341128060696000006e05006e08403034500103006a410f5003003101c82e224801c0d0000780c105041e542c40040810422400d110451002c9103600c2c140900848070b40307041241c0c0c0d4803060384071035031401d141c102d2290007030000d410002000680d10100c0c03c1180c1264548010a002804d407401c00e882e690040340300640001890b80d0302002441c415850924240c40c403000103030911020307800035082c000550041c00d6110107140d82c1c1c0c1d50700c180e1030071041350110092482031100e1000444098224100c01403013424480100d100040c0071034110324140c4800341f1900e0724004510f91401950464615a03003000148000e10000750340e044d009400407039600400c1a40d850800154554070394980b0226048 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 80944003 1250 80942753 80942761
    0xf06040302030d0c1422080c2202160506010e1501050706110f07030302030a050a0c021c120905030a03050601020304080706080c0409051602120a08060f03120d14090d08 74
    0x56402400e044401401c0c4441c2940942e02e888882d50800d10700d02d07003035a80d5030032070301b40c04000714004200030841e001c09800e105000324081000e100494800000780305c902805c107454a00c1c0c035411181914130703d1030406c00c0c0c05164075019071500800e203c7e0701c00352218200400c0c2d40b103c00c07925034940000140c4901e842c0c0b401d90340d03a0101400c040d04082c5194201400850341c4c07000c4074402804c285110f80d800603540d11b40098904100c81c00500600c0f0311626180ca03820607150009103140c024550311045010045c0f0100742240e050304180e800c6021241060b007000c0c10481d0001c054a00c1202c42d031800d110a80e54100120b1390f0313004500c00c90b8850f41c070013441042200d001340600703074012002c6001186090f4850754500c090f03c0d016584044480f100500100107154144244041105800759040c940003038243c00910301035002e05018400e02c032121581d400e032394081041031005580309500545441140b100c2c103004094080c5a0034003100c044000a00d61440801c600c0d524a9203501c4400c5603482d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 80945253 1250 80944003 80944027
    0x40b09040209100306020f120108030901080103080c0106080706090801140609060d020d140c0306010e0114040b0315070207090b06090a090507111501050a0b0a020a020103020c010b06030114030f0604030203 90
    0x200243c182d0859400145002c4040780441c00100340f80403d40e881c0070303950020f112481f2080c00e8140d00096076600213202c141000c1e039000e504281186c2e0003810403519608010000ca0040c01103510584a6119038800020580d421004000443d5101c000800a0144006680701a803004859003036001030140d0001e400d900c1d1006808001a0010b04007a00c914403c0c1c2d50400200c10508003016554004010620b02d454100304c1c050242214401d084070715450105003114508030303002d455204540f510141c00303aa4800304a11789041d0ba07901a80605401e00c404040d4644c01c20f40240c0105504200d6819100d08044049442002c0040e0000c0b2a107454071101c800148030191604003004103043d14195600010170882400401c2030030a28425403400f81080101d803131135070103440e1061051082200c140d4020502900d41502828050383da0050320150600400f42c98480640c0240301200115000590300d0300600c50340310503003c590b40075054405071590741e00c0231a00180140e00030000c08580700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 80946503 1250 80945253 80945269
    0x20903070918080403050c09060d210c080a18090603050705130204050a15080a050115270603090c06030603050303040f02060f0c03070501060f0503031b030405030d020714040b090402 80
    0xd0400d80701c44950004990301d94955034400e50061b201c55110f4103c080340c0f403400c11300a5800103021280c0840c41922a0381c3e044000700200d0300c00280c442003002a04213580070b031219651650780404116a2070009030b4000d800f03c02d44c270781c0004141c0d01000011030901100d11980040e01c3e005401460851b20345003c10038164022140450802d809000c0000c40c1e482e07a6009101501d03000d080320783e100e040c80c0001031810b003004010410041c01d02d0b0040000800c4c105001903c108a460318000000c0740b048264080d00341c21030f0100684214242c0001c400740c1c1a0311111b921442010b0310b040059840d081242941c101d400040c10300c3c2c200700003113400144164002c00c0300c14406400c9a00742440440b00052035081459406a550000030300c2904120080c03150740701038250501c0f1010010704003008a40d0324042c914484145201054801207510810010381e0000c000090840e0122206480000e45554140c404c003100341e041c0c100900d10903d07040c003c1c1d08101300003400140e101d581c2c540030400301c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 80947753 1250 80946503 80946521
    0x90c040b091201060303050703030b040b0f0d140303070e090f16050703020f03070f06180312020c03090312120709061b0f0204090605090c03060c0d0e1609060e0108010209030709 78
    0x101e404044890b402c410b0070700039000110701075100e0540302c0c3d0284c100541540c0b02d42e800141710700e14110300d01085640c1c1085020344c61030166a0619051098a454565904034180c100006c0c070010081280311130780310308910230310042590201419111108100300001054a030b290034094030001e6014071510a80181404038043d204171030607064041911b0381982d00084003900d001d1030710180036040c4815805035408280c42c034000b884488031030381c400031300b008840343c500d881d81a00001c00c4520150200295044880001e0556110420f03002c0c81e03881030384c40800751050b80c095500004107124040d014070002ca41c0c2540b504500c4071090141c51581c0c1545240468030344001c83c2c032040c09601c4134415448200c1c481d00c000500340c1000e04490b4038111507003042521032b0b4031401c20401205e9484050f6104001c80c52004100a04041c03645424518940b299600c240b0f04080009907440d5107400c88400c89807000002c01240e62500c050500781d102e400071050305030b44142c42c200480480d41d4401880 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 80949003 1250 80947753 80947759
    0x20f042403050c0406081c050913051303080705040e1b040902030f0108010b0d0f0209090a02030a060b0f0a05090609090f010603030c0b010b0306011d0a0509190506090c040b09 77
    0x400510101040c0d4064a1904241e802d43d0100b18508250704161060728080c1c0110340092000c0c691000310030303001d444581502c0c400c0100c04104a41c142c0c44100000e41540004402400300f45040490041d4524030424158009070300310300815819800f039001c480a0b540300c50910800c2d50382c0c400140e00726141d09035041c1400e1800b000000b03060085440590b014000c40507420003907500d4903514a095a1046803010f00c1000346040c0b55001070996201802100c1e415aa9189196102044030f42000765903035029426000302c0d50403004011b41c650002c40340b104100c40d1041d0303400410042c03054040361802901d07000b29014012405610b011105503030300000240444115200e80da5a450075074000d1b03401240480c451a00505c10800070291039405040d001c0c00701400e45c544080002c00f940103803580134082c1001840940000d88541c001240500b6000c0d00d0b03002941400703a01302c0e81ca0006031303801039000c40c54403020942500c0c2c0100c4080c094011105418146030404182213196030280d070720258 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 80950253 1250 80949003 80949041
    0x10801032d02060414090601030213090509161d0901050106050706020919080c09010e150118050411120f010503031b0a0507080d0210020a1209030507140615030a020f04 74
    0x2005a60b0f000050010300700c041a5035011480341d40c140084094041c203164103040c014008a205507a09844c59000ca51400c00d002c0b65a40760101507074282031942842c0c55480b29030240104240140040142ea8418103103401c3c04242c1d941c0445c5801c0311070038014140021000c12142002ca003450300505002c0000800c1c180c0c4186402e01400c0e4203010300c0e800354616030801c01540005217032440150740145060a003510b1230b443c01c00d00450400041e00105418000705030550460700111015042c05408098001c000c03a541095080e209030b00640386000385140c0b410001000d1140c1044c1d80b42c1250400341c0290b0400c12070803500c40c5502484103c0f44040d101c3d004001c03000c9901001190010000c08000d00521062020004c0c01e01c10003040d40381c141070040080000c41940b014030042c2420700d240d40003403e089203240449141c03144500150404900c5582000f08820220325103024482020401d40e0034103049050645500031210081e50000342080c0304891414541c001c00c42c030845c1e0014101c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 80951503 1250 80950253 80950343
    0x309020616060501081504110607080706050c07021002011e050a0b040f02091002280327061d0906060309010b0d030203040501020d05040e2710020d0b01080103 70
    0x100080d10307100e0949000ba240d100402c9070340c0090005460008549081070200d1405407a01206a0851402c00340182e0700021400c003030020503421f03518030310343c4103c061250342000e07040c074161034204800070f9214220300d501c40c1020b40c0c0144181040c944e00c441007204c0ca401218944001000018000076007103484005040c1c143d40d0314071500700d502e130200c400140c8a6100ca07082c85001c40c110080803003550f12039806160849100c42c00161804017640f801c20301100e0616040760740264000c1c50605c1c188510500048109203100b0040c1516183c2c0c0d204078040c01c00c45020354213404c400007111341009510700812400d003450707801158070501d000004943c6903141e01c0800e1075003550f01c40980c011380010500780150342e41401640110039491070b0060078030b410016460a850b10150006240030034001c94080355a400b00e00b0010030360294016110306c400116140c030040d5010485000c486d51410740c00707030050360080c0c0c0301505a9411100b002d1051800d5450101802c840c13514540701c003c1010411 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 80952753 1250 80951503 80951527
    0x61e03030c01020409061202061e13030803040b0a020313081b07030b1605040e1906050603010b07050f03030403170c040306050406021206030615010e060d0603061d160603090206 78
    0x10400e01c0c04441c0016075070707880e01c032a1404540c119000906071440c14201d0b1009680c50300d058940309081040090461101008100044c0c800d1070b141030361401c9644400400e01021502640c4a81c1c003071a0201c3e21540c07200340c0ca10891208032850008220341211a80105005501820000101d03c801d81c0300d81d40224503042c0340610b035900403548009a28100310044880d003d8400401085041c6030b4141810081b280703a0382c00c80100441d203108480020200048103d80040d80104805040c42d682ca5031620b20381841a40306000681c0c142c071400d1102c1e141c01c0e60000403213100719016500c410490b40854500c140c3c0c40303c05000b01ca1081c40600010001c501644203883c012031150400581d10480c940e003d180e128001000c0501c203130804401c000c0c44c2d08021284001100d42442e020030b41d9849075000802e90302803000b40c0c1040503d0700710080208140c0740c2c052a4944800100b0f80c000c0710011403520340e210404030854aa03900090401c2029070f000303070880400203100425080c00c0c09003103054 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 80954003 1250 80952753 80952757
    0x1e050a0b010e090d0305040203030d0207080d0e010b190b1209030408030a0504030b06031b0906010c150608061b0418061508010f120b0c03270a0203070b0301060206061e0303 76
    0x2050702e12a0b140c1d400d20050040401c00c01d00124010304050203580361580004c2d03206c2c000c0c1400c0d100060303000203100c03007085100c004072203450610000400800b007107100014001c2404c0034603140254580d851002c4020503a146480443c0d0000704450b2502e60f000107803d1203543d01409000c0d40d44414040440c20030300900203004034260f280e851984507886c500b080458404040e142900035045038081d807046c6008821640d0003c0025501100076440d12801254900034040d0080c003450382c03100c1d000344845219003050302254004402c40d411501d80070f16190740d41c2403988041d01d03c420100700420542007900340c1000030f107060b0340001076801c0da1001c4021031205120300c18000a040711005000396210800004040c1c40340300050b41c00b0112a0740c40b00142100502408044440032000421a2100b10740ca808801c1c00d6480c484198503038903101543d03442440d1412446030184500101d1480d0122040d070b41210300581c002c010a8540d40c05001c660002d0b05940120150b640d0380e00c411941301000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 80955253 1250 80954003 80954009
    0x909030a0909020903100b0f030703030305100b0a0503040b06010207150c050f0105060a0306020c0c04111306020d090303030e0a02270c0f0403081612050901020c030a1e050a0b01 78
    0x40519514991903500401d040c8690700034121107481404164065140014500445666650002050300c0030000040c14101000040ca03458490541c001c4201a4140c02190048a200030315000650300e4000d0040540107a87c05040021014800100406c2c417941c03105800c04018015103043c1600c624482b907281440b4020100441c0401d940c0d40100700c0100400282011200002c1245040420000e10030401c60300c8090415038002c144907003d0a001e00400d040d40000500421001000e01e09440301600074011a810f403885401002601e030b40045440d60600b41d00c0d9070707031610303450a550b070540c01000e101e2415080341c40341044140060300c0310f61045406622031051040382c4030255010012000d0006c080e400f02582c1400818841003030101640d003603d40c0030043c503031150141324041ca190014640045c2021364000321a000503a0010000c2410381c01c203900703031030312580110285941c900341e4540081885180a03941304001110603040f03040c151180058a12511380e070385502000540030f070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 80956503 1250 80955253 80955271
    0x22060303050315090c040504090303060b2a0a1a070e0301110408010b0604080607111f02120c03240103020d020c0601062007140a03061b030609020f0409020901020c09 73
    0x10522079005140783ca1022962400c40c0c0d13a0241e07103040105110fa40c041d61180c6030103035072202c0c1d00004243c06600032902421a0443c1c980c0c5a01008807a0484c0d00300001000c9003034180c443d45100040e5020402800e010b81210b20340001564500428011000c000c0810081010f042210412540e003030040041c00d56404040681300ca040841c4542150f900640c00c91003000108401c01110401060040d40207102e1709044485180e0044000d08144101112815415074220341400300c810b241d0240509800c54810f2540380e650b500c81c130301d10340c2c4000d4030142c00f8541900c1d20248202d402005c0280341600c103140260406854198800a9800c402c41c0400640c0014005000050f8460300301c03030229003401c06c0c000500450b00c3d1890384400c503a00441c603d050710300d40391107159198a000d150045500a50402034103005144c16a0708081a01c0741000081c1421f000055010310381c000c3d10490000a84e04034075003441c0920f280001d520103100745040d070041d81c504000640e035031508544124801 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 80957753 1250 80956503 80956507
    0x92413030e0406120b0405070803161103070e010305030301080c062a031606060305011a0a060e06120a0c0801060e010e04050a0608030a02100c0305010609170703050d020d14040806062206030305 85
    0x11f4035000e818001d190700301c1411a4420b01c9411103000440c80c24001031504600340d0245c481880c4042070030105903400c2110350b5680c2c08000010844000300a5048a11101c107803031581404004000e014442d0601c042c3c21218282542d10f401e4078120b0f02640c2c0c10300c0500c11030386003015a50055201844104007955020368801040050090a025211400000c62446804035907114009400c40322280914000c1020308011800b45840d4241102d14801303408a034032215190400d8407402a000d49240b100c000307851134000140603402281c0601004005840c1d02d5005030a0b182800000c000c010300350014545c83d8480001e40b420203000800255582e50301510480c610a0501e405554885c038580c07042510f032100421076282c0c03004581c41513495a100d600031003071100d0159440e05295410181440c099002e45054042d0001075003041304540343c0b0744845000844071500d6481c090381c0b150907415084400020030602c3c01c3c00048101107180c1102c1c2c800e00c1c0c200c81c0080212003664100302c01141300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 80959003 1250 80957753 80957761
    0x810180b010809030708041701020903010504140d080c0f25030314070503090a0b0403030209032a010507080d02030405071d07030509030712080c12092413030e0406120b 74
    0x121400035940414110002d40c9000301655501b00380344214807880040c84818640029402e07400c0d0112030100300024000e11040c2401e007400105031b44c0d801a030300032501c280d401214000f8021042544201c0402000d03604044480307403200103690012004a80121124081042c01c450324200300c82d005009581c0060086640c050003004854080c21840c182310040c410000009000a00c0c0301079140d101c0302202194885140c2a00680520300013950315010700408003150981d0321071680008280c010004c10303021116001510944100800544050410000111804d281d500119001403040f03040382c420b81c4d42c94084880c03141c02c806041290300311000c00e0010069041c0189600100400041d40c0303000010b50301d94240ea0010b4501009100d48140011030340d81c1a002620440c00b00d4881c0b1841c0361501e124407503203501d11034480c4801ca4048080400010004100f55032041d8895501044030744802c0d1019900303c058043d0b40c030342c001d0302c4020104410b1100301d060309005124a0041906082c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 80960253 1250 80959003 80959007
    0x106080106080613080a09180504020406050105090105041401110714030c100206060d060f02040b04031208160503060a031401091214070f060603051203070305010602010605010503070810180b01 85
    0x3800742d100c2541c5030302c000d09002c00c0340c003d0300441c0360850340705443c070f560f8100550b0f095404043e45d034890900111b10780c0314524185003a82120344601e02c00c42c1e0400000e074688005540900a02500078006030f0705100c10301c2041c030310310b241d00700300801410b02d407216a0601560901e000b5054122200450890924860a080810240100c040225000c0f0100c00300c020000f55200002802c10b4458030101441c201404825449004684100c02042d9903d9845070700122056015202c00c5440c6e040c0c0c10349030035940f441440000d009801500314904070303401c0241c00b1505600043e00c01c84c0c0c0300f2890b00e00040001c001000d44c11a00940f40d002180307400840c141842030144440000c810311054403612507802481da001c4036500c6a00c040050814074990078150020b20070358000424902c00c801d00e2a82c0c0d088400d0195100d0182ca40c2d00348202c1e078031160b0482c261381f450312845000c0f0b20207002041d00c00d40110302c0a82d20000c82d400800707250399035100d0100e00991890b48040420354030300306000c043d6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 80961503 1250 80960253 80960261
    0x1703041b0f1a09010e030f0703030224040b04030509100804030e01020609070b0d0906020307090f090e0307030503070c06110a0f0905060a030908041a090406120201120f060b070501060801 82
    0x204110554a8050840022000c0915903880b16900060401d0039030b00a01600514020140840743c4100550388004d588078140d0105402603c070300700d0622490f808251410411000c044002038050300ea070303503034560403070b078050011001e101c41800f60103001c2e00d4680c100c182c454444e41d0f48500506050501400303c610400c10079046410880400441120001b841003ca61440b04565a942420040c02c0001c1849101c004d10490000081c807400550190941c3c0c15260700034220390341036955076000402c450040c8007840349504140b1180700440d00550246602055500303006600e0210344d0380782030458500401c1c0310002c0318040740400e810307079024558002c452418241540403a0424000680600409485400700341d2240400c404000d0001c003903070000c00b108046084040500314401d000303500101d800d07074015440d0201c0040e14070314442c14040d5854068448400380054213510f40d01070485482d02841183c6c807070800144514010300281112070041000103281c81c100f0001074291 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 80962753 1250 80961503 80961509
    0x1503020a02150c18120a170705100f0501081903080a0e060907090506120a23070609090f090f020904050313090902030c030109030f030207240906051f0b03041703041b 73
    0x60030b17541103541d9046000180c04003551360031030440182c2203040300a1041521600b14000d14038081c020790750443c072090703811004040464560501640e0b80b00d6041c0b17503407908001020080489480303c4040400d02440d8590b03000160b451020a40c10b956402035490701f1001c1c1c8040c2003070303070081a08000302582d0b80305840e0050303001c8694024000c554031a080c1d5400c5609006411143c2d0301001d81e0904043d031b2041c4242c112a202580c01003036480c0c00180c030492040c0300b0250420705006c0806e40204407072041d6440e280d4400c0071025030081d03d03002c0c40304401c00140304990a22040112000c50314072030311078034002d204a203030214a0100501c1858109906030560900a0381000d181000083e009814840445418500140c81d08040d0600e404100100702c102c80030050203405055014455400405906002c1e181c01d01042c0c8400c41003104401c1d510201103110300c1944000e10200b0041e20007140c01500a507a2419000d40344e0880c404182d006031811a5001040317101c054990401d0a691001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 80964003 1250 80962753 80962759
    0x14030105070504080a03030216120f021c0504140310020f09130203040206070803041a130201031d0705040c02150f010302100908032505070b1803071503020a02150c18 73
    0x90900e8801e440c5c0c0d8403440c50000038107042d004149035160300c0c040a1908021a04030f985106403071500c82000e0080e080c000d00a20040c06121400036100f45d582c02401e6500041d035490503e0140340500171050300b215082c00342e505003d084140e900d40c15250010349040c0400c1c000985d42d8104c80c5041005440c03201c4035003040c450040c4204405641c404e0261001c603508100e4582d921741e558500101010001464003d040c03203801c0c103001240e482c1404446440f13200303072020042450201c014060429008000010b41d61268005200f80d040c0340d080b10741c2090042c01226003404c0848a02c00040001f109c00c0ca052400c00c0004005610b41305401e01c2e1b081855080011002c2e090008054607480703200081600781c6c0c80c4250888032555190348280c1e0b4150008251070301c1c00d865000400d0258445076000790000c0161502060928002c00c3c100110b5041da4001c16000c10800b9040c0c1c0a0341000040c00b0541c051449206014042d00064610039000030210641d6544000246001034444d0324a10340 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 80965253 1250 80964003 80964007
    0xc0a150c0c0f080702060c0102030702011a0d0209010605090109030c0b0901021c0212130e0405010b010807030b0901030213110a052808061909090804080705030d0801060e030a020604140301050705 86
    0xc0468507400e00c840b25550040d91040c1d854009001142052042c2003c0d641c6541c400010440320550650128440801410209441c030768000100207980105504c043e52201c42c25004000c424020350060805103010305212100c1a620344030241150781942c80b001a04000041807159036074184841045003990040740e200020000e58000d48d035207420400003c09803000542e811200e44400b0701c180c020404254001018549441c10502800d4184e0b44a8003080c80c94000c00c202038060b002c2c0c0c050f40e2030040c121401582c0f0315000c01c040705501c4c0c07842f209003603034910b1700a05c6081448000c286031103203612542d0740da1a40f041b0303043c0b10340c0303407140d80403c002c40340c1050301d11403070b404415960403801c100d9450310744910070b080c608018a001d500001600345440440307002c01c85c1400c080e008959032042954081a84c4409254884040440a40000c4c01740001400909e018003060040e040f001750840e00e0040496001c20f0955100e40c11130f000d03c102c40400707068185003d00595a001c48a40791842c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 80966503 1250 80965253 80965277
    0xf040606022802040f090314040b070618170a021002040f030809150a032f07080c070506030a06090c0f140d02130e09060f100611030c0a150c 62
    0x1d40b28000500072050021200b00d05400022641069030b61064000700200070b15480602d120008210625044010401c9201018404408202a078048902e040c1419140c084035695000040c140e52608111842a4198140c045403c1c065108101062551040c3e0350f0b151503c006485c100c8410b010074090750041200380704910f0002e95000071240e100c44902e0704c801429000404002c1c4010110074041002301e10007041c20ba26810800c000c00c0c100340464030491008041d000c42000d032100c1c852400c1c408022400014401c0401000d195981c0c1b03081d617040a490301e0000d11960b0080e9a03000ea02600c1d69401e0052a0035482401c2e4032444030705015074010780d12403003d421040004224580e2181c04117958245013007c1e012a210305400218006110341ca86c41401c000920a840300c040318030a401c0000c1444100140703082c01780f2048422030780d4661524800300c4030b443c010103140000e030009000d40741e106081044001d0b6160302c80c41e0040980600460043e049071605040740003006070b100510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 80967753 1250 80966503 80966507
    0x1170403020d0c0204020d0f02030a0b0105120103030c020d0b0705030a061d190e0a1a09031206100e1002012702220209031504021804050309010309020f0301090609020f040606 77
    0xe00050941c43c1001803a180320703400050300030b0180c003040349409802c10381c03100c4880d80036500540c8590b0800e403040114030f109100445540c0030303015000040c160030f0001840820300591a00d01000c0c4003e043c1c100190003581d0304d220f4118150368807404140e000c8144861600345000b014040e0031840c101070001003111104001440d005401030313005032082840120030b40b10940141c0c408001182c22582000400e02d000c2e03031448084910225a03410300303c08120b012502100322070020040104415150700e480040040b61207900c5114001c1c031200c0e1a0030b09258442c000c40b402d45056070380001440e0490010801604210f0f105401d40f00440d440c4080300580d0398034044e00b90702d45c4d41d850203c140950007a08a00900c502901e40754103104401c0c0b151030280300188030318481e074420f44080d442d04500740c0b00c0407607001082e60001c01e1034100707102811180d442030f0301c0443d02d540020300380480c13401000086400c607207180f1801da941c2e42d05c40320803c041d42012444011415416201040003900d08000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 80969003 1250 80967753 80967763
    0x20a020103150f080a020a080309100f1b031220070605040212120c0d03020a05090f0d060e010f0b09060f190e010605090102010b010f02030a1b06060b090117040302 72
    0x10080c1416510030015407039012490394030020b0143c1d8a28041481d03150400c09550707070464001244a28030300e680c041050b40703022054860005c00609150702c80320395580140e407104514200c400c10001e134012042d220801c3e448140c2402c0d40a038a03498203502c86113070500180e80a55003d1014102e625001e80c00c2d9406100c102e031340303564100360001016116031002840660010340101d450384622403840c50070110b4400141382c503035540da0481d020070307210030300540507401196508000314034140400d003200e0030111860010307044010030b45034000020755590700440e00307042d03454900c0c0d1703544030704072000743c0766610916005030011190060306142100004544d4104850b103103001d902034540c0e80da081075651404c00040d02030400d6524056131503070030081c07182c1c025502640c015801c2807040d0701154001c900e00102d04145501861810b214040d040d11403244000e0b000c980c00e1021048440403a045208020250001260b0290749070307190310005002d41d52020143e40300c4104030052000003a00065 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 80970253 1250 80969003 80969023
    0x902010806040e011104240306030f2909011a01020601030807060902031c030b0a05010c0b0403140705031b0105100815060411070c0e0a1e0e07050d060c030b09040302 73
    0x1004946541c0810a0304c0c05800d2440c0720a42000000c41e0210b8180142c4c103500401100b42c0300010210611200101c00b0f8440c544009884a22800c125801081d100d051800240003104005c05281c0310104000002c0101159401c0050750340d6400f08508107480e00c002c4d54004000d100422a55045464205191045401c018200c0786d0b50b0040d10110346050240400748400b0740d280c44048001100d0180c0608007040a103031050960b0040403541e036008a8410003c030b60090303188009960355980546100c1c0410710200d00c0b682c024405480001d404000400080003401062110701a1305500c580c29581c01804d0000c000702c3e04d200c1072001280014100070304881d00301e200301054841c50b021500a000f440ca8107124074100140070300c11701910403000d00445d520501d01541550301d400c01f40e0102c0c2c8900d4091a0300e0b00c00c10411980c1c60480d0b4205102c015195030960b4025561200000d10441211400b00c69003a05c48284107107540e01840303802030012080d18031002c0740c9890740e402911901c1c1a9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 80971503 1250 80970253 80970259
    0x20a080f07050f0a03080328090b07110f03040f09050705040b0f0a050d06030614070509100c0c0815070f05120402190510020307021309020f120f0303011511010902010806 75
    0x300f6143c2440d650081c50b90015074000a01c15541e0030000c1854105407118075403042074100c3c0e0107411401039034600c0703815225500038240c00c0698459020031980c2c00e01b80d4441c00b01134441c90000f04181e1100344000c0005040c8201560005483c101c2ca100170b5500090160090100610042001000400c2203800c6402c8500c44603176600242c01050751305000d404200e684003480d101d8044204000c683c018200f180c114583c0c08101d545100c1c04881a11824100130b40181c040004e40c600a806010200e4800b44071300c0c1102000c68982c480540703010700c1040552541c28004080c4050160090300d0303508020362500c0d00300e1401910038002d2103a8080500002c0c0902c1a640005403400c00c8400303484c01070b1500400040340381c00701c0800259250003030401a0700c00e4802041500d0644903074403030400c00b03c0d4007034201045c082500303003000740355400c3c00780d1601c0764015a034000c1d2010b801070000354040c000c4c110b81010120682c010003405200f1a07807003841a40c0c5051408400350380c003c0c440b00e034458011 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 80972753 1250 80971503 80971519
    0xb07200615010f0221181909020706140f040209181c020a060c080613020403020d02060702060c01090b010611010203092104090603060504060b0a0f030314160f020a080f0705 76
    0x580800c80c580401024034286007418008210080070200006220203070509001074501c841c10010001803207c000105601c010b503100d81084480d0707107900a4410980210720008120405100310b02d1201c00c203c651980e07265402d010001146810302950b504210340002c0c01d81d8800c804064160f464000720341d88100340d81003240a2070050b108100c012600e0794000e4090140c1c89540720040c180104c15507045100d085140e80741c80441035a8400e0381c045a80040c041072500440d50203125440c4e01001e07080e82c00030410410032800520900030068542e108240741841980b401070020916a00001203080b164010400d010701030380d00040c2c00e98100030346007124100c120f00b0689114284196808071010720b0400303c000041c031001c0d40c0a03920070313805980700740b10310302d0032001300700c1ca484060040b8401c51030309800078004a88036000703019001d812003902c41c3c03515104440305035101030140f00898401220001c940300718104446007100905003840248003148029241030744865142c00303038902403401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 80974003 1250 80972753 80972777
    0x50c12031b0a0206010305010608010e0a0809030c090405030406030f050c0304031404180203011401020106060f080c1605060601030e0106120b040f0b010803040303030b09060d1401090b0720061501 86
    0x2515000c0c1e40c01c06541040d66641c0d010400010791580340074482610726501c1c1c03c2c0005980d51040c0154118608008003510075a4101d542c1e18400c0e40080c0d00203a054401d01014940c4ea440d8811203a000e41d00400c0116141c510b4510000d0070f80d21806e0f40c1640003070400d010f22000800c1d0100382c0f50810b0345400c0c03912044a142d40341038054040d55014030fa002e40d01c2e0281c0038030882d40e5401541642d10f0707690241894048032005a00342c2c0c00318410b2000188482d0340711003145106820040d007029192904030324203101d40c0780143e460458a5001e41325600100148180c543e098400d5102c68015503009101079450f00c040c1100100d40d91002030800152031002800b0042284440060030358055011f103911358464902c0c9903130360058041100800c0c50a00310303070b0340c030320300b00410034856080142074482819a554600308035050a1b4074891441d92100a540005254924103500c52100399450059450300050042015441c1d101e0114282c2c00440c10700024042000f200600000b080c20440086c0c0a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 80975253 1250 80974003 80974021
    0x318340e06120111160203010617060115020106090c030b010e0d0213090218010611060a090507090209180a020d240e06030f0601080a0c06050307020a0210030e19060c050c1203 77
    0x285942c20000c0c8500260994802040080e0203800c11b000354001c024a03030320f48803100003120102c0420401644040010001000c0c07001c52044011014400480e03040d5072488e541095401750502d0301d02007034075600c9840003564403074040c1640303c2d41190b803900100901d401040606480c42d035011205500c45480c001951500345400b000411000d412144542c1e44000062000c88900801c030001d0280c0008504d0b5440c1318061501d18940080240c81b0482c60204a00000e62056560603009500e0303085043c0c1030340100441ca0311903c819100965100d45100c042030440da040f0a00d010240005441c0315031782c44a64140c1d02c1074805c81443c4120a44600000074948003680c0b408008a01c10f1070004a19034001141003420580b0030110200103e45400341034405000881c0c1407001a031000e40400c015140140540450030703980e04001900c450641103031400d1080b408074100c00443c03108010010410588103842c2c082145140039070030078050f40c40c40c589503001c0c01c2450313000c03160200101c0d501007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 80976503 1250 80975253 80975261
    0x3080d06030b0f01030c050108150f0a0302060d0b01030c0201090302100f0b0303040b040305010b06040e07080402061b2107080a050c030412141513080318340e061201 73
    0x54110b04200d84900c0c02031090304201009001c2160200039030903000540354026650340d802222003a42a00003604c1e000203120402c1d28481c03400d6030007004100c1c000090f80300d800050003038600310034003c038909a5000015091720401c42d0b01c0011685403440070f2000c00e41c04501200703000c122400220798011420141e0010305150424075525020014000507820060790082044078400d100a00070000b0990400c03d260007144035019100305108000741c1c00038802c810045d44944000c00060070400c0c11300c261002c11070358000da40c030b041e071115030541004008111108445582030500d1454156182e84694181c003505850200340440403078110f4030f0030014401d540280c240b60345070b4050301c00341e4100584d60030410004100c80e8004d80e41c1c14101c00030b0301030140748180394040d00e8982c0741985544492203a40020490401c004440707000e6242d260081c8514800108031203c001000400c1d9040080303494680411421015405c8500700141c43e18114110750040084880060301042d621006001d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 80977753 1250 80976503 80976509
    0x60a050a0602030301030606050405010f05060a0c05070f0f05030307030e060d09061803030e01050114010e0103020408010507021501080607020a030e030a050604030503100603050105030604021c1212050708060a03080d06 96
    0xc00e034600041016603002015604a81c0148024803180e6680e8040c8002c0302c2082c0504982407051000a00090500f900108030078950340c0382c0480800d80340e481d421309001d215001601100300b80c0100f00031046a14a030031000d0201100910b15162065401900200c01103281034011031b000b00d261581042c103035005002c4150040420302003280714070018440081401c1049000ca8540399214041820501c034041c180d800c60564a0101c4250400540d046407580450504042d001c11005c50100001e0142e00e000711a9500204083c0860303140c031209240058001e9080395000004000e11a130740002c540ca0301c9070301810201d94a40f0f43c1c002181c07c141c407018000d000340c41074105100c00c250f03011000350b125104d0b80010708a03030768450504809849080c400d8642c540d0003080803030003529120303490700c110306400a429000032016640c1c054070500301700c6110010402850030b600240b1224001c10740d202000346880981441d0070320000d102d07003502d03000142402ca0040b8076800002e0301603000d0005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 80979003 1250 80977753 80977759
    0x20c070e2203020606010807020115230d0503090319030206040314040e1003120f120b0d050d0c0c0e010305060f0a0612060e010608070506030408070201030906020c0c01230d05060a05 80
    0x8011110b08001c0e544050507921240010b10440005c2c4806206114400c4002c1c6d0580381015a2854001c29680310942a55411041c41c548644c1a00310b945031054440000d1041015680390549441014100502d5034906001d11701035000c0c0d1400a680804c0042e402681800e12414441d095031000810340036a8121244480c01d4201b40001c09000ba401c110480c0e10580100410510405013140c40c07a0f4042d603110045052014064803200c029001940881c2002e0100209030031a5290540f42c40503d41111010404240b06d290a2054070500702018010300c040a04240d403441c0e03921aa50b120041c08010844107500100f03d0035030994110000800302844804810505402c00100803c1d601c0c5400c0c200d50329012000410410202e20302c0c0441302e005200d2410359070759807941d4101303071700802c4e0490406941c2d50001c800503415101a104404c2ca80f40109031050151001400c543c0480301c4400b100391202c00c1e141602e41b20b820482d80c880111640210b240d8864802041020704184c0100754 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 80980253 1250 80979003 80979061
    0x90606090e0c010203041505031308190806040c0503040303020a020c04060b04051201060506091e090a0b032b0c060b060d0e07120201050702120c041518020c070e 71
    0x32030140c141c001c40418007400040d1210103a0150059a5900c598485e89180034184c1881501c000e00031405140d1041d64081d461410010b580c1c3c61440542c0881c05d450104145480506411503003d4060b55100b02e060320100b1807078540001c00b9119000041c001420550009902e82c00a4824445500ca0a02c040e1040c030545454207500d20076504640603c03405810340c0f04a0580c09030050040000f10740001c0d10051500d20b03444244440803102c00245011185079032000030040d10385c00051446200d14450001e0f621241008060810000d00140d2800d43d030890400d05410400085d1240c031144c9a09010310f54518074507040019111070241c90743c1c0300c4400f003001001c0c1d4400340c20420189860605440310b00f44c45030b200443c404164400a4001070f0207000c444014205619412015001ca0040340d440c0d055080018041e1860103d45900703140c1e200b141005107030002c2a00c2d8400c401c1081c025820518003004040c0e07606918030400c4281808000031421440340c0000701441e02d803081c40070705 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 80981503 1250 80980253 80980259
    0x12061409011b0206011d0c0403080c010501060e01020c210f120a030e07031505040305091e0406050105040b03150411030c0307080c042402012c06010f050a090203070201090606 77
    0x540241076074422000c01040b001c0c420101c1510201e80d29058808881041c801c08a066100060f181c10040504002403020440803001c01c0c04400540b04812210340041500d60400c80010507a64601541506650191290b241d140d03440400901c0d5840354003031070070b02e1007070f19030002842c100c15501394000030702410f508903070300441d21030080042c0c003910703101400160590721500f5230300c2005103c090080840d4041006822004e40c00880d0064001d01c1c1250601815000040803080184540741d4580c11042d41c3c0100c170b00b043c1c09408010701c0f090030000d040034608000d001052000030815801540d10442c0e01c08980e456501001400d034280c1000c40d12841c0131034030100c459009403007041c046200c0074005508481d81c1d000b20380c2903540125207101e20405805c40c0d0542c4140c048564810740d502c0300d20051080b0000320602809124000010715444d030290300341810200103030049040709219080500003501d03490031200c119400f080300142e4990303a001d0201c1c010b1004000c004d000c81c0c00c1139400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 80982753 1250 80981503 80981521
    0x15070b16180303171e0403051303060c051c0b0a061b08040b040e01080307170d11030903040e0901050c090d060603020a0902180f090604090206040b030c0a09080102070804120614 78
    0x7005224910341303240c00c02622050f002e403262102c110706424400840400141c00248210050b00148010041882820340c40395100b4064030703c5440103800050010901c03400c00328040c8984401002c043e83d040114000c020003142c9020b0440c0111414000000101c5c00180403d80100b0102500081da0940340d030f45440340c6641c0d903405440b0b404560481007001003000000030040301e400326801051a500c0c4004440358100513007050001100d00c40c2d5442d001910800d003480114480c5800c28080c60b512070074102050a840c0c40a480d88079107a140008100084446004840c04103030125481c928104052a04078040c00381c40e007000307401079171014000550410300e0f00a8071001c0700c2c2908036850407441406122007a0b404207122076000580a0204000b81425480f140c18103001401c501d252070744440c070b41c400c540c0c0151580000d41c1000a2000f418603400003140001d0848400203500c0c001715a1604041c6028034020803090080d550b082108214155002d001454a020a000d2741845c1903104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 80984003 1250 80982753 80982767
    0x50f0d021e03090d0c02120706120e010501050907141303050106090c02030315130e01051303030e0a0305040b0a0e04090f03080c28020c090406090215070b16180303 72
    0xe003040c00d418100c81c100a4000010749200b84060001008540a02503003141c2d00103002006030781140c510001041c0060040c02007102a240703540743c134090f81c480581130000300c07010702410106692400e401441599101400325420601130320b400d8501c221600d140d0b002e94851006019000c10f02c500002080000640044080322240c00c401c001e00751001c60143e032030b03102c03c98452440b24846000ca0b49245403200c0c101f903800e035180c400001e0264081a1042c2190419a1601050707034205490508155143c00b8011141c0ea1040140144480070b94000c3e040c3d000d24050406420400f2a14440785440381c0c07000701940b42c00a00900207001036042c0320601c40202a8144e0000328640d0001e09030050303100c101d039a50340c0d400b0711483c681a2080740d01615400d2015200003107000748082d8001542c1c600c0c580310b004a004041c00604804e092041144440200400060b0302d141444100701142c82d544991b40d1000b4100d24003c044040c807903040b10006420b85134410260740300e001c040306265002c1c803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 80985253 1250 80984003 80984017
    0x1507080601080c0906070f060b031f060501022e1503060c03060b09060f2a0d02060a1109041d0303010f090f020708090d0f080a08090d03050708070f050f0d02 69
    0x2e41000c15141c00d0900d09051056207281c5800a2041101d040046c5105110314050360184000054900d18036000a0800940c09040500405809030014029100e4070403040141400d000810b81109920101803130742602c2c404c0507a020320281c08444544400381c0003503540c0141c45403400001600c0e4903000d40249400c1d2507480000e8644900840e0592101081700c40d4844c0c020001400c01507041c01203a07240c0e03c0324451041c2c26401221143c031003048100907050402106015042d40b1811170300c000e20303040005061854031420451000c01946480040340c81045003076801090720b503040103030b88907410b03196641482184000000010206c0d00c4589140694101e01170502110070f410504070705a0040402c054030040c1c00b00306841e00d914203855544007480c4641c000c5135400000d612107440035001000414007040c400d0701040004001405120350b400c00c6c90804000320305080000406c1035900038044020300c2500490500314501810036a01485030340c1040a1791445801f0744e01020703400c490 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 80986503 1250 80985253 80985257
    0xd090302011401030308060d060b0a03050a031704110907051c020903010b06030603100203090a0c060807091d0a020a05071e031b03050913060506070309030b1006201507080601 77
    0x8146281481501410316041300d40660310066562140001c000c0d032886c082c1c134101d6850f540c1e40160b44003505d0700300c0d04034001c500640c042d0000c500e80d4100a007140c4c0c030a00c2602c0f8142c440c4400c000000340801c02d0fa200d031050549090006e03540b440c009480328420700740d00b1041d00346040034003078901d4039580003414060390580003449440c1d508002e000c400d000584105038103400121050302030403d00d50281d5031104030401103905030040b07038a99500c0107210760005800245124200f0031010303001403484005218a61402c505a543c0b10f00c1c2402000780548041982030700000c0108140784108183c49181e5001a0038140001803400e641e0342c400c11600d070440201d01504070044d188a1402c401e15507454141e100c0600e4070b083c0340200b083c1404240702541030299580b00211b51a01d44e9070142c20010302c01d13240d01440d14110704184280c142e00410104144e109440c05000c1554042d1005090000100001c81080c2444c000309081c00368940d14491111a02d00400000790742c80441140518000c1e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 80987753 1250 80986503 80986511
    0xc082b0603050c04090215030a0507020c0d020d0b06060409060801060323030406180b0c01050703060503030c070501050912060720070303090b0904060803040906060e03070609061b05030d09030201 86
    0x108815500c140c4030180007600300440c0510b1606068201e6803d00d072000748001c441440c4021801c410b9041a5000c00030265100c0410254980400c0072030411032084a4104c10005183d000909000d00a14018030b515104001314100303468a03000c0c0e80c09008284814403d030b03510780c443e071030003003201d480242c410b100d11a034103040924680600744e00340041c050141d0300d42800d120302038500843c0c4000e90f0095101400c400a40b0386100d002038560032034601d001254900b00440d000f000d0b1040c6400051098004000101400c040052200f0444000f03003400350300da0401200003041003010a90b4241903018110420410540c89044038940ea540c2c2540e20b030150300000600396035a96107010080205200b2201800009a41c20142c42e100700000d01c00b2a1960f103409a1605542156000315425511150103200107501300b2510030951400380c000b4105607242280c010300030104d91107100280452704004100c10a803134030744101e0064104e01141d40c0c4400b245201c4004021410b001d1340154a8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 80989003 1250 80987753 80987827
    0x10606121401050a050904050f0105070905180c19090302030f0109050709090206090405062706030706020a0b0a1805010608031e09090601030c18030f0c0b0301060f0f0c08 75
    0xc03860349641610303c050104d492503400c10f401d103e941a4080c00a0b2a00d111711565221158001d000e146c0c440e101c1030b61003501080c9410203020001d108a108000e88032514070400011a072103005a410340d54060400070070b540224982030795600007e41010350907014101c40030320713405415040905e400388200c00700c034495640da00c2e01c10200c5400d600700039448a0100140c000501d0141c100c0d0317402140c0101408003100380f2580d42a0f0f120310500f182202e4555801c01c2101501c1d05100490040142d4009403910b101c80d603550105486000740b9440100307640350381c4145411030304080d4607681075214008004660f26040c48540d80c4e08192480103043c3c48101800004240b00c1c000c0da402480c0207403440400f5200d070001903000c0c2000600a00800c404a42420b00d2001d00601180c01076000b00c100607a00c0302c203030600300b00f400e00e590000d4508400410040100c2c95110004885810952501081c0c0d8804c1c408102c80d0399284000140644d403000c10701d900d4000c9201c9941050301e408010402581c84 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 80990253 1250 80989003 80989031
    0x204050618092b020a170906030a060602010f1a12030c1002040e070306060518010509100801030204050c0705060103140a0b01081605010201110904020322140607170c07031101060612 80
    0x3007001003c0181c10032141040007640700c40c1170140c0a00c80f6040d260030505642d001c180c05400c229000e00340551908030400419130284104a61404201c00c107002e00f4440c003844510b440b00640b41503008401200c00c0b103092840034006e03650000c0c851313415039101205d14580200650441d0003500043c103501d001107414903002c0c0c440c403011101ca40c0c6030a4103000381306029411a68004030040d040c480108000b003015038444281940b02c200545a6000742d50450060004640d002407001040a00404c007040c0400c03000a00035044a0340080a07071001c883c860245400e20098001c010100107201e0008100b0342000325084c2402d010f4410f001e000ba980d148012801d855004c00c145400440c100041202403c4ca80c0042d9402005151042d04001070140d22110326200840d06440b566110200c00c1f014581c18456160070040e5460804519003424400c4540900050300b541400380000429100300340c0684000348040100e24000c200c5a5a20603028021040c9000600d82c06481c1c200e2801041c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 80991503 1250 80990253 80990323
    0x60504150f0b07200d1202010f1401050904020d0303090b180606011707030b010c050601030f03091d010b09010c050a030e0a060203120106050c0a0618020a080a020d020405061809 78
    0x640c00165000703019211143c80078030321389070400d81034010900c03200000106000c0d40b0040d04020155000158405001d601e24080380c8100003200601000e401c01001540d68041c2040d42041c0c0450300540d04403a10300c1d040d8004c1c0485000103100030190410401a034095015207204e919882c0195440c03540ca2100446045440083d488008141c44012800081c4240d101111044060401a520b488941c480f2450724500740c2c070032584400200c0145e0304140c0d100c29410001c0c4184100da00d1fa80410f4204517040301d03414001c540c18103501060001c0980e101c0c41d200520181c010342036074001881e9050040171482c210348081e019101d038500000b1580e1002044071940c5100300307654078159090241c00c0b0340715402400201d0707580c85101500c01c082456071180c00132003034001e20411040f4042e0310521119500303d41c05403003075400841492001d0b0721141e0208260590403640041c45a0380e4130f001810000c0e81441c04100c0f10000d404103d012180040c19903031040c0411030400840400303150f00440b403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 80992753 1250 80991503 80991517
    0x50403090501020d0f1d040509010e010b010f02030a03050402060706051501030e03210402150d02130504090b280908030603010b030d0504090213050d050a03030f0b0607020d06060504150f0b 83
    0x174200030012101c00d114142c00c00308103110502070b0620810710400902a0707103044d1500051079650b101c41111a540910a81d1014034080c2007860301c000d10901c01075224010502030005264403440050119030350103040b0ae00f81603212800700554240700014801c08181200d805000c00e1500c940007403031840000544d00911550192107071180c0204010054007400030344126003055518a5451600011201030401d41e05040c0c0b0042e20340d02e645021003a085006c2e801140541c0ca44005000420086907805500c000484611120201e1001d80040207c8106000d40b542c80c1c5414951010462080c00031030003948110001c0c0031301d45070003080544800b0640e850602040c4200020029100282c0181a0300a20b0001518441d42c1d02c00c0813076500d0368081e03000ca0b20f50b00700780300410806415101e060b10344a0381610820a0240350300100d02c3c107101e0402c019100340003402c10070040240c1500300340c1c00f410000e0802c0c860314000e000c1c00d0180c18440d0081c007007040704800c4c1c04901034a06000752040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 80994003 1250 80992753 80992757
    0x30c09020316090b0a0509030f0f0a050d0c0b0609270102070201172509050315010302031006150516060f051e130201030509240109060609120b061909050403090501020d 74
    0x317000b2081c0802d075501d601000f00b00f80c25002d060100d1003551000c1c041d010b280442540034024100311840d001d400c01900c141c404d13080c4880054001b01050b0b030040481d91101d01620f82c0718103030b111214081c003241070001c91b4004240d02d800c280c403d0918103402404a5900c01c0e2280e45002000b03250b4030345004803c23105056140100c040c0d40c0040c805003222025100c40905040040940724800300b410300d84024990035043d0a00d000410850a00700300d000400c0e8501c0b00100304141c01c2400325100c24200018507010840b0204800c0e520744024180c640083d84d01000c20044d10701204000f0018200440b680b0b40c1d01c3d110101841c002030b8403051014031980a03500144142c0c03449600650040602a00c5144140301c0d20090400054960f000d014035026500c1c8082c1c2950324202c449410f55071903400c040c00f04000503400f0404000501400741d21a9400340c810b80d900d45d030b4403011640d005000c040400412603422000a440801580b01a0241c4d009a460411031600c500040e43d030740c440712102d100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 80995253 1250 80994003 80994007
    0xc01020714060702060708040b0403050109030806040209100e060c0f060901060e0f01210b04030c05070807050a0302130b0306070903030806040b180901020f130e07020a080d0510030c09020316090b 86
    0x1c0140b900100070f0200601ca11f035040d051586070080e95420341c0040e0012141e580d51503a0710400e00d60446040e40d8011002c845c107624003008003020851041880c1410001c1c0042076000c900d0582d50182501c19100e0250116003d140c1c0103000d442d50340c0025140360b50709502e05003011520409100301e413403090301840340c034090310392030905460034002c20940c031b90001c96184040b09002980916641740218040e917500a41069541071003070034004194412075290b40600010003417500d800c62441c0441f1780494400e80030300c1c401d9004502030442c1802e80c0f41d1501500c810009019000011001503e009540b111700680d101c1003408104d6882d0b0f0040d80d031002c4189500850f0035518003155500c203260354005070034842c05600c3e041e169007154031480c0694051080c140700c10280c25100ca54441d00c50701c000e00b2402001c0e22a40c045105107011030103156104c5000803400c0e688490304100440d4000480501a56650603c1c1e00a40007662104049003042d040720031700754072949042041d0b035540002d0354 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 80996503 1250 80995253 80995267
    0x130e1906060f05151b0312010605121501090509090c19081614060d0608070902041d040b040807050a080706050708060307140625050606100507030203160809040606020c0102071406 79
    0x4500c85c101340e110710400b0b101c200400019060303d648624028600350b200c840d1500101c40d50350000200003044000205000205070706648c0c0e005540074200c0e1f10965030092161195407600e41008918a8202d070405152a0240a804070341b070618801c07580c0d500b041e240303402d031104a0141c2c2c0745c42c0f500c600901a0b110312401022072504000410084005800014045a90b14035950a013040b0781c0c00004210f501150400c0095610301d1801c0451202d900c400001c0e14080eaa0001c0031030340500050480c0d0000300d804003c11a04010014004e074102c0501c0e502e64030b1500c1c090001d0882141e40d600061664408506203050014052082e18101c01002c0b40c950b1804050004030382054601c15001c007a0385410b507100580c603002d441d14040c02003002d03104a2505809019451001e0124a41004020005240071079408001d584801c800f03010030107101c6e034072070400308858080c02c540e03180d0280c03503c000002c0c0c16400141c1080c4c2641d00b0f13020f484245940c2c1820b02c009440e54004250060b204008003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 80997753 1250 80996503 80996527
    0xb0d1202060132091f0f060f050304050a170d061e1707060809031215090c07030c021c08161103030408280512070201020c060306130e1906060f0515 65
    0x19031740174405c8405481440b48000c0801c1441c140ca91151082d20340001d01440080e510645401d00c4484509101d840e40c00c0a030b0751640c0d12045248041e0070001d4150810000d030031000308407000d0f095119800c1c0b12094540080c044021500b44403007180d0b00046400040a40918031042d018032586405002c0b0140ba01005456441e001000301c06607000400240040400081c11a030241c420140711032141d540700c00620425140103400c2408220b814010280040c2d44249100040d9a040e1482640c50307102c9020448071380308000c00203162103004a0881c803400b000400e03550390705004038030b40070b4540b01c0c880c18142c50b842240544000f035044114800c1b000c10103014807100c0003920055450307019820352560f0f401c0ca813145200c04882000060042d0556a04200c1503030b40a004503152803441c01c049000a20301410b030f88119072199221015400e040c1824003c05101c80310b40d038910842d03071000349460001007034503002d0071480200c07601000c50181031611f50358010350031610740c56240100300455 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 80999003 1250 80997753 80997769
    0x5120a1e0614040c111209040e03090904030c060f0906091a01060c030302130503070611010b0411040303120f110d0f02030903070b04050705060703090e0a0e03030a0b0d1202060132 79
    0x1603d090288101020200403002c00c20600c0300c40f200c0d040b5603224a0b250b4200030583d0012030301042d09e40e02c01e000124841e511070030342c244c000e41c1c14140110998603924021000e40260303101505880d01e007421120a0140f181c000c00c41a07841281400020100c1c84070303200480c0400e006a134002808424070790001f134003e500078201a01504540c01c2032030390701c1c0d001a2608020b030b0003040004d40c5601c0720105100e4240110009480116020b02241d40854146449030042d0721011b0b00304070240381101c11b881444d61140803501e407041d400703000140e08100411050752116061000f5240f4102c1032050f0340256100f5607000b0500790025501d03008086d210041403101c090070584041c0103032940043c1c41d5907446c008162080c8030ba01c50012840c54850988061007006206503d100c6c00c1c00312120030a3700101c1100c1c1e0011101d030f40000c002c1401d1020508203400c00b03a00900504003481030307842d0180c000a100c0d040790405242c000540b00440010290a81905031625010401d50f4004a040c5000c6407 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 81000253 1250 80999003 80999021
    0xf090e0a0c120f06060605090306011202010c0303050703020c0616090f030b0c09030f0607170c0a080406022a062208040303050306120105070309020a060203040b0f090105120a1e061404 81
    0x8560301c0c0b820142d02e913030f81212229800007000c0364000034903d560342014405640100029211007a054045800190035090200d0000b0101030b0f9600c000341c441d03402681500c0840203c6411a4094074141404001140088100701d02040701034000256206542e541c4100796640000c900c09140c0342e4680c400c146412103c007043c0c0c140200200884820400c0106501c50340903039403131591800d004402c015019030f002e40180303518001004000075440c2c00184d195002680600c006a80e1108042d039051309500c07400700b641a19049080c052042031001944501408104441c460b80e2041d4100902c02c0c500006001006844140300800129001354059580107601616007490480d900d80710a0848008079040400300360344102e85000d60500c1307100306000d031a039030004510300303400c01c00490a1030054500b00308012400080d07008550b4410410340f0400d4950500d111941d050041540001c0d0803102c820309146407440340030010101d802d000b044100d0b03002e2054030612007852401d100c060001c0d84 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 81001503 1250 81000253 81000263
    0x803041208070503031905010909020d020f0a1206050a050702070807151b0803070e09100504091109100812090a0302060a0c0203190302060f0405120307020709060f090e0a0c12 77
    0xb01c580000b040e000c0c00118890801c0c168040810040441840d08460040c1c01003022585020026001070300c4102403031910307540460304241c941c480307200001c20102c402d41040b11100d2510362094100100c0303800080c05000c07201350500c035a80e210b2008980e6a6454812825150b106250400080d41c15000301d249503109442e024070040301a1410200300401e00d40121032000000027005002d5a10042000d81000103c036664000d0a01b80185513000800b400745c01c0c40b032076030b40703401d130081001484002a0789c040280c802501481c100c5640c0c2e15080301d0b4414120240513880c0303202034a01140301102c039074140013400714564a00f19000d100894200e9181d04040c0094040d490340540d40070400015800080b07039116007001842d00e002400d080c809071650500ea0f0149040c04001500807480007403122180c1203254a0380d5a0100483c64031015601140310f00c1d10f060707400304000e1030740c0d2212410780c1d625140c10311060501c1a80d0640d226804a4007801011203e58180f180a5a030070040d40b10900070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 81002753 1250 81001503 81001507
    0x4080307050d0903091d040201081801090b04050706080702030307120c18180c03020c120c03070c0e01060f020a050718021b011401080a08030705211515040803041208 73
    0x480000c00440f040e510b000e0303020600c0c2c100200325140d02028290300d00a80844007031001e042690010b42065005803c03e134129107035065038484607030254412100c180e04904242c100d41803500745541c440c0018081c4400240e54800054078442c0000701301c1c0d005a00c0c40d610b10900d031200413200c90007400e10303410202c20840b10000c26040f4200003031540e40a859207500109500c1c940c5070500048038080b5000700c013414014809840c40507404035010b0f000c004448200d80e51143e844520303900314407914800500300e080170900491140000b804190594005444080d81758180354001e82e074444aa90005045920204040c418984000500610140b810a001d0704003151a404d8191600c1d502030444000c0c0e544070780410f01509129000350040c03810f030003e45511071141d194401141300080c011800c0c4034000692010314460210350086c004245048a0a1410050380c110580790561840da8450450103000c0c600f84441c5100f250200c41c2039400030b501d880c2c42c01c0424403a0801904094460400c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 81004003 1250 81002753 81002767
    0x60a05030d1110090302071a070b0901050604050c0f030402120709091407170d030513020a0b09090703021815040902030c030712090c0b030603010f1802010e03060c030408030705 78
    0x810400740714614030381d840c0d0142d210ba0740444249040201e00c1d40c1c2400d1800c09102001003500403074010f0585d0700300c1223a054140d0f42400e0340607040c0f042c10300080290b03e11808102c920041036004a003e044122414001030b100c42440044a000c0d44588034400101000400c0c010f15010103440d50b10202c04068500a540c4e40007070b0006c8622010054440d1400d00d4a4002c0c1440240040300c0546a025900b00c4002c44609a0079501c900c1c1c14200c0c0b06159a40000c5500704001112401a0603401000c079849a03486054a420a40100010600502c034100c007188805000e8001c1c2c6800103030541d00b031240d088041e0100010120343e507510410100f4100004a4401200e000851180e0402c00c94107903a4140080e0083c66056201c0039994401c5c600041c03400080c0365003079900210740000b200da507100d03254480000e005128903500e40e8200c07460000065402e00d000c20300d11100b14000d0b00c0d1390925070644c405040d1540d4048807a08003603e010000580011074150145821800500e45203040c034403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 81005253 1250 81004003 81004009
    0x1109100302090901091112030406110703020a0f08061b0904020f0f2208010213120302010e15060103150806010521060c03040b011d010b0904020c0304090209090609070c0308060a05 79
    0x1050701e1442c2c0f00d94650240c2c0e03082c40ba495610310842c1c002601c084680b010907900080d100d01035800350b4010000410501c0317030440810040c010140d0f030001c2941407010740d51100f074912800144035a00060040e603000a1190403400d800500c0c4000c00c0e1141850607580d2402c00000b5801654108249036080c000c0e482c000c6000e9000d02008408190308032241200d03503e080794401d1641e0b1100390b0aa0041080d001c904071846000d008590f20701c22042c601b41210b15059000d0a124046d540340ca1142e600d811140380170b07040c1802d0003840c2c2030303d00308004551803980662034049030040c002568000c3c00100a81e04013401c0001c00c41e903501e18032852045080304600d0428000340c4400116000200610003880303030300484180108005014001c0306680021854a6000140304d00701e80c4443c0496a4680b40c1c0f21034044400e00320f00e403410350303640343d40760306e0300800a4119034800c50055055000152540c281110b18078013491140d01d07606002200b9590440702d01900910864000a100c0310014a40c1c17 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 81006503 1250 81005253 81005269
    0x80c090102122b0e06090a05030409051e10051002030906040e070507050304030c0302031006120f0201051c0906060807051e030106090c020604150c0504050d050111070c0e060307031109100302 84
    0x50410304001c640b2484c02602d1074a0080060300c603002a4005d142e50030000f45000086504031484028041080d80e034403000740504220245107400405010002c04c40c0c10541c0c490344030180c500031101c40032218800b203800c0741c2d28091a850940c001c00104000c2c41240d15243c00c17151700012500d025403400d1010b54070641150090f92040310007800c144414021481d040c1b207161002138040d00c0070400d141c908000480c40003a0084050301d003030005082c0400f56441101102c003017104ea004002044814018150020a045c903c207a0301c41e440c08001040340c5030f0104503282140c20003040c00c102c1c480b000c030201c9440c92030b103000298590340e102e00000301074000d802280a0001550041e06082c54030f400c10820000e072a484c141003482c500180500701c0d47d0440103a80c00d0700d000f555145a614503500d40701d0300402c803056076074040c01c1001c20760408022103102d145041e50b092144041040d1222014199611070b01e010082c5401c01034102015241008000c80307500c88580c41e412000903561f900411000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 81007753 1250 81006503 81006577
    0x210b0c04030813060e0607150b010e09010f0501080a090c061d04050f07080a0e060a0c0216140a15050405040207030201021903022205060d020307090305060f07080c09010212 76
    0x83e010700c034400c01007190000f18881004406482c1c051400c400703030307444003807440d0038000e4102d07121307501c480203100c40e4810a81030350b4030301014151922070750b1a00441105010a4031070b080c0040d403414001015090980528101c542d440000400b07107a0030054144c0d07219800c006a800054101104580c140d5554050749002d1840074441c01214200110010318545d402089200d145007032801c640c00080001480950028094900198045403003c0484c1060b1242c00000018016501d000c0340303d6a10751442d5801400031158110755540c0c40400d2004080790800703d101003001408204a1410b0503002449164820300c00145400d4101d86003006c95101c4000c60b50001307a001c20402010709004200c560401e41c1e4070401c082d154a03000005219114400340e030103400743c011000c5071559005140002c0615408810340e000c174944501c102541420231541300c000510349402145801e06141d085403014201030740580101c410a0720072010640c8118200f0030041a4540c1d11031404618600107918 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 81009003 1250 81007753 81007777
    0x5070b0c030f24010509010903020901090e0c0901060801120212100b1e0a050d0203030c0a0305030603010f050705070f050705041a0301061d01090902040212041b210b0c040308 77
    0x124105000ca03481c0c0b071240240032802e600d0f00d02c0f45140ba0440021504049080240b81155842c000280100c403001e406034002500010035400210310400503400421582d10000d003100c0041c003501c810814080028860a00403600c1c03070005102000d0f0f0258040005400601280000c0ba803004683d0325142c1910309811140d9070303800c0f161045184c5074002200392082541c020180e04040000a810303107250b0300c00c0a10440040410b0070464070140705071030807890b100c010f84050400d0390a000e0601d5201302e5503d4407a5103080803e0440810521445003d03400954915040501c40e80d02c01110f210504400d4030203100e20100001d8664860044d002803c030f09410a0f2a5140c08030700b4582516001d4000441c1c0000042c01102a0058590711a04644103030801144030109400401e0081c0304030b4000d550700001c0082004240021110001c00701c40529600c4000c02c1d40c0c2e62a0717990300000c07000184890602c42c15042d00414251280b05412001e0344005900d8540d80765640290fa5100000b8154 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 81010253 1250 81009003 81009007
    0x90a0603050f0c030121050109080c06041401140c03040606080706020c0102011d030306010f050915041404050108030a1d0603010905040c090902010203040504020a02030d0e0f0f010e060a050705070b0c 88
    0x800c0d2004180d10340e40088800700c160f4119410314440d1101202101841900d0f1286c0c03042484c18000250400c8441d25084040d650f0307200070300c88196880d108211015220304144a1100c1c240e60300c14800e0b0714041c80605103502e240e07101e407a0720000d15840a442500c4580e12150007048640703050042100801c0745030003e2081045c408006401c0d5081100000700900c910300c0b40020341c66001c01200d6020009182108041032650415580c0d80100400140c0208504070b02030203079100b031001841a54013580540010030801701c01c102c181c5400340a1442c0c01d8105001000e000c40c01115aa050358a00030a83c5980d80d80c0200030881c5c0d40c01c241c1c040da0782c4580301e030300307000a204440c03060700007034281d242e010f000c4441c983d00081e50341c1c400d42c41801d000da50300203004c0300701c640b00b4001e0380d148a82c0240107004000602d901a41c0d10691102c0c4940701e40101641103889003414450450164403200c00b8013055500c40351240020301c1c4c0104241c0504c90208aa140000d11a640346e904c24147c0010f065 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 81011503 1250 81010253 81010261
    0xd0c081c060e150306100b0a090306020a03050103020a08160501051812100b010f0203040b030a1407020f060106090501090506090105190203030f06090103020102060415060803040303020c03060f13030c020402090a060305 96
    0xd40c1c0307030b10a0912140250022014030071210351151324441070b61f4014007010f80c1c461161600712040c140380d50001c1c0c0340d54804140d00314200d506800250480b402140c01c441c5680e01c5041c10f0b5110510456441c1d84040d91213010820380d4042c002030082c10241e00f070408000c0341c2c503401140850310302c5054618140c000035484c2803103141da4400d0802c034000030f1038405820609040040c9d901d00c03890180b91400381c2c0100004001100ca6040031080c1d0405d501c24a880b4240030001075035802d4552211045805541c0000c61118402c1404108450059640c0700e8407a1408080c01001d030310801c039090412204206490031064020b00080103508154021170f503c0c0f500c174810856601340513141ca449841c0540041016030ba00046070354100da0041c1074803a09113804c0d00000c000700401d80c440e10142c00045000024540c002c01c1c40340c0c4203c02502078400942e01c0390f1541c03442e81c5044858000d03100c83d00c000800804e1186050b0f0003802d10107000113180440e158001491402568041d0380003d848030204 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 81012753 1250 81011503 81011521
    0x708071214030a080a05040c050409030203070b010608090714040603121d01050901080408090102010e0f0d080a05160807020c090a06050f0910060c02031f020301060206090d0c081c060e 81
    0x1101400c903440302560901c40c038400001c0915402900c1885486d4451010038140f00215175683d004000007041001400802d03e80a904c3c3e0304840000d65050b80100000290180559816031045041c10081d10f1518200400700311240c98808000740c100c0c0d56000c0201c0002d4150900c1c035103480f41781e21140642c00a1021040200b030407800003a04201041c07207040d01998105030460b4000f170b40886441d850300c004d040101d00503c41b05070002414403482102510407200400c0c0c00302071580554070802180d5502c4040307002d0343c1d0107696860a011704210842d110b140310301940d503000ce10070310588001810320070004840030ba00342c82c030004d43e0b079480a04010625124414801424040c2c035803040780c0c41c0a0200c405d180030035114810038400f61036070050440d41c00f40040700d201c12140d6880d1100d0120a090800290400d000d000d0151203a00081044070a0001e61002683c1c06aa2a04001e51484d911400150031103c2400060129104460381051007130080001408100c840811285011420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 81014003 1250 81012753 81012773
    0x603080313022805060d090209190e0114130302120403120306080d0c0809040e060906010302040b010203031009020a030209040c0f02010b0d0203060408090d02030f1507140d0e07080712 81
    0xc20146043c22649035610300c990f03000c10204e40302280d1064458046010200250010301002075000b8046803c001d4484080c801c1e0507103c0381c5421040004080ca0a00c0764222460030b03460110f804180c00000c0c410038103c00050520500c41c0c41943d10440e0000540034854005801c2103d5044000c0d140e250b45ca0380c140b04110040403001c0c0200700c0c0404e62040036154803440c0d800a045074000149510140e00c958103c4030b005502403044a44510b80460041c0d00c0c1c407000c0c00f0880c4101d0510b07100250a42c40002a01e00030b880300d4440020b82480c2c507001d040254800f104910500d41c0a000340c4940b0359986c0b04200c8220074903103540c4008214880020b00311001049185d11840d588030030708001da100040d0f42544140d001c5466507a60400100049020285410080d0306100340180c0d41c800308004503031040c0c010966400842a501c503503201351030500c1100e40d40c5807004d00500806050721000d400440c03486502c0c005607900c5545854415003420302503040754000d5101102a01d0800001c1c0c00b07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 81015253 1250 81014003 81014029
    0x309080d020a02101d040903031503060e060901020703050f03041b090f060f0b0f34030807051602040510030c0906050111010204050d12030f05040b0402120a020102120c01060308031302 81
    0x42d0401c190509124181490f405c04020749002d5592141d4040816009a005000c0354805048150040d41e6074504031010340341a07a0240040d00640022036a421414029290080c1d896142c0e10b09184043d5030844150700000c000341e60710400e40d6010460382d074411034184080c005182d008144204040c0801080e50078540c0110754420341e1100402142d201c540507985041c133070121a5540d00607000040c1c8250080115030981e201c000703468045803444d02c840e011000c030700c20b03200c451455444800c1603032140213031010f2482c03001c1212682c100501d803603071080da400104141000c00c17094030390301d50766145a504d030043c0017503540d03d003c203000f00d60300300301c00429600030b01000b94549130601000c2049009002c0000301402805001054028017941198101420308581081030349081c0c00d1044090100341d806900a22074000c6c0c0b401c407017a02080b00d09109070180c0007072000c401c403c40c901d882913001c01c0d0400c1003550ba65001200040d101e000650081e608240c450483c0c030110b00400a10320401c1e2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 81016503 1250 81015253 81015257
    0x100b030a0f051303080115050c031909091103010e040204200406030b09060310112206080703050f010b0c031314030613051f0b040212070905040207020607020d0309080d020a0210 78
    0xf0300c00700040e60044a05d41521191802042450154034080c4d400d4002d441e40d1600e140000300e00c0c1f00b445016040e0a20695003a03550380e480d40b076600c404200c115100c2d803038240c0b64100100018050984050a0760b038001d40b000d00001804034081a8011180742036000400326010002000c105450703041c010400106000c8a14031101c0c01c0203400a5a902c10f00d425001a180c0c4131405c25140e1030142c0c0030b071821a80d606140008116412250911507a154003a090200384480c0100784210300c644101813045002d0b4a5041c0c0d141d081c100e03a0b04880e0131141e4084c00e94030041141981481200014900410754800c07101d08945e50801054201034000300880342d2108214500b0012510009051621900c2301c406165003c00001c68200a0000c0c1248207810500020b08044202620b01105201785060350301c41d45115191010001648510314001c1d5020303030284018170251900148000383c0038460b0a20030f44e9155203805e41070034807851410400150704944185415030074081d1140d07841440ea4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 81017753 1250 81016503 81016531
    0xc031b030b011715060a03020301080706050304030507030e030309220f11070b0603070308030f06041a03070311040902030d05040305150f1f030c08070503070f050f010503100b030a0f05 81
    0x8140000d00c140c0701c10001403560790f03500e404074000c0341d80c1151411100c03e014000d20f60340c2c224050041c0103507000b0700c2003c1192090040018070280b088090302e00966040d900c0718034004443c5c90840c1c682506070816a89030204200348001580d440070300d50356024a2006842860b0f0080e52510100e0315a400061820760030301406075041000b1a0445480320307030040c0d690340b680d01d4010209103403c0d2281c000902e582c20000034000b0500e58665417500c40e0104403005c0c850400b140300c02c0d69042018580c0c1da0342640c130600052002540b9902d840001d0080548005045000e680000380b81c000d20740010408a0390004040c010b10006001e140c0850315850360b44000c90030300c0682104d0313401d4014020004000810310b071154600582228600440e0401d83c0341500039268541c2030b0300c40b022841040c1c800c1c480d807078001031910b60015107035044900080a07904034000000044d2034540c0300800480e034003400c200f400f060061038080607500500040030b00060541108240e403003100d070090f0a850004101c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 81019003 1250 81017753 81017771
    0x2091906090c091a09090711060408031602071a0a02010e010204031b0b040b1b01020d09030905030c0a030c05010c0305071a010302130509100225110102160b070204021b010c031b03 79
    0x4004c0817030710300200030f5440c1c082c02d1782c64403800c0320030a0041a071340740a80100da05110a02282da80558050001c04596a1200d400d00f40140d070354244602c500303240000ea540109a01c540420094542c0b45114000410012448035440b070032070b805908200d8902c2800701028414150030740500d0040c29422860300d26180c100342000380c3c035018a400d100302030010300f802802032180a406607641d83c80c0202d400d11008032541790140115649001d40b50081c8182061210a45014542e40c0c00b169080391007024002d080900468010300800002e406000b4108105400030384450080c81c5c05a40481c6003000c103504603c10404400c0031140d40f15000c40c01c0c4400d000d00c024010940504103a0540300060396000d51200b81d84211484184410b1903100000c1c2c40380511110f50504000504241e0075101b03180c04590b200041d0700c1c0d450090360f139400403d000b8130005040c25401458544940440c680c000500744010238203555038116404006912075442108103c5030782048265071007641818826522 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 81020253 1250 81019003 81019049
    0x10f03110402031302180106080601020316020d0c05100302130b0901050324060a02011e0207050a0f030306180b1509100302090a0503150405060106030c0c02091906090c09 75
    0x840d960440c81650700001088038000f4007058280c0c0264042e203440140746540c1805520600240310f2080410300c21000500c5662010040702d80500a0f10031049041003a0380078007599400c010401c031071030740e85820041020342d19018440e4a03c01c07903542c0541d490078203d61341c0b500d0300c41e035920030000840e040c00580c1c02a0f8001043d80c3d4017094080100403414101102c8102500320b6084440d0800760008200308000c1e410b4000d00c01e2041a1801c44070055410450441248225480a4480c0e04102c10700000039007076000c0540014040c1c031700071a0240e100c00b280c0c0d06110724041140c214943d00e4801c00c580b402e21407007070742c8001c00007000b06003440700704400305480a51031900309007016400549000aa44c5113040200502030260480346601020f01000302c41003000c0d101541e052003a400001032041c0f00303000750f50041d8a035070348070701069041e13174240b1100b5003000e84200325070352060300d1420180d0140c1c4241c500078904007401081c1480c100c41c0241081d00c840e0004462062401c0000d44510 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 81021503 1250 81020253 81020273
    0xd0504030c06050c0a0c06440a0209031009021003050108031e0f0301090203180601061704060e01050723120c1b0303040c0311060c151b03010b03040308010f03 70
    0xb507030b41c10a156610940d6030030908141d55610010b1104114080200ba041c1c1d010007214034900c140b00b0a185280f544508a50b034401190003521480c00c0d811200c41281c010b440c60640d0020419000581031005060000707050803058490400c2440da00c0d0408410340c40c003081000390030304440c1000c2042d0b50405014a031644601c840e00b107a046849500c0303182c4078000b00d040b148030000c0b541c400f94072943c4a20b1030314065881558000c80000450510310400e0b440412a58101c544580b114600703201e0101c054004020300030020384441d582e48030794086c80a02070007540d1160a4507a03490311a54882c281944071614410134080402c0d00a00c883c40d0210b150000154001044041d15a110320b04050700780c0050703031400d4082074140004405c1c042004003c80041c0c0589101d09003406080140a003405014058540142219440464070710b00004280d503085410514840224030001078203114880190b0003a845504d04803400002c010526500c060b001d40504900b40f500e0100c84c1c0303036454100d03c003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 81022753 1250 81021503 81021509
    0xf01030b06010c020a0f0812130303140c030c0d020111091e030a1a071205190e070b0a020a0b070207080703031d0406090b030c0121020d06030f140d0504030c 69
    0xa0034a100204030a68016080207240681c0101400f14107a01c448250002c804140b241c500c891240d51088a9110600c509a609800030034041107001071542c0c03001c840c803600304c400c2c02034800000c100340610134000707000600250340448010502c103000c080c0000d003150741d00100c0342c2010105100243e21076a8190b0a920031780340002196440b00d14140c002801e0281086e4002c18048021104010303605141c045140310706440d441e8010441c11800704002074850460380445035003501d49943c0e414410507484941d8064581044604e916200d50b4826510b500003075038000940d006d110040200114030080a6100300d562000d0003080340341070b20b0150303102d00600004043c400c0015010b03240f9090755021908181004006000d055900e051040092901d901a54000c1c0500403210f10b05500840031660382c58030f00488001d5940905607400c0094200c410ba10040302e8841c903001012600010482d40c0842c0501540d541c0300c2c003103009251810310004000410700100f80001c0001c500003180840c11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 81024003 1250 81022753 81022763
    0x603160503180d17060103110a05070507090608030702150c0703030c05010e010c09030515090c010c0213020d060f06020106030203060a0b0d050f030c070605040b0412030c140a0b060105030f0103 85
    0x101d8990102e9001884084904002503100710320f10590104d6002c103102400301e185400310302e101d0300d40c400110142c51584410040341c41040180c010791921a0000b082218060410340f00e00b2501d884c07040003560010b40c4060169840030400b01c09500c2d0500050190000d64022645812002c0c4491500e070042440050107000162101c0e00c1409000c0d0020360711105400c0080003551203210003c1e040c09058041900c0700d115000c4040800f60340081d4540c002c140380300050013000358183c01110042c0120758101d81000040590300b15009250016180d03020b0520800310361f880c14100c0e004d51203102544901c085a041c24010009600c0118410303810428600b80420130f0800c00c808101603502c1e20780024498030854080000d0b068022001e02181040d18040e03608940d92118200c800b8041c078002d2004100041104200300c030340310141c85111502c20305100f000400c068455002c210605a0802c1c070a13089481d000341000340c034003601d036417004090030541c0c00d50400e240c040300d1102c0b05000040c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 81025253 1250 81024003 81024007
    0x4030f02060306060f0a09031203020901021c02030f0301090603030e090f0f040606030b040302060613150e0403030b030604050312010f061e030f0e0c0301060e09030d0b130603060e0c06031605 84
    0x24407a26107100b00d4030200152007240d580d40100b1b04004000064501c000d944000b4411070000b20240f1074002c480c205c2105900604440d000d500c04001620100c013500001d506c801c00402e0101c1b080c0101860007400000000a5107030714604002e40311000d03032045244180e0b01c9004201c00c0d0324a030b00c65280c001d00c03206021131030f0b0f56807850103200401c080c1d000a0a0030407160100000c140d400a0258450710050341c0e440c072041c406800741c0c0c0685a00c180c000039030600c512014081030765103d504650090092030013050310a1a980070a0034400300380c038241c1d51600006001c806d420800b101080c010400a0003440f0703642d15002e802001a075a0340a010b8840d6075064602510718401c0c0c0100800c220340d088100000e011050035183e0b24101450064000d5091003400104040d9031180e60717110341002c40240d8588038040d42544018180100c095901c6652800d042004580601c1540041c0d44203040000340f442e05010b49a10b04819a14170500ca500c00b0400c0100d9003080460351080d03980c09062003a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 81026503 1250 81025253 81025261
    0x1021020c0106050a080c0a0e07020a02010c020d02100804060e0c0a23031006030215041d0a0e03030a0905011811040207020303040b0d0903090e0f04030f18030b0105030c010504030f020603 82
    0x1e001d85003c0c0c0c40990300c00d08190703020814110105005840200480c0e5981c946a6903484940e104101110402c015800c20201e440140d40501e42d07402c10b0520003021030300c0301129a13002071490b0407520103880005d41650108420805944540500e5401c504010182a407060700020300c0a01c03107025400340d0a8405054040410244201c040d80b4140203040ea24a07008259880740241894131060380305100d005041800d8020782004c903003e07942003545561001400c2d1414100108020b0a4410b80300e6840fa00c0507050361080c400b4500611072924041401c2d125410a1400d4542059071702d03030751054103586900021094042190840f605450260311503000c0d00020f404c60240b540040d0545000041c0400720301e1241c4d0110a659100e501c90019450720384040c0710f52141c4c2206c00c0e0111502e000e000c40e010a005000211080c800761174612443c0c480c0c100032820202c141d41c400c032510f6031580014421032034240902c4064000c20300c4c1c61414585143c0b00e40002540500c0040c0c01240c0000105e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 81027753 1250 81026503 81026527
    0x3080f0f040c0b0714060a0c020c040e07120c0b0a021501080f0606210a0501020d0501060c1106090609130c080610050d110421030e04020f07120e03011a102102 70
    0x5885504620042d100907241c01a01c0345c7c0900000340d50580113003e1a003800c41d0318a001c1c410019415480c400400d40e9500f000c100d0180074002400a0307411441d11000062111100b900070090101640d02030000d01c91110550301201a068000e2036264001440300240c1110008a4644c0590115400b20810100008940400307800000c4031f410750180307040c01e0040c400150014040b00300c841c103041001d41c1c5d031410225000c0c20a40e078010701020740e0100f95800c40c682100641800c1c0c10013070a2500d0155000002048003400002c10401c150b01e6800100b0001e4209100c254002c405640f0b82c0808040640002c1c03030340c440c02c1c103025901c0390f50341e0b0000d4a5603100d0054034003514001d03152608803521080c5000f5900c03540c03007045001488900c3c00607603c1c03c05000f555466074108162905100c150394400a2221148000c0130070044400f01d00300c0d00382da00740151042040c0480304050100c45510520400c050036005a4051050810303081c01092000400345104400b40c01c0010307164400c1c6a52 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 81029003 1250 81027753 81027773
    0x507020c0907050c0118050d020d08010603020f090402040303080a06080118080d090b040308100504090305040302040504020103090803100807051503010e18010204030312050703060608070c02040b0a0303080f0f040c0b07 96
    0xa13640a98a00203005400c40142d00300000303031070300400032949580c00703606049940325080703480d100008403118010010a030003500078000c00040e005100e4104a07082010a0890300310740c0c01980015400130511106030401d104200c007428882e4001e200300382e04c01d07041c01441e190203c0c00802112002a2726918800030760311114000703501190341ca00600b490309000300025000d4070b4008041c00d20082c002058a070500c2044001c139455150181064a10303000c20008000091040c4d040c503171100c0ac0400000e03a100300452040480b00740001e501030078414220714001c2150000b6018184100e0100d44120034182683d04480c18004540c0352955030920310317541c000414007982c820b58008100402019088404410300c51140b40e401c20095072000822815149180f040c03101003000040400c5030039100d4240200e81038000340012403100280b02c00b01e0b906480f1548160009040c0b10305100c800760500e40071540140c0141d650034640d0401c0d03120101040c40500c5082c0d40c9240c00100381d03041081c0c80c06 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 81030253 1250 81029003 81029017
    0x50c0f0301020c03181801080607052505010606090b07020604140a09020a1d0d020112050a060b070b1509040b070503072c0a0803040b040e090102070c0f06030b040507020c090705 78
    0x44d240c031130072529002240389034080c416922940800c0c04a0f6000303030381c170902d49048401c024020f210985400304103a50039031100c40000205150100d602105000607400160800c4c822800011154030b00700b0014101001908602c008550800074403008d03944035002e035403c1e254840e0156040040070310001d0000a40c50380940c41c81c50020522010302074102403090102c1100a544d00c031490200b030200000091000402030101d6988800c007010302041c2e82c0100d40c0320700000c000140541d200d01c0e50b07491035042003e044484001c1c42080000c6000400003580b1040342c10b58150130306003855038440c103001100400c07880070090003100080c00280300741032048a25041c2c0308650f01150591481501303909036544800d00407260900001050000081110202e980c00d00b0500d0074a070a016800503484000342054800d59000c0c40404c0104840070210001080c0d400d6090000c02d18201016054641410085214074581410040210b0b00400c102588080132036500c038217542e40c68030586041c05011 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 81031503 1250 81030253 81030277
    0xb0901020f070605030405010b06030f0f060f0a0e0115020703051005150901080604050607021c030b03030405090c0a080c0901050301030f06140a0c02120a1b080f13090c030603050c0f030102 83
    0x80b40040c40c0d58210008501a034042c4001380203c0c0d00b0942030014500c01038860301030000e80c13500080c140341c0c0300e1615141c208500419a10b006202080040e9200783c0ba504201141300b1010010080507990741c1c0484420089030020b410058a10b03142c060712045040445202a51641e00103120321220744512548031000418403103041d611030796000c0e50342c182160121070610544000c100e400d0b00028003480c10300c0b201c0d210f0f00c02003038031150210301030b08a00c003480360188014400813401c0e40e25804854411400082c40e6502c408032400300824981000c0c0c20380e540302c04104007030082ca0341d200c0100d80c10350b0b070455400342c801512031502c48002c1c24482c0c0c5080211500354144048052030307800c03400d550040756084540141c0780304c0b0030b0b9085114081040012844501004803060341800d10030146600030804d4a06000810403440c3c55a440255404070ba550364070018803a4400b98030a440c0890f409280401c03841d4296911143e5904402151600c02c1ea5403084403803244d07500f50100c4036844900 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 81032753 1250 81031503 81031513
    0x907020f01061202032109040b13050702030324010804080c0a170a12060b070b1b04031b23041d0109080301030614070c11060c060708090f03130b0901020f 68
    0x700305000d810100304500305d10901440444228455800c1606040605140001071800b40c0034001c203c01010b00a820a80007a1150380d03410400c2c0f0789204643c898903003034018561f00d1800701c07041c0c00b0250305004500b0b0520a609140d0540b640d10036541030340a50b0040031150740702c500c4208a07150031440350b0010080c80c00c002d8803000c6165000c028010300c1d500e54940c400b201d0f511141000540d00c0e1070082c0e020031201840b500e80803401000d11983c11046065481a85010b0b0802941c155030044d001641c040680c0d00d034000c0c034000038800d000700601c9075841080001c0c10084580f2480100c00c40342e18452602d40365290008000c1d113084004481180008001903419450500c0c0c281e04248002d03500103280c003106241205825010b0761080a49544984141c030710b5584d50b806500c138071040b09400c40400d1004400002040100b18000ca015445229151410808062074080c0f4001d081d92550002e000004041e0741425511082d50021a40b6507110101040101d141c40c9012030710303c056100d8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 81034003 1250 81032753 81032759
    0x20c0d0c05060a0f030b010306080c0d0807080f07110f09070c05031b010f05060d080a08040f020d0f1704050a0e061302033409090504150e01020d0506030d0c020907020f0106 76
    0x84001041304030750380c4007805400e00540c015421070f1640d110b29841070b0400050b541091a025221203d842c0c480d008903824842942c42e4846182c0181c1c0320f018500500003104018800c0c03103041100c2188049900c3d51412000002152000700041c15880910207201e0389401004800d200340c90001613880c3d030344049209840e540b503000e4989102c0f440052498000427802c282401031481c1e0020780c024403400c0c5801c001a10495480000500680301c82e100711900600590724500e100903001e0042d510300b40e40c000c042c14182400d1103030300d060f90f4007000c0400040000340c84050407401264520615035580d9a1580003207100f0000d1050101001d6100004100609500c901c21240c0b40a05034800c00b4502c0380b504039001c0a80701841d00c1004240000020040e1050320b4000c958003910a450b4046440c12400d680d006940c0004200400b60f5000b240a0030700100ea40701d0380f944944214020110740285101c06080306084c41c8003e80528505800502c81a000300303c074018000019008106d95a5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 81035253 1250 81034003 81034007
    0xc270306150108150303030c0a02010e010f020d0510030203060a1a0904050109030210061d04032601051801050904060213030f3008180a02040204091d070303020c0d0c05060a 76
    0xc0000526021600800100c1c40120844d161042d05107400307170040d440c42d1202880c1c002c0382e800840c002001c540d00c03950000700c509130038082c0d1046002000d0000d622210304020913415680c00804811002284440c01c001503940024403d40220b540030f80000c0d4000f5800380c0c508842c481090054216030b0030070074403081010550018145034026402d4074643d8044a941c40d003958240e2052000301c000d041800850b0044a41c01660040d20908005d450f80c4000440f040750f02c1c0340f2100c15a00103e141e0010040382c18443d400340300960007000804280c1d03043c000007509480000c0d0020301210f41c04561840c6100b5410f00104c06035800200c0810b620029180612403010b0303c110080000006411303c038a14034519032020440080c90b01d44c0740865070386400c40c690700c502100c904840b91103000c281c007016031220b200030000703044010000306100c030903000211711400d055070342c0c000d041d07002240810100ba4045444040719108071046034414149041c220042e951a82240f60310030800221174000d19 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 81036503 1250 81035253 81035281
    0x18050303281209110a12030f14042601060603020a0c08030403050c07090f0c030902100e151201050f060f0307030e07090c03050619060c140f0115030c0506030c270306 73
    0x201e412240202146d885d248070406d000c4020000070003050006042d06610f50151801d465a00601e04829013000e84c0c9030010240c0030990751101000705004407168049001c02c0c01218040c24040c1001d501d800d01c1104000e0240000c2d68020300880e85c00b00c00718081500c10011194100e12580440e00400c1d25085101d0003040324100045910b0300d01008003050758064041c4000c199001001484200f01500701a41c10088800d003099104010301c1440c0502d42074003010744841103819046071040d605007000d0151607075202c40d050b40709201c01c0c00061480790b0188222913020307009240114010780e049100c01d141030055000091054103040703c0c0952643d05a0001348605000c07145130110715900c1d680e1007000c90050082c0d800040002c00d6100c0400c03500201441d80184000071610004c0308802d045007124241d0403000d0001034003942c1042808079030200070000e010229512840e509001c8200001d41c820b48a615210008a405107510020b10151902c5446009401d80c0c1c100c4c60990683c1c1c10302 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 81037753 1250 81036503 81036533
    0x5091906021507080114010305040f080c0f070b1305010f03060b0a05071505090d0f020c030601081f2f0d090627080901110f0304030318050303281209 66
    0x804002c0002180d0300d100c2c160540c100c074a900104882401c40d0300044019080050042c0c81c10a1074106000c0015860030003480d030034004da0090034200d554440007a05000c02075011141c064014410680c8140c00710300e880080315070900300b03d030310307000b1440042d405000c4660103522400c00204028030480d03040790041100742d100f00f81100d5141d0304180e060080760401e0b1340c070068641c4250700f100d10340c0740655514400541c403030045604121080c80060300e0140240c2103910150400341071128062410040b8048407003c00c5402c1c04454599501c3d061100380600a18142c7c40d00c2d070a5469402404e0412150100082c002c244000e1a550402c0030103002400f0800c000e104000056000f5007040900490750b80781c0c060207091504100b1401114061045140c4004902445000036440c02003000244000e620903255201c410002c03111400042c0004d40c0000e000e0341082208004640210904203040800202d94a0f01010350400888250380b4030a08110820710342503806c028050f01c1c1400e0168 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 81039003 1250 81037753 81037783
    0x6180120010b04060510020715030204081b090c1603080417030f0402030c0a0302090c090402040f0602010f0c03090b07140d0c0c020909120d11160b2a07030509190602 73
    0x3c9995910506c07082c08a040074140040c1c00c8601c2c00c3c820b00788103210108520280e0f150150600351280c0c821805d100403440c252104090010f015002400c01000c1c4940c8500380c001100e090002c4503500111550140100408014440d80050300700410402024210b90440c7c14070750b2289400220240c081100382c0b020b80c4070b803043c1591103003a89004002c0006603035014013a44480d8030f5107100300d081030300240c0205600503002d210100e11500c2c291110741c000c107141c3e400401d1380a00d2081403001c5a01e2056210304040c100000c40020640e58050704c2e80000c060320b00891030315401d20781c000c204c0c01106e8089401c107090550300e5610640c061407220741c4500850b20054a83c6803060815580c21252501e070307200701003d1104402500465109580300c82010b05040d01d00712202118559000389900100e030010390882c03e10500a004041c0880c1000303051a86480d2421407946110300c074011840001d0030401c0010b5503a595440d828403c0340d10494012569524544851020707495461260030404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 81040253 1250 81039003 81039011
    0x507020a0302070b04080c090603010b060c06102301200d090608090303090703140304030c030303020c0c0a0b03060607020f1903051b0a0605030c1606050610080606180120010b04 78
    0x280c0f0130b948400c403000c85102070028003045409401f440038403800104140c0d459565040c41c00c0f096211100102100314009010340110f14010b0f0b1130829080f1140c200440c944c0000c11a4158600e03200704034407090781d0034204503030380c00c01031685000303542075003040302d942800390300c8520405036044200355041d210707903032288281503403501d81040d5240802c1756a0340b92030f0301c07030001040840d46a0b12121880ca143c2c1d815645401c2d182d844954021103254401c8000036400107030b0717148109080c480300030761140440e032001075149000081d00c4103001c05000c0901c00c4038001b49000455544071281000138102070240f902c04181c0c0416040c1d5034905110943da02d00419551110300078401c001030185080082c2140b1003541010811151074000804003501c42130104107c4118820b03124078561418031581c3d010400b454108180300c0601000405101480801c1c4280101541c4002c1540c0c800071448100d4200102c030b00004035a0344100008440c005003072040061500401034008001030101a01c040c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 81041503 1250 81040253 81040259
    0x418140f06060702040e0102030621120a0203070803101404020a170603010b12060f06090108060c0708041707060201060b0a1e0201060b1206010f080c071112030a03050603070b031308030402130507020a030207 91
    0x407200e82e201078206056078001343320700c0b40d0341411f010161984040038030484c0e0400340141c0d20310f0001d40c42500d65000c0014406001c00c400f088851042409440584081d070520001c0b02010380f84490503e4100444c01200000580e40c0d1400d52221064280003400c1026015003c9501600c1e41400e0b00d100710103194400000d070480c10492241812540c019001308090754501f2041102500a0741088401c25803c000c0000c0328002000c600d003c0c40440c0025044181c544100603003124140e0703101c10b03916a02405045149504207501120b01e0002c541512842120b110007280104100d421803440f600011404d41c01d103141401707607a4800c0d0002c2e200d9040141c0000c1040d80c0b211012240b0803402c1e4010001741c40001e06080351200c081720090091003880c0141d0552504540110304210000b0b41d444c8104080b0f4603041201c0340080c40034580d05803450030000505500c40030907500180070240000080340031900d52002d4203d12075500003080120f8201a0306c001c2d26043c49801c00d40062190102c08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 81042753 1250 81041503 81041539
    0x503041a04080d020f07060509150f0c0403060f02040504110c061308090f0102160b2206022a060d06031a0906070f0903080a02030418140f06060702040e01020306 71
    0x20500580d00030302903500f0f0180c03168500c00658030006403942c1c858000e00a2000284650084a0003100e00c03201030710101020302c072001c49040008152203d8001d00f0307000d002d80050040c0032101525080000410510030f6026030070702910913944060340143c80d04018142e1608650042c000c4810b500c0241c4803142c441d140d15880c0211298000b07000d180041041c0360040c5020400d06c64505018019141c02d44011000305401000076031060b0309502c0001140081800940c100880c0604180c812050550510034000d60380c402048109020788194010b0400b681c4402c6045805050000c02d21562071203080d444102070071b110b10084a450072850301401004514000062140c46810000c0c003666941140c11030f034483c070511322602448030803a0040003041540300207241a4041e60015a5624588090f49041800708405442d030340f4685801030000c10740c60060640c00050701189644981c44080018482c4c0c0b1454000035071062030000741003800b00c41034024610482045800c2c5a0403510140a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 81044003 1250 81042753 81042803
    0x3051002090a09150b18041a01030b2709030c03040b07030806040c0806061309020c01060608010608100303050310120f02042306040207061806090b0a020a120b040e0a03050304 77
    0x19001e0780b40910003040c8140310000010300020310140d215032203d050002c010602300e8400765461003c0100c2450020440c0d40c150003203201842098400003440040c01422000e5204a03100d00e0f84801c0110001c105921000c1040da2490b44001c802e60b5a1503070384083c1d0002e1548400380450102c1d0b10440054400e1800e4496444062144c2d115847c103aa244400c11541ea80000c40340f0400e004842e0300481c92084500c0a0400c922100c0000541c0c1e500b800c1d8080c008d403805078030000811245c40100301d07001810039800003c0303d5050900c0c07512038540d808000b072003500070f400550070441c82501820501c594201310007801303402500c3c104152260402c0400c0c0ba808001c03201c0f5111010352000c00c0c41c0e03050580c018965280150000580840c898030140e0040f100d1000507241603444000c4038003400390029105800842c4050214680f011052002d02881841c1c2400008540d40f940608260b4407182c0100c2c160540800030b88803504203928024025800544098500502c1420141c2440c4001d42d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 81045253 1250 81044003 81044021
    0x190209070e06180604080313180b01050a03020705070b0307200708031b03040b0310080d02010506100c050f0f01140618010e0a090803070806030f01090209011202010903051002090a09 80
    0x5018504075068079211940803c540301103030404020070001814540038009001c0c95a0000b840c40382e0503190040140041003240f20400d40d00c0d1078a250510700e680c0050407603046c0741090401580321601070404a0030501140d100d018010000005c00003415031155650401e845803500381c0e120503500b2100c1560715225402480071503031003080b400780300408040364030000d140f400007100e181c541c85805e1500250410703101e01280741d14403001400180b20a01c02d000c10880310748002c1003149003960001f98003010b041e800c0c10030311103600c00c2c00d400d000c014819440030004840465110100c0b42c0c1016009000342c18200f510190003001040031031401e02c0c1c0381906c010000254010513400d1409076400342c01c02a081c43c1442d5030b0780c83c000b80001c3c1c0c4c28010f1032248466442d06800d85c03038440107241c20b1003002085860a139240000000041e90360480ca24150b0b180b0305c05030500c4400510050b43d00c130388590005030962040c60280f918499680d001000500d000b03646c0c28021035641e4000409980f0941 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 81046503 1250 81045253 81045259
    0x50a0b1f020627010204030309080609150f0402040902150d06060801031205031f030305090406060c050706200601090c0f0f02060f150405070e0f06071e0f05190209070e 74
    0x41101c0342c4506140c000215940114180405403074010942246d00a51049021070b004503420071100f076040c00943e5120b441a0b024080e01c0010f0380c24020580c070f0003440503812051040201e41951100c2c0d02c11415264003600e1014528030303102c1051055040360300c09480003402d10801158291203401994100c90340002c8541070150342400580b41a00000d001c1e4a800c41c1c1d0388035a84440c819a00014001d500039144c1503501e0700c1c544e00b804107540c0c16803c15414070440c0c20b1400005000080c088085420500d0280e07200c4100500d8488408031100704007101c1c1c4242000403540068940c4190203c0802e0786032290100700310101582c81c1108801d418000d03802c040e00152900c0e04050a0356881481080d4400800f540c03030000408603441510440001100b6108650311801c1000303041c02c02e404210f51590a060142c0d407000c3c40352040e8500071481402d1024440100082c605114386142d61102c15200e2070032044001c05e00da443c0951040c3c0c071800042e0041002c180c09031028110681001d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 81047753 1250 81046503 81046513
    0xe010905030f031f060c0314030601020307020103090503090a0b040806070c0308040605130b01031208010b0405060f1608071a0a0225020d051e010b0a0608040b040c0306050a0b1f02 79
    0x12007040541da04002c120520f2208040501c0c0e48413072030a9001c00180405072a0043c42d1441420001c02013040c201c580c200180040081c0a001c0c0e030000180c0e82e281e41e0903e40410702420741d15045e811070050041554000d50000c0340842c4071012074002e4410b81d54543d048600983d510f80d011114000401c1d0701070302151641c2c2c04100490700b95081950312010300410759018841954448003680426030061b0749036a5290910304006601098070307030040404c00e8100d4141824107001505030722449024050307280b000610509110400f594080c1c110f80c20a024640795038107410001a80040869074000f61030420000a02320340d00d5100761215600035243c2000b04402a0303144101583c01701c54144e038081328141d0000002841080381540034074819082103e08000b8040305420350705550380d8188103e0041d1b009114455001d0f0000ea03009400090101503500c07141082041c40d103507a0409032449042000f003005441c0950011115200207440140e22071b5440da04044990014080100050300700c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 81049003 1250 81047753 81047767
    0x1401050604120303061e080f0d080a0b0f04060806040c0b03100506070302011b0f0905013e0a0302070314190210030605040e0c0406170a0609031e030f0e01090503 71
    0x20309002034102e14440c3c140020080e488000c1d5111400c0242d1158504603a049424000c805050040b808100c019000500e40b4035100070000c2c00341c41c002440d010805035500b01c030120541d01c2040400000c00090401c010b425220a03405440c1c4000b101c0035241c003c01a40300044406a07442120b101f9034801c1800700d005070a04003000960b90100b203050f411503403640100c000c1990b440d4244010b0070001c0d2654603060040c3c00700035141c100d1035030043d41800a9120140c00a40c4c0e00c51103003010f14099030020940c1d00880c1412990713040805d03103d001d0744c462030a080e4200b5400050101c1582e0007080c17084002800c00c281d42d035441e254901c85030705144811140c0742c01418809c0745902d14001c50301f00820300c5034540010400300c0780c40409020b400c1d800744503006a80d0429104500c0948018100c0d60660780f208031019a0710000303120002d1055958003244028140b240d40130b1340c40b00c1070003c66400d08003940f002c0140642004603030b42411740c1c0303450a41101c20300f05204812203160301074047e60030405 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 81050253 1250 81049003 81049019
    0xa1107060e04051504050f07080601050a020705041d0a060b03061012030e06041502030403021305011d07182403051501110106120807060b0a0303050d02030712020301181401050604 79
    0x10020b01180c134614840c00501402d9a100d0090703030311a400711b2041c2c0103c0d1a002c60020545040074200c0345c140b2074104011042c450380420141d040e928240c80c00b25007401000f0343e0503504203403800714000d80d0184540c08803c102258204206004044089480b61385490095800c0e03c106031040b140150045481d400000780101d100d00c1c111100103003401d0070581d60300300701140b0a140c2e0b4114401604009003d00462901c5400d046c0110040c0780100801c0d03050404000541507411000804009060001842036200c1e00d44040c541d401c0003440019142e0354125500003070055240c20f20510740c16000c50403600c1c4240301d85807040361041d55940c0448200c0380152440e04d03041d84141078a54032040041070600040c0100c1212070310915407590750b4241814190102c0e4070441e4014810000c0c24030810100b030b400f41c151868144c940034010380d65100e55505a5170041e40090090460380040000110020908200740420811130414000300114840e5103a51318070074021260320036410701091100c01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 81051503 1250 81050253 81050261
    0x30501050a050a09150b1606110309030319020d02040e0403020607030e10110412080702150711060306010513060f2703140f100b10030218040b030a0b0901020a1107060e04 75
    0x10300d0074002c03a8816a240d01c0341b00c4ea107074090340c405110502c0c0d0400318001c0010902c155428524608032140c110f050064000da180d200180500c900b01000d030890001e22103c03030307049880d01136019801310340e129510b0299828100c3c048030150b000d4002d2200151a40703029024a07250606800c000d064010300a8040c0310003009040e0f031840b410750041c400841c224102c0c10030400c0b9079000c9c0c2403140d03e03014280f04002c0041140c140d400706a042c02d01c041c03800500426200c0b540607900b04c03201501e0755a50801210030303004241801e400303500240d400140703c6802481c1c002080300c0d00c1e502c000b08032192011402403404040350f10408954500401c2000c034280d559950240c0c503616040d034192080203500240380074205518070071050b551f0312080c58146088408000f44000c142019801c1402211070303401e01b103030040000da02490700d034a8244c076a175509001c844038032039010710303951414100a00d6240c002d4114084540105450320060103035800c00040700300894949694103103903c445682408090 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 81052753 1250 81051503 81051521
    0x3020910050613090b0102070f050d030c020409120f170606090103231006080103081b0309030d03140106020106050a0324020304080c010506010318060e0f0102030412030501050a050a09 81
    0x50305003004041460341d556001000d240d2004124910200d0034081e422040b1910210b049055601030703c001c00034251481061b0003210b80846a2215100d05030038251440c11240400030342c81403070041d4410030030150100d0512032012940d503041da04102d0090a441d0078200704000054480441c000500d01c0c9004001008600c3d818074000c24040178607036070010643c0748109074690341e104c1d07a000c0100200d0305207510002032400c2c1c50300301d10075403454440c5e1030148203003142c101886441a410700107e00c0304008490041d00c0c00303070441e01c4100080d48010000c00c14602103a03840c24000380001030b035903c1401244142c5600400c042240d52665460030002039503000b200030758103094108440100542e1019501c5036004054041e581e50841080900b140c000400140c14540740c14048081d141602040b109140c3e80308600291203050506081d14090480c00110b00f00d40c000020003042101c50010b1502000711038800748510b9880b0010000b410145000c0c0642040360504100480000c0d90001045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 81054003 1250 81052753 81052771
    0x1410030204051503060405060f0f0f010603051308040902070c08010e030307110a0c06090501020f01061a0c0a0b100e0a020c03070209060d0507030501060611030304080a080712061d0f040b01030209 86
    0x103164a9401117800c0060880b01550580c02000400000c006452401030740701c0b4803a00e01c0600361404042c2040b0106040c0a05030405949000194820b0040001042e19580100740c42d40c45969038402d11003e5800b4490449644200000002e40340303205004070038980b05218040c5096994000c5c040f1159000e685403c9550b1003915001800715a43d003504501800c415a5162101818130001a280c000c4107406104260300d40300b010440e10980302180100d40110f0580d642e07803110070490039442c01b2084000030b0002c4504c0001d001e14209a00e040201b00c5103c242c40d1005643c0d010000d0040303005d02050381c50f02d43c004021500051034402241a8005070080804030102c089880301880d1103455007080b80c8903075440100348611904506005170510f000f400461070351806948010703460091001000512249401203003140740190811320318082c0c810400c0000a54414074041d42d008400c0071008522084008281e42c1c0e04090015849240c02c803078460a541d03c1c680c28050000401020022 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 81055253 1250 81054003 81054031
    0x20f010909090305041d07090e0606130807061413060e0a030614040201030608070b0706020a050f07050d1404140904020301020d0e01060306111903051504020f030703141003020405 79
    0x80003240c912409002d5406540e07150b464500342407640c1000550fa10790440811303103290030080c00b2944090050b0944500313020005540e02d910f408a015401401e80c1ca4250600d0b540300031502c2440014480100d0b941682e54094072500c0913501242e9101c1e0140c0200c0001d00c0c07030400c0c0704640c02200d40e1081c0c01006410350403074540c0c98132103e007100c1100f2400c0141300c28070307014441550fa05000d01000380c524030016001851811039008014415050000c0c11550007041c0c0f0300d180340c06030095038000140c00f0b441c1580c850440c6411500c0b8041105160041010350a0103c4101c608509481c00d0718017038101800c03504901400c00031014001482280d156408002621030400c041c0600c1d1450903c5c0000400c0340360551030000d068940c1c20a064004070024003807003144400800240b0000c140904000440343c0703440013400614410701c04075540040c00004c0d003020140a41d402988111295034082120480c0c014202c0024181503814003094000c030b4405201502e000c0d4411500702c078010308808 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 81056503 1250 81055253 81055259
    0xf0e130c0b030a0f0632060408061003060f02030712090609020a0b04080708010504030806190302060403080304150b0a06050c030d060803072105032404090503090f01020102090d020f0109 82
    0x160482e401110089080780d200e40c0c29848035038180c02142c010302410106420221981e0038088000000ca80e000b46170146c408015000c241c030303080101e40c0900070f00003d88881d0325111140070510000e83c030044911a15100843c2d40c400600d100b03881c041c64465035011580050342500700d000d0480c0800941d0304030781d84e940800060355400c92131001449610100f98031980f80241060a10000303620840b260307410442004002680030307580c1c59100b8021a52003611a5910450445c00440f5800003904048006404003c0c0980709011b144501d100328043d04402c50400c013000207a40e414001e5903000341428001b40722450244002c3e00740c140d5000d00712800c144603451180103980310307540b04846a410003c0d1031410b00480034100c9180d0700705984403030681c01b40d5038402421403100070044460100e0090242d00341d02c5d4400c5100030300c41c0707000f01300340f110048604040b07071207502200d0700c20702c01c45807049041e0440d4018020782e00d4600004140340d01c0c031901c640a0204a1a584007041d040280c505804 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 81057753 1250 81056503 81056519
    0xd0f03120e0106060f020609031b0304211401090308010302090c160602070b06011d04051012050f1902060f1e0c01050f10030807020d0501151e0f0e130c 67
    0x8075024900d01d0001090032480c081024040514055606046400036401c0000140380001201c1400c40905207401400350461015411030141d60000d501d041e03c0d611100070b100141c403884412140c015040000b010040f030210601301c0e0800100107020a1006004201602d44044030035407110301e03d0903051030325014104034400c0604444088518640c04143d0500b8810200e07152a800b000a0074955149008400100010b54440030340c9441142c0319030004100070001a1040001c000c11405540404400c0c500365407103056030407219419200d40103c0340200d8140406030103420f60050055490103600a058140740c0d8080e4561943d100f011034501d0541c143d2a6004212001801000203002d090000c0300d86080100075150000602c0031000500205000070101c90200758104d5081c0816282440c01ea405000032000c035103c1e17040c1c540301c00203601c00502a40da00000480c542c2035111611100c500b010b82c8014081c0c00c144820b2100040c00c0d070040400504810303170149000c1c1480070790302c241c9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 81059003 1250 81057753 81057761
    0x405030a05030c060a0b03100c021504060e010c0201020301060f0c051e0601030b0603060601091403010b0619020c03010911010f050c0703150506010906022a090a0e1603020d0f0312 79
    0x407140307548001090700c03c12400303001c0c2d80d812a0751380b40140102e45140c00000c1d9500c1d0541002c40441303684008e60010540200058142054002c21440b13080c5024240000101040e031884c00e0b4950900100f4004c0500c1842281d040e50640d0701c81041d0300c9045a02140c9050100104079031512502140740807040c0841e5072581b030794050b00014800c5605602e002d4994141c05070209010b6400b000a0000c960380062080d802e07581414081031070081064000384c00341ca200c40742d4a800501c0003030030100c28501c6441d03001c6521419000c0381d07018104071083c54221140210041c10745490b000c0821034a40c400c205180301820a854440d00f0103e014901509028040e40100c4c1c0a003400d960102e0002c40354024658003d4090904503005441c0c4107019403070f4541c10604a400d04116080b9800c90034180c02070600484d0041e0074482c59151000d0000000c044401044646104401c103101e0641072030340142c401d60360702404981c144034481d958030a0050903207100b1002e001044a80f402c1c0e501040c45 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 81060253 1250 81059003 81059023
    0x10e060a0315120819090302010c0803150d080c070503070e0c0702121504020f1f05030c0d0603080703080c030c0a120f0e070e07021b061602031203010609170d0e06040503 75
    0x8003590741c4d5040d58819170215045810b80b903041c02280d2404101503a080390200ea00c00390405240742d5250785c0c0c000500d01e070107440078a0700c0d071000c542c05120013848180320140842c1200031003200c00c055160303000c26560351031034802e1003881c0400000140c1c01c00719040203045c8261014001b00c240700381d00c840c441c1c28608614104550b00b05088104020f51901095084a6090990742c00d101d112800d5252a01a0300b500801d0081c8040040441c3c2080c50300c90407104540c44294040191300d4407894034203016480180d003900000d40b2800403480005901b81105cbc007d88654410525086038010305951a040070941c99040703a03902c250b034840d0300c03100b4043c4079007003520500600b820908205d40201940f4014201d5002c5600208500c00f07402c075905a10094480b04a959a8841102c4920400c0240160800035014041c1544100800400e00c000d54180d031045d4803881d0ba20b41c0c503250355190151b402c40220f83c059004d09000c02119004c0d80c0d03180500b41028005034500783d1030b000030a1a10550358 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 81061503 1250 81060253 81060263
    0xa030840020901030311060a0501060f2a0303021201060302030c04090c050403060e0d080903160605090703020d1a010803070206030408030711030a05040314010b0a15091a09030c010e060a031512 85
    0x20b54080c2c40c44e8001c0c000c46908c6854014100025418500000c0c51000c490204200f80005445400c2d078498a0b184007401080400c602c50038071b412180b07402006074010805011548040740000700706540a0700a41e8418020b0825442c1481d24081502000d004807220b81c4060104c2008040081030395401404d80300f9403424010f22080040080c014a44480141403003c190410f221000b11140e0328040250b90b51740042c40420340313440d20b03c0c1c228105234407684003c0d1b000f42403250f141c0c100306000300b00c3c45641070700303550401c280c1c0e80e00d10349a274491181810007035008030101700150000d0f00510107160032002502d4176540016072480e26610750b502180c1040c1c04220041810400c200c1d4221900403101d141c500203100d00c00314500491360340442801403003040c40090078092403003441030402e240200100324580f552040b42c0019000142c0c0043c1901c0d0081c0244c003901605540100396016110402510b124508036a00404030010704012512040044e4250030018003c41d6500141032194052 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 81062753 1250 81061503 81061517
    0x5161a01120b060d0312090203010f02181503190f0b0a140406090b0a030f02060f0a0305011401030c08010b0d09020603040b010509011224021b0a0308400209010303 72
    0x58107141d00400d400401c181e21451132080c428002a9000440e14100317801e800e4003050160440c40040d02400c262640704004d50700c00314181d8001c00d800c80c0c0401240718256909000403010800c07416242c030044411040c18541c0810895000300c4030340c41750711a594521400a2181080e01c00141e201c50164010024203407200100c120502c0e0030300c9072500030041c100f810040c003c409400300e00381064a103c00743c0401c1d0301140580c15034882000303e03012000304842080ea2840405000b400920080c0918100600e58920011203540280300c0d01ca0640c00c182c503803c0349030f0303e002c480712410f52001c180049000d441e03821175001a22120080d6005071303c100c81d600c1031903041c0010710200000c143c0c401d402c910000c0e840400071815528440d011988c10201d09141003a240c001280680b04041c0b8214844510001da003400c0c05000c61070481584c800d0f591202240c6610820f190240b503000c2c4030904040408a000b000f030310700f144400d85034403031104070500307220010b0700000d0b031509c4268070a502140003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 81064003 1250 81062753 81062789
    0x90b120a1b020a0204020702010201060e01030b0108100209091501120606051e070807080a03140c070203010b0108091f0608070f060f030603031202030411030102040909020405061005161a01 83
    0x1240c01811501d034844100d5001e4040c20072002503585215041c06400781b0341c005031000a69200f900304002600301c02c2a00c4050b960750b80383c441c0102d4024401e11044e40a4038440500700c2c003180c021513201c40390082441e0010f4440c582d00007030022030790b1182814801840900c640420184c01480700814450b00c0b180d444856048010401490483d04240026001c005071b60003d007901098441c1c064101010644910544906038014002c6803024000900c0000c10010500403103001000c40c10300c290003d00640c2c07a050010b541001003550010441d40011208404894250000001004180a01090440c0ea541032242050320315040a0070b1214055401d00256800102c2040c1c01030741c40c5420040d4528540f002050141d0102d8613401094000001c1340c18040c510030760002500004008540c1c4558401d0710703a0041c040380b8802c078007441c10580007440d1803800c0c40c5204222403e03915400d28282c0350400b11514406e15120880304410134410a03d821002c140e4042c0c007800e01e0701d841030241d03d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 81065253 1250 81064003 81064021
    0x9020906060304030212030703020706020d05010501031404080412080d0207061515050301050904020d0204060f181107082107020a0309090b1f05070f0b04020907090602060610090b12 80
    0x600508490181c80100188400203900040c0d0040042405074919140e48501c1003c0780a071141c414045e111a00120b1098002c02c1380d1360185040310800d890801c104003d140d1041d050220848001e00000e00034402001403405000070808010f2045800a140000544400040360882d0205841075981d4100e21504c1c0b444511481000e07141140740c2e010101640c0c0c200500c81d00c0140107a44c095040c080211302191103000500e8803207a4010414040702d074480c010102051f1491040100e1480c1a00c00031000e042c503031242c80030300d89081c21010714240881e10b40250301c0d409980c840028000c1c42900600403d4080c800b14082e00300303517016101200300303410000c000b20456003002a0645c41d00255a805a85080342c000c030419020b155400700404091040d44c1c54010114003400015801c1900020030811050311803003940308a031440a00d442d82981100d181d0468040c02c40580c0c0024040750705071402000700c40f18000c1c2d0740f60145003140c64410400c3b15800c081c072903180c880c95240034450701403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 81066503 1250 81065253 81065269
    0x114070b071b200d0819080601090e010306110702090a05011401030212060d032a060e0304050306010905041110030e0106051225050904031101110a0c02100e040f0902 73
    0xc402c0d401c025903592099142c9108503124180e03406002c42c9002403681543d200c0d01c1c2103032a4a50080c2c40c030358031b0f0340080d0581e1610b0406802800000360240001640560044041800399111102011203507070840d9640c1c0f0003082500c2140110304000d01c08800140e032000314061003401500d1000c03406501d4490036110702880b807403080307040c9801404460101501082c0d83c940c03218045400b0400c0c00e801e4101030707424480003203000d44503070701c01c44404080c10303807400800c40b00d6031191804115130600c00d2400c070344034010360203010b50603000703000100400f49554100c00c0d00325004501042d0740103000300004816290317022070b40300802e886409030041c05000b1f02c80c280c010320080e20842203200c510319500703445004001201c40708034181c1c1d0812803d00b1009030340e0405060060314003080703824a42000b40018041c100440303625803c00c0080401118070000b0750b07036628150b8485c0b000c0d0364815400c200540030903030302e140e082207405070300f51403203695034010b00c0710784140c45c4000a101c00703182c01401190 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 81067753 1250 81066503 81066527
    0x806150a050a1803080d051302030d09030213050403050307050c0f0307060c17070509100309050d05031b090f0f0f0a03060605040e0703050c0927031206091b03060114070b07 76
    0x200c2c0010400c00210b0700c171108581642d08281400202503840d0210561200402c14004e50107214240701c0c3c0034400e03004003410042e40e000729884c0f146c40d01c80090420a450781210024000b60061010a0300d1500440140401c25143c2c416144103100c0c0359005861600942c07403c1d280c0a442d018100302240c0c10a54841c1d822460704100030f41440c00300d8018101d0b00c40e41c40359500661603200e91304500c41c0300f64041714a42d68080300303940e10801d80c0d81c5d0042031500141c03404440c41c080b02e904401200c01d202d04031942c03c0405071a030321440380002d080003c00352200458641142480071000305681e11090030700051403140400140150400301480304407510040c5840a907804840b0500c0030520006800d856098103c0d001d02d4266a41d0310942c1d10814000250000c6120030580c00d0402000031002d00040d190f00314444180340d032a80200110408180c80d000340500b0601403040e50800300400a40d4014018140044411141882c090f2a40e212100a40e0b03410007200502c07110070b50101c40c045030703 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 81069003 1250 81067753 81067787
    0x40e0f0303041101030b0111070b03070509030601080322060c0b0c07050f010609060f0f0909060603051507030507031803031d070b19020304050a140d120503090d0504060f0806150a050a 81
    0x252235000c80f00917996602c0e405001380003000071002411252003002107400000d4050203660103565250070f42c691344c0d00068061000a18526649030081401c3c2601e13408032040d542d502c1a4041c1592103002c9a00070280c48a4040d0004001c01c40c0418030400042e041c80d0761100002401c03611742503000d000c41e0f006400c80d2081480c50300c01000924050300010b4269550390340c000a289060389031840041031903a20042c880d0054941515040342c40d0607580e40703d81c41c01e840030b01c200c0d507400e50304034125180d400c00320f84414400c00029010034400d03408151001c00203803046040d40040c08806140c040c0c15845180e1140d40006c523009281c40e100b2a11000b9442c40c00194105401c3c2000520307802c1d41030203501c6201d51010390041039036642144c0d44038480d40202403401c0c070081c400c42c01419035000701c4401c0071b43e1081481425a0610801c1254112401031f5a503c80c80904050221000d0b04040d040d150310444408030501c0c0306808800070801a145504c586036201c88140020304604800c03a40045 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 81070253 1250 81069003 81069017
    0x10503060c0a030e010905070308030711030f19091a0409060905010807030f0302033007080f0604150e01060f0206010603050108070e040f0f0506090f010911040e0f0303041101030b01 80
    0xc4046820700a80b150588541004a076009000c0e507454010441004040d1032031007012000014010300300d0055020b0001c59a48101c00300041c81b0203552403099031b000c05043d48081154407080b400c9401046103041c1649449954203994000180c841c600410040b00590343c0003404100c101d10f944100401001c4d0300a09010940c9006441620b80e009840081c042d0083c44132180101032080c011100107030306482804e08039085588568417580364002d0107011000c024404180341034041e080583c070680c0840d00c1e02a4964580c41484086d041136003a00c60451180500441c0d40d0490170701c0c003806000c0554403800240000300c4001c0c644241a888541810318040060107040710105089007610f90201c400001519107145c645c40c04810002c01424109a0581c0002009408240c49000f90580c00849090880000d5020300321414104000d01e49064101000c240d400d09411800070002006c2c15a50440711705100349003580c0c400c4500700c468a284555a042968061060031300400303007840d01071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 81071503 1250 81070253 81070261
    0x6072f0f0904111201060e04021201050f150a050306090c0405011a03071404170106050103060815060d0c081b040c090b1c11040b09031b060418020d060311030601050306 74
    0x640341c000090000380881110400b101529141e84100c031000c130b84508000c021045e51a40d0440c642c1c90140c500701e00c1a0081c070559001b000c414010603024900e031115030202502c500415850704003803500155084160710000044681d81070120511031424100a41134103d0800200022968160041c1c104000c101000a02c0203003c3c6090325400241c906050544420041c0c041d001d9020341d501031100b0940d1a0680d552480040d00302c442251001e0320f0911030341d03848801003038640c0c00228030104101d40c120000782251600f164080204d038060703c1404035150322203080030304180400c0c0407400100f0398055280c2c81401c05100349041619585485982035042c00201c0c040c62044040d450700380e01c20f11400e00c0ca07a0303445901030b12900c0b81e54502aa0350700d40d14030401000c0d800000c0d425101c2e0140002c04540c10a200c00400c106207001048ad0380392900b402e00039101c03801100c4c43d180f4000c0d17080c8184103c80301584102006103002c0c21280103841d0410041500d8244160803440c040d40220041c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 81072753 1250 81071503 81071509
    0xc0605090d0503040609021309030f120203010b090402091315080c010e0d080d1512050705030d0905060c0304050406090e0105072c060d0606050a080703060803030703050606072f0f 79
    0x3da40c01541c00031002c100b246840c00021600f100101d080c001e01d42c03500140310101604040c20040383c070415100c075081d0180654248040380002d106644000800700803481c0c0502d0103900404281c00001c00d084210a000341c0c40b00122201102c1d0120340c0d80b0898001d100d070400c10031404016000910b4103688601e050404107036419140000240103117000720344280c001c1550b800241704403c849602245995442442c3c540d102810401618140a00c03807011945c0c0c1400705403050a040245c46108a0a240000f402035603840078190065902080c00045019170302da0080b400140045000070400755540205642101c00190007882449901e40c8410051100541e00302c180c281594007022500041602180c0144216001200e00d1454180f011405036040f8003d405800c429990743e00c041d03601d141c016400c136080c82c010f9405560040c00007a1800b032080e08016030004000d130202d8181069641c2d02610810070b00b50219078608001000040000c00a4824407c0042180c0d409103000000b008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 81074003 1250 81072753 81072757
    0x11d0103050316081605100e010e03030601050a1404090f18031e0509040203090601060306080a030801030b070c0203030d0b031908090906180108010912110613020103110a0c0605090d05 81
    0x155800012550301c5510074004d106064840040e0041d1045204407200e1400c0341c0c0f5840800c4140c90041e142401c0d50b0000c0f5070500c90001051445001980703103440d10707070054407160011a21395080000c108030382565500004054001007042c0c120110b40600030f0341000b000d48203410b420306e00209440c107e003800b00e91301c008240400c028440e80bc001003109148101c80328805c084580d42c000d070000062082601d80040e00d681200e400c6d035010410251100321158452612801c09400903401100600100d070031042c4003908140c66051643e8200025808207085401140d00748095031395400000d85a41020303c4440030000e11180c3d000b66a90280c1d46144583c0162450113014041160000385d0039101c03a6500c0c1c1c1745200b034104594542d0303580e1001034003074030300500201c4400d20521a902c4600380640d402e014640300000c094581c6540e81180414620b021010a03070405855a0b8840c5d1440b00081c02408180d0361985da45032400c4803401d140c4143c076405030102440e54800b01005521591100c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 81075253 1250 81074003 81074017
    0x10210020f0a0c0206040f0b0903010501090603020303071523040b10060f0c050307020909060405010f020f09040506030a080a020c0306130b040219050301020318060906041e0303020f030f011d01030503 88
    0x10890b03030324003444c0007207a5039000380d821410f10307281d20f02e8000c110004040003600c0100d20807402031043da030326072401d00103460300d0303200007900b40e8014404400000c8000d0101c1c5075104c58000c002030033aa00300c0e1001055400101c060603010251800d11091141c4003005607440600c202c21540740901c0c0c100d0051916003541c0111003000301ea1485c4804016040c4116140d042c2c0040031054181807441542d62144003e41e812546c0d9860b0020003003844000b070003541c100302c3c83c400c00f05003000700207400c0c80050b003070090040780c2c0b40c0904000c68001600700400b81455000740d40c01080b4000314102414907288029100c50040d150181509000921007208a07070311650659080c141c0380c04142801010407403e0b080564954000300801c00f0100101e81400e181394048070881d00d07151600c00000b07480318001d030307000352409c0d006a0301281c100c0180c6810004443c4240b600520700040c10b50364a10320f800981c1c01d041d4180001d401004a5180c00550f680031000098800d04203500d07607911545e40c1c0c81100303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 81076503 1250 81075253 81075257
    0x30e03010b060406050a0e0306040303061508040803010306020322120905030f0a170412031d0d021e010c0c0f03050606031219110f0c04051605090d021f080105010210020f0a 76
    0x1440c507460351241f0020548003502408581d1281090300d0007601621181c0603101d03401d5a00355040840350300ca0a0340034001c5d508110064070716421621010040d40c8020120403c468036944440e002690070f10021409038021580c6d207801c160f030030700028058030041d80a00c1c030961103810703c500c2d0030b071021a0001c01698400d040d04424404a00c42511601445e8003c5032044444548101030580160090ba1000c507104040204d80320544100a048442c01d40302070341103881180e15103151000051100344c00c180c141071070318840d9010f99607501039071020b0308008001c0c0d086040800070814200b050320740040044026041a007011f00c0c00c05802d000d0503030b805804a6000002c1c0742003d01a14505d00c40502c1d02c02a00c801440c4034010980d02e000c0700303030034078001c074909800900560307124981c900d507104441e600c3d1880c000341d0304208442c150441030144d90012035a241e441c00301d801c1301c00030441c40e07441c0d0310f42402c6507140a001900b00148401251200b500411850315648852000c4800f00d00c118 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 81077753 1250 81076503 81076507
    0x3020702090a05040c080706050703090f18050403031107081b15160e040501080102031602010612020609040609020a0206011403060f01030b07090b0a09030c0f08060403050c10050403030207030e03010b06040605 92
    0x6030425640200c1190311200f01b500502d9000710b4641d90150003000401d0003a1648102540d0700c0d04400602d422604c503200080c060020340040300c881c08d41107290868007901c2c1c040340794084c07801c43c90f00b50f50141ca012601a080003032030350300c1c2c03a8180004103581c110000c05400f190100b41c440203040c00c0700911f0002001c0b02c4d00d648448850044080d0078010401820402c05076855141c80c40c000e600c20354040710714a400500825101d07105000e44c0f010f99a0348050901c03c46130300d40c2405129002454115070058441c007011460b0074141c4040c00443e9116401850035500d0700c01c5a8614944503031125002e504103000300b000d510300d41c08401c5d04403680a0000c654981d680002140c40d511a6001140821000a8908401684104000240e07405005100c01c095995287c032500c10640388200700c5103402a0340050086400f80b0007800f1020380e02c00540b403010000c006044119501214102c020079804644801419032240200c200740c4000e03800dc00c60040c5000008865001e41d00ca07000801c800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 81079003 1250 81077753 81077761
    0xc070c0e04120e030a02060a1101020d1a10180e0612070303020d09081506040504140d02010f06090e0a060f09061a01030509070e160c02060a180603020702090a05 71
    0x108800010080032405a9400d00e81001d00c1e184a1441c0458810800181c03003070004401854003080c65074409500030051490b06c3c0c1c04803402d8544942c2c0b0304110265550902481b11725840c80d010710030f41030f031810b46140e02502001040000b50418280500d04000c00c210450541480145814064680000b00ca50b8103075a4800040e4107503e07002a201101e004a4200000f01034001600c4054283e00da181c242ca015125015159a2142040c401d0800148170010581500341541b00c41d4102c0d0264854442800001c0640c600d0065403003011001270f9960800c41011b0500391042c0e80c0541000107080c04020300c4109920340d00da02240010b4240395440c0d078180c40c900e042d43e100034101c82c0d1024050000701e0500082180361804001e010380801c0c2040c0004d21030b540080b9206040e01c1d003d8620102e103881c5c50960f014607200340203841d824400002c003403601590381c071030142c443d00c0640d0f9116607420410803003603030b42c1c0f44a0350300210506005001d00001a61200b03501da6112a110b0310004039991 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 81080253 1250 81079003 81079013
    0x60201060e01081009150e07050102010f110d090302030c0d020d0e01030221360c010206040302150705040b1812060105030d0e03030f04060206041e02090105061e0c0102070c0b040b030c07 82
    0x701a601082c9021f1070240301011315980401c05008480b0260000c100032100c030035548040d9056810000c880d0603041210b0040031b100707a80004400344c041c0c41124104052070701c5551408905002110241c0e0100d1400c90310541d00661845094000b032809609019a070746181e0703c4140780b242a854540e03d440300003261003010442c4618099008410b0140115201000e1400583c102086203042d000321465035a8075400040d402c3c1c0504e0341540240100c0c28800d0f000b45007200c002d4851410803000b004009088481c0c030020f00840c921950480071500d080d00200007000c0e801d4450307204250090001005250b07400b2070604504400d03400d01034550070904001900310300c070b11002c2c80a104004038002c12460750014078a03219074411304101491440c070181c03041254010b0980294040f41500041c071090411a01074111400100c012003519078109448000681103801084000c0e903010a0702c8060120314121803004007015840f29290a00b0003008450f00e00c4014809040304000140c0101005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 81081503 1250 81080253 81080273
    0x15010c11131805010b090108030702090a021306081501031e020c0c180105090c09150903010f05161d0f06070206070c0603050412020309011d030109020d0b01060201060e01081009 78
    0x3141550100400180c0300d01d54010303502e42d12029280c940c40c10440542d07074240380c010581618801c40040d0f0804946a003001a003d80c0200380c0482603070240a40c402c0300e400b94455102030201c540392001c0f1441c1420140b04217100c103c010904140c1042810211003a0030700d0b4618845901043c0982d41e104103080c140c2c40d044544031071640041c2c0050000f20400b0106455505a6038211128542c07504c0c3d6800001440c05490b0704c5513400b040700940121200c00c42001000c080e50b0242c0003181c000304004da24400c8910032601844e200300c15421112142d64013504c03410548105602010380303400d081d0082101c035554510440e000d401c0000d544010f542d01c03c02650219030780210300300109500c0f880028060207050342d080b0f580071501c0c5040301116002000f036407960304043c4c0d9041c0200c071005040264840030028100c2c4c00d9542c91103203001513166007145008041c0164900c0b0080d502d0300900a08603401a072007220100203900042c00039402c04107420303810141d801030105d108440c80c00c0a00d0300c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 81082753 1250 81081503 81081529
    0x71101080c091201050907060c080a05070f0b040302060105030c0109060c02121c02010905161404050c0d02040b0714060f071d090103060e060105010513030213060308030f090615010c11 81
    0x111103c041c10f10800c01c41508000e1080b02c00030305a0300708551ba0355040d2803090000000a0105005000c0000094429005004054003481d00e0902c1c20344941c07540444c0e2801600e066005800c11001400340b030500700112000001d0030f28000b0707205490020000d1880400302c9000f0720407085104803043c000c1c01045000d0709610010030010460516100103402001e0b01c00c0304a680d40100c030400303c030440d41010004111111249480444000d440800008190042201a10103810712842c04000722901c0540042c2a262011540d908040e0400b03100b00c1036203400e6204690b01240400c6212000f1030207072500a8414145520001e40a58000e0780081021000c1900440402c000200703002c4a6004284460a04410790b010750740c03107400440700c5204040f080503580080140400042c01c00c030104c00c40c40c19400e40c00150761602d035912204180e20680b04114504e0030304c000e2002d008020300c2519000a000c0d000190000c0c0c040e400a4805501c0d041d021f401001c0030400d8020a03140d0420102c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 81084003 1250 81082753 81082759
    0x60906011a070b040819110c010215180a0510090605010f15050a05070f1a090c0306010b0a03021201060509030d0c1101050d18080d0e0307020312070215161106071101080c09 76
    0x140c004254001850303403280b90450b1f200c40c42040c10299040d4004100d8002201a10650401a58411030380c00c58081441030002c58612410720308402003001440354281c100320014004c41c4011050401406a540c1a00013084011041104000f6031103c07040e12802e008050900ba51103204004094800c0d000390f01000d441190007549000400c80040c080c5561107008001c000d08a441d010a41583c0e54020030ba099015030046005000d4231000e100030b8030740784501c2d2602520f80100c044a50b0581c801c01e80c00b07580403e10100e440030852030b042c0480c3d46d452080345440355403041248c550b00009054005801d060140009480d0304200803500010001000f13003610030301c44880e42c035141601d0342c883c1d0003070301006207440540c1000480c044111001603800a0040c44007000d100103100e0b050b40441c000f2640025040d2150305140b40c1c205c0984a0784101c1d21511400c10005e0a2103c10180d0051180c3d101d400100b0819000410903484000c1e000c000b880c29035031603550750000021910941c040307075138 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 81085253 1250 81084003 81084037
    0x20c3310091109040c020a0c0302010e040e010e0c040c0f020303010e19020a080a060f080c28140a140d0f020a0504090b04020a0e04080406030e100e060906011a070b0408 74
    0x440d82d610a008080c20242950100315800780705d0002c80e12000c213460300805440150504001540c41115054030b4050020b100081031515280741030300310f80460340c03024150f07084180392007845e00d01442071403001da456040c2050301c0c80703000d40000e40340e110500800e5406000040810341c4090490703000c402554010380c0840d034584a201019000340c404403070790390b4854142800420460401c420385000c6480c02002084181c0e4801c0400c0f0392580d0700d002088100c0c421241800010320120241030080a0340b004000b11401220144100c07800c1c00e81100242e407030b4000262080c0d880f000a58042c3e95004018512107007020700c001160544254800303540075051001140600c8900001da80c0101e2080f10b0300b4219990f54154852008002c84d405022000c7c00d01c01005800d01940207210410070420580e107400e400c142d8003400700e802c50800b101d06603000100300005098100000350150640308a0070386d404001503840c041d1031003840340080c00d52150308003250401c2480015110020302c41c4146032 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 81086503 1250 81085253 81085271
    0x2030408030f010b0a090b160c1d100605070303230106050d0509010506030a02270a020309010f06080d0f02010204170109030f0804020f01030c0203070209010801020c331009 76
    0x3a01541054070030440c516801d200008414019000b02d9150700020344800410324901650340e0380c150000d0f07141000d4481202c6c5d0080c0011241c64080c0d01403d92410704800181c420b400f0a51000f1006020812890080b00148020760308801510640e03a81480d0105201490300b1003a1820605000201d661a000c8800400c200c0d17000009490034003048a0f04024968644d915182610030a40c0c2198154000040242c0542451400d490702c05c10303081d070780c1e0100601e0300321104041d04c01102e0b003000d802e07408428000c3c00d41082c010344445018000b41070060500340340308552540000b245480c2403040046c0042040c60013034060b50000d00c04000d903451074021484606010704420441140020940103410340c000d40658200ca0041d900908030103c0924031030019001045606010030542c40140425001a9200710316140079052000000d605e0340c0101c0800e0b0b00d08110140ca8840345190882440422072035180e4623824000981d0418146440d19013101d100c01c8896040400482d080c03139058 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 81087753 1250 81086503 81086513
    0xe151306120f050c04090504021c050a02010e04050402100f110f03040302010305160c06110f0a02010c0f300603020613030510230402040b040c03233304020304 70
    0x10182071400c11000e10500302502010011100c0844a40c0c0440d003090000b40028015036206950251011380784456180c20f603100395100800719030f01250306520251988045583c451100e2b100d0300c00640303042c48642095030002c1d1418401c01c0490f0104900f11a5160b0018454003090b40880c0c2c60405942441c1241d20b00c80e501c0358403501083e400f00c0d0400010890310340e0b00080c02c0850a07141d035035402e001e62440e80d401c006805081c00320010b00905000011114075000018080c1104139000001c0164150101600c4418a50460000d00c82c01b24410200900c51207110110032403c58001080d40f24442100401003d0741e0b00040e400000200b041800ca030481e44c4080152405481194421801c0c042000292070700320702580c051301810b440c410600c010000d1100e80140c8010004240b141c050740c042402c079541c2092050000391201c0b0b841403181c0c0701d04d85031825612020504041e501d441c092035207428020341920410f4005014840d41e00180f603004007041e8030700c010f20556030b80c03d0500345 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 81089003 1250 81087753 81087767
    0x206040209160207060c0302010b060a03020c0f030f160507030b04141002030c0d05070e060c0c011e0207052206030c090e0718110c03130611030301060e151306 70
    0x100c0c00303403018101041d0300075940030700300c1c800b03450aa004104103810f1140071a00026070007411030941d92a801000166a981d0025118081c00c2c0e030350042e02c410780c00d18001e14081902e40e0116075900108554100c412241080762000080d0480f4403894803241c0c41d12515160141d44080c041040035010300c0100420103000b00c22003402e0b0f20803190803407000790280049100c2a03940d911540410840030358007004540180e41d000d00c281c02e004a0210303503031010801a1703201c40b11840c01c80c1c2192481e12599a00001301010000c802c031190b84400036400400382d504c84040c000d2070711810800703400841e0605010450200a4540001440160707500c3c03910441c034203081d0041c0c440c00b504107010480400c41c0014804104c5d801604100715030b28410800030002c00001d000d0300c0301644d080141c0a80000e080009010300a402d002d031040261410300c1c0240081003802200180343c00030801000075a40c000081110b11303200325141c03040b9040012051441d441824031580102c94400350006600f03400000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 81090253 1250 81089003 81089011
    0x1140c07060e0a0e1905090309090106050901030f060f36020306010e010503040f03180f0f0e100305120904140a0b0a0602030f0f0a02030c16030c0e01030807200409030206 75
    0x60840c0f80c562101e0b1480d605200803101400c888407081d002080c07000f04c6030442504000200c00707580c42e2502c8040800c070400b00980007140031900000308200d545d40d06209032001f550040004006560600c8180200301c000d07071080e5559040990641c215901d601031882c0501510246145410a10402e8010203504121540b901090b02c040c403c4000754001c404a900c2140e20001c6120300d86220b82e01603854078546400601c0c0003810b080302040131b00844900c030010380030410740844000e10700107040c054800010481300c0ca03a1001c260400010314001b4413282d000120307000a80c1c482c11520041001031058005850704614100d09020b040c05c110340c0a0441c5400c240c2e801c5d81e581e520385409a940744540d01c1109250f81040003001548800c0c40d025080c00a6107105480c40c018096030054507022803401050461f00c1040740030410408603207d101d0007080c00c0d40010b02158516100c00071180103110014011159130b00070340480018051182d1800c0f00014800c00c080c03c1036050007540da2900721 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 81091503 1250 81090253 81090259
    0xc051516030f031d0f06010602010207080406030507031415010206070201151a090a1d06040b0603070503040c2403180f02010c050708010609020913090302030901140c07060e 76
    0x2a044011155194212020400351800180484686941c00c540071080c280c040000c05555040340c0c640c1c00c0c1e208891300c00b5480082c0090074248858070b007103400d00c84180e100c5015684104607031360000e00203200792812074060b42000101a95441010f5010b0892500045145401041004150a0600d1402510074000c0c0d084031066550100207a0032076a84041c081c00e4010480340400080e9040440005020f00e444681d030304103200440815850f0282c1e800169181d0654008107041d41c12075008103071701802c11942441101030170800700b581c40c407002e40700600308a0004002024082515030000040c02c012110341c0c0a58040d402658114101084400010b0700b0189509101803c6d09400c0400c1d9400140010014600d64010340b001c845400d0220f0b080d0090701000298284207100e0b001c01003004220160fa204014410132141c1c003005800706a2071403920b0801c00100794004242d40d02041c080c241003020500040d0300e444180644401c919851284140202e6241e07888410020300300025 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 81092753 1250 81091503 81091519
    0xe06011203020c1012020c010612060902150313080901020a050a0305030106090f0503030a05070201020a0c150807080411040b060408070803040f0b04030b06060d0f140105090c0a0503130201020304080a0c05 90
    0x102e08204d00060403c010300c0009000840b0900030014507401414224840c10000521680e15820704048120780401a1807499942c0020320541c10251020311904d40c3d6035541d40c0c070307524261404c020518513a0300046c001d07400c04549174016034001c1104e00f1006800c501150220841442c004005a0090190f40300240705640002031805050090030f083c0c0d00014040d608082e80031500b00c605402120003030781144580f064400109281c1e29070400504411b02014040c00c101010242c500d403800340010381003103c80c8cc1007001041070000a00d0741e01038101c44c0841e07403442000020701d841c016a00002c0040c0600386000410700e1000000300f00719041d00e64400c05c2c040e6540545d0200f40910b200203810007034650300003203451402c1e000a065104511000140514055115008032800d1045502020341034a00600c00340c50120350240e800220540494030300550707044010242d0102078500c6080001c00601e5008680c024010740307014100000485600b6020703810408210b801e20320805010701c0c21 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 81094003 1250 81092753 81092773
    0x30a060914030a090b0a020111210c031e04050f030a050909060a030f0308040303090816020301050906070e30060115020109030903110a0504020318060604091101120e0601120302 78
    0xc8107890f9080c1e41500c8001c4558903010505a09502807026002155601c0000d50500d076142d00c040c100101030703042e02428288130550821204040641119404d07001441004010110000c0406042c0c48820074403210b40c5644c03500078501120303000c2d01e1005000c0401e01c101d072903501a003c0e02d900c82080380e001d5a00c0c3c071043c0034410058820301014001000a440000104c0c0c0164880c61b0041d01c01c0c500041c00141d641c032050b0f6190040e40151604920040d44074055103000d0003050340103c20480507280c1030a001001410800100318102c0c005d1000054282c00004c03c07942e440d441544e2204100c00700c140104030503803264801d01819a541c032010000780140e6205200d90001c280d03144c4c480d01c02c45810340c0c80e040000c00b002101d036a4003d58540011400d0b440da030001e103024a40e229440c0c6c6181c0c2c503440311281000002407240e8091468903d20070042a0201c42c0c10844a9082c00c00c421740345001035819005d000b810f00071440c07038418a000080c900e004030307503805a03160080d0301307658901007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 81095253 1250 81094003 81094043
    0x70c03090509040206030f0c0c070f0e07030b09060d080708040e07020d14040e04080d0915060b030411010c08070501050405030a0f02010e060714040f14040606080c16030c02030a0609 80
    0x4103030f030065007098050000509184610795039582014110b61600c3c10240305d8012940f401c0705a40042c0c4070714002040821920003c80100d079009012400c0c02c0c4842102c01000c43c0072407600605442c42449403036000b5082c04080fa0803034280d9070700a55030582e11a1680380b82030710340c3c0059481900500c038604041071154820032203c44541c1c203110a85142500d0400b2200722600081e00641d440e58041110080b9a1080d110303140c0042d1040030318141d003058803c0400211519507005104000d02002040b0001c7e0306a80034a940307920908011510705918104525540501800100a9803901c0103201c1800790020103000c18203083d540ba001c165507083e008900343c500402c0400c029034040c4004c1554280905550803a40341c0401819082555511048180c903c4642c000b00030000800d21000e418200360058501400090401c03901a0509102c6282143b0480c44000364011540b01c25004042c403447e0803800194009084650520b51414072500500c1307800811162146a03540000d4604 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 81096503 1250 81095253 81095269
    0x10807080d080402040b01090b03101e0602030d051b04080a0501050a02041211131104091104080601060c0c1503020901020c03070f0b031506030403110c040b061b15070c030905 77
    0x4195a95000b0340d40f1960300380405448010210750600403c404089030451190020b54417507d000d43d1904401c6242c2901028075002007000540e00f02240300702804656000030483d841c403000084002043c0d030b01c059101045294001c01c405000e5000580000c0b0700c04002611050140294002c019549880d01000300300e200f54424016031244041155005c03420550748100c0f651006003090101d895900e0350381c4200c41212040d40b401c0100030506015a204a1107602ea100380f8165840d454241044107160351550144541c1c41001000a05c42c401c0000c068402c000a040502c07035a081142c0005010300030f9084080d06074018410409420401d240002e81e807021690452014401c683c00c160b89440a41d00007013050b41c0d80e05040c80307801d61640710070006603c1140aa41d0704848440710005950810749e140d0b40c85485141004001c1d40e0560311041181ca120a00c0319055101a0788036171243e0804040700c440129100f011410840c0051304900000c004a2103035480c0342c0f80c00e0b00d64007049400707 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 81097753 1250 81096503 81096523
    0x15060c0606210f110402040609380705010204050d0b01170601060905010f23030402090a15051201150f05041805030a08280204060f08130b0a0b04050405030301080708 73
    0x1c1d40d001c8000c0c0114040c0c1018550300313802494410304d01c2c1c4040000c101a6800b550104000400c83c0c08200305865441506c3c818045007000342d110035204821002160508001901e100d80500146140402200350b040b1001428060314102c4a901c043c18010b00350324017481007962180600d04081c01481000c950309050758042d895070030b841400c141c01180e1380408400345606010540311208a1101d9020814000305da041a03019034a01c2e2070701c1408220480944102d800c641000c81e4103003003024800e004c20a0310300580b141c048904035040454094805103403480b080e017007610382c0411008000f0111000780e40050f10b041c004d00640c009008042ca0300d0400c05025a003041c0150701c2020f10400d106604414503091001030030b020340311041e12100032400840f04207a80058200a40c54000c009000141e02d00c0c10045080d18000c850552460b51800d40282800d80150002d01a072285621035203022801070000c04c03441c17400c2d14046941c0e81c02801603d6107072088010000700604002004020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 81099003 1250 81097753 81097799
    0x203070c06260108070302010f020f1b040603061415030a03080606090607080f0a0801050d080304030c050f010f020c0127060e0307060903051803061303080a15060c0606 74
    0x200e14034240c82102d09042031003000e1684200d0641e1040555552000d20780608041e001408040b841c5d031002500d07012145a8500542d00803c011191800700420300c4c403410901d00a16488100c601000140100100c0e0801000c03549401d915011800c004264175105200e0484a04003982c5400101561440c1d001002000600f03418002030716410000702821090b54040c06140c240502d56641c04202c4c0c1020b100841d0000b0045036110f49540d119055078010542078030521884030481e118140d6070702c001407026081c4059481c0c800f040280c100f001025182e42d40c0000c01400d10341140d28000b9502200c08401250700b0408410201c145110741c403043c1d400242042054940ca9998101c05001d403d085404c3c540418010f40340483d845000c1c40703440510a03034400d5610351014070716454008c60b44403030380d001c1e511072010082c5090100c91146107054040c10000c20035555120043c0150515100c03610200c1c41500c00010015004490254003a00c90381d01804000d4446086c007034207a40000e02135074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 81100253 1250 81099003 81099023
    0x907090b040b07080d090b1b0414041508070f0501021b090402010c0623012105030a05280f080a0507020309010f02011404050c13090b0a050c04030b01080706030c020307 74
    0xb014040b010010301c50340d03100d189100d040250301c0d0f40080440d214140141d4028a100c070070054080c4071403c00d0381d61a60030101050915003850310391504e0810b100d8840c0c0c003c50307a03020b910391140780d041c1c0385c1c000500018007141c488c20b84414105501001d00e01c900350251103120489174030258002040c40800001901402c103969981e0011990f000c000582529103d07038504031000340390f07040050700300c1c103641e8814403004039407516950300ca4462072104242003070b40381007064200045010040301c40c0d08100c0d24110352039140c08403606502211021820780f20440096003442810340110500c2071000702500e49015590b1003850440c147c4000300c03403540040e00208034001c0d1750b40c05544007100c0c0040070302c000034580480212000b9000801d50701544c0c9580022010001d519203201c040d04131400d092414421161542d980d907459400113000d00c0a52a12200084c4200c4c1000d0260b80040d03070424208802540d40d142c05a071641024056600020f0400c00e0402807c1d00000484003601e0348144059 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 81101503 1250 81100253 81100259
    0x10e0c1005031312020105040309051c0308090709021b1501081f1b090e06010207051c080702060a1d060702010f0305070e030f01051f0b030408180907020109020907090b04 75
    0x10740030360004221910b00d9010f10320420100d010040c05542c0c00b1040d80001609003001d007005000480c5982c423480c49408007440c80d03c07a82c1150011140542c0e40741c1461000354803a10007250400d4510f4100312a0540301003510050070f004c104460102c150300000341c410344415504459565442401000c0880d030024803c000c1042d00b40c019101024404080010010842102d14034110799080050000030150705c1c0030303c00103c21100307503030f0000c000740001c00c00e2600e85030118411a400c1c00180145a0030201601c050100e480c0840c0c0d501a40140040c0c0e8500c3d00a41c0074103915a00585040311b5100d0004400300360900004940500350141c403154900070f50340342d0403070180200902160810200140e18141502c0401c85170171222103200011032146080980c0704107842c0c01c3d0110110551180000f00140d5200ba411130350002c0e0002d1140d55108520170002d283c941040d00c14036000700b650400c005c0036039419807202d85541e00c00c885080558881c8081184c81405074000e5410f2004100710070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 81102753 1250 81101503 81101507
    0x10503032106010c06050106020f010c09060e120a06141e041502070611030907170601030c0302270c040303030b040911010c030e0d0506070207080102070c03060b1201050a060503010e0c10 82
    0x365030104052411302d003880800da0714641915400c1e4490300159005111442c5120428090329500d502d1515214520324034080e001000d1a8090740d50b140102c140710b1440041c0d0000b4451095038540000090020f60400c4050342000401281c1c0d5a04100a0381091840f0034084207107103001e240c010003501c03601d2a55284000003548610070407942a940c44010312081d9986c0c5000e184504a22400303000c2c5c8a2a020140414446043d4409400d411003001480000c0000c0804000d0303d405850250904642c20381c1c11254842207102a00501c0c5008100890503690700d0060007502e201e03942c140a8104421b00b0f11050300c52260004002d00310103110148903501c181010034172180245050600c0503003450225080c94002102552941c1003a802c1003210303a0100410001403101c00c0c0214540103490700d070b901001c61a0701000704815120b240482840c0c0d035101140548481d04002045030341010981200240780030f00ca414003035420a605d20700c0000e0040380200309400c0103007050384c00344000841 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 81104003 1250 81102753 81102817
    0x3030a050c1e21040f030c0510090633090b010219080c070e01060503070509130c080907051207030204180c0e0105090c030405031801021009050a0b01050303 69
    0xd294a805001e00810340b10078142c0c18601c0356000d040b06200e55a00b4600b42c04074072681d800d4010ba0400c400340c002d0200054002c1040b1050603018074224000ca940c1c0d16020382452960310302c421455043c00c1c1010180320341d0b5840b01180001034203c11303c0d5051145032000519400329200b00035814407000c10442d111060704000c010841c144161a040c1c0c110144210740058541c100350780181c004125403d4800302041504090111402004169898210014514070000306420204000855450543e480d0410346101d202e803020703002c0c0312410019030000d020840c101c40c0300c0100d1190b89400150303410325815481c0b08500d002c001d04029030668080c070001d442c119a101d8000e90f003042682020482c0c1c15040d5020f0030000790990841d501d48020800d01d5907029007003c85110041051100241002085a03014001c00d038801229a4000d001070741000e110034450356041c2d091100c40b83c02c000000c02c03003940300341c13142c14181c0c481d91320f8200340f503500e00803858100c0002981750500000c20f124502 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 81105253 1250 81104003 81104011
    0x1902060a0c1407030e0604080723030106082503020d050a0303050c03100b072904060e0c0a0306050403020f0607050405011805010e010c1103034014010909020c0705010207060503010803030a05 84
    0x403036075180c188d80d00c20292900500c0ea0000c44410718901d0501d041c0d400d806d42040300003004030000e20145080a404c00d840c1c601044c0140c00301d0301d0400c00311981c81c204620701d100075030300144040307285141c0d0709000e92200c88142d811070000c0d19000004510f01c0a4406403401003400d21075400c00caa040600c100103551003500c3c1030f1106140e50740700885550390286920a007481c01c06500c0c0d43e80c00c2600d420015070704444000c1d0030079000042e080240d521450062812647c200f000421151a503086c240e0411019030b44e81140c0740a1181040100b0350414000e2003141c20a0b600c20b81c14001d962045e80d07004000c3d005003030000340a4604038071658400d000c120210341c00740c2a800040050f0f07400003440e5612500380342d410f810000280c0e08010100d1b4840710749002c110340d80c2c1c800f00c00761080b940002c81e2190058058004000240e24490392260014030064030031240308550345e155034101e050340d407102d500c07805006119880c004260207100d4410b80c0d0403601042e0065040d074642440c0c213005040018 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 81106503 1250 81105253 81105259
    0x717010510090f0306090308010b1e090d050a0c1d0103081902030c030a08010501080703140705031e010801050103140307050c0d06090b0f0a060512150402061902060a0c1407030e 78
    0x302c040f03000c0500054020045200340400103c81d81a03190180c0081e4050388032444210017072007000c8180c40d070040c00460035206241d08e5942c074a142400161060701e03544c0040c016201c2c0b207044508002200501d581625401001445014005141d81030140740c00d01000303005000502100c080d2100414446030340100a0040d03034101413400c3c5c00c0c1461900680742e10300010300c0202c0100900e50304030f0500b68010206140a12a0051040c11040e200030054040410088000001102c0c8402c0c00b4242e403145c18010001c00c420b507074a1400c28040d2000b800b003a205148042086004944000700311000c0581c0980a0301411036100100511003038079240035500940c030b078056100010300d1b0a1400740304035100380009a860921080440442d00305030091405030101101c240e10400703001541642010007080c0c0d038800c503542c500c00324140d4000c003541e0042c1c1101140000e01d6094000c02c001344647c2041c5002c006080c1f4200003111020410f107107210412a080102c1c0340482c1c828503100d8085400a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 81107753 1250 81106503 81106517
    0x3120207020103090f0602030a0609020a0c030804080409092f0307031b090c0305070e0102010c02030922060b04080f0625030618020408070b04030201080f10050411120717010510 78
    0x9171903034080c016003080100e4107113500008100c1000070b81d01c0b801c809410720080131402c2000085015121190030400501401481c1000a080150000403139010741000310003481485803926040c03459600c4606400303c10135070075092043c0311001d115425281070004004044451440e20703a071080c040f0042502910340501c50000c95103004601a1750000e07211503a00007124540b410000f80781c0c1152100780d5046905203604d503448503600000750307404910121825645568042c0c103170b61a8403101c540501416050031070025180d8402c030040d00854101b0001c2d5110307186100d03081511800121000784080528421001158810006a16941d0040c0c1800507041c0d03100c12106a000c81212003162a5030b0b000507040c001c09a051203010000c06c00103605a083c641180e001800c182c030020311b05130700181c0f501c0000b1040c21510840344024500544104101c03640c40722040c803a0b0b800003400003804482080400c41c0c0c1489204020f0100d411031100c600140d0030b010400c590040449a400100441 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 81109003 1250 81107753 81107771
    0x180905010504030804020f0a080d030c0e0a0f0305070b0f030f04080c070e060102070b03090d0c030c0b240906030706050a020f0115030c060f020604080d020c010f05180a03120207020103 81
    0x200744640d6000702c0c0603803102d40c154036051040200051460114038014030040c402000030080001d11440d00d480c040c00c001c00c1404000c03500f01c903003811306050ba50340102c3d82400000d01e45441940c42c0c3c140c900076002c1d1481c050f114034020340c40f44150600e42d44840c80c10800562071902c1c1c217480541051203034003414079190107861581e03d8841e298110f036290154007414013030a0f603010070a4400400c2d455038407a0031031510340d01d407584400c030090000052240700794100040600c600d40c280c40f020340c82076080d144c0d4140700780c00d080c81048118004541360030f0842d0800032407a0040380280714045c000c008001e45401c06904840340d42281401340f0070343c4a0940410300c1c82c40c00303004070145414070010802405245082c0007400203400d46c011028442040010389030346a0124002c0d81c01074019100658900140100900034843d10107131106a528021000c0c100c260a50052802404034001110060340c5003c020b64441485910080100304180d0340d60904040742d40107082c5139030050400027011300c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 81110253 1250 81109003 81109013
    0xc0d031418040905010c1b02060702091506030106022a030a02130204151d0105030f010e0403090b12040501060801060501050909090309060403050a1401110703120b060a1211090105041809 82
    0x141c0c024111650394490788070300322031030b4082c1281f4011520941024507404032600030030518480c41d034001c1e000318000300004404c800c1c482003040b59403001a006564a6a58100c0251202c5030110600310303403c440103079030307010860008652102c002c006007d803d101d10aa0300700a00080403881483c0690b8080c48000390700ca150b00d982d08020203680d00e40c0b480ca10100805000f0382091800e080d81031100900511683d4401018550305444961500c0e40d00b40d10740d41001d03101281960f10280440000103404d044618070003160303d0199101d04000c0c4400b9454280c298240c480602440740012002d00c44441c0c185010340309a40c202c02e010043d2480c000e110f502061382a4015041a034a0350300465185003045480318404859100310360003001490040310150405100d460b40290800800791083c0b0030754003c6900c104c3e1414801130115603207406046002d000390702c00c821000d000c54603111000e4403e1080354110f03419104140d403064641401c1c41c000150f403400c00640780307403095990041075000074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 81111503 1250 81110253 81110261
    0x312100806100501200c270a020301140d05010b031603020108060108040302030a050f04090507090303120b031b0310090b0615121f090c0806091501080708060f09010906080c0d03141804 81
    0x20108400310102c0e001f50100c07140d101900644000852803040004002d6140b0078070504c1c02d039003400c403000503207941c103810840c2c09130468031391310703603040c0905e481001840304e8045080701140c3c030031780724502c0e5a9100c00040d03680c04030440c2d0280142c0c00400c000d05480748a01e004200741030001074a1800d00351101c00c60802c0700c0c8100e0f5203202107440c1e00814400d142c0c004004d080c1d0504090014820301009401080d21440b40d20450007203490315881c200002d940a00004442c4102a44100264031080c1480218070710261082406041c0c5800148440c0a240081f9201e003140c1011002482c0c07110000c1c4c0940309241c0e040c2c11010700050001040b03801140c022140010a43e960f0140b00d41011030400199240140c1800284003d84503040000d0340c00c060000c4d03201146041103489551241c000c1002040145002648684c0c414004540c0030341545c0144280e13200141150103000342c0c0e03418007554101d02e0b18041c02084000d084e24140400e540000c02540c18140020381401d50803001080035a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 81112753 1250 81111503 81111529
    0x1030c091701020a0e0607110d020f03060f0106030e010e0601050d0c08120a09050a0e18010e07030b0a14060112020f090406090c0807021b040504050312100806100501200c 75
    0x143d400140802056604c5490300b03d1309181260350502d481c41940e2021303240d1103008605405410214a800250741d0303080c590851341c0310090103441301c07413a180003ca52052070900410011910b441c01d00c4565101c14464505c0050351280102582e03400c0c0010040041c1d54010200c54402a02c0400701c0c0c80e070800d00c00d21100303192608165481d055618000f400e2400ca9411540c01502c0c28801080590300700b00001e50047c100e40920904000c2000c00e540c05003141d085000d10900c1064000000c0000b9120441c0c81540e2800c0d00300070b8034106401c0c4182c8560140e503c1c0f4001500b24610b000050f520341e00030200e101c000c0e8040c40c5056803100c0441e0994002d0f500612205039140c07890f403142c5402c6000e090344464207101402c1842800c4500c210480580d03c030540c0078580d13510000d420000100112254200d005e040342040f407405050f00b9412200c07902810b00107001e02e8001c200500c105007000e0050352016161140c004200309510b000b44500361000702081c1c030038084c550703420380c54075038102c81a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 81114003 1250 81112753 81112799
    0x12150301020c0a15050709060804050a0b0114040513020607080c010b0315040302010f0c08150a0b1b070b07030e121504200915041113080c011403070e01030c09 70
    0x22003e02410004c01c100c00e0009032181d05030405041201007a4004409010380c6c1650819081640b2a42031a034500381d8488030042c07a40500c100003241740d85141c0c4480d291180c1c00c07642444030342d44107402c07400c80c0386080d64000e40042c003d11542c40018210005040b071180c95034000514280c0100007e86050105441d01994100f9030040c4020b1540c2030103134951200007098184400025044000e02a42d001000072080301025004240c42e40e41e030580c690005d0204960690f00c8948407400c01418850b104085501c0b8801c01c4000583d51180700c06946a658151722001c0e405525142481080a503809041900b0700030710110302c80e007581030088107000c0d0f8014200f0021603206410b10000320041e0741410352143e440308041214190200709804141407045c0c0300415031808442100106001d80f0303001c18488403040001040090300040d00006181c4240d071400f9090030030300b002c40c41d80d1005603610b0700080c007210560202b65020340c2140780392031070900d04040c20950310300381c0f007603110510000098 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 81115109 1106 81114003 81114013
    0xb01290301090506041803050403110d050307050c0f0a0803160809090106050a02010c0302030f0411031c030b0901060e0102100b1f020309100306080312150301020c 72
    0x5581810303440356110364003a4040c08040b601140034515052194201040d0802c003504150b81544585180c1402d5031240220188414403542d041014048002c000407010001441d1a80c010030142403038404240c10403c00c01c87d8007401d60321884c01c41c00240032400c03000c800c035030018001210441d843c0c42c86141841850150113000380d0f2103008000000b074040d422400420760101d42d40c0c001c1064540d408000d40480c0025280c7c00f41c0e4000c0d82c40001c00088585540e4402d103003004085844a2606c00303090b403200841820385038002615103841080c1400c010040901405070b40c01c00799818650b000c0003c3d80c40c1c661b081090102c3d07031143c640041075110304071012440d90740c56035026503240c502d0101a41d2940003c0645005400d9500c0d03541419103c1d100301030946007010003841c5000c6090000f031004410240c40c1102090303c44418105507a03092004200c0c40ca50310f00602 = true := by decide +kernel

theorem cover : BRFrame.Cov 80935253 81115109 := by
  have h0 := BRFrame.cov_init 80935253
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80935253 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 80935253 ≤ n) (h2 : n < 81115109) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
