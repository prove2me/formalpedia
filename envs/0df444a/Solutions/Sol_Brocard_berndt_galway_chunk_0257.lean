-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0257
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:47:18.02185+00:00
-- url     : https://prove2.me/submissions/859f118b-baae-419f-a27a-7901bb0e48e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 46043169 ≤ n < 46223025 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 46044419 1250 46043169 46043177
    0x30c050f071e0b0906030403020c03100c03050f010b0d0b0a0807060e0306150603040602090d020604031a090606010e01030e0c06040e01060207060801030f03050306030c060c010b01021005040c05010f090503010903 93
    0x418000d6818081454071104103000101c9001440d0202d0f8105500c2040c0b9098051a400000502414020845140c07645005030899460241181640d0014649224540c2c0000e00b0070b40450020000d444410341a0b07003a500c41309107007155000300d040042c46488500d41d04011000c0000030168018800c0c040209140d0301d40070038108280f408c041c20058002d0069020a440d180b40d07900c81d844040960768820344c80000103a40e12450000a1f2884840d050029401b180004021040000584051002c1c0d0000c0300c1c040425120030004603115403040307031860b0018041d0310303110505600c26001000113164a400f614000100e10010800c954003a0700410382c180031103001000b22540c1044104010b100b00d01d80482e465040d13680b00450b01c0c1c00c000020301005800b01c041200c13550148102c090249005201640d10451080020302034400c1001007030150088901c1301c817104040d07000700c03442a030f4480040040141004010b55440001c42406c0c401c001444c540850541c4092086440184c040d4503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 46045669 1250 46044419 46044433
    0x14150a12061503022109120c070801180302010f050403140d0204050607030201090212010e0706120b030f1006082103100b0c060a0e0c01120b060708040f030b0c070506040b04030c050f 80
    0x5c02010a0342c20b40c11784034083c45400c040182461000c54040030400c80c0c80041c070b0b9120200307025203190181c6504022120752070070703882c1c44406641d074030360052030b510a40080c8040340c0b84144180407203904840142c041144070202c4540030094500034025840d000340300605168580011440c1a0420758044015030342d99485d11056150000400e240e102940c4000d005a54078117014a41f107520300d10804040c080112203811220403141c00c02c0d19294005000c031610320300407080c190341c1c81e890b2103801c074076a520340f000c0811903007000700d07001b800da6060071520071410b0702100080342c0c1580010b003c900040351248011030b42d00700c600000c10318640e41a00420880c02c0c100d603680100c0d040e0a200060030703480302c60111000d0342c00c689200c0c0c0140070140300103030003600707040450380911410400a200c200002400300703400380b212046405584c01450032100315a030b0b060707003504640301d00d1501900d0b0358003050014002401c2240c2541c1e215200f440e2140c40a01c141d62460b240c054145401001034000708 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 46046919 1250 46045669 46045687
    0xc0c08070504050f010f0b0d0207020d0c0513020c0705060702010c0209010306020c0c060909060909011808040e01090903020307110310050412020607021911060f0a0914150a1206150302 81
    0x406044c0c0c02c0000c3d030f41d060342c0035450600b0070301c42e041e07003840382c090000004180d15846411303c0c3e050384c1d60940c002c0c141045400007843c040380703c0780311070141b00c0c802d4404200d29020050b89100343d0702d50940090041040c5030401e000c01146410070030003281007040139010000141c84221409009510601015840f1418001414241380d480c40c045c6000750014000c0280b1903071a240159044071007075a05020f642c0350f81c9000d502505805450540e051040d45100d820021440d0040c002c54042031002d0310140d884a5030b40055843e010b0000d80143d000348422070204120030929218144002c04a0b20030f400500c4216055078421101270720b5008000e9803140d021034040c48001c0e4001c0c10b130b00c00350a43d001c1d1005603542c18003108030003030080f00290780c0800050301e4902c201e4640008804503140c542101c3c10006245c0742103801510110003481c01503038001d041c501c00282c00d406e50b605100c2c1c10084690780c03c44558400380c0412090744c4e180c8070001905031140074282141c082c00c0c0c0e405030b5034604003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 46048169 1250 46046919 46046921
    0xc020a0c0b0702010507020f04290f0f03070b0319061502010b042c01091b1502160308090102191506050d020a05040b060c0304060c02010f0c0b06060306010c0c08070504 74
    0x41d4002003a00c4810045480180e910604492440e50304658182c00a8003a50210300101221032912084800384500720503000c581095150486c40b0880b01000c120704503005003c1b9041600c0c1d5043c0d016170003064140070981880307018551080d01c0c07031200920908000892405da4030240d0000100c1d145e03548250003072642c203002d0400002401c1d1003d10108580942c502d0a00040840a0504009010100c500102c080d08460f4005130001e00340caa03812841c5464101c1c0d400c29126189003660040340e5145003500100380e080741c240300382010040091440d20303003155a83c041c039100c41c11400ba80f06100540510141031202c0103006628840c80c045004000038111900c5400c114840c04c0000341004c01a6522003503801914003e41c1e004c1400e02e81d00022070214010132106c58507901000c45c0101c0d0040e0f1101c070300c8864a000740d80d80010001e0303114054036000c0c40c07100c020703101e240000000794050411a000710b4201c02d0606d06a6111100364035040c0345445103810042241e00900000c10645c582 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 46049419 1250 46048169 46048193
    0x30915111c0b01020604080f09090a0204090606090e040209040c0308070b0f0105060708040506090a030c03050c03010b01080f130302030904090311070b210a02040504020d0504030f05090a05010e03010e010c020a 92
    0x5007801040b020148030b00203503a445009200900486001520200d0161110b040d01c0309200c001d018003005040403102c4c6000380d009030144486a91601d0710004005204403490303000c84080555540540d26140c00b0b2008102c00180296a201c60103030307000002902040003016002d025104000e95400d012104c10440701c410381c05548039880900807180030441490803a01200d00843c1d40b1070f9201140c40201e031841990b640060810000d40b5000000c4c0500803500a0031640210000c101c0e25003d440103640c256000d40741450220062000114800e0712507009601d020701a0048074140fa59400006082e02e00c41103045001131b802038a5041c2c41030041001002601c440702c1154106600d0b1002703010190344480050002c10019800f007a0717448072030350445000c5c200142040d56114080c001c0100500b105840450001314560b17860300c22103100d9000c2c0c518200000344404051480d200c01101c814040f00741c1d10740d040d565480b031410a200244540c0c9481d075515000307003089201605100301d8085c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 46050669 1250 46049419 46049467
    0x20909010f0807050423160212030705070609110402191106070c03050f1c1a120d03090203190501050105090901090804050108090102120a05011e0506070303091511 72
    0x800d1981c10300041d000400c3c10340603030303505440c0090f5251030601e612101d100d40207401d00d0380307044000c14804c001c076080c1d07030210054400c3e408450328088440e402c1e0034548012079103000040c00600c00d85000500e140c00210649014041c24a20707003480e980001c0881c5c1c4150b400100740351582c802c4004087d0007c2000101030312030005408507140c10303000542001c200d10f000400704440018110b090700501c00a0301d1080c1400c047c070143c28149100008000c0442061040c0d0303813090724070914442d290005c1a45400881c00025000050b81c41e5801d030007411541c28202d030705000f000400c80f000040303408031000c3d19000300e00100300c65140c0418003043c0744010300f104503280d0526003201c01081110040320300721031080c80c0c0210b06d9500d030000e0030f00901601c880d80381c80320a407505100036a034203500414103860000d44040d440b66445e01108440d41c01724894207070040b0041c001c400200f4000c2d80405000360098401030b8039100b105a00e18115015000344007003461001c107803c9003c039041ca0f40380301815 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 46051919 1250 46050669 46050689
    0x171908060306130f050f01021810020705040b0301020403060908070b010602060903040312051c0b0406050307061d1206010e0403030f05040201020c090a0f0204090203061008040f0602250602090901 86
    0x104041000c07030745400703000348265250034403503010380c1c20041216803140380c00383c21a0540d83c603c078402d02080d010f5400018625442c6921611b0b101c00d91510a400100b1540b00360020b0985a00c3c05044c000500201c40b80d103685558203000c0080820241e0140f100300303520a44e0156030b50000ea140c400100101a040002103612503810448031403000070403a400c2d250407000819040c90040310440d0b0038406c1c505200c2c401c0e074880c501c000304101c030360304010171684044905001c0c00761604245569072421303103d6000060300d20105680303400540102c1c201c0c142005480c02100441d0705c4000f6103000e40a0b0301004002c5c802004001c06d25a05202c0da06011131030000501c082c1c01c040e00001c1d0345408201c0d016200e5813460020998a10856101d10155047c4c0e010564a1300c0d51122120000d400c1140c8140c0030701c12110f10b01d144030340700c0c3c0d50041c40303140e00c1803c4040300b02403a12698001e401100d08944682d46040c0c20f492549602003880359581c0c030810000d81e4408038038040c00412081030384040c1c1ea10f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 46053169 1250 46051919 46051921
    0xd06030b10030308040f06091a090c06090604030b0901110c060106021204050603010302130914210c06010e1008070b030415050702060703021606050c040515090102030711030307171908 81
    0x940c8480820340054001100140c0d03045603040030030040c22942320040200000b00c900c0c10441c0d6010401601c11000b000560f881003140c8424407a80d4403070410303c01d0340040100024000980e455080c150012984c100000394285030b00c031180c60581c400d05e208849a44214010048035a04004080144800c98110303400d2a28007004508240810b020080c4142c0c1c40304917401c00848150300c03450181e500a100101e441000c070b8078103520303010500e0403e0030345d8200d82500e07551401d090b811a40301c004100010110707070703103400313941f98000c0005000114401d4100c00c0c006506441000440301400c1a0b44410b540d9003070500d041c4144e5080c180002d9a001d00300400c1100c00ea030040340040d0701904a090240c4c1d150795000300b1000c205500e070b83c01800380e481c14003409004450800548140c540c1564103c00480840040950900480e030030f041c01640100281400680300360b002c0005071002030304483c03c140f00d690b140d001c1010068560003c035100441c1d8a00048485040110b82c54800c0c280800d01d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 46054419 1250 46053169 46053173
    0x5070201050906090117010906060e03030c06010e040f0501090302030d06051c111203040f170f0703171c0b1903080d05090c060d0509010c03060e06090901020f0d06030b1003 76
    0x514016040807602c540c0004c5808003660340540c00412082c2c15843ca0000c0da5038681d00030304c00410a602131940094091540000c0504000003103c01000d42c00c4028001c513864000c00c0819100c000700129041240d401c09000003c1003400790348403452080c1c0242d80c4541c4044e60400485d400c9a01441c07081210001810550712003051000526030081404424502d18070040b0b40044072243c4110342c4e510000900142500205200b18160781f040519480c0c0d04101050f1203903558900c48500710140c0001c4004c00014070000b40c0c1c0c0348500c585d00e110380e0501544001c500c1042c041140745188154032014164558036100d450104900103001c2012141c41c2140c540111a001309129001c01581c0c900c0414062801040582c0304150010100355403294911061006050b041d28801400c1d0700303001a15045900038003900040e80e045001108080c0d444d5000c0000803440a00a00c01030f541c00c0011460002400c40140311000784c007800841d02d00d02d9454082d00c04400207120300c09001e00b1072001c1c40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 46055669 1250 46054419 46054427
    0x110a051801091206110c070e041707050615030c0402041203020606040507021e0124060809010b0f060703170c070506090d02060c0a0302160f060b01020a030806100e0306071106010605070201 83
    0x810b840c2c00c100c3c005081740440700320200da481000c05014031403051120001c1e01100c004e201510a62096403102095030100d01d80803400d02600c10002c0043d0480c07400100c01e038410001e1b9400e00803005048444034100000400e0889c0e00c240c10034071605c603d00303202070706068040003c00d81209003a1010003151604610080d1a854600c205000075020345440710782c010f00035081000b210741200b15040166035400802d52090290f441520080f8030700500042c0b0181040c03082d00715194002c3c5c410008807400c0d004100c61540450350803402d10150341c0074084a0b9003041d440034800d1607890780480d5250543e0802d45c0c40c2040080658010340d20246d241500e107903001c04c2036a00904a135420f00e46034a11294260041d004d0f01401c102d002807840c500c0c50a02c44401010451540650001c20140c4150001280c4920721441c014022402e1407001c079526003010080c070054019641b51089074540c0d5180000e0030204255400030000c1c0d814610740f601c42c5414010303603005282c01d0800510304041035001074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 46056919 1250 46055669 46055699
    0x3060405072c01021609060e07030c02070e0402120105040c090b0603100b0a02101401091109010903081b01020f1218060a0c030e011509060602010204141003110a05180109 75
    0x44002030300a00c450309074001c02511918035800302c1718500c132a4503900c00f02d00030860391003441284000d6502155a0b14024421a00d01001a074098003000381082400d111070400a042243c0280c05680c41d1211014288502c5000310310a6080e040b126291481d2401581c0007080840d100f0b000800c2840703440c121607070030107003240c501496150311070f000d580301a81000c3e07d50038805c611504008800c0059900c00e514035041e9440c001c2c0070062410200181d05160107200303030140c08030342c0321603090000c00d01c1ca00c00340009240369007069000d40c4c1d03030b200c80f40d081e80c000d200003540c01c51011482e8030f0003514404006030300c928204011000d400605000079a0b689014146108140e614000c0a2040e80f0a030400e02c001d0340e41724000d00c400e51a0b482d04010700000c2e4030490310707280d05d001c0c800701e482031046c0200c504984990032107401e1540804104100842c1c003140c0501899079940c40c549841c8440406004400c05075100c0d01c0e25404072807880c6101c61101c541060410030443c41c144a00408032600e1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 46058169 1250 46056919 46056977
    0x906040b0a050d0203011107030f080a020f0904050402120f060402120307120c030315030506062e030b0a030507060c061b05252f03030403050c12120d020306040507 72
    0xda0083e06030700101c0e00400d0800b18001070381350000380d05003d054001401c3c049190503665403407401c0e039466031003000324002c0c50211900040c2c100040712192402d03420032500940014500025403070403d05071807405440e10115007058109000f004254030f4540311307260b0000203c5010710302d40220740c3c0d201846018080201000c0c8900b01f04004e003414882c0d03014449142c1445200203400f41c80b400e116a858108454943c858a41c0c0c29410a02c400d03038190319015104254482101c494074110146c0207482c0891a903504008204000408070340100304840060010351510440034035070b030400b01c05441000c6404500300040411240032258840112541c1140180402901e002d4804c1e108605111003030707000d0301d800e0180800910003080c03030742c504904000e060740315414100c0b081c0525441e4042c61101074116040b0010b503510311308101e0b004000001001d4240d88905261810040260f004660f5400b1b845034040200005402d06218440d000507160138146240703c400404201200103052003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 46059419 1250 46058169 46058179
    0x91015091e0303022e1802040b042c030f0310210807020103091407080303070207080105010b070b040c0b0711090a0b090c0901030f0504050307120516030e0d02060a0e0906040b0a05 79
    0x908a8000d125100d0503038000070b444080c070001e03100d003009515001e0a00c1b420380c866480d00940e01c05e9450301d071090080460303503200102d046949404d030030140d000102d840b07502070307010401000b082414000c00a61140c42d1200b003041481c0d042c6040e030110300500d8100101900e25940010740480e40c0c2c04203643c0380e41d0342403801080b404881d00c0d296030500e404a050000d54407961401050504010002d1442840d0503400c842e52180d95496082c240c8000f88565281d5480c01c00c46580422455480e07154081c1c0502e2401c004640d8411100165a00c90001998a180d00d11740c1702c84c861800e415065008407001c0024881c0c08201d400150403e41c5c0644041d1450800140107040c87c0d00a401c004110091800d0401c0b15250505005440740d21060045440119008900041901a900740c958030b01085117203480d484c1d41c03513906036070741c119000009600c003400185c00d07801603a4000050070381c1c0348a40d82d12001149008148003242002402c0b81d44500d0401c1000c89442d00e0303005080c000c880f07040350 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 46060669 1250 46059419 46059463
    0x6010b03060a0e091b0a0e0604022109030406021005060f01030903020106090903080103060f021603051e0307050a1101020c03070f02040f020c030c070905040b06091015091e030302 79
    0x1c0082c00c0b900c02c0b940000d8150042d4020081c0880c00407401201c002d06402030700003a04620303004c002000600d0300800381d602e0700404c040707030850900b079014240d2105488940001b00012a03245420041300b10340600140e4400202400980d5052103410804418070b40240007078204140080d00314550000018101652402c507181854800d4201000611160000f04681c0e010350030001c004500c00d002c15242c0a051400602c480800d9200b16a030f2683c403507610320903845141d5011a0070703070b00c007160309030409245165124160f07003000025409028141c4a203940d8036a40742e00600420300b0000550080c4c0d10501c25458600404070840708019072005880c40e031400380b480010003c1c84113a03007541c00b6610104101c10700440000041903400f07034000442c0c02213030341d0704a0f031015500f049900602da201140045007160814800b030741d030090401c5400d130203030680768103500b0402c1c000d030000e200025084010410510726201c400131140451040340d242194110744010355504071402c0e0088084140341 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 46061919 1250 46060669 46060681
    0x30308090a080a020a02010e06030403050909040f021f020f010501050a090903090806010b041d1b03131202010506011407121b050a0305070606050d0f0206030c090a080127030206010b03 81
    0x10041c42185a40001c00540780c4a0030440255506040c1c0070481c0803c4481d02d07961240d2500724152440b07940c0c0341c1d403244d01d007201394018803140308405002101c10b4140c420780c800c010f9640003080356207075641a403070151031418000c0003454101001d481c4882079142500501c00c3d600c41100300e03415641d940c0804290100c440c5003c0b0349000841e48259214003070b44001090780300460000b0003c440342510a000c044c6401c02409220000517114000f031040340d43c0030952950002409180e0201001d07a003400009440c0c2c40e4000d0b4803650902e80001031759103108100c0a503070000a200039048070382c901c56007000e001d90741e11240154200802c01c03e10008a811160160310021007000c8940d010080d50060f0609103006055a040044101c400030b08090000c205414604181d042c141c0c1c0180c4919401c0046809101d110fa1001d0315500c4181d5042007036030110703215861500e0042008000020ba40780068100c850703541d85076240008003000d0170901c8408280d0026156041d11030741060701c1c0da262908 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 46063169 1250 46061919 46061923
    0xb07020a091104050d050d0908030315010309030905060a09210201080c0c0705060705060f0601031e0905031b0a050c0103090201080106141902010e0706020f2104030501150602010c02150103030809 86
    0x991144d0f41c45444e442041c0d04100c0d01060388042c0c001203840f9410496190362180f9102c1c0400ca452600d14454038561480562007500981c0c001406403c00e0a405500c034800314056610000031a07000c210303052010820388071250b000d030f600f900e40600b010180000c6030b40000c000900251280c3c1c01d5400203d41c9131130310107041c405500103240042620707985101da8606240c071401c08890034503e580d82000021190f5019014081a0b0a401070090840f600440d082d00c00512070f80ba4165090b00c1b041c407000b10488001d102417284500b0325401071001c592213141451a01d942140d500741058100040d19005036084503040b4155105810141e22251100254400d0780c028410030011860035404906034468040d400051103100c010242d035081a190a8140c0e5202c1000161450950115000510581d0152005003908401e107411500d465500d4640030700b0b4031007450001140341d08244c0100b0031240c0900c41c400300142c241c000f41c002c1203044444005036080502c8040c2c1031048c08000144001b04c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 46064419 1250 46063169 46063177
    0x3020103020702132a02060606030f0a06091503060b06040e0103021201090b04111810090e010e0106080303010509010603060302031b060c060103030807120203010807120c090f050406060b07020a0911 87
    0x80301c80108007501002410300350b500b4450071712010404161040f01080303031021511511600014104600e1500d9289942108400c020000032056540305000301c2e020029001d84400c0038500030b1000389150a40c01e00c45d044540c01c0f115140302c2d410412041182000312105241100e4044600710650080328900a0140c16100e9006250341c5c6100b040204102202032a1031042001765041410340741012801d4180200c140c4a0321845403205c8001c0003480d40c2c1da00200e4950740100c00201c0d0210200300100c0c25112a40c20000356500301100512107420040315003401001589000e11145145801082d10f80c4240a03c0c1d4650700444803040715540ca541e0b0032909034030f42c03c0c000c9445540e0b4a0034014988082075446d140020310f8a0421000c100c0b4500030b5074184da100304041d0010342c0c9404580c14075030103032406c120399400e0013201c0050507001d03620a88480e44002080410103107410300d0140e0443d4220742040700143c00074000e034000f580703400e810300d0144c03120784e1000500300385244900241805 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 46065669 1250 46064419 46064449
    0x7030c0b040303021b0c13020307030605060412050c030a170d24050a0b0c1515090406050907060507030c0b0a020f04080109110d030804030806010302040308041e0e0c0403020103020702 81
    0x204030303051008055241d4010a018910440955240c10f100480c594492100b1800c0507844103400010070429140c590046130483e10300d003000607846075202c002c43c40c3d07900a42c0c040a50b11201d00300300d6081c00030034005d800308101e046014280e41c021a035120608404104036102070440049040500308a165100c55140c0c0408480034540011120b510405c81c035a901071603018510000c0c1c00621440c0d454259041c0c1c00083c400b41000c01c08034400401025070080c20b4070b40342c545401da9034400d81c480d8000b050250703006a00100e0f080c82c20031455440d00001d94002010044200030000100c0d074842855551140d00032105055034903410310401c042d000d1040c4109100b000001d00041c000415070081103152312902148000034410707410489a501c03803840280224084200003000244a036040940c0007505040040c2040e4a0351a14a40303a0090303001010910001c2496944000b8105003280080401c0c2c1d0428402e07203441034070b9200718000d074400281071503004609881155141c281e51760b0810 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 46066919 1250 46065669 46065683
    0x406080c18070e060d0e010c020105010f03020405131403031006023705010e0a15060521010e150f06030106180f060308030703090b09030301030804060c06090b0423030c0d0507030c 79
    0x882d0401040200d800684641c60007190300e42241c012f0050078100d803e0300c8452146145541c00f80000ba2400800c08800c10450042010000705003180c0ca618a48051004544a1901c0d10341700d6420b144540003541507600c4051f1f8003200c101c4078080649040d16001c00b506241d00d9500e40200541c0511000428550801c0102d500c580000120035200c14002d02c03440480d5a1084056011034015000325500301c001da4040360030000c2d0000780300c0b040122000000542c8035001603050700300400c101403c00502802c0051018018060641980015040740200441460520190284a5003003030400441d42c86850507a1281c84543c0400002d42c3c0100e0120382d2840c01000040050020103800c03a0000511400b044507000c0010699060740d03445026949081e04150042d0742401c0c644000700d900c2c0c1c1c2c0722050340c40060740429400780141d11582c0d40540c91241002660021004155400c1003940103004034041000002001d540048183c201544d66410b9401d086807611410000079100f0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 46068169 1250 46066919 46066927
    0xe030d020102032707050415120b0609060306130209190e030405010f0f0c0605101203080402031b010801030b04031103040602030904150b03070e0406230406080c18070e06 75
    0xa40d4064000314864410200c03524813a1110341d41d8411040c50710440d4803501c0e40103100078070036420f10344d2100230b151000324005850140d603a5501c00154080d500d049800715445014052941000010250400070803406020035291004c0d14401300342e80f8a0000e80b1410303002010412002d21100400641d0258000a0000206200050307540741d1140c802c00d40000d07e02002c3d80d0100c0e100356906ca01e00c04490780c5e40c055140722901c2d9000600406015030001c2c0580b05000034070582600d00a4038000e10039128404145410700406041c80c44c500c0800000610183c02e00c0d00c41d0b0303030110080341502d80c071032414803d54032581801c58900040e29402d07903540c44000b5020072032a070008054044000106c42c01d00140b4005c0f51404800d00c0503118554580c081400811211070064503071903607541c0b01070000141d441d035905a10b10307144130f86140c40d0b00c1c00c507841e1181034417420710380960006459000300800c0c00d1003103200400e04140019030700c41c400c0c1c041000440e03001d5110300300c00b02500100800c100e0321 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 46069419 1250 46068169 46068193
    0x20607020409060f0f1a010c0203030a030506040b04020703180618030f05011107050a110301021e090d080a0e19081905010609060b03092a060c030d2c070e0604020a0e03 74
    0x105446c00c0c550702c00c81c40b291000e294541c8101000101c07e54054040d50070f040d42844140c01070071000c1c1c0745070303840341e210821403849407141d00c040c00c00300b402a51703608068101c003c61804003182035000320707041010760b1041c08140e0361481246c0e82240d0f0301102241c1003040a041550041003e080300802080d0000394401c140a00000c00150703207401741c2a404001101841010300b02e20401c403144d40055440c8003c0d0214443d1a005007801c400c0217080715055801c180d82d81d01e6164440300540d000305050420403809420035114868401401c041c24501c20b07030404d01c40540e07840c0a210903c1d054441c7e044d880e010000c1c2900128010003241070103001e040c5c0c45981036013550300200c89003042c501c40c8221800b1610a40c600d03401502d000034900f124500e00f101c09000d01a84501c0c45455140701c100140588132032180f10b00c03c100101c40c003003402c070708807403000d2040c02d103240846d00c0c401980b181c4010300401c1c000c2008950881e108840042c0c1e03d92280c0022344000e41084031842c3c0c540601200196 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 46070669 1250 46069419 46069421
    0xc03020402210108150106110f100518030f040e0c0f03010b190807080106080903070519050d090605090d140303090c04060609030f12110601060f090b0403020607020409060f0f 77
    0x2d14040c559510781c000ba03880c1c2d4034141d03880e044681601180301c680001007004034040d118145021054000303546141040c81455494142003960070800301da038a004016030340c170360b50400100c61428800518540524a154040140124050201d4020408022072160950383d400c85064400032411103481c0e41e51016a0303440ca4002030a283d03240c4051074440d03c4c100d8400d8462034442c0c1c0701a12000003990820f0000c5540d0800204200da15202c00c01c1132070003040e010040c00100040911004040c1e5110385055801d01c0ca440403010140445884180502500301050315042182900c050042080030300740b1030380100c40ca0720351000c00e004c00000d0080450700458900c121030010785003804000c1d561001103840050b02d20014148071001685800080d01150382100f070b90300a843c0021082d090340301d00906004082e81b000002c500b6001e07543c02c206400c4401440104038956156043c1403950b0007185e110b200f5094020312899403607010100701300056004401c8460041401c0040b02d10b0303502d142d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 46071919 1250 46070669 46070707
    0x80f0c0f03040801140c0d051503030d0b10030c0801060806010c0c0608040201080f010807060509130606050d06270e0111030a0e100e03070209041406040f0b0a06060207060c0c03020402 81
    0xf503542003c08480c0400203c41189001d603c100b0502c42c68030080c01486d80041401401203014030403421110809958104054800314400a4001a078684460704008102ea4501c00140c149402c0c030071005041030f00110030b24112038580c2400d1600d540c42200490f40c0b00c5910300b00500c0900010320228040da4010f00c3c3c10f204a1003a20307212596203680000d83d201a80034800c04580d50300414060018030300c10070161061620140240c00911a6000120f05548441d040f0303600040020a01d5000301c483d0b40a140005e024138134221001084074441001c0e003030702841e03c103c001621000e0003030030f01e00254071440502c01c4d030444a98490801ccc0000c1406810051007240b1300b403140100707a40c2940803900c41e040080d4150802585411166070034019509401482030f1894035207500c0842516200740304261207240300d8200d103644d040315454480c004400290030502024908041400ba060300020700d0004c0d60802d0a02c0c900c5103086160000c2c00c6086c0c1d40000350003038004500f4681d034000e031101da0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 46073169 1250 46071919 46071929
    0x15060f08010b030a38040501021207050301150e03030d0608010b01020c0913140a08030103030314091b01080a060906030f0c05031605060a0e060703020705030601120b04080f0c0f0304 80
    0x1d00082c41120109a81c401802c0c0f0040c0070790020a4031003018540c84200c88501c0016240741000c00381d00203c00104011080f14140c503242d4001401c0c2c0b1101c240c0740c0130142d000380700341071503410f47d410402c1d541000109114a0070510044d010a2100740c0e5082042c1c03800d512007507000340285500c1e5070480340600a0b120b059809445041002886490480b180d648640b0480300f4205001e500c54039401003d102e200e1110605015072103500002c00d11150045000c0c0d8081e403408141414082c1c50000314100090810565410068440305241d04035445544160400d1070204455201c1c102040001d003019070000524610f091400400c1080c1c02910001440c017030403610b2807041d59034080c036448014241c1904554100000c050040345480c40103000c0b0a400c61070000c000300381040100c0c10f40e902c10300c1d007a40540c2c07000d40104002d2400300501405402d0030150714441c01115507408101c01d4002d403004141c4034021407914240d000c050144c495117954001200c1160100c541c00303603140e40c0b1901403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 46074419 1250 46073169 46073171
    0x2031909030c170403030e04090309050d0303020909010f0b030f0612010e0c0a060203040b04090903050904050a0b0a06050a050d201c0605010201020f0a03020901090b0d0209012006070c15060f0801 86
    0x3c0c01010700c00755040d83d0450b40c1680b500b441c84444041000000c042a00f4100d0a01100c9403000c2403540340d810b076249015102c2c1c1c40050760303541c83c20304001d60702c04160700840c0030030307501e180c00c0c40701d01001c10a407030300801e584000340c0c101d44410300000e88031000b2440d541e0b483c3d2300e440450300c00340d480000c5601c40c418090301d54001054548404036128810b90060740e2030301808100400c007083d5540e03c000001c0b4024174150307080c04081d000040640b81c06407541c05403184c480c02c0c1001c50f0302d0321104641c000c01003410014505046030501600900585d000c0000c1c80e0743c1c4507540d02107803082c0040f03c140746603800f07109603480d9a6000d140d200f41400b581c3c400380071440d1040105555005100303ca003412070140206091172581d1100310069801840c8041c100510500b002640f4540d0202a200c048000103000d41c0300c1c9c1d6050001030494001401c030040f0f1000742041d4848807000840c0d80d641228246c0342010110302e050800807162090b004081d0a03691a00303100007a1a50350190a0040d2884100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 46075669 1250 46074419 46074443
    0x20103063206040510110a0503040e1503060103031418030d0f020708010905060c0a050c0624041a04110f0c0a0605070c030212160c030501090521040902031909030c 72
    0x38010302e40500d004003500140c3d0901150802030050440740d440328050000c651101c0015603485082d500300c0d501024400c06044240700c1070180c034002440c0c2074230054005040700d40c5142ca008101680480c80b00114410005003501c0c0344402e00c4800b000e560001d4100c4110100d24500201007603c030b005040010b00810101140b81300040c007440c48115002001480c003511b880c8210281a480501c900c2c00344802045052a403403018044284075441059050b9174070605600c040c92065003040000c0d200b5403030310890100b80e001c805c802e000a14410b890000301d040410300414500c0c0b11300e00d100e0705044808600c4501a0340001400c1016502c176460a105070380325074800703136a9030310000401000f580001203a215203482c0072014103001d00f01110054000305080c1c9441e081c41113603810a540c16512901d20209100d0300b00114002d0480002550000750003401c071b680d21030700032801019620f5400001180025104400c0c80300c0301030b00001c040140d0509450050032a1262607001c803403081b6031603 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 46076919 1250 46075669 46075769
    0xf090b0f09120a05070b090f0405090a030f051314030703020612100e0603030706150b0703050414060f04030b060409020909010507021002030601020a060902030a12050a0806040b060409020702010306 87
    0x8180c4503e00c1d5407240081c101c8600348610032026030044100706402141002c50304045a03594040c603070203280380c0c1014110302440d5060040c0030301001c0f604030090007401c105d05c0d07200c106a40041422a2046010071404d0419500000d0904003241e0011b50301090101e0740c407104040c03424201e802040b100b05001022a550034001002000440c0d22a5041d00700703000032408034403142c00c17064040080f1815a61030984549008000c1e80080c40258009000810b05004503040104082000c620880360135044c48000c0c04510850300c100d000050074207418002050440d2250307000f260483c0d030b00a05500740e619018040b18020700084445400612920004441d0450544200c034042ea0f070690261400040f541c9031440a0070003c40101e130940b1907080d40501007080b100941c1c2d440d45c1e166442e81d03580c012403c1e0040180c3d5000d01580c1c488c902d4014519040d58900044070704840340c40b50090b0315203004c0e00061700140659130100501240040c0d01a0740078a13040e9414030000301c541d01c2500089500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 46078169 1250 46076919 46076923
    0x10609180c0c03050d0603080307021f0509060103020d03121a01170403080c13030807060c02060106080105033c01020306031005090d0302030415090c0e0105040203090c010f090b0f0912 81
    0x1a00301c1008244103010000101e4803541c0108050701c901003002c1403181c1d403540d5031400c9510484414005821911010501200c0c0c130303000c0742014000000500450401303421584c1c4940041c80000d2160203d18003410405008440786442014429010841c001c100d141e1007008120a08c1c1541c000340c00040c214000c104005a400c0c003658056840b0280d958078021401c1d4607a111540a46160070300074000400560014001c1050502c1444041a800100703c0040e16211040e003000c01840307402001407015880009100070074080c901070700801840703400d10300303403030004000d48800841c0d40c1c49076198840b003015001035026103020340c120745004202242c031300b0444d4801d841001003031304070441040b07000b071003030b00516000307409050707440190b4a46299000c100c660003041224020b848a000b0040801c000003e1401004151400e5256260005805031100801d51410b07043c0800c40081c0c42415210301d00788405480f13590107603503407044501150807982e00282e1803248a00103020400b4030030300d00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 46079419 1250 46078169 46078181
    0x30c060801060306060f09172109030c03060114101b060e2a10092d091109220e03120a09051002030a180602070201080702030a0f1404090501060918 65
    0x1b668601c48030506141901000524001065440e4412104910b4461980c900440c0c0d0034410107000340d580d00b01c10014181054100352440c1e10a420190040054020410949044000c00c907800402c001c000e41c0141c5030f8010011400c0d8107402c411510108001c595400355100420b141c0c111400c2011101c40c48000c441c600d0081e03504c0c503000d400e40400600b4140e10418400c206420801a41034071242c81040d0350002c07070040010000c421f0000b680460340b40c1d0303052020b0502404188441d03007004c5003420492007041c840b18001c0c2400f01c0451a5401d1541000402d2850040244840d4281c42e4460350349030000c9541d045000c0248010400c440814840c2001e0690301c070010700201c14a40040d031000350801000380c1d00c183d440c0c0d1306a1742c601101c0b0700303ca8a0f85100300d000580323800c144c0c000105041001005070041d0743c4100034148001d900141c001c0300c442c0c1903161802100151058560b1940030f01d40c44508200e003000008543c80350441058000d80380c0302c0c2c8a2346265503105010000f0340321 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 46080669 1250 46079419 46079447
    0xd0203070303020309010e060c070b06090c090d030e0402130303020c030309030d0f03060510050c15060f04020705030d06030c03020315280b0307030b0106030605030a0203120304020307030c06080106030606 90
    0x120400c94440001d000b60003840e40004103000000b80d07103240c060401d06000c000c8800209003840025218108244422241e40004041e0303060305042c0f40c00b00303c2c20f43e0b0b071251001040c400c2c2081c010f90700806100d941144c41a0700e01900c01e40d00c400340024010402d80d901d000c200d000d4064440c0146075030070700006a44190320002e000b03094200004c042951030340038088144040581701c040c0841c07030b511901010b02644007150794107036440300500503244c245070703950f800c01c4081c04004003480b103180d40c0c600301a080b0358001c4030b00590359043c41c600300789180301e140f41f20140b0300e050007000030a10280c510103508580c029002e40e05c00091025060300c1d5080c00304d50303014500900d09201e201c60400c0c5145045100078590707000407481c90b5180000c1c40c200c0c0b1988219990007107140140500c90340f6000703407001468198018402d005450b4002a1030b200c07451956080c0103404800035003599002c0102000a58010350100700c007503251003004105071001d01400c0d003c07a0030705038002105403140031291181c078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 46081919 1250 46080669 46080673
    0x2d07050d050604141c050304030806010206040507050418021801050406060c08030a09020621070201060909031d01090506041211010516020906060c030a091d0405030a050c070e070f020606030d02 85
    0x3e611581c0f04c403208403907a004500c491048000e20149000c40c0d07081e80c004101541ca0f00ca441e071034245002095104014600340c11034000c54180700010324000342d008143d400407280443c04440c0410450742c0d280e500c050183d8052281c54113807800001c60009903059800c240c60a04c007264072554141d0f030b00030200c00c0c001c20100e0104005000714083d64490f120542c4010101458101040c0280511080720580d5030b41050010703041c09451502480707810001c01d07000d070040c4690305003a117010300002144507007040754040503052031846a1003625240d0240400500442e204c0e41c03105440110300d00b000604680c0c00d50602160b640940c021800e40c2d003601c0605184404801d000d5003404400c84029014035007040c010710402050031828070141c180c0300050b99604240514098824501c0406541c0c010184d000303c400703200200304080100c600d418580c0c10500d40e0707102d14940140c81d111280c1d0050310100150384c280aa12a0701000e0307030400002c1c50b421952a501c803441016110f85e00103240001507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 46083169 1250 46081919 46081921
    0x609081b0a18060b1c061509032a120b01060801051e120106091e0903050405060309030408010606030f0f050f0106030b03030d05010e071202090d02010c052d07050d0506 74
    0x45004602611400c4002c200200d05a0350b00c40d102c4255801c21400f51035020090303203c06400080511503100140340c078840000c0605580074002d03044598a00010381590075103501c00038000701d0f0710161240e94a4801750356800654400c0c544c0c041100d095411140a070a0700d000143c0e403442030584038162100204035100081c0ca08040e4200ca1010f95a440d81180d0250400240a40c0a02c1000700a0500300d401141c0308071050700003e000710100e0081c2c601c1624054101022039030044c2680c06a03081501d0301c9680ea1a8004854510301a5500a502543c00c081c00402c0199044d0400180034070b000c0700074090a101d1900e4441521411035035000d0a900240040003028800c2d00841196440074042c1c03490411180802001c0d99002d0b0048a2980484802d00110743d500c104520000c1070030200441c1010119000070700c00460500d00a41007042c0800c0c000107000c02400b0603403007030035200500c1030402034070507081c003208a52854515240c0510b61002441e8141820164241a03121014000d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 46084419 1250 46083169 46083179
    0x10b0c0f120d020d0906060308090102010b060f030403030926090405130201020c06090402071a04050c0a0e0610030e030c0705010f05040f2c04061401090e0307030c110a0609081b0a 79
    0x213401001c0a056200d0301d6182182c049061440344001450080814580c0c540e0705100280c252030745010200e02903001080348000c1684a40207403604254980b4004c10180250b080c00340c004450078506459103603a41c118100c000780c0c104001c000c0f40406580030704c030f1540c03224034031041074285502c040e0152b00501c0041c40c0f80d240210041403d0072000707000604200246e04c584460b00c80c00741c41455410b0800081c402841000c015196203807400312000100d0390304001c3c581d605080c001c0c2899014440e400c80c0c4c1d0a04502981000d03040440180440384c4030f401c08001c0d6aa900d000303120f001c0c04103100c4600e4030b902a1150b4100d03402d850b2080349488000d840c141085050b4180ea00120400c0c45511032035503504003c0341d240d40d02960082002051852400700c0c004003010040e80500d1001d4548851024102c01c04000d54a4050301070034241c60b000c40a0420300380702d4031065546a4000500000070032159040318020043d00e51314003c80d4507142c0c20581240080b22000489580800c1400013009 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 46085669 1250 46084419 46084421
    0x50d031202041802091c0f0303020903010915050609010614160611070507090f060e06060306010e030706020f060109020315120c0904200a0303140a090e010b0c0f120d 73
    0x8241005200051805564140b00da0207054140e041900d0140c00017031281843c07820a0070f8602e0100921781110342112035030340744510002c9804004042c10303008034107141265000e50200c0e19154012044c070a96201102c0c100004003401c581040c0700d0b001040c0081030007841140c120040410305044645407090384840882251081c040440ba00d6442e030b951440700b042c0c010040d2010324801c1008003200d5040040ca90203540c001c540304c443c00d601d0070200300100f4100005544c1c02c8407007501d9041e901d844000040303a02501000c01e480d0548546030b4000364469000035200e81b80c8504000341e0705180d0302d5641d80030a07840103840301c100340c5801e00072000306890001c0602d88054403400403500881ca014012840442049070141c41d999085045111401209036104144000443d50960f602d41141e07405405418101c3c1013409107000800d280d0103450180e02c0000107010b81c081c1d04846580e66080300c2c1a141d000c6001484e090051180d101e41542c030004040780500d00341000c0c0303402c101c0b515815170 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 46086919 1250 46085669 46085687
    0x3031b04030507060f080114060301140d05060c1e04150503060612070302071103160303030b030114090d1806080402040f060902070515010b040b0315060913020304061104050d03 78
    0x8501100030000000061000c000880c010049070320341e501c05000484c4003030000c040580c04a050310980300f4844032240c0e03c40d01200e0546000011031354011103560302042001210000040680c81a20700b4055045407a4000d095000c403a0707242031020a1202c0100599400740d885100c00688a41150111090255015503030101024040b07a0510130700c0c42d4a181009425100e06012a9000501c0030910a1075000c0b803005603400d50041924400d1100001c0122046100c05420566170b00e11125143da0300303401098580c0010f003a40404d9050400c142525a08100c11007400b0880000d507907140e20f021492000c0482d001610f0702da140d507a42e50203200203000e1680500c3d4107503980e4400407405c0c840c240b02418526000d42c2c006c0807540300300000384007880e10681002e07038a127505020402440705100f040329030100008a402c0221290200490030324041c40a500d07900009030203518110400e95405144100d014078002e0041070b540e15520012031180e8010903400c012006c01030400b20303005130502 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 46088169 1250 46086919 46086961
    0xf060901030b06181017060909010204080a08030f0108150a051504060315050a0501080d030f09061107060501061403160c050f0f0601050a0807050d06021e070b0a0507020303 76
    0x115811014100107429988400b2208402110301306201825062440c100b0700792480310b003821750b0803020855449983d01d900411003440741c4a2400040c034017403800e405907402825403030100e80c804040c61420f01401c0c1c1046600100c14400c6100008000c800094180c0405030b0200c2c5d59005501d0301000880a840000c00a01c2c1141c80c0c05100311094581e84654001180504100805024407402000580d440030703049070095030410005203e04034000c510b44c3c00580441c180000d00c10410380703c44015040015014040b1841e000b40c1ca02140340c40c000802d46188110b0781000030380c0c8c944100b6192000145401081c024052001030b981c101c0f0395107010801c488034104045000200da40d6103142c01d00c400102c0040380c1181c0c440312402c40e01084558050b05d001c6480c05080303810007000c80d6903075425104192080e42001c00b003405100444e41190040200433540a0f004801501e441417140e201c12001c03542101118002003444640b44100350003014542c2c042c0d80b464903542002c0200d1041000c0d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 46089419 1250 46088169 46088171
    0x2060a11071b05190603050702211c05010e0402030d0c121b0c06030b030c030105090a12090e01031109070804030905100516050d031104150518030a060b040b0105090f06090103 77
    0x4103050b600c1e4030840d1811142108000000c83c03c1520040c2030f0347c0094200c00942d80309820300c4403d449100040446405000021a100c0303442c8070800c2100c4000e43c6421100c540307483c00206881c1d001418040c403480c02070f0200c03852031210300d90480d00c1502c2504c0c0544180e080020b0002c48521070904a204d041d4403003a00070412026484070400078000303a02c0340b00402c0d13442803d0f030080e0506000e0170400c0c807c01c4008102d946081d4070460f899003070380c0304000d0048241c0f0100d0b00741c45004031040303405000d410700340303074055a12454070304001d0030710101d050f10401500000812151081d9034052040364180d40d0b000482e86003105102c152041140100c0500009003e180c2d01c1e10480c1c68041a4580504003c003080c0c5c1c100e000140840720424074035403409204120030721820028040d031410a00c1ca614100c2d54bd121941801c4211044c00c1e10000e525004400c440401c0c048103030001c0da80c0f030034100c2d4100082200080150307400d214007280c0c04c2d000400072039820020f140c1b11015125480301810 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 46090669 1250 46089419 46089473
    0x405030609010b09060a0605040b03061f0e09010e190b01050903160f0807050d030c0203010b0d05010c02010c080709210c031b150801030b090a1403090102060a1107 72
    0x203040040403500724529039540c2d01010182d10b0a0710181e500700005807030303041c54503060000041c61407056000d401d010f140c0010215400ba164809554114214219200302080c5550307130061250820404140c481d100c0100003165100301c403c849402485009807500c17040f41040ca060001c0e10040744841c0c1485024801c2c074159840c144200c0750002035103104681030506203420281488050b81101700e141e030082c1d100b0300c9951548000040d1032038050401c0740c502100f510010f4007620440c60710702d42101c0103540000030001d054011000780303d0035070000c0c04085078081c0c04541180f0104d45240c005980c0c0101000100e1681c1c911404c9900c0d400010b200031615510780b07880141d0340d940211f80500d944001070745401042c1c2680c41c01350258000000809400c220000c1031002c043c0809010102a4004943c042c1010460881c003543c0c040494421100f900d0101c070b840c0d4201c4281c0d1800b41c050000040c00219080c455000d40d42c01030347c840e1713061060540f02e040c90703100c1e0f001170741c500d408043c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 46091919 1250 46090669 46090679
    0xe09060a080303131e030503010b070602070203030a0e1002060601080109020c010605061603090e0f1506120a0b0a050d080a050a110106150f030e0c092e05090112050304060c0804 78
    0x1100844c41014455010068a4600d241041a0a68880c000340e508100901c101002941c4035003100c0c1151000a10700b038488131582032050007481540b000035030511000401d89805508414401000c603000c50320b20324120141d1006036140c2c00102c80c1140050f03101d0b0014000e032400e81e800340542e510110000115545c840c03000c40c24550041c441c030f900d440b400505600403d5800180000a461002101d020360306101090300c04803040507005886800000b001d20030551215404d0b120002070325200c3d60074130308140c0f20300c000800d622820395000e6411a54007040718284040b0f81c1c40043d5000c40700701c0c50700719085c03421245a0044a0b40303504200210015400b000300c240640c5016202c44140360080c00c220a0024019120f0088080240750601e107c60710540000b1a50f0312482d241910035260a554480b50f0025007012203106c615070202148000e5482003c00100700103072241503510296a17600c1e81e0075500c548110803001009540200004c2c8016441501c4201800d03115621560501d0344032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 46093169 1250 46091919 46091923
    0xc0109060e0303040605010f0b040308070305120a05010305010e07030206120a1506030606030c030903020a150f02070c0f050117150303070605010e19060609030201052a2505010e09060a08 82
    0x800400090b610110501c400c0c0491841024010111395814041c10b9190400882ca640203621014200303a00200707040c01810302a0044440e074a00c00c004d0b5804510348010480014002800151407641c81c1000c04400b4600000390702007500d0f0010b21050034414046951040104003d1080890503103c0c2c03074002007501a0070002c4082c0c0b180741c0303010642c04e09045008080700c00c00171628081600700403d03e000b19401080800d40d40303800020b4242c10f81d09841150011340110344201034034a00c000b5915081c80444101300c002c1e5502e04d8116048d29942c0e20046540080014007114986a10004240707000800c800ca0303580c01c1800380c296410001a0307250402120401d90041d03a00031034270800c10100c4035160794480c0440107031040400050f420048024401c184ca030000030b06020000030645000144020b101c2c0000b6840c04200044c442c80820490700c03001c09010460b901d03401c0d059081c21901d040701170b50b416100180e480c205c18030361078030800244400107440c40d5004407003014081600710003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 46094419 1250 46093169 46093181
    0x120a020909100e010603020a06050d0605060c0106030302060108071d1308030a0906050708070207090e0c031903090e010315020f122d15040902030f0609010902091612020c010906 78
    0x8103400b400307051a504195805642c1c00002c00d40b881c0c0d00d401800d1005a840d039410f01c003610000c0c94000e480340c0c912a035030170051240c0d8001550000010034002c0907070105410900035288654207866450344d803500104d40d50f560314002e0070309030010a00d132540000340800c0120351000f002d1504c1c003c503103896164244d00d5482554a10f000d46d88600b280030500100c0d01030750b03422250038540b422051400303110094440b00d440c0107600b002d503158044011810000c00c00c0b502c400e03074010161380e00c4011940001c15040030b406011404103501c01e100054100203606068100c0780c001d072105c00300d501c400c03802800079030080c080034a0310354050090526084010302020306c620394a1070317000c14002e4201606083c06110f480222100c45807070080014185004805192100082d14081085c84142c40081d0038106040d01d80101440340d40e08215054005404c408101030082e140c0e4441c544400d012424440c006402d040d0110710080c040281110b000c1d401801d03040d924900024602d042e030f50314407081d07501c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 46095669 1250 46094419 46094431
    0x10203041e090c080402030a080c071a0a020606030708070306110f190207090209010e0409051203280c0f0c14030d05010512030301060219020402040e19060b0c030405120a0209 77
    0x2101400c0c48228843d10030b03014511290306104010340f42550020780c0d1070114041c024031868001c0388004d03990404200c9800038202c2440004080200003151604079000307103401c800107105117000f1807103c1c2000306995040d144200060804582544c8502000c2c10705008040ca0f903480030807041c070310741c0d1040028056141100c41603066424000c0802071070504603401000440307104010402c983c2c1c0e00400d00c440a0b038000e8402181d0b00b09281400e5041c0a030081c1d03000d030f00040010400051541aa401982c3c03104c01c421a0780940c60b00b00b80718411500c444060710081401080c03851a0300b0700501c00b110700d051051443c54243c800e1107003072900316001044080806a181c800601051170595280c4018480500040d41103601d4020025651001c02040f41c0c058265404c14074191744603501103034058010041c400320281802d01d031180e407480302e4011002030b041c54081c0c00704000f00120112003980300c884d4002c6003418101410000c50780400c0c4c160601c035124074030300c400040e1130348101c2c40e100b04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 46096919 1250 46095669 46095719
    0x3040519030210050903040b07150e0a0b0906070503010609091d07090905060c03041e050a0c0609140109060207090b040915020403150608070306020309030c0f160e15060901020304 79
    0x410741c00800d0f400e0380d00c05007900729150401d100030700514819100340c608094212410280a20341c10000720000e007052a01c1041c01d0003440e2011062210109d00280201142c070104e4030742c6e41c1c804008444da0702081c0a4117001400d24017040042da00507801030300c0102603034092180b4035411010030500e4a04a0362201c2502a220301540040c407030306000300c56001490605003841c40c9019a280c1c02550a160358500102d6070b040040000e20030104518940307549d0141121140b41e4659202500d000703a18451420720041c1d044000140e07510400c0c80804644040d00146030311410115524080d004198580d84c005030343c0c084031008101c611036242000485000c0c010303501d07811400c0c000d4841c450568004041030030202d08001541c1d00003a120205d0f600301d640141c0f00d0700c415001c107003148140e06000c1141c0c0300f040888280c0c46004909090000003070400e003c140c603518800004886e0f4103c07030520303000000c906880d400b410070b04005d0201600503c1134a143c1034641000c2c0320a04003555a924484c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 46098169 1250 46096919 46096933
    0x130908030a0c030e100e1b0d0f05070b070812090a0b0103060b0d0804030606050a06050a0c030807030b09070f02062a0703030603170405040c0305091b03010f020409021201050108130305030405190302 87
    0x401b024007800174110582400424030706c4014002c10012000c00c60018140c001440294007800350501101015146d03240c0ca243c1c0e1002c90b400c052400750072440d41a1008405000410074403000003a9240300b042e8004541e80ca1a07296481c0e80008002155069800840700049a40004c8800d80244040c40c420840080c0d0203003080f05020041c0101c4d0030500501c1001c00440c50099005402803043c550b141c5480e419a58030403c084000e0b000703640310103400ca045041845000d03a00b00c1b100c5030019010382e0807038036155507020170640c03800c40841c000c16414912404180e8012404001481803d000307050200d0103556036a40d5125202c403804801d0304189007c6020310070b80c6000c1c00b4000d20bc0c50180b40601c110b08018050649800107e96100c0c5841c0001524842c0c6850a400c40407101408400854485940f0425080a9400040e02e02c034400703940700000c6942d40c022110580143d001d00e000c00e045041c141e40c00da07225800584261490303c01c3c4c110760740c1c002c0802102298002c4c4a64060645 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 46099419 1250 46098169 46098191
    0x302030f0d0f0501050f0d110109121202120405060729010e1602150609060d050106060201090c0f0815070306210210020d02060a0b0d020307090209130908030a0c030e10 74
    0x4866040e00f00512561100e4950180d907600d83c90744070447c980018072a8441c400c00801031303428051a5100c1c140f00b500c4400c9080070722900d0b8841041104071a000c0d9115681c20b03040001c241d00c52405483e1344070300c0600a07000412001d54894100c80368000b55030707a1408211501a100920991200d054140c2a004100820340901502d441c40344c100d0000f0031000584070400c0f02e0503100144100c0c0100411b00018900f81c0c1c4200500c007010b40c008000300402525144000d0103002d64131300a541c02c007400500042d107800b06240c154100c2e030b000740c090500c0c006d004074101640d10b0302810160415842d800c01240c0401d0018007804140a00058000003004e144180034049801c0c41e8024159000329920798099900800d20303e0780b12881400004944081c800001c4c1103040c01c1501940511407000041120441540185000e2104031184408011420030107804d179000d0541c002c01d0110140007044039050160031140d1402c1c85428040f034150391a80509240c40c1c084e1880442054413040c0d03080e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 46100669 1250 46099419 46099421
    0x604050d05030f0109092405090f03281e020303060f01030e1507170f071b110112020d0e0a0b100305070b0c030c07060504080c04090308040f0302030f0d0f 68
    0x4090a0181441411843c0c80c003082d004103481446110100c82e21901c800d000c000344003204402070400a00501a198020b1090100a01040341ca450f0342d0703c100032880d405008004299040c0f04698000226450072000d480100804401020014002c07180044592501e20100e83c0c444081070b43d00542c3c0302e00d0450f003000080a00071a80b1414946003943da61030b00700e40881c81c010020300b055085189034492a000701c1c3c2c40107240c3e00d504c008900c0b01c028840c981001c512010301030740059072079031981800010340d841d00781549540201010182050803100d0350040c00d6005640c101c81d9001807c010403036804c542500c8030103002a01d15003040d081c81c403c10004600d103d070001e941405400f10f007410342d5204c03030784d0340384900a4011208000c0344003d110881001168910440c0c1016103e40503969035010b400c54005000d0410700c1d010b800012105800c1030302c00d032031b81141c0541c3d46c0e46c920344882e100d0a01090300301c001901140400c01c881412171100b100184480007011034006500c030882c5007104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 46101919 1250 46100669 46100683
    0xf0308060603010e0402010f020c18011802030f0a0f1103040506060406080313120516061709010c080403050c010b1009090501050319031b020319050c0301060f15050f0c060405 77
    0x140c440c070400d00050107070558a480090f0300960a0800c400000c1e1203040991400d010300c490a90b110160004034a04105849880da040318043c2c104251034101032540075040c1e004c111800c3c2e800c1c5c021300001801d2040c840e088a10045814040014071941080503c0400d500840703080d035041c0d20281c00d0002508262080d5002018010051410404601c0280480c02840e10648800000101c0c001061080501c251980c4c5800c1110b0807032065a100c03000b40500398240d20718020850600d0000314060010300890441b1605a900c50400ea178455405880c3c1d80c02120100340f0565a0fa080c0e05081d0f04c034050000708081e000e84400401528000e100d4041d0341d0140c000303038085d0b0844030102d0404161100440030f481e5144c00c05400d203107000840701400340c6000101a40c1072042c1510b890340c40e5803031841c2d004c146015038280c0c0e9174418200d05250a8804a03caa030b10200c0e0001c000700504068041c51900c0707840c0d1460700324505024920405202d420855404007150054010b00c401c00c10108215 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 46103169 1250 46101919 46101931
    0x908060a090503090d0215030711120c0a0803040f05010f0b0411091509130501030605101203140310050904060b01030605010f05030105040c030603050307050601170c2b050a0f0308 79
    0xa10050280c1d95030140c90313010303181080c1e0045c05200c00c1c3c10110b66460029018426240740050340741e20340820020b04a89049210fa05140514103020a0001c112411a0b00880310344004028040c1d032a903c0c071402d94002031098440e034880c1921100021001e02459201828182010604030700100030003040b94600340c1d4a81c5094401c0020340d59944910a03000c480f40300d0300e64059200c0300c42d04089402d4540d611281d552051805001004000d01c0e0740c070440c0121070300500c0f04080c5480301e000e00030790740d24181d01501140f000340b80da4100014100003075602040c00c4c80b103c0001079651000c54603040c000e41e0100c070140d848130180704265034584074550003000c003440c0c10a0f5800307004001a24a00c418081d013400303582c5a0315050310b00c6010f60010700c01554424203c95507510039007444d586070f0341d0a0042c1d80998031250ba032980c1c200000550b12440e100000d00110305c0300454000144030701c0c0009403014100c01551500000b0036810301107192514003406a0701142d010354134000f08105001011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 46104419 1250 46103169 46103171
    0x30f080105060703090b2109030409060f0e06210a0302030c160b0403140a0c1e09110d0203060a0f06110f06010f030212070b04120b01080a080a1b120908060a 69
    0x1c0001c0317580203e2040803211a580b81c030395200001080f006c1c02c1e61803142e1200712804400144100302400200500441b600083d081010544545602d8034200307c07403284071b07036100c2c0d03420208103030380380c44a400301550075a9a02e440780d00140c00c200a0801c050901c0640142e080401e03030744520342051014040d44040342e650b0a41c0181050010399031401603000161046503108180307105031200b0064001da444c0c100c0401c3c1c090301d554a004105030f12461210346e6900d000d054001412200e02d01541c1e0780f0415480307506003840c0c000740c08031b4001d41000300081d60001c4920703000160a01c0f20388021028000e1130f980c40250380e03800e61034945480e0307010180054a0703200e000100601e218119203002174039812103126500d01d0000100520303058140d0030000e0803d200240004e00c415601c0c0354080c40c0780c8140c011020581c0d803001a20b40b50345100702c015001c81c00410030300c1d903400c0c410b6541100b0761a0b64003151501070059220b1540a00400380c22030045a0b407000f06200c01003080002503400780d54168 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 46105669 1250 46104419 46104427
    0x7060e03070201080c0f1c06030210030b031e03090a170610030201050304030809100c050c0705030105040f0b1915030204050c03070c150608030c060703050612030909061201020304030f08010506 85
    0x40000c01a88006001a401c020041541079480401008071404851510210702c241e007059202c0000401e809c1c032080307100b95004040200030a01034013414444900060190101441c5002c0d041081c0070180038841550201b005010514ad46480c1d403e005007151492803212505034021062600001802006d01a0103043d01000183c1c0e00c88112035001e541403420450946502d10101d142c0400d171040300540d14240040e0000700d95003d8043d00c0140345210803600c11543d11001d05080707410a0360050500184407882e400401d0403164125000300c608002140b07008102c018240860725601801800c0010065042080d03180c240039041d00981c1c100c019078a1805c004c540135003c42d0350310b180181b04c0002107c90004107140c9504c01c0313001f482001c0c00d8a80d070b080001c0c04242c40342c07812079204020034034000c080f03181c50800380078a01d14072290034015807030042104100081110024110342e8010449508050500300c2800514004c03803090701c17035108034552018042c0c03002d2016040680158002c1c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 46106919 1250 46105669 46105673
    0x120204110c070b0a03020d05040b0403121e0207020d08160501110f16030e03120c0d030603020105040b0d060302130207020a0509060109140f040903050a0f0e18070e0a0b07060e0307 79
    0x10440c1421504980e040513aa14038032802179001e40114a4070b05203940c40d02e8204402d2000440c3e0151181e8403030350b19030b0103030031010040300b0859291440003002900411440c01a90304c43d54010802240000c015086a041c2a0740390b11042e07110900080c00140c1031071031001082000d020b004459a080e07030090341480801569032019008051403000b00540d40c4200505040c014890045820400750640c0c02c0310311000c001d410141d2280c100a2814407860200711b06480c4a40306007000e99905070b407086d16151522041c51201e030000310500b0b492540ea4000040143e03030f0003010440205100b48003580b15101801080001b041941c001e0b4002c000c08810400540e80c01100f21003519a1024940e09207500d45c4041800105130414058006240594106c20305400030041d04861041b0f03601c000017000714041c116940070202281d0783c0c001c1610701c0000c0708081c1c2c0c200c0c0c0f1603004400d40b6251039882c01c0704001450060244c0e12400456400040c01010300480b400b07450016150100154545034443e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 46108169 1250 46106919 46106923
    0x30c0904030513031e0302070e010f0b070515010303111605091303030207051203010512030403030801030b0a0b030106091509090b130302150a051e100b1c0501120204110c 75
    0x24030003000c0240004021050044100600c0051500a07503d00b002404086103401659507801080c0c01510550318006480500c0d4001e041c1642c03216850f49109918000c03000d58240c000030000c644500410560700501d944400849000b140265900d1050060f8800e080e810034980b1a6400c1c0c402034060381c180f089844481d20540c101703004d01c0c0250b06901042c1002c40090092050092103401a16044490851100061810385001702da4a14900c00c0640883d03031b0742e22079448001d02040c0c000c001000481e0303140e03001c01e600c881c01403404074201043c0c42c0040c1c216100340d009009007680d282074400107100440001e602425501004011314115600c5010b00c036200101000b1001e020910351404240c402d001d040e0140400a907151520f040104941000c4c5c0f40440740400c640c02c9580f00d03507000100c10441d2a000e20841201a075034903003000c0038400300354411460002031359200520920101503601c5414006e1040c01d0074425030054a00c100029200010100700c1801424050078004181c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 46109419 1250 46108169 46108171
    0x9030316030e0c060c0c060310090501080a0302060f060d150c031d0a0f0302010605131a0108070c120e0d05070509130b07050304060902040f0e010e19030e150316030b030c09 76
    0x211607560303c4991903505d49240002e40e400c4a03030404804420701c0032051600312203000390744001c9000d0000d0303a2950800f44d580e90040c00041c0050340a400421003a1240c5440560824409000a140311003a51a99061400700b20000410503546411015005a15106842410f0300361441c551610401102d40c0b03a8810207210060f2280c2210018482018001d512402c01020b0240c0480800c14280304a000240340700d4203190002d0410012140b0b096218070b80452041140d510341c01c480702c5503500c510f010744015000030b41c180013030360001009560398610a40c014603c2a4010b000b101d003400b041c86003000002d804503103410540340c0000c0006008000d0b032039114001e8039021340c50745c2d0380e410018007030900044069080b9103401c40584030601c141d0084000c1c1c9207107070001e21005100102c855984d592500000c410700c0c0701c4039a45800a44245050b0400e160024440403800c00c0724080c11803540e1003134403141e440760381c20380e00401065018040da000d0f40300101c004c0c10300c00c40340704081556204 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 46110669 1250 46109419 46109443
    0x6030c0910120c03170906030a05070903050f030703020f0d090e0c0d020f0304020f010e060406050702040e010606110601060207030c0e190606080a06080601030c0e0705070b09030316030e 82
    0x50000203441c54516030055401042400100600e01140d0b00780079011420a0000b40e44100300c20721400c04509044c0115010118042c1101e0f00e595203038070000e802004040d01d42010004000030002c08100c08100c00d038a0911840003555403038025144c013074501415800400c8054000c035482c0054941c101c0c00c90f804980c10400c201c3c2c0c182d9075207294850a0b2091075074030b4208500c00b0800c1c9001d40c68480240d44298401c1c1c1d078a0542021640c01580c080780191112075001c0402c010500c103252141002d001460720203040815809418042075003500c00c0e43d040308c4c0c0091101c40000c030303420004100442c010074050015164060035511100440c40c041d02070341e241d5802c0f070408078600c20224000d01c0c009078201c401c01c2121640b00ca10051000000b61403000d034050030104049100305010170740034103c90740400f140115900d0030b60a0514160000c0c13104007488401c0c482000401c1d94000802e06c12203a071806142c0c4c80c60035003080c01707001c41c1c0360b0140c508052801d103440b5100c20300000c1d8882048 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 46111919 1250 46110669 46110679
    0x61f091407030c020a0b10060305010b090a0312020703060f05090c01050310060c03110105040c08060c0a020604061109060703081909020f01120f11090f010c200a050a030305030703050f06030c 84
    0x101000c64180c0c40c00b220b141e0024154100d11b0108004103101c1200c0c5c406407007055030300744810b980e6018084424000c0d0310585502c200c0700002000051448001025140d00e03500580d40411754a450b1102102c000410403041203444604002c1c4550040c01403200b1074200342415421400e0151624000044d01e00034203050001d424510350905000750788681d202d850400082c000c1e4a010b14046006810300d100e9444c051145d480843d0310392000405983c0c940401d07500034200d681d41c40d00c070321018050070106a405181c08012018407612482c0c014280140a922004d0309030608e0f502030443c08402c10000d0100d9441c0038441c5005036144551001d080c074091802c0c029500c010710400008041442c4503070aa14a0f03c0003100c00418080c001c2d10400c02c0c11a01014990820b900540d4034403d4458020300c140b210464061450b4850304030841310910107880107000c151100003150300c0c84030582042d00891404000c1051165141c0200390b80070700c40340701300e40c6c20382084000320f5941c030310034100c0c18428 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 46113169 1250 46111919 46111931
    0x7050a1a070f0204090602090102070506030702281202060412030501120605071202190e0301020322080405100824060a0c080c1504031101020913020d090203061f09140703 75
    0x40109594882c19440d00108104100541441c00200a50002110a015004181d0005031620701141640d2048110740c025015061145a01c1410360a40c0c00341403241c0c2c0700c00c07491840802e2184021215501b2160010078103401c0c03030700f0b249500000d000c514100301070903c001400380d1000c070407101c80440da21000120b480c0e1507c4005aa4080c0c400c0300002e5818800300d40c845955244403128207a0a280b51191a0303e118840d0500d401e0b440304a6042c0b072300040300d104200c0100b59000c21161400d004520a078146900d0f01d0016009010722246980060b1901d0180002d005901c2101c440070708000c0200074105c400030000c11030a008036a2640d0a1090495120061102c41d4007251090f50081040c0c401101440b6840d81106a09485c2a00000d91311001800c6100301403085a9080c24018128962415030b41304010282d44000008440d10b80c07120840310060b101006118002d22010070304502212464120100703145079544400c940c135003020002c2600680068000d600a40c3e186000321316 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 46114419 1250 46113169 46113173
    0xf0525230d0215090a170d0f02090a030212071d07110a0f020108061503040606030b180c090c071e060b011404090207140303010603020307032003070809010f0c020102090307050a1a07 80
    0x800c07401c15001b82004010304010311030140075030020940804124001c01108440c51a102c00b203000c0c0154584c2c103c13032154002d1000d0b03e808003164a6005c440402c55550a4442070f00700e9078411900001c42d0280110414001501d4104a100700e80c442001d00400750781141e038803aaa40307101034081c081c1c18014800041001e60f15980041500c130800303208102c1c0c3d44d0510f480c2500c020000e070700c810b440552919000c6609501d0ba80380721040d51034450300074034903014160708100b44080050510740c1406020409440014201e40004000c505810090354280703d441c208102610500b049207410480c582c004030880c1800c4c50160781c1600d03895040141c0b100301c60316118641e580c01004410302840044000903a0f2541500210302c0742810f90340074809040056020049000d114500c0c00043c0814400142d00d02c4c412920a075001c60184001300d12800701401078170440355a8601000141d40000c0d6207101030a080090170010138059407400300591800c030320303002011b50401c807900c0346080000e070081c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 46115669 1250 46114419 46114423
    0x1e01050405062d13170313090c08010b0c0d0e0f0a0f03030e0307060c0303090606050406080a021e0a151403070305060909060402010f0525230d021509 66
    0x7505002d040c00341e49002c0040c0c0007001403007026078180703140240000074030300e035004100b030340c4060200d0844480d400c0d041c1600c0117500b6022036521001480b06100c0c000390004000181c500420409000042d03034043c00c1d400070403200e0141c100b840303820402c1021420b1100c0000381c3ca2165480b62402090f1603c922000410078900b06c40002d80c0b09210400201c1c1340102145d64004580c425207030920b208000b8002d16861342400e01c18080407a000380e4003240405d00030b8210180e02480f036000003c0640d00d900010f030803504c081d04039030307115400b503401c000440c10910401e00c401400070646a007000344200000c0c00c03850340c80c02050880080c20740d5884c0498001d0528030480d1522120542d124035210307000070010041180c4452042c07610030f010a403003680105815004680603540d500d0864134070242500c2c1688040080402c04521360306014900382045c1e11001c5580c481c401401001d15841400705c45c290180304100015002518400e4002d070300010350700c42002508d280f50384a941c808440c18 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 46116919 1250 46115669 46115677
    0x3050a180b030718150c0b0606071406011503020403021f020a0501060e041e02030624150307030b1c1203060b0c0106091503020d06090f0f0503090117061e0105 70
    0x414410000c0180f103140e40d040780c840e455080f2040220025250303501c00a2032260802031101c008244421b2002d80810000c101042e030000000d440c0b0343ca022502e0742d1fa00310b40301202400144540000c0018800f0f05c841c0c4007411500320789131406605050564002820540b01114010106000c4c3c0020024603030080c040d00351015040380007003001541da041216146001168212041c0d00844000240390441d0600050702c1030300980104800d9a070005107010703d60345201083e25421210001e00190f507070300d000800081d000010507684030b0501c01d80c042c0598a4100981e40f02d520b1086106030780640b80040c421205400200020782c0b964451020f80c02030034150400c980c000c200107141d020050054200301e0849074000130800840368010f142c425455003502009501110324010500894050b4000c0203001d40030380c030280040e0b840c43d9110702506c203c603038080b100345d040403550000b0b035a00300c1c9001d0020302a180c2060b08902d040c2000442254400004007810700b085114181e150b4481d0080d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 46118169 1250 46116919 46116929
    0xe040f1406010302090c0406020309090916030503041a12070c021f0203071202070f0603020d021911060a090809041a06040801020c0106050a03050a02060c01020d051602060901050403050a18 83
    0x4021900c5100021500c1e91401d0105a000f840c0a8001c51444d000200480c0c0844015902540c1400321103802c01c8100d900152621030305218110544040a41c210807850045106034011aa510b18144002c042101014410744a00301c00b48070354060b45480c100d0043c0d00501c60b00e0b120640c01d0440c80014a0408400401404c0308604001100155000001010842e0103a0131800510350511001c07a6104c0f420701900c100300345a84020001103000b50058010f00c00c602c400941080c0e01242c280c8030300803aa003120000030b2078000d40c407080408284946a04501c5c40300003404400510344529416100d0b6804141c021580c4040340403100c5190503c4400c60b030750007809555200da0340c0303110318081d4015800c114165441d04000184500c0c0645208d0102c030390103000f41c58180c401d5001c206044d00552450f205554080003581030000741c92142034800d0041c102000820030030140d0091500000400e01d403520782c541000d1001180c0c01a0a0307913006000340c908070903051940300443d10556026400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 46119419 1250 46118169 46118183
    0x3150106140712050a030f090512090a0b0a030c11030301060903080f1215030106170c040903050d0501030606090c0c110603190203040803010303030c020d0909020a031b0804020a120b010e040f 84
    0xf400b02856803101c01080d41081594081c000301c05601810001c031144001e00a046170300031090913101c0410f000180c107074000c0041c0804881035840c58400210b6000181e0400040d07a1035410002140d0801000610740c041c490066040d5030400740003524540490001400080b4003140e1819900c9a17541282e0800756809115000d904110b4450f0309035400202d130075403195003071101c08180d20909490a4074001c03010350044c528141040e0a10004014000040c1d007000400c02c0a000140785900500740210700c5800700092041c980000a01250200e40e02c007420480e0f07480f00000844c01124580c001500121000350340d80e2901240c00b008950303aa181c101940340044100810720980c1000ba5040b603000703443c1800680c00c2010201d07181c5c100a441c220204000f40818003500304d803a80900010062410f002444c034007182c07040e400500f2011714500004002504100841c02c01071109001030510390f045001d03403e02036881e50001a01405001030a6a80f90001001d01c0740d144150030a25802201d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 46120669 1250 46119419 46119443
    0x4030609030201050f1605090f04060e07050703090b0405031b01051306120608011b081b030c0310060905060f030901020d05010e0109140c04031b09020c10050105031501061407 77
    0x90003a0184c44125880460107140d880041d141e008201d8044461600643d602e80c54490041b0400c50f10b0a03041d0301607608a9600c48020500440d110344039802002d142e280c1d503442ea940ca00c1d0080880c5810303000900340301030600003000282c80000d00244214880070682c82c03102c0402004035040d000b2411181107098030b00c000003d400c1d80060000040100c034540034040079403078500c02e45c01d80740e07a00465115803404d00c1d11403158074070541c000c1e078102496150901e07041a0050152000c2e4005031011102c44400206001c0c0a00341040035400910460030042c018900d404000f86142c010600d040b00c016100000050420500303504640481e05000d004004c2035868074401003a00900340590341d007980c071340400301244001d861402072180c541c00402d0b82c03600c0c1c116610481d40034440c200181c09800103000200d0f0148260001c0c3c40d501055600038807003514000b0341076041d13460603408640a41c20001680c02100d00d610151410345010b802d20650701c00301c001e440c01180c411500081c01c0300b45428 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 46121919 1250 46120669 46120673
    0x91203010f03030306080c090f0405010207020d032007080c060a11071413050c1b0a1202010c0306290f07060615080601110a0201080705090d05010b150301060906030209040204030609 80
    0x480c070406681c003a07981040300a84a0640c60740e281c140000b5541d10005c000006502a80d8104480b42e020340b180001506241481e03011a2462000b60030807404140186080c0115148011900ca500742e07200005080e294a4001c6150f01c0303045001e041401801c001809242190040300394900208a07501161030640e59181004410190045e42d00d2141240040c0413142000900038240160615040c40e850b040381d903040e0f03121075078400405070f0f4140240e140e0301c0086503814410f112503001c46c0c0c0020403c0d8401010080c1124815008280c1414031700704100c489444020540b0301c044030740c43d1516030725094001b450905009003080113082da4106000400c00c0254201c880044c4400f070348038501c0d20303102d09005440ea00798035050390a13258403454005000d9841817880580220342402d00516220041d07010400b2624491010384843c0c2d1501400c000d0345c00c010642011200c4035540040c215414a10001c1014090b80b1442c800c1607004146c04901d9078841c0c0c101e070001d40d0310101c00c200d00c1d1118 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 46123169 1250 46121919 46121939
    0x70b0301060201060b0322210c05010c020111251209030b070503070c03080c1b0114010b0a09060e010e0423010504020a0e0405100503070308030103050d020a020d0b09120301 76
    0x24022207005508100000401d102c440c0c003039078090f0302c0c2d80140d04660803040040781c40c80a50758000781e540506502d130800071400701311b500030381548040d42c4285203245503003000b03420358101d102203908680c5001e246036440107103601500e08141d01d000030303000c488030b459440c110f00c8400752102500c5203400411010003540c0000d105000c0b20700c90820010603036034002081e0b41038003080710380d0808a070300c8100e402e000910840b107443e071041c0c10300d10050030b0220405001d1940c50b2810280f841581d03541b049542644001c2c0c41407401082c0c0d0140352454607403280001003485502d445690305028205281c0502c581c0103405803400060702400800280b0250b210324580740003440140c1e055414082d001240b503003072500031954044030700e0b15a5040d090200c0140002010000c0000301c10b00c10a070030108180d50140140030045018903070290f00ea50550414500309100c00c86001709542c400c1510a00584035401904942500040e01d0700c00f5a40702030540f8141985004400f00c060400000031440c5091 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 46124419 1250 46123169 46123171
    0x3051b0609060f22020613090e0c0310060501090b0a02010b0405070f0e0907021b0d05010213080706090e1909050a030207081501030b0610051219050a0203070906050a0c05070b03 78
    0x1000c58003d03116210740384002d03500c0e0028080ca0760350941c01c0420101600f050303002800488441c2c0a4040416540d2010398100e9100002074001908003440d001c80e0fa14003004bd804081000702d1b01002014902000609100e0041c072139245000c1001c546080201e0003035000313120380c8001400c2803004e441d02e20300040c0f00b0f01540303c48001040c541c800032201410001b150038440c00c0346170020160340d030b4654010100c0110b2000600c1d80408000c00103000103800780041d0452084038041c04182c1820084142d09060082c0c010108102d81007000308020320909070750f10340002011008082c00e911000001001d003401c041b002d800c0d0b1280ea0882810141c4c00540001111000300030345c4e00e8480303c080ca07503070102402e1001503c1c42c6403040c085503903450010701d1352443c0600c07420041c2c03810401d09100c400901e0112600001002c1000d2501c0c034078101ca00403d80e1001e00c0e00c00851641c5050000034214400342e005803800c1000c00305800340310b240030b18480d103240e1360020129402c056030b611149059901c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 46125669 1250 46124419 46124431
    0x7170c10050604110702010804061d0a08030103060b22020304020a092a0219020f0105070b040305030601020d0f0c0314040f0803030603100603020a0b0d091208061809030703051b060906 81
    0x13280c41c0c4020361081040d001c0d5042e0b184e059655002d281c40b15118480580f01c03142d01001e020309140c2001c0c0240200300040b1910610070001c2d56120341c51030805030212140003845500a00c2c0b070f001600100c100e0008050760303220001034016100c0d100ca0001c554035942d41c0e00514489442e280085010030012017080b0810034400d440100c2ca90031080e01240c0f2101c01012001012116444200051038a01d1000e0f1100c0e20600d412400d00850392505088034505480540c08500008240581568180422401c0001c20b080010744081140380080c44030121840c06010407071407240020013451042c044070020210034804032001a00c825a00b5160f034010b41e411882803107a00500190206076020b03c0d030440386c00070030000c02d0520303151030702115a0042c2d00407200160b82c0e00d025000192078602d0b41041546d550350f486102c0c60b0440c14841000c5c1944030003c0104110002c01c040c0e100c00004aa400315070601e4001d4403090988041a03400d4101d0354840c4040c0034203001c0140c080800240700b84144 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 46126919 1250 46125669 46125671
    0x61109120a060b061312060902090f0106020105010b0f070b0a24050316030206040b16020409380c071110020c090a090203060606031f0605090310050c07170c10050604 73
    0x200e1100820130b0a21071801d15000001640100b0030140c08800010307074419005030408613880c0000d40c00520b6220044034a000d06280100043c0001542441040d001d81043e81c500d514121015841e11180e00405c60000c000103e4400012030b03481460300043c41034110314250354200c0d03566131248450105107020300c90003481079041204203200c84111510449030040c204502c3c250070221000c0c0a5031007200303d05184040d180d20400161983e201e095031680c041c1a03c0f1b20000601d030110400c1d06000c881c0c1141d1029080080350707480e046803030003136000300e8520281540d42d206071802800b41c82e00c0002d01584004001e590b00300381900440c1c40e44504c10219030880080d039a04440c02d046400600d0081c3d01a4000300001e031a5090000066800c1761103640a40400e18401d2071428680038280c000c4000540003080d002c2d0310b42010001c0303003072122001d80c085c4440d28046045c1481401002805030130800c0c021100302c2070040c50320490b131881003054190344d0341041c402c0c03056010340020f0711800d00403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 46128169 1250 46126919 46126931
    0x40209131a090d03060b040501030203060d35092812051509030c0a020d030905130e010f09030c0f020111070b07020117040b18070906060806041d0a061109120a06 71
    0x43d6203c0e20908060702e000d66025410241440c00460094000403c0305400030344001b5410049070700721051107111020b0303110300103c1c0c50740d0752081c0c4451025000400800201030007112451b43d607101145243d600c1c440444400100051101103211840b0b9000108050980707200c513007880408211440d82c80c1c00c0705c0d8000210788a909a05641c1e00c904190116030707800c0f8090000051900c0890f03011414000d00c0d180b941c054a0703c1c0000d12000c01038020a03134880da54104185122400c1c040e102003112503401c00c2014003c661405403226682030001001007034448040c500316806445401c080c14080340443d508291103024104095000c4081680400e0320031076020103044d2035000c1c56206a0b8440c01040080d255480c540c0e801c402c800e02e00380c001d401000008a2070440034420900201315650711200700e814140c0c1400229000021a400c00e001c1110100d00e9030703400000c80080540c1c1c002e400054990100c068000c10740a0001100e0740a16002d906a07000600020300c034001d40d029060130480 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 46129419 1250 46128169 46128193
    0xb07031d0a0305070303030c12060605030601020c010e031b0d0b0906010602060603030301150c0320010b0f0306010b070215040306060e04050d02010c08010b070510020307051e07020108040209131a09 87
    0x30507001e03201c02461944040f105000081c80f9401941100086042126000141000075000e5410941142e0000758011081140e15a0f041102c04030107030081c20590070702c3ca4018042900d030001e084003860541411076003001c9a0b22034428568100750050b04245d07140c205280d800740c070b0308001e103c2c040040c0b0810010589501e804030803030341201c88640f40e0704d135070300e843ca942030392200004171081e0b05104e5203210482c3c5078030801e002c462003d1411070001980300b03905800c0042e041e030240f9500c1d004c0d5120a0040c407510050600f1038210a0f0100c0c3c0d5441c482e0320700d00b240c0360280710b1508000c0241c3d0130014000345005010740380303a0280b03104a05070381c11120811412400c80306204110000035804000400141c2c00780360091903654043c8041da42644454003094099900079621003000400014001111285581c2c48095002403145644e19103101034000071300395013020300080d20480444004c80d072026828440d820b2803039400492442110b11000707491038440030454503040c640c0111a00d40c14 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 46130669 1250 46129419 46129429
    0x2030f16020d050d050402060c06041b0f0e010501030213030501060803030a0c0e0901150207080303090a141203071b0506092a0102150a1401240e0603060907090b07031d 74
    0x50b0712025a91854188402c0d1840d01d0050b110140061360418010000750b000183c0600c10035100c0d9002e18a5a01200318003260007005142c0d03035115100310040c444041c0708000004035414110b480910b00542c45500d246082d035901d108541c4010302941c60480002000d039400701c040d52207205510350821001c004814251640c04c401d41e1010350140d500001400100c4a202145400441c030f44100d8940701d4941550b40d11b03550007612904010740c400113040080010a1050407e50282075014080f181200342d01401c2c40d00003d4244000e102d0480c2d01406008180c64070303800c0c1c558001080b2a41c504200500d19101d803508001c080c144000c12042440004540004280303894045c0d004190304c1c00d80176504c22041402030800d0030102e44680340b2000240c00702e401c0b503000c2c1c030540d828490303018a501c5404054480a40340b9806008949152401c10340d6060b0a503907004000340c64410303859076411001c0b9088000c682103240ba03000049541800e05502c880c2180c03c4084084c45c84071446901401c01c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 46131919 1250 46130669 46130683
    0x60807090b06030403031d030c0a0507050406030305030a020706091218050a0503070306180506040308071707080c09010903080d3206190b3606040902070c050402030f1602 75
    0xe40002c4108003090002c6d00c03a61049815181c0c107400e64511b042c5801c0c0260942c1e016000214040c4c2c0304000031014000244a02c1004003c00c075802c01c401403640e50060882c0c0801020364683e02d5000c907001e414003580303401515185500c070300d12100040c2948000b81c0a0071800100302040d0804180100702824214119810380300300a004001c1d451075541c803103003e040703da12002040603850600b500002c50402c540e500a6110f0340350405c0c03e1030b041c4030081250540c4d100c4d0700b42c82400c00c41441081134024090f1900710804801255403031720003e006a446544a82c4020b0014074005203000c0d040c0141d900c4142680c0088165280801c485240c0000d0b44c2070240c003042d01010707040c02288040c5803681303103d0540220b400c0e110003055901c4149091356040880500f0801030495410890b201001c0c4a41c0c0c0500c18142c541d1000d0f40801c004501140641c2c01607508540d80003805605104e107601d03031407009040050044d552881c248180c04a110b800f0344d424640c04070b20b80100b4410500101c0c0031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 46133169 1250 46131919 46131941
    0x100c240c0f02011a0d0602090406060906080f07140a020f07060302180a03050706050319050403020615030a0f0308070201020c19050d0503041e15090309080f1504062c0106080709 78
    0x84c295038611040090351640d0801c1122202c4d4200002da000c2d44883c01038400400c002c0d2a03040d49180f4219001c2d10503940180000500c030070075402c00200700d420070303071490b1170142c86051540c44807030b28201030346019001e5035050f005110b10807001903080d80c10740080c030ba502c1000701d6130700c00690f00d2010b1050101842c000104140c1000300e050040700d21900155910403001101884100c00031003696045079026a81a001a0002420002c00408100096554441c2580203142c80c0302e031070700c894000064001000381005404400f040e20746100350103541c0082040c2080e80c004042c0030705c090390351240340d0383c00300c6881c012400c4c0400010700034400d592007250081c42c441250240510311105a91411700112045210b105600a800740d0354443c1c000028487c0d00e40205d04c03801d004106107000300c1c00d204082c4951180300798185440c06084040d0300f240e8000b6002c1108070748085101103c140c00109500c100c086c80c4c2525200500541040080718440000c3e00c0d00280c480b001803041c0d46d004144 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 46134419 1250 46133169 46133201
    0x4140106231c02090a03031205010e060603060111070911040f0b12010303030e03070b190b03071409040f051207120c0c0b07050c060408010605030105060609100c240c0f0201 76
    0x2030740d01e0180d007031154082d048595041c0145030480b0800040c1201c4d000340c100740c000400d8000d90030000040c51051030f000d0541c42100000c0c92904d00c00044462100801c4141005030011080f030b96000c0c20040303900500801e140034030170480e0168110405401920a01c46468407030203001480c91100400c451100f200080600ca80ea800c40e1070503006031800003209035041c801080490080b440d18100140a4a9401e0035140d510a11080b0301c02079680f6000d0541c0700390882d2404000044c80218031808410044d80c0c818000d030707120706204403c203d440902a015001d0030505503003940e03900d0700401c441442681202003681c007076103080700d2500c030758180180b0b079400c201424011614000c01400485200700c08482c0800e05d0000854000d8015601220310790303444150601c0185400e0142e590300481c00d0710a9401e00703400b0000940040090b4030058140100c1040b01e03428800c1d6180820340940e18041426000c02d403440c050707801445044a00f0000030713100b080030481c0e18418042c000e140c000e00d0782 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 46135669 1250 46134419 46134427
    0xc080103020d0f06110307020f070f060e040905010501170d0c020102030d0e0f0d03021c110414010215040803010f1410050a0c0507080d020d050705100c030b0414010623 74
    0x10900c0124490b000050ba050307030902425100066050090303c0e10408104042901c13400c200ca0041d2030304403904c0307030030061f07810006050140b01108a00c0d101111020714110744501c4080f40407078010000031001034059420007002062010742c1a84584412110104542185018407000c075208402600c00030b00581040022034011101e0350000135880300f464080c1c800b00300c0b403001c00d189800c0400c01801c01017500440d002c0b40d03404581800f0a1075401c068414800b002c110138080001d8800c0740112204503855262010440e4070800a400a2602c8078a1030714541c145800d1040d4150024440e5400f00315038200701282d0b510300800c1d1108901030182227103c0e050401002076560741c0001000a0400500758000340201e0300c03c01c03080d07004107110070103080e944200d000000c1c2082c91001c0200e0138040c0401c050000200f00140317030032184890780c3e40064110706c207040440280003070800c6a0f50040c18821440c104060b4850140e048600d0b94442d80320754000f444504840e402008904086100140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 46136919 1250 46135669 46135673
    0x307080304140d09030b1b040b0f07050a11040b0d080a030b03010b06040303030906050c0a02120c010906050901020c0c040c05040504090c1a0309070f0f0302010f0c170901080a0c080103 81
    0x40051038115119050715414900032011462406054804140000740c80130410000e000007446280e422400d02c3d8406072400c84400300364000d1f841148202c000d401070010302072601001039800c2c0c8455551010680380c0d0099241049086241850196403045281280e45e41c810719000341007003182036002560314180300c0c0300201607005254100342c1907015500c1e40300e407882070ba480320010030185111b0303240010821890304114003100e40080158610340c40800c182405260000f8100c41401400e00755291b5480f110f05c0c40c1405018a228020082030034502132001d515410f401400d4880600300880b0080c1c1c3d1000e0030081502e458402800105c0c1c0100000e0040b030620b0703081000300e24001d4490302070311562440002440641c0e10661900000701105110071400c00784180c0b802003401c10004a01c10307041401c06400c004040c44003c0c1440b07044051000c82d18002d481d000c5d03600d600400742620030501d804003404180d100f510420300050207040005d1058400e0311507550224159034804007241e00710f03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 46138169 1250 46136919 46136933
    0xf01110301051c15050a02130807080705061803030a05070b13150f11070506040323030a1a1519080f0114061209010606080105040e1c031104030807030816020307 71
    0x1c070b0140d6691410648120413034425003c1e86000f280c28410050b03a46c1c1c150b082d901103450315500410000d8010000410151400061b224140c5400301c038116510b040c0b081860b8002e0301481d110740e0705070101040c22085030b9000030140030300c51b0003010102e26aa40382c15070100d0a10034403000800c03056042c100121310030f006511850300c000510324006404100c1743e1f28610260005042201c4c0d60b400311303082004140c0e000d07968407030320240d0145010f00c074014180000c1d05030100400030721400e941c40303115555401c003002e00310b03201c880064030314400c0003401d508080842c1d101c04072140c42060321444000110380300b4100c562150100d8008002540d00309103214104215520303070280d20107028403904400c40204c811040c099221480005045441c002c000f42c4a0141680920311031482d0201c0c00c0759040020400c00e43e101d581c86888807010400350021b900070b08041c850b2001c101d002040110802640c0c00c01004e03014001c0d2214615a66810222030181288a1071640103130410322a0364000742c05 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 46139419 1250 46138169 46138219
    0x3030209030a0204140a0b03060c030708040f020603040303051005060406021b0a0e090c011d0d06090213090c180b0105040b0711130c030c030b030d08090115080f0111030105 76
    0x8000d054822481483d00000d050741d0700c0e180f040f06403e001e0000c1c0700d0095810b01c07401c800504240c0140c451842d0030300151840307020082541082c00702003800101084000718060740740c0ca074028001522402c003418020001e10041328150b0807110076890204513441c0ca8000d440455007143c0c001c0a04201d0f0302c1107152113200c021000e0781c02041c0d023140415080c00c4160b06910030400c520051541482031000100380c22000d5a24041004450004034090384943c018035242503004200401d07010402e2010608003c00d88004084240c40c00389503104114101d1200d1080303c81c074455500c0c031002d00391030a200312400715032924007280003040304002580c2e140010700203584c0103880c0216040700b92400709006480500c543d1007015034407001007030600d41510507415865010300d01041030001e1100425900c089540344801800785600028800d2102500002245c0c0750100055407100daa829405e42d8440714420b5450303155084c14058000000c400d001e49040b12001040401d01c1c0000008603190b140c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 46140669 1250 46139419 46139437
    0xc010204050603130b060907120209010905120d02060f060a150207120309051905030c040e120703080405120310060f02010207050730080301030204180c150306060203031003030302 79
    0x502880000303202e5460b41e028520410f101a10710404d280740d840c02160102000380814895940141030144082c0d110b40c86c14003503030b1440300050303a03544142e0059a581c5c8840c0e1100d0f40c00340482380f005142e00000301c1c004001c0140c075021680d1036100c0006040c050603003150b0b001d030040385100040020341110703000245075802030b005460400f500d5050400403080000002d0b40400e42c0c0803030401c01410301d4560100c40c004038810144a0318104000030b900c0d0102111010310454488524011000c018880c54040c03124003540c06640d84483d14014050000868050b078242c0030f6200070803443e01701c071400c0b24821021880e841507901e04000c03041d01d003180c041c0d2102c5e00b1598203012142c001441041766030050700694001011f0a1400074041042c81c950100b0182d2844c0f0001412000031544000c0e03c0c15030760f0450f000308010a100710f1800000c1c1c000b880c0a0014028000001600024482d080496036001e503010321800e61034440a03030342c2e880295504401d071700d481d020400c007091183d0b003e010a94 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 46141919 1250 46140669 46140671
    0x50c0607140601031208061c020405060103150e0412020307030e04050705040b03071707020102040302090c03060d0b0a050a0c030504110f01050d11041701090309030b0903040513021207110309060c01 87
    0x290780d5204861078944243c10807900e008400600300512030300103c4056010b07004541c0103046403c17502c40d0460b0b8012080c0000d008a40341c00100307005a00940100d012006200d42d80c001240c0e0315261030702e06920035901520b05250002604850340e102000b11500507405456596001c1c204100b480003c0c40018820350402070184000310b00007016800a6010300416510f54802c000103540320307000d461700074014000750380c8104403c0006841e0080d2151780074500e4401d40e40c4035602c2e0ba000c980e00b41508140140408440030402c4160700c2c01e07034455070044c43e0442c0100580841143c080d42181c400741c6010701044d00030300a4000c01d1800c0074018201e090189071443c103040c40c03d561101500c0006c00c540030b001310049400e1000b840d400b9118118142820002d214040d01c40c1c4001d850080c0ca400081c010105040c0041c02c1c1510800c222001480080c14144054611820440080d0824000b40c3d0f14051007501041d8080c0c1f00f50701442200b042ea002030741c5002c0b05901000780135400140400015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 46143169 1250 46141919 46141943
    0x103110102030403152418021c0c1106150901091a10020a1403040b030c0c12071a060d02010828110306030d140703120f0903052203050c0607 62
    0x28000b211940020140d4000c04144480c3c49503005004030044c81c0084846520703544100040d1070104480c4000520310180181e884000c00349c951304503410000c0c07240b041403d103007440c045039500004c4c0a8807820414243d4503261140c6002c3c903140030042c0c0c07243c0c0c1d019400c86c0061150740070603031195010302102d00422a90110310000704108145080f01c41e405a0001c00c00780e03040c001200060102d08480c000594a03007424500c0000c910f0202905100d130415000c00c10701000390040282103401402e00800a441d0b105034a40307545107909006242c0d0340c42221001040050a250180c03801c0268141c454500076942e40100f10a102e0810701001d4030440c100c40c070039015100601c41c1d40c40018641422503524501107080c90324000c0c0c0c003054842008061700d0303180c2c050300c0d5403002e0710030059040c03900c00010180d0740b4000000c0c002000d844002649450781a0b82055001401000a1540d102000744002c0c40640c810910700528400034015400844041d0180d1502d41d000303000b041c0c40f4203115400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 46144419 1250 46143169 46143173
    0x2090703140414010b060c03070b04170301080d11150403030c0e18040302010c0507030206010312140313060608010207050709050402060408030a0806010314090c040f0f021c0501050f06030103110102030403 90
    0x401c100681d01611940040d01d10000094800c0c00740e03803214001590b41c90f18101d8618510366a80c800c4010240006500c080441c0400c04a103c0b80480d03000b4401d1840d4a0b96102d00d84135840380394200b8000d010038119100001800804210211400e10326558007040da6110384090b0080c012881044c410400c03100104145656940e800c801015104003100b0fa4524143c41d0103400c5821286400092082c2030042c01c00003640040c05130f041d00e1744601d01d00c60509088009450841031a004808a090003000f0488841400701d182003025001d0301d0b090000b1503607241511b00301d00c180300340540329422882080c4110513480e04056082480030b8070070341ca040d50310310040e429600f1035101ba000084481c024082c1e90b46c0d05004660701c10340c000b079400e030882c00c2060310640d944d400420307010b020799120300ba0010b41a42c1c0340e001103118a10460b0555580b1b2000c00c0d00000798240041e02c800403403428001051a0601c0400319200c000064000741c03440c0d007035480e603820041d03520804a045220411002c80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 46145669 1250 46144419 46144451
    0x50612100b180c07030f170702010b030d0809030f0304080405090702030307030f052211150405040e0f060402060c03040b0f09040b030c03100b030703140a170307050702090703 77
    0x100495642030001c0c101c0380240820007220502d624641c1d480d2007102c14080490000d004032405030354103082405030700f40c000341c051f90701c4208880d1500c103e00d0440100100503406411054929100701d06941d0300360f40c0058155424081650000c1c41a4001d101c40c0340c802105200640d0004d0058500c04c0c01d2a60f100c0009481c510b00715018401030308048203114186030940680c80d100c4401240c10322442c0341041c002402074200c4124100241c10088000c401d001110103000070350075001d07125078821030f02c03051021241d40c894400c01d0f00a034600a415070b80752801096070180a0f65400203040d041e12640c08100c42e0350010b6101c0c1009020410001900346210b2000317141059401130391644502a041c100000c40d100c4814460094008608401c940e941c0414042e60031926014005412011080428a400712a8000410074000c2c0328480c6070100000906840c49481502044d0400c180240180c51070700064903407401044052201c000107252490103540d00102c60316001410018070401c9103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 46146919 1250 46145669 46145683
    0xc02030312010b09090a090b07050d02160501051602030408120705030c150a1107020102060109020d0603060e0105090106080703080a051b030a1106010f0b0301050d0602041502010204080c15030406050612 89
    0x100000b0310001d04c05000b400d1044480f540020344000c2003041d4507468130389020051000302000704100001600c0d80920100368151580b903d8900c041040d02c8560340b81c158028001540c25480000120100180c1e0520010440b010350b1000750161054440c12810080365030406281115140802e0011019a0001f040402c03048441c440000000c0d04048200c0302c02c0700c00840b00c1681803042040300d00c1c0540d0300000c1c45c07030440e084242c005030307214400f2590500030003140d0001001c2034103040420380c20351015000a400b41c5034000003001002d0b40c400d81a03940c1e40d25480300074200c88040c456111100e0181001c0c00340560703220703010780c8441c0341c2c01031040c21a48030104180114494040d1815004c00c00c00015004d4400030010481903814401c2c1d40340c2901052107001d00c0750b40d08510b13490411a460701590010f21900204035000c0400f4140a03000c0c0d00036005a0402c1c0c03040000c1204145444003a5038411000d132000e03a441c503200c070380b184805410020540740c0c00c42c40604103001046020400d403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 46148169 1250 46146919 46146929
    0x10e030c010510330905030d022409070e0402010203250b0702030405010210020f0c03280f0806060d0608030301090c09080c03070e15040203040b0f09061005010c0203031201 76
    0xd503c2c6009509559665030b00d8000b40d0004204040d42020380646070401e200d4401001c1060124000c140030465560f081900700540500030708590301d0b590713a000100e40e03134800344034401454050101c107080e4441e000100e5000303074a41d0120804100364100c240d1850303042401841628608400306410308030390301442c0764284918000301500c0c0300340a028111250462602d201451801e4035140000b076440c40c00c41d03a0807081540c0090305c00380c050002c0d07003210000310000046e603440f080305041610428030351080c5084d6010916109420071482056200c2d43c840958580400720345450050140d03581080b145410030903542c54001c242124100007460017400c0180002c00c41201600d0300400ea0704150f806482d0a50152080d002aa0790209110301a00e8090035000090b42d40c42240286040100e000349422510010901c018030580302602ea100750380c103100e008284d80b119680c0e0340e070705e800c11514a002882c0b000b40c140320940c8680c3c003c0105500040441c1d042104100c9070200c008801e07804 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 46149419 1250 46148169 46148171
    0x3040c030b1503072d0902030106110a02060708070f0c0b0903010c08010b0405060307050f0a092d09050c0d05100602060702060106050f090103020c0a0501090b01170a1103010e030c01 80
    0x81042007069901403198845503005442030038011040100c1d03900d250314015442c100c00002d02400c4160301c0b20010280d503a00c0317601c1803411241d880c80100000e510a004210004101d41240070f40303008005031207000594042c000620307007001c907101c00545802c0181c044410320008840e040121300440340300000380c0024034131950345a2007101014215040031010009100748440100070b0301e5141425542203800a642581c3e481e580e405d81120740f4030440b2031131882c1d414085011056268001a00790940340881c0c18032603030b04604420650002400c840c115444d503600c0005000a40c0650020758010908a0b80c80303082c240c058001205540c400c466448007004042000c00549504011060b080449400076040d80d5041c00c2e001800c2d48548060203500d4000000c921240740d121790304039802c50fa001c100b0384681c0c0031700340fa080c1d000e003205a2094501c989800008603c05481ca614200c900101c18000e104030195580c419910950810545506540e030f19602c840240717003400100034010080c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 46150669 1250 46149419 46149443
    0x3040b0711070302030705090703090f0507030213020405060a0315090f02070507050604121101090e010b0a080702010e0a03080408090402040b0408011802060a0809100c05181005030f07140304 84
    0x20300144102001c0300c1c581c140d41c0c016201000541ca012681c94252181034030310b1303945650750100c141c02403e07010000606110001c0c07884001d000d004a1020156031084913440480200c2000403402d90196010307841d480681007080c5080a070295100340c10400b00c24100c004e08660300e0640008560000080640150700000c480003089001d00104010700402c58209040c10704000800c00031042080c0300802040d20317000791841030303130041c00d6074001410443c481d00d503d0b6131a08202419500858059008a2041c2020402440c0180100902c64101e2401801e0908403500d0844002d0030150007036548103002c0204041036140c900050001c0d04004a035141d0b0b881c41c00b40c0c0d0034211388000303920070207411407480600b00580e038420480c5e40b4501585084156612001c0c1d1841c100040c41880f03c0c4035038640080c2040da035402001070142d000c50032a10b941c800340350f030041c00712aa842408003400914100000b90a03035510071038a0f9000000c91401c0c14180a00c0840c0c1810b5510694003035034007451031a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 46151919 1250 46150669 46150681
    0x6020d090c1502060705341101020606241c1e0501050a030809040e1b04060503060609040b071808060a111c0f0e16050a050d080a080a020d0203040b 65
    0x70701d101c01445600c103007010307071a42c9100c0251200000b07450f16042020005a1507641c0311540c0d55010390303032070340345000c2c000c5440102140700805c400c94044071914808181c00c0f9441d03001052061017a000a0b00c0c40840b202c0c0186451794005c40750101210f0158284209603000c9140300049400007803007800041c00c03810031854185100a0080c01c0c543c118103000c011700c16601c1d212050811682c0c008222900c64040000150240c07941d800c109031284150494141c14150303031400103184440668042001c00e032204103054940c80102d40058108a62101140000c0d1942c569103501c01418a00300305c00d100e18203005034400d0050752150102ea1722207000d00c001b404185c4212113034003d0100b1110300d0240101035040c03182d80d00d809843e22050395140d0409420107181c001e900d192a520b800d4505001c0c0b01e83e601d10b01000b0310300038139000da2080b6802040b00c0c2082c1040c400c000c0d42180381d01d814000034030000c0340d00c00e0b4000e0540201035000e203e00100d0090390300141d409940b02c3d91030300e0f44601d000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 46153169 1250 46151919 46151933
    0x1050903070c1a071709090a050105130207050634080f070801050d0212070506210603030a020a061e09150b03031306050d0b0303040e04060e06220c0306020d09 70
    0x10350008106280e405100c150050250307404c49856560207100d400041204c1050b440840c001c81252a030440d12010401c00c400380b0903440315060383c1c011521106d00c80f540301c00140c1203002d0803000800d01e41c400e1001c1403c1e040b44589c904000c0300000c0c495104420b5070004402a041401c2c540c00108201206000c10f0b00e04d0359508a92000c568a400701282d80361a00048158518610107400b4000b010740802d2140010f0007443c1c050007000c0c000c03a540303503000040321214051000300c0c001c1c00740e061408a030903846c010049840c0b000300c640c000e1040d0070050b00d13107600070032034500700c031103a030390402d81001c1000b030b490068a540500030403100301000c0700c0320b1510b4207035200c80344018826002040340c01042d12000c5040c0c0c065801a2420a80310000003288074020460000351681c58800071400040c0170391312981c064070072480b6000c240002034a80c1c03030b903c2e521202030311200c0c20820341e03405a12083d01d1218000c046540200b058014041d500c1d140c000880c5d02c15000c500c80c294031580400c05000300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 46154419 1250 46153169 46153193
    0xa051e04030c030f0605130809060a1107060f03050f040b0103080c0f16030302150403080a02091210060609060302040b0d0c020a0b0405011d072d0f060203040f050301090b04030807050c0105090307 86
    0x245110382081c0c100035690300a180c03142740040341c0701307100c042000d00b115446043d80040303515001040300d5000b5191b80c00900703040c902c0d4280390300003410040002d182c80c04a400392400303a40e04c000340c00450390840e03407000e00d55088000b4070340e41d03841007028021201f90208013801416080c4e03520102603900b5410300900b080440d402c04000c003a42034040c880003a500101e0640d000868250041e200c82e0107800180c2503d61a4003404072901c603440941d0044081548000c04275145504c0fa02d603d199a41415016801580304601e10350500348144d000301c08040c1c200d40072007040303841900d141311460396a00a041d1016030741500c45a6403511403a08080040f6a060301034000354004000300c920780302c0c07c004492958075628030302c003440403419207107201c004034200042d2010f52007460032140c5a41000799240c01c10301c52000c0c146000c200c0010241410312036032554541140c90030316140d4071501d0035540083c010301010104603003008800c207005004e22415010301c1202000d0365440c10203007000031401178 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 46155669 1250 46154419 46154431
    0x40b07050307052b08041a070212071a010e10060e0d02061c0b01020102071e03050405060f0a020105010f0302130c110703150e03090a18060e0f0702070801020a051e04030c030f0605 79
    0x92079414440818600c0702c40c00565800040c030303000b40e90b071a410224100404030800c48442080460300c0c00420210000168030001e33a0300c0030344403d03a66064040c107040415940706142400114081c060303644594500000100040e120442c18001940801e807658420703001b250510404034200c1420760040d020303201010000740f000b54240300e1a42c075060b9103089901401c043e2034501030910820140510203460050000819040d154111080040d205503c074010b0130005500e84000840e027072554100d4031040c1c90300608400c1c140756540072140000d000c184824014804030824501a5500c1007142e20003131442070a0640740709500c400c581058605041c04c0150b5608188080805910340542c0c0f0700403111511100003005038151288002022240c10584801c0c0d0544104a0805003091455000d031505900b01c50360203aa43d9185801c0303002d440c0e69400016010006290003143d130b03528200c90544200d484614196581d9180401080c00354030455041880201c0142030111600c00d0b180d1100e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 46156919 1250 46155669 46155677
    0x1205030a140f04140406030f051501050a150e012106140402070809090406020c0105040605070f08010e06010c02120f0a0201140901090306020d0e010903111b06040b07050307052b 78
    0x2031681201240c59001d0fa004022045400c02005802503442d900680001e641040744441003a40c941001da49855004907079a81d032010071000042c441c10915025411648410f081c2020900060300449854000e103551300c1c100050740f0000b00c0e0005100d00c0c40c0b54800300c41580020410728140348500c59609a40040d84903d1040c0720100100b0444000c81d9841802290440616070340d03403901c100203024004001429603e000200820041c0c2a480903000c0c203080c3e2646a208880c20004840b0040240a1454544194400700d0899406100003003050b45c0b004205000e9003100c80c0c501c2d443c0c00d40d0380380d4900e080c1d40320f40901415035801140c00c0b400075000e241d515103080226030002e4250741051000030030035540007a003100e2005040c0d1055400314802002132042c1d484030f0900508500203100050507500411182d0100c51202424071020b91030050580c5080c240350503c0044960010301e130070f42e0203001c10003030741d00040d806121411003900041c2801590810150b22090610600003802c0180 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 46158169 1250 46156919 46156927
    0x6090d03180204090503070803010b0a110c0d0204050603030c0322080d0804030818010509011a0a0e01050d060e070602030403111203030a0e03090406080606030607090b0a05131205030a14 82
    0x90301400005101d06501a1800300b00443d070b900d4a24510710502d9006080c240000c0000b00f2000c07100001440715040307603518174043d18241441c4540325156403000e180e114031040d01e40c2e00141010780001d5448040101602d052002c2e680b081400c65000409100700b240340004d08104d8488821070b0600174044400040a4010900201030711880e00a4405414014141c2c0080d185006a40c190012b050200b8001d010a081801c403a0b4042d0820400c41240844c1c100e2401c0d141c5e00700906020125101100900075a91924003444020410742c0703001c2e100262101d0100090941c2000800000c1005500850351180340d418110340e000e81007103070b0b180700303010000d8040e144490000a0340e8101d40362000009811940803102c131b02c2e5106091455801a00340280020440400728902d03116000035400e840035681c50003021201080036000b03131190703240c00b4031403c54031074442c1c00030340410713243ea0070082c80c0d09403514100924842c021404440f103620000d140c0d800c00b540080b10ba40e80000424509041c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 46159419 1250 46158169 46158191
    0x9030503250909050a06150507030807031803081e100303110601030b06010f090906090903030f0209010c0b0c040909080c01150503190215030c070b090c03030319090b0906090d03 78
    0x40b0010362042000e001d4441c00440c9040266612080080002d4030040700c800880c40c034040d125800491064010801c1100003981c3d41c0d000c4c4c0070740380424200322829801000b86035016200010701800c500c1d0030100c11510220b80c201c2c01c0101600610601d04000c0d2003c0c50f525004200070480030403c00250440001003000a030342803040f03034100034242407502a1161040f0200c4d10448140d200030f204504025001800304481e5000c07041450191b6410700114500c411345400364410207015030700092084000d40c2c00301341c08280d51a0042083c00401d46080d680c3c034205c20540c0e046900030760318400c7c005900710390900240314522011003003c203140170701454800080d80300c840d401d8414220841155030f06c0c04640d604655414074141c18074259403a800c04840404d00f41c4c1142404580b9030030510045004100001040100a08001d001350b1950f42c07109281c18801240a540b2443e164441b071143d03000508904c501445516500020107141c600803c2c1545402c1e0300e009140c2c107051402c0c1d80000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 46160669 1250 46159419 46159427
    0x50d050c1509030910030506010f0309080d0b0604031401140f040210050a020708030c0a11090c04090b040e030705010e0d0c0c031412030103050c01030606050f1903020d0903050325 79
    0x5158107000515180315994500700e00d00754420501c64582c00504c20007003600d100d415030b11080c01800b0a076114070300d410002409404444080d04050010320b0207001f0503480d10700c1c0342c0028000e04800b501c15800c007560385e65031041e00d114140b910030440e5159402044034443d4140241c4d4446256200b18180f030a054020a00003000701c0302001c2000700014941008a008220000050099074100c03903903002c403024070545039000070034202e035500c400c00450a11807a1181d03003280a903540e00903842c0b401e46807040700340040a0215085070820b8450f504003880c1d0340d0034030103407144a00810002ca80341001810040c05c0c551204241010310043d0106607012074000803810060f0381e80140203c414900413810103161507240d0420440034070002001104000c0c001c074503901d480d48280c9060100e5a25020195164014525118420300c0144424a240d1000380404101c0403868200145401008121a01504d03184d0b101500443d0b03000040c84021403c0d80d045c1e6151603903410040c0318122215400030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 46161919 1250 46160669 46160683
    0x40203012102121603050d0f080a050702120a08060108180a0602031509040c08010c09050d0305091810050910050108040807030905191d100506210901050103050d050c 73
    0x700020716803105580440d00e40a0100e50480d00c100d0450b0301030403004021041080e814001291107000b00c0f0281099a40900191000d2600d0741c0c0f00d21200d030f030300c540c200c03070040400030100400c41c4144c00d01c01c88580300c01d600501200c07075260b0b2004510b1502c00000740403294040c0544403000041e00e2654942a0041900c00e4210303400100940d680c1c9900d000040700c1a41c412101e540320341c0100074401005041450325045031000b100900c8002c0041900361100049413180300d4000007074411b55000680b14038010042d0507801065450110390a9903800c180480880c3c0f02d00382101003e6003885240303450401e003580b200c0300c0c607034041c1110f041500007440c4d400b000d40010007203a00460b02c802054020b2000d4406000003400140340245061a4803c0ba41c0041c8a000e0858207581c0c0c01e42209240c20326020b20540c445034034108800c0c0b403c4140314440e80403020304208a2000110300392480092a159805110054000f003240d5045040007030a00f00103c20802c2440802c0190b1030b08480081845 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 46163169 1250 46161919 46161959
    0x1020f031806040e0a060303140304030e010c0812010608011404110f090d0f08030604240b0a02011d0706020708030711040506060d0c1101050603070b0d021303080c07080c04020301 79
    0x101a040c4808040348190041d6040202000040005c0150100701d40c0d03c104204c074000d075604141d00b00300c21440001403200b9600900004c80d20040764045500509804450520a4149610f0040d1035036008003450001e0b004480007604010040125200528001106080031901000070740c801040c5140640310703007000126001c4000c100c0d411140d88602e0400d00c5c0740d4203c485009022807500d0b040500c0e5000300d0382c00b88500d2a041101e511010a00c40311640d001c0386203d003903401c03818090008110780025214004564071540c1030705454900c45240101c02c2d40f6000106810750820030003034104515604501c0d500e510a01408010680a03000382d01d15000a4800003035585503000400d0203486400460b01c000c50a01c203601364196840194403901200c2c0708020811519070364100b5441d440d10344210140d042043c080060519a40c1d40102a10342c14038400220305540c9548492032500162410012030f0403411040000c078400303001071358107581c080741d0451540d810401c02140c18030307404c0e80e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 46164419 1250 46163169 46163197
    0x933060d0c1e0206010e061c03230a120e1006180606050a02060103150f0504030c051005090d030b1c050a050606040207021507170c010204050301060b1306180b0703030b090601020f03 80
    0x7c1041902e418505881f4010700001c041201c9805044c050400100d41003001003414a80d0002c00d0342c1c40d40e03007003510038400b004d0b81d45041c50f805588001010348410380481d03105003d883c5201e0100c81d914401d20300103000440c110440e1072080321001044603410350209040c410100b0000c2d4002d9408500a4190382e0f01401c81c030400c160780d044140040c401a540300505078a80700c1440107143c4c02801d105402d9205204460031900408010800c3c2c801c00d075920411507100c039008030b44082c0aa041902840300181807c9c044401c541c82080400c81c03051815101908446980411301001b807080a500c81c2080d0740c00e51030f0104a6001c900741410b80c03a1314480d00c036000720391082080000c06001240c031181d42c03981a00c900da9500803038000d502c0348c420307079100b9031a00c0b0000a40c41101c0058038148802109941103403860008141c5902108545500560088900c04901401500060300480e40030f60750020300b444010050100401e4080d08a42c1035502c40070101c180140b000040319102114901 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 46165669 1250 46164419 46164421
    0xc030c010f050f0a0923010906030905010b030601060e01020607020114040b0702010b1f170103020f040b15030709030209090f06190207021309050106050933060d0c1e0206010e 77
    0xb101c0758010f503041c40010310400601141c4ca07075801071007581580e2a204c3c1c01d080c400381c11412880c5041034104450701180d40f8035020044a03000341c1c8200e00007070103603001051480b0060000703418880241c114101103201640d105680c0e503410000b4a80c086d909000030040603120f00f80811003504003d00050080b0341040005d02214402c2d000701266a40107843c80980c0b50700f0a524006902d0300c032214400081c3d040d46001c01404415017454103c07034000d0b00030446d2440540a12002c0c000103220355030000340403c2e102e9018079201c0029440341980d6525950624114810480e03121800742030a40c0c954020755825003411030100e5801d410590502c0e990a4400406003080040d01401c1000396011161100f111007014098005c615181d02c103a000300050f60303c41d03040200d10311064813110a85880b40507a11465160401284a4101d800e680f800c4070743c1e01880029001d40c481c01c990450b883d1100e0300c022100d908901405000b007612542e220210542c0d000c02561081d0501c11250050040701c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 46166919 1250 46165669 46165697
    0x60708060607060b0d03020c01020d0215060409030302090a09020d060905070f030c0e0a030506040501110a1706010201091e2105090409020d02030106080706090f030c05131b09170c030c01 82
    0x40c0c1300c0003808034041e101c040600c1090501039183c00001000360302500030b944185e0100341c030109009401101080041045882d65002c2c000100704526089080c0755003001a66420381d0b54064400042286450240c0d8400311002c031501960301d90b900c00c0d04058100001d2141d0b2981101495031750070880e15000030480d6215030b04a6100582031781558000b0410003003c41070207804100640300305e0089000380010602070a1000080c496064070300c0001d9580354030301000040e40303440181c000070144000700341016a912007080900686640d0350340c444480381204108802c0392007084026040341c0f00c540d0031510f110070203081fa2080e120268811aa83d141e410b04542d00c800d144030009402400030007403c0e841c0c0f00c5c0355903101c8c4540a010085513828600051001c01c0040c0d00e41543e07444100b216249240905000b55009140b5840f5811a01d80d50b003c000041d01441882c07084150350b070381c000040d242c20102500090703195041c000da60803203468250662070004001c030802500f0f180104208901c0c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 46168169 1250 46166919 46166921
    0xc090103111909020c0c0a0b07030507050f0d090303030507080c181503070203070b09030a0519020a050d0306050f0406050a0303080613020a090509010e0f15030c03070902031806070806060706 84
    0x1044060b582c00050180403842809541c045d0428822500c1200d50041e0742c0410880c0030403243c07007541190101005000000b0780324101800005102c0c8080342d1260513184003007400e12040040a00009a030382c0d90410516030b043c001c8540042e5a420500b24900300346e9100c1c0501e208801c2421101d6490319120001c0382c55010503040317040c0021403801e450703003490341c2d0094403a84600c106452092001c00800d1448002104a42c14a1800e07100c00d0301c0d1504140c20301031440308900909065020340184031020941c1401980c5c0f010342030b070b13400048140c20082005840800088400d001d9850180c080c070150312000c0d6000705880e01414107520a54813480010700c2401a14920709007140085011208a078000030402d040e60001c60b001001a80c0310350010080d4401252411001c42c000008a4100b0b0070081c0104c0c0084805000c2d611048040d001082c0303030800c07030350103503030307010750000030080559100c464030f00c07c014110010b403016040161008000040203010184910000542d0200300116 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 46169419 1250 46168169 46168189
    0x20c0a170f180907050c0303061c02060a030603060608010b031002070f1b05100503070f0e060d060303080604060b0405060415030f06030302100c0f1407080d0203010b0a030e0c09010311 81
    0x103104401c541c0d403003540c80075001c40c0039624112806903121401007081c00d4041d009903140c0c4c0312614020b50175991070004200035000901440007c40e004400041e016856840c0108aa4192610042201441c52410030304441140e801418264584034114810f0354010840c91121010b060740580c88204074101800265041a802041d600e010300e00c0f07801d04e180148203081266400ca031000c205a1810400351414441240d810001684802030720346550700905590150440207080c442c10311409d4078000e03040712029001074012412040800140317140a0286a01609480199609180c90b04021801034050307401100c4070b54000c0c0840080c182e1007680103035007241c40c40c0030511513250703a130402940f00d0b88407500002c2c2e1a8100070340f0760f02250140020814a40c1a9611003511510380c070b008010540001e034003100c081c1d50810210740441d00c680080c5010b4038100d156155608110000501164240c40034003503642c08c641d6510350940c1e80d06a08504503608000c11410010340f040000d030302c81301 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 46170669 1250 46169419 46169437
    0x70f11030109050d0201060f1d10080102030a020904060f0803120a0f0c050c1501050f060a03090605070f020d020706021207260405010905060702030c010f11010c020619020c0a17 78
    0x8030b0302c940d1805100340003480c2a0a407016800030020f00b500c601101c02e03104194003c1504070351400e02c10100c604034a0a10310b41c442070005040010648414845007640d2094030b100c21a20303004600c01720340d071078240310f40c1e0f0003040c582441c040140e1909030b80584030b0107600c03241c0d05020222030010321028500e41141001c00e0304040108048401d5113005441ca8020000700382203440b984922500040d55a4255410307960010440c0701d410101c0000c101290388a0a0b0960030181c070340030b14000041d803a0241070302a2007181c84219900640c1d140003031901230001c85100455004030b50802c004c90f00824681500070a10750944c0d5918803500304603a00101c44041d02d1240a10b11101c0c10303031410400003030010703600242c1c0c034103220b00d07035900030020a4000c4800180d45600000c880600c00d601485021196111900340b40f4605812108540e0846402481c0d00d000758209104100502e06000c140d0300850f40b0000c0700314104028110b5155451300c5181d4024a110040d15207200f03458006415296540 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 46171919 1250 46170669 46170671
    0x50906120a0b1003150c0e090702010f021803010516080105090402011e0e090c04030201080c03100506030a020304030210140f18010e03040f0f05130906110c01020304200105070f110301 81
    0x105107802040550005880b013500d84405d215158201078800b4001d0481d40080380d40c0d0815903901e650100851507001909403030956680300141500e2003203074009020a03c0712400100c0080c28290b060509444000340302130581c41804003840d000c240c0001465040d2071007540e02e210607075602d2006a030100d41d006200b8400000b000640318046510004840501c401600c0070000c0340c5441c414440c4a00890100902050760a000200380020420282d03910145854450460564880100e0150b07441a60880c005607000010481410740400240b0300c0005160401c200d08102c11000400c0c81d88090980c045802d0340601003030302000c0843d003000003581108001c001d0105d41107061592607025210b41e950640c001400001c0c041c000d401d5400880384080c0c4910810640032500d5002040304d0301c0e0455a02d035131041d00035a00e0340c00314094000061103000060f0f40707042c40d040200041207644441000425000441e20107a648801035650540d404625032005500606d054400e454904440907059 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 46173169 1250 46171919 46171921
    0x408190e2206050306060d03080c07020d080408070518060f010201090204050907030b06040c09060f1e1706030606100507050c03060c040620030f0a02150a02030108070f050906120a0b 80
    0x540084648014421000c040c01c000c100e43e240189a15564110350540c0d20144c0c0134000c0010038041c828881d1f000c502c4d5040f07140342020179070004540c1c070703242c00c001d8640070400f050a100e096810404071001e03200441c1c20201d0b003003100240c6011884001e0040d800b030580c42150181e40d90003508841001ca43c007c00a0140d86003814203103950f90814401554400e60f4035000c03600034145842480320009141c6d44605040d400d00030181d4415006100c0d400403c8907801c00010100d0451407590f803030300840c0d41c980c0b1820400b0190b039955050080c06283c40f0b500803009022882da107202140d0074400307050500a465200798205039040c02044446282c042c06400100000d540851000b0400e40b91181c84911142c490b495104510b0601c09004c80150381c0100940310180b6801c10203020710a110b0f104840941e2000c2c3c402e10004141034440c0c004090b00840103100c00c0380e040c414480030700b5035a803085010514040020b50507036070180c80c640c090152031511902c800014084c580707000c1d4020010001c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 46174419 1250 46173169 46173199
    0x507030201030915090615051504060f020304080a05030d110901080103022403040b04031103070b04080304062702040b04020a020709050a0207020303070f02090f0106050912030405031b12060408190e 87
    0x944980e080003400105207140101e652701d071044441381d00215007070515003407034149001a2290510030600d181136200603c00003800d0001041b20342c0b00742e44100069600d902d2191440815601c141a40910750030040c4103c00031039a1040c0404d0469804648190048541c0020300c0003008840c1210800b2000010803c414030111500d210302940c4640c2d0350b1a200d00e8109a00c80c0c6034003131500d00030080e82c1410081008180a1070146820074018640001c180081364103e00c80c0035800f00234940703443d4180f00c980c001e5103060712031818800801d40d41075140980e61907009455190500400b051540d8440120350100300c15416034003200da003e41180e1b070711203030f038140f030b05660250369030407441014101c0001c1d031170800710740e401c504035007040d2106410301c1260000c22501c3c0c940918281c0e00c9101c103100001d001d075010000091480d095409203a4029030300c1082c0040c0f03100e015604402d0b03602c418180000503628a0403140c5080d184108501c1c0072444000880f0780040c2c44d100c05074000303894038090b14 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 46175669 1250 46174419 46174421
    0x9090302030301081203061e010201020d022209020307090e0901110a0822030503040f020d050118061407021911090c04090509010e03030a0f0608120712020a05070302010309150906 79
    0x2044e2484603040700d004103010343e86856a807101b01c2d030468000710383c2000d0140d01581c2c801c07184101641400058102509603c110b0f01700d070410600c00700e0b181040c491001406410320a0b082c0078000182003549186056800030341148251b00c00c5100700d08202d00002c500200039407000302511007444000750340705941d040c000c0031f488040e034820b0101c00102c0015180c07030b00f09185030703040b0583c1504e900f800c503500d5490741601c059021000741c2e04103045900301000510203120b14100c41c008454040340048060601034100d65008000141070034480050000d80c41d000610b038440c0280b020007420510506203040c00700c103000156095041802c03501440000002d8101610603150b842c035080240c0d5440e4021030b0300b61408440801004c0e0002c201181a07600250450f03280980990400710340596110102e503c1c204904561240d84e041c0890410308019035001190045036207440245880c107050340f12151600d80d030341300080c145562a050740041200b0b48410420b001c9040c4000c111200c950304001e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 46176919 1250 46175669 46175671
    0xe0a08010605151201050d11040623030a02030a110d050102182704060f0605120d09060807120203071713050c19031e0209070e010201060e04030f0e0109090903020303 73
    0x2e446100e1482a01c0f2000c503050098072004150040d00000517403038a03003402110801c9000c01d4408815603100302c28280c546004400007030501c82081685854020b02505083c0006c0311898860b03000f100c940c0300981c0e4001207041c042c81c0c010504600303800b0400c001402c000507200000348607500120790000d0041030714000c20000c000c1034405010801d03d00c64211120341d104407070141013100010110b408075034280d00c1804448103800002414a03241d500244201001401c1d0300740c6940300c4c540384030460303074001c1500005204034103002c07201e0b040942d8003901e075003000b910280c1842d41c08000201354a00c0b840c0d200030007901c112000e80c17540c10544081440700100b1324059500e07200303503a0641c04908081030594845403203006590085402e5075240c02c80d0a1305044840490004243c60901582e5007600b00c50003010315031101070000003031a001a0a40e001a4061440264201c04200c08207800c50000212002d280c9031224210040303100588200130650410311025141841e42000c040d0004011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 46178169 1250 46176919 46176929
    0xb030a05060702060f070f12050702011e051e01030b0a09050102090a0b1905030105060a0e13180b0604050105010c0803040f080301120606080304080312090c041a010f080c090f010e0a080106 83
    0x12a602e43c0c5982095440015070b2047d0b0700050584603a4103074030321a550106402843d1803002107140e5000d034080381140300c18021484051640c0b43e05101ca0f08803046501c402c50b01c11a20705044561468641044045c0c2c000c00c0340d00655210600743d02001001c4d41202e44040000303210040307864480062119580066641c243c10a00d445003000446005405036030490358000c004a1510221400488401501d4131000e81c0100e800309900304480102e005419a5091040794034030078040f1400d00a414200203070140303018070300d098014011a41c1c06600342a5050300001c3d40c0744c0e40e88035072400300301c809096a0040c040020110002c14039401001c941400c40307004030810310019846500c0c560702c9108910501240c0d9004204208503d900703001302c6036014010308182e400719492100801c080c0e0301b12501100510121480d0810b456800030200c0405103142c0c58148410b16001c0b0f410311452051070005842102100c81c030554076807044e20701080d0b00fa0702800108016076128403a5010344124003034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 46179419 1250 46178169 46178191
    0x10503010e0601080c01050901020102040807120c060504030c0902030402061603020610081605011112070f0b0106030203040b04170702031006090e0303040b0703051005190603060b0c07090b030a0506070206 90
    0x5204052480010120f043e00d65401c05021490030f0840151929401a99039030b040d550240000540c002c800c2c44240000d145086454106952078074090b0340c03102682e0009424480207000500102d01560100000e40701550001681c1e500c1d85d000040c0180500305424840036808050030302050740c0494050301401d400d1403210380e219180c58030140c549410400000020000c03690800c12580b240d101c01c20f12030204002d1754028100200250425401103505443c01420a02c0d00d0041103500240030740188030518085040d420596150842014064030107081804141100041c50b0000380840309140e90050490740020141d201c09000707000c2c0c0344100f0b900d083c540b1000c07580009020084074891503118008101030f6a801200780d005110140c0001c55a040160703001c40c661722520000d0880701a00300d01c0103001c900e0504000c0603181d090b00400901041400500f460130700001d5801d05403019090085040c4204801007468201c180d04042e00030b114010070300649640110b42c003030041c41103000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 46180669 1250 46179419 46179431
    0x90703060501080c060f030709050a030f0209160203090118051801030605070f05070f0f08070b15060f0d0f09230601060e060d051e100602010b040c0203040e0403050705070303030501050301 83
    0x200144c50b40e1580801581280c420089048607a5601c0300656200c8000d092509400b038891002c580d40700d1054000b100d01d114400d80c05415403825600c2e00394484014040c0704100110804000d40380d0250006503418040700340c0600c5800b003821156074007d0000603010307030617000b540f98480520040a200a68020b4a080c002c1411036111340001107081d030503030f01e584c0d1412581d40d442550313007140c107130041c1c460036000074540c0d001410003001004000d008031900c03415800d100714480b100c503a01c1c081c0e441c8180001c00103400001c21400940b132300d0388a4000d000842c0a006001e00001c6d04126078010400650031588551100e824410340750000c103590111407090380c90b080d050301d1140d108101c2c3c070f40c040307024015540401440c4c0c00c419071040d84c1c10544c0f220921030b841030701003140c01550040300d0748440d80c10512074031754244554012100100c8041c03029800089000c0e4980c82075000f20145203c406000070b0905005000700d03803403181c0c480d080b00c080e01d81c1c0c0c0c10002c0050400380921031003942840e03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 46181919 1250 46180669 46180679
    0x509041d0109210503040b1e010b07021201050708011203020313080718050f010e0a140405030901030c08040b01060f020f0d0804060609050402030c061602040614120319050a03060905090703060501 86
    0x814500c200341503075113402e460f54456490340300d8101e9008059110424a04000070b0404200c0c4620f14000c002400400380c40e0400c80c8108400c160714210107400e0b581c5810104100a64030060003811101015071140c0c1c502c0c100e007000c0b0700703601ca07032280b42101e64550b5000003504100020404100c9030300c1c0719800c1c42e60400c0100340c1c1c00e403041610440034042454006115102211428139009590f0940025910301e0442003516401000c840684081e000403031410804e582600551002c414680b801384542d00d42030761900ea0406042c000d980070013080c0c14455201038003c002452102c0e10310300c1111100444850003d1001c682110300305d8050b070030704000080e02c2c1d030640185402140e000b80544040380340c1c1010f104541e0002e10740811440f8100c00c50302c0142c1c8035480340b50f02030f10308003103040b02401d1204140007420720000500c4100347d00422502c8210040d09103c01c0c8094014a061079a030900c0c108210068209504595130302031410061126000c80007990804aa100e1041406540e0fa21 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 46183169 1250 46181919 46181963
    0x3270909030c03042106140402040b060406051902010b0d05070306110702011b0204020d060b070506010b0708041a07060e031e0c190f060c0507030806040b100509041d0109 75
    0x500800c0ca05510500c01405003410404858280c0d403040c83d1071000c031031171325203030b020655194269400c0780030244814041982014001d44801003015551ba9141600d0000c00811502c81d1640c0042e05034114038941901920030b40042641c036400a10344c80c041c44941c1001e41d00d600c1144412107c442c5000b03600b81450000c171054030400c0340c05071103000f03554507100300c40500d50f0001c0104076400703942084400ca40c50044c0c4210f2029043c00030740241c54111130702c1c00c24905030040e003042014034018000d07440010626801c85041d03030f030803c84010600700a0505043d5501403d54000d140070b083c00380000340100000003038401090307240c03000e0301c1c56062681d80724154400c85501020980082d002607140c522007035007158125100d5038001410081035220030f02116602041c0d031000540010748501410342c81102c5c990000800c440c00c02002c080100051846402d0b050410280701000c5141040c5644650080617146480c8611060b0b100d0b507510309034000c104811048401a0120080040040039 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 46184419 1250 46183169 46183177
    0x3060303080c0a090e011509081902060c0a05060c09040c080903030c0a0c0203010c02071e081b1206090618030f04090203090f031c0e010203070807030c020327090903 73
    0x168035441807980b500c4122803590380c8000741c54014000300d00c0b0002200a0b426007458002c4c07403052201d1008920350400140600310f298864045035101d021103006003030040001750103850307048603c940c0e40d40d400e00390030b0304000d001d0f140a07190b0300132a01000200b440e210001e11000108a4041241084080c42540c21285c145c0750b03103e15900c00c0c000030700e040c03c0e030380020300324615030f811704480e1482540d00103801d60f030f43e01c46d00b100141c2103480e08025502c9840241440070803070716110302c107075403e200361079541e000c40000702c1c84201ca5070000413031a034072403e00042d9111040d400382c4445141801c58a95110b5064a5451881204460940742120040103803103c00c10391043c0c8502d4107141000720b002a40018103002c201e80074421108943d00c400700300031b2070400c0300b089900500d034900c91035910442d1300440d00010543d004000b040781d5141c2c040e0341d483c0d008000d404c002488070346c1c00390200c0c40c40c01252100b892800d10762403c51b10400c000b07514810900350071140d41020317544030300d04d85031603001e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 46185669 1250 46184419 46184423
    0x30c140307050a06180f0501020406030506010f02030a030231030b0109140f0618010e010509250c060b040c0305090d020f0a030f030f06170d02010606171005040501150e01030603 78
    0x40c260b804000340c55604074160f45c0004c28109043c241180e00c1e02d403c004440c420803202da07940020108602509170007600c1d07000c002400e03c4140341c80c054002945900c500344000b1300701070f400280c103029040300c0744680c0b020a0b50540404200c44004c0049040c140446c0070540b0b80c450790390000140b0828500402c503514085901d02030842c0c803800c04d5000c032000040d040650280442100c0407440b4610201c3c00c1c02040c0007410315845526200500c5002500030b0465140a0041583c040d003c0c0d03140306854926200518082c103141c0c0d950b04107200180141c0801aa1041c00d117094101c0042d03268100c0c0b400341c0c0c2d2403415904480d103d004140d036a50350704410340e41503401141d034400209000d500740c00802442c030304020807071002d500c02050444a9580000b41400b40d21a2a042d00d103800b0032468500050740d00003000020b0900c1409048200700c1100845603020183c00242601c0943d4250340040001420512095844200b451000305c01d21078070000161140d640e59a10358030a000d21800c580e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 46186919 1250 46185669 46185673
    0x70212010b0d172215020c010807080a0905030a0509091005030d0f0302120f01080607110c040c0c0b0a0903080a0b06040302040207020d0c0e100b04151107080604030c14030705 77
    0x340c240d95514404808a0b00412200030b070074481220641c90750640341e0082d030132281049045900b4000c20240717103032000d581c3ca811503001c0101904140d0b040b03800d4541003407803410441c550b652810f040202800c403401c0c00038920301011075515041d80d0000003500f02c0c25400c56008a6a98800c81400300041c09807244d2a419485403450f03c104901401c100643d03814646009450020411010042c58209454500400c070705030340104864001406a19040b4040340b0b00041561360102c0c2d010303074070024181c070184926030302c2807080c156a008049081c6003540c0108000641d2500c840800010560051700340c010074009400900000d246104e070107549900100514281030a64080c0402034000800c126044200d190781440840e43e00300844005203600e1040c070050b45842c42240400c090346910500c007680007404248100412003802d03010503901858605000c01d403401c0580d1804415a00c29030756805040c040c0801c1c0342d4841f58035890315010700d0220220034000c20180e692481a00c0001d0003d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 46188169 1250 46186919 46186939
    0x3061902030601090306092301050f16092301020105010510050a0813050a0c090c0c2006071211010c080108061b1c0906060f05150a0203040911070212010b 68
    0x40066901960300050185001110540c99590b03030012a90203820940d11415401c541c81004581c4026501c0d08140d460000c0c8160b040c000244024070302e000d0030700070005a4046918805a1007100004010a541e403511513844004004410641000b124464019424803001041c039080600207104070802a84da4a40f4203822000c00710307011200600042200703034048022070f002c13a00401c00400214007521510500b41c0c90405000100c0d07140000c143c05115602c0590030109440800280e050070884030704044011440340019206c1c070070105c00910400310b081c1c4114001c5d07842102e84801c1c50f0b012000700500d404d05035058500744424400c1a200783d110704001455610b444075800f050081700b00c00b0034100140e00a545140094002071881d000e6960401401404100d0040400810036011060748150414012401010710807028410111000035a4002e451080003182e0041c4001481000005000919440e01741d10101040c3e1080c1c8100e140c03140404011302c9166042c1030024002458 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 46189419 1250 46188169 46188211
    0x20604120509120d080723030402060d0c02280b0705210a02070308130c0312020a0b01060e040c14180402040801021b0d02010e030906071103070303050c0c0306 70
    0x900244a0408400c0000502c003169680d20340045a01600036060b01030200306440d500d0080c0200c2c0e000b00f41d101081103403130707010841c0c2d1030302500c01c840d03c0e41c0e250b0305c00d40c0c9a484d80082405d51003408145920b1038035010030f8811980e40402d50038086100650580303e00752032141100d8a40403c03100103041200c01d40c0c04a1521409040104071403502c1d00d40046503e4044540010040da00b2500019026000268001019805002568081e00e2140b65110080040e110035182c1f060501000742940244a42c1c0346205008205880780039a1160226502e981c44d01401400e0070320800170700307025078100703070980c05c00501038403054003120140ca04480c20007010b84010317070518034140019500315038200008a0002400e0004040103052003140d0b14a442e01d81c200075250007080e2104a04591400c0900221110f000c030481e80484400c036426501e81c0840e00b00030340381c44007040f4a2a490300c04ca940010405802101034402089000291030b0fa183e07030380080c15160349040700c010302610b40c0d42960141c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 46190669 1250 46189419 46189433
    0x9010213260105010602030d23041707080c0106090b0102030c0d140c01140714030c0702220507020a02090610020a020d05011103010b12060f090402090403030e190b0c040303020604 79
    0x44000a90400144a1400014032500f128030a07008503006820009800c1445030440c026102d6410400d84208241010060352442030b48010740010040c5000c4100315220402000c1507802c0c80d0b400000d89641c594100203078900800461058100b514184024440658000710595107010140001b0b003980d002c500c0800c440c198040ba821882d140000e0181c00c0240e4001d100d10022480b4600909240d418a00c1001d4400e0f86405108160824100104622011000c00b65404e035a07060b10700b540d01340e016024200e0307804c910808003000c040c507190420100d5a0700095138200c0301c0c02640c45031840e499040900c80000311034a0784801681c030040001c0018100101c1e0710141500039000003507824904042080941c2c001e0380b0030f2484104c0442c0f04c02045001c68202ea4000e04200c6100046480d250040b0303643c8070300100080e00c00c0c0001400101414000c0c1c004a60000714101502c0164508105440014500b03c43c1075581501510020340483d03004000c070f5060f01d40540040502d070f90b480c0c4d0703060 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 46191919 1250 46190669 46190699
    0x60320180102190303140a0e100207020d06021819050109050909010b0a08030301090c020304120609110312070c050406051516020a061101050f0705160203010b1e030609010213 77
    0xc0d04500c0f6401000340004031002c1140b4049210350703808191502c03860302d20071003160044c2540a07140d181c03410850869000050201c81b1106103100540c0711442400042c05d841507540c40606001e000041080b0440b0103c00100c07040d10702220908024041401c03040c0070780c00e942c000c0e2400f080d030050b010700162500d04095540040180c0c000b107090b5986d1808144a480560b112440b654404001400718003c540140c80102c8201e100035400d0903e000c940e60b052509104e005003005541c0c0c407100082c0804d42c01e221085800250440c1c81000b894030350f600c0c0c658045d0000b0768a004280401103220b19290180030300f1507100400702401003450311418852584403000100c00c2610818030034005855803580080240b450341c0310000030320a5104850300b52407000341226000361104041000700e982103829294a541140c0804031100a6440400d0051010407015580203008082c80c0354108003c0c0c2c024100c00c14160141c610340d440360001c203400e03030042d0f40032000303481d088103c1482010140c040a17 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 46193169 1250 46191919 46191967
    0x224060f0409021201020a080f130209070c1a07030b010201020f0a18121109071e23041202120a030c02060304030909050a1406060c030d020c1f06060320 67
    0x80c510006500044c24241c2c401c01c05041c594010030080744554002c900e55034850910b2248241525151040406a01207403000074811841080481d40c41c6120324050940e10741d0201c2c90304a41e40b02c1504845105100301d40c6800000c0c02e00c1c0080b525544103000f580c12849100d40c800d400c0c81c030300c50780c1500c50741004600280c3c49400c0500024030864011104403125000d00c111540103035005040c0b09081c60300402c0f11060002c0085104004002490340548904040c500300400241800ca6801f011440400801c2c5410380810040340324421101080700c0c5a108a641025442d15282c4481e01c0320045607025000c1035440d140100582484401545d0040c8240b8103032500c16141c0100004032203040d40d8403000c250340c030440581a501c0d81706c120741c3c11001c202c030528240529810265640d21603c40d421004580100b001019600c1c00c000502c812044103481c08512034851102000a100c144500f81c0060300f4911150304201c41c1e00504400d02c4000d040452074013090903940e1042940c04041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 46194419 1250 46193169 46193171
    0x1030b0306040c03020f041406010e0a05120f0105090106050a03170f07030e0a090b030307140f030307051e090607020906130e0a0201091508060d0809090403030506010224060f04 78
    0x110011903809228641c86144102d202003201d40c190b0061110410501c60020300840c41c2c80c1d050303980070041000d80b55000c0d00034609522200064400300751028480e5000707a421010b100380052aa00c00403c90140c080c0c5204000c200070b54800f0302c440d00741c0350140301d0302d83c005c0d40304001440480e072440e51a141c1d420443d0354407460840c9581e028041a409000c0950000390844030b820b880c2d2600c540800c0c000c062404c800e00040103440b0000b9141e00c580c0200504078010f10b403884500481c24414104642e0034103007070303d8603864401e202800c47c0d03000b19100070703115041c9045408006504002e443d500100940030a0920503140e0030b21400c8003010b0040c0c0d9005868540407070b11903034140100f441512941303002e40420740640c4005400030400d034015118006402e41e8114200380e10114280d4440310071503070f0312102c0c2d005040c45c0000348511a441c5802c41094005c010515400d80c01c05401030f4070a070f0842e807140c41c10700f03c14040341c40540480b0400d1101c16010568624000c5107080c100700000304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 46195669 1250 46194419 46194431
    0x9040501060b03010b2503050919080a0614070c05070506030a020c0a20010503040b0a02030414030f27090a02090406050406030b0412110d050a0c050d02071e06020303060405060103 79
    0x10941c80e401c01d074802c91136044e0028041b00d9104c9842004a4000745003030020180031503170354014007640100e22205005020b2940d40c81d0201c03d000700281d008081c0d0106407100d004403070524101506aa030300000030010480b01103041030380f04c2c1501c000d210303030424060040c00342020100011544090015900e19030240300e03021440d501801740c400300328450829001940b441c5400d020702652003039540d030f05024051040002181c20100c50f298001c0006c0e13001644e81e603961425100040340c0f40e0060401c0d10002c105601003c0c50b41c0c004040c0c810020342d0b000c02e41241105120110034211199a802c008018042a488100c54001e001d01183c0204041f4002d0740b80c00128048400381c0c0d00a0b60016040428002400109070121031480e41d81d2034030703c1d42050189541966440d90144141c01c1140004030624854410620180d40c0756220b010741d4094001d060000350749010b1401341e02d07880e80f4048800c0c070140c00b03401c01882c1110500d4000d14150780c1e0b103c04010040c03c0051000703043c140ca841e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 46196919 1250 46195669 46195679
    0x30b0f090d050d1b11120a0c120203040807060806030709051302041a03191505040c140307090504080a090501020f0c091009020708040609090b010503010522020309010603020906040203070801050904050106 90
    0x4612000340b91040e52003440445c9400e5110340b400c01000349044d0a82c00400801402d40c0d88000c03401c032081c1d002210440ea144504000301d2662180d5072001d482c500802d1004518158020343d4240030b098220f00720b9541329180d0b5174850440340240d03001014102111000c1c4014207003500801050101112030700c0b01c0129a1001c0383c1020201901010300b40b450080007001c12020621600a12500020802c400d1a00340e8509041c0005030042a140944190460400796010406103024004810043c0000c0c01d1071310340908c0c2c6800850a0301d0229a000c1004942c2d544000b584400c0b025500b00145101c58101d01030240700d10001d41007248015140002144007503040c00140300042c41481c607030356240d140581c0241080200d030810400a0f0801000c42d80680c1d210050303a06480b0100c8580128020010074200194101c04032006c40b5400032081054203803040d8403a80489000b554500c040d541c442c01080101c0c8001c0702d22801007442c480050119080041e445544688544000910700d070f04c0f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 46198169 1250 46196919 46196951
    0x2c0c09060f18070f08010e0c070320010c0504060e010c020a1406040801050903070201090e01080303011502010209030d030f0b010309050303010e0c07050304030f0210081509070203040915030b0f090d050d 89
    0x854a82001c2039081e4104c021466010506600418421000c2c522506100303801840d20310410074040c040282640c0d0016880803000400c01c01d10725100002c000300350307009402500d00c0d0080d104040204503030a408207000e500407032030529110340c000e04c01c0c00d0681c02c001100d0070041100701816007220080c0008948a03101344603140c003488100f801940c45548030704c001000303103101d03402c42c0ba0510503420041159034000410799055503043d400c4440070340c80c40b0f034080340240102d60396181d25118883d850000c4d40d0300b661043c41d8010001a0500c0703030707208840040d810750790644070003003895004000410031150002415600407810a1041c2d140400f961a9030f895500545c00959114070450000c004510300300311a8007414849003450f2800b8902441c0805400c21008c501901a807074010000790b0b01482030089801800684000300580e01e61041840445241d501040300c40079000c01c0450508003040c070f01c2c18400d005400092040c118000d008507402e030800000d40030443d40702c00003070f00340c0041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 46199419 1250 46198169 46198171
    0x7031e0614060306070f0c0201081518010e010b04050619020c060d05060103050109090f060b010509040c030509010e0102090a0b0a03020403080403050307020907080108150603030c012c0c09060f18 86
    0x20206107442c1403040030181003503070140100043c000d03400f201c0e92101d6000640d030003645809092500d0140c1c3c40c1040d80b4800f03000440c001da40094070814080c0c0601e44048141c0c161001d174500305815031f1729015034030094403031802001e074031032014400304c21142c011414144400c80c017841606e03030810f40c1d580890308540000b15043c0030701c0d40b940200151540e040c82034078014900300d0700034006404c1341e8a400d09a4041c443c40541265100c521020159005000f111078209001c0d1080100b80340d42c51000b0010300301911125450f500302032031540008414020307185101e070014080c1c404a07181c41242c40302540481440350a1640030302c8001701141043d0041d0004501a00145036266013030710420101d044001c11020078010001c0c014040f21800140034134101042c0740386000c840d00c800740040c3c514040d01004280c40c7d07013088441010040c85192130046d92020340b00402810650084d0b40d6101d02403403ca4640100d009000601c492400d0050015030f0140600142801d03032a80c0601480410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 46200669 1250 46199419 46199441
    0x30301060c060c0c020a05040c0c14010605030c060306010f050310030507030c0905100e0112020607050708250602190f020909070f0b090f0f03100c09151107031e06 72
    0x44160148824854a0302890810343c40f0740c94003880c00c00c080d90001e01118030f40c1c0115400f540c1da0b01c061200384d0b80100300c84030151b03401991400c145c0c560b0518080c0680300a001312402406032500980c03850030402c0640707015090585413004107201181007191a0f030001030055490b06101d640c00404a007045c04204051401038003a14082c90800c0c04c0e02c0306880010700509055100190304120762556030102e6415101c1c11501040510300c40c1c0000384a074060a18003405600407260005244000004d608590801c168500d4103821883d404e050b901c3d112034840c0320301681046031480c01c54202000100701c050b116490050321540369801088031488200c0f40c00b425503000d65010303c580780d40c100c0b04000516000302d010703191001d030b00c010804558448041070700520000c01c9501c001d54051064040108642004102c24114070307200030000c040c0340c42803130701c0c041d89072032000c0220740301d40c040c00d10288025006054540c615600c8180640c104090040040c0e030407811311000030305602400340d00344 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 46201919 1250 46200669 46200677
    0x21203131e0501050f01060c0c061407061107030206090a05070302010e210706080604020708090d03090b07050a02100305010e070c03090b04060801030203010e0604030c031206091d070503010c09030f060b0303030106 94
    0xb140850841c09252010b030000347c00d0140807001480024150382062094400c503140041c070410200724001f005d80070342c0100a09950070078400441030f006150161242d14001c0d401c480c901c0d2265500252120301c02d000180183d081100300b0700155024010070081d58101908948070040c102c1d0341031018000d150b4200c00c0325040700f00b04104403940850942c2c0c00c05000c07202140390100c16034800d2440c4c0f00f44101349010702c080c00052000c4c10700074401140140020070b64135907180881d1a186464083c100e0040f031092a070510703003c110030701c86d2085070305840010300c1e2010152070b05130045c0c40d4120800c0c4200c0070013031400e4021a10604804c0500000c2c88aa2030b00754841d4110720405081d03c10703003259492150300540400004c603038070054000445403d41071103c10340e050105040c0103000b2580103e050a030030034400c00b0036400c0a02120320f81c0c14000060712500b64440c0704040c02c0e00d8181c4050400104041c40c00c1c400b2960003205030200314820f000025090404d00c01003400c41e0002d903c510701007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 46203169 1250 46201919 46201921
    0x203070804031d010207171207030503010801060e16031a0604080d0207120308010e0a0b06030705070317040305030a0b0103020903060c130b0f19030f110904060501021203131e050105 80
    0x25401c070101410fa41060200100c0819640700000e554501c5803181102040400c0004c00c1240703405d105480c07030503400d04900c540c2c078106401d000d00b2644c002c2c4600e428079860b10310f0003c0c2a4031100b2501d8090042f00300394102500041c10200d000d03000300a00c0e0202d50220007204081a0754400c01003004140c0c08000c2c0c0f00d681d410020185c1030000a0340038812149845c800600002e034044a4241540c46400c007d2032151a11541c01c0000e0105d1810150044400424800c0d03040d0040040c11001e4800e82d604240e0041103402c0e0204203809440080200f5018004078801a0050b00003180049040c0340040c20700e60300d1400139140c0701050f1141c006845001489164000c42c2c80c0741d040203000855260391170814171080000c1c0c03510440e181550b902c800d00072003958481c403d4000c00710b1403100c402d0031300c00070300400c54208082c0d1290000c240700302c2c6040c800141c01d500101c0d0389011070310007018007404c44d43c50907400c041c0b09910394002c070388403a4170303407403d030040342c5090b8042a001740584000601 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 46204419 1250 46203169 46203173
    0x918040b1608040507030f03020304080709140612060601080606070203011107050c1903030c06060801140108010b0a0617091903020607030f0501030503092e1e0504050112020c100203070804 83
    0x300300c4401c0386000c00c0034079000c102c08640c0c00202c0d00c040300e40c000802c1e002c801d25810f040b800c40c090364201c020180644a40020840c00580000d0a1601c10241041c00760303c40d4000c00054000008034149150840c0700080c0c0550302400707a51381d0000380035003101d00d40880e59000078211040d407109610f8540010440409000c410001070104850035103103400b50302e00e540408015484148401001c10a00030900020005950860700050664900a01902000c8140440140d0090160390119880d1200300798070762400c500c00108540e996201c0405078580540c1009404400402491140c0300308480090084551070009245c907000344c1c042c1006040141004050300d942041c0c04807031506010051011460110031120320150459040006c6810000314011381010348425402203603903410b0410005070022074422403266000240560424004000c1d2000e000328099107000452900640c1760007500c03580245610403010089829841d480101c94091b030f4002c642110004810b48103202c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 46205669 1250 46204419 46204441
    0x20f04150311160303090807060c081006210603120206040b0604060e0609070c1b080105090f03030c0a05070b010902070501050a060803031603180c170303040206040306020918040b 79
    0x26500c4185000c0c0071491030009008514016800003c8602d420380c1d0b40201054000e620a142c05a8045026500c940480c100a801000b01070090808aa07040002500180f0250300480c2658403c2c1c481035080c508280c00030741044c2c14001c81c100216561200400403d100403086107201c84203034010109850603192248409001522701806503087c004280800100c00c01150391011050340c40c504181d6940701c04035640415100003a0001201130302044e82c5020864009003600d4085c0000d003c00c3d01c0742d800381552100704459001d0250410b102080784820000300134a0403458a26046003402c00c0c0341c459aa20202c283e0041d0407072070b030003d00c807010480d081c010264000c8000780f0400042e032910b0319140c0c07130b848000d0400d201c1d200c959070050601d500031342c403080d004045590041151449850a00034000d81c82c010072404448102c02d8025640001040b0707072140354003500142c1400c0c80c5a880382c02a4201c0e100c80307548201003030449c0b107000901e210351a00c1540100c80b01215401e240043d18 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 46206919 1250 46205669 46205699
    0x301080303180307030e041113060201020405120610030222050109091703100509180601030506062e08070306050d030c0308060a03020904110103020903060a050709050105070b0a110904020f04 84
    0x190ba0341c00512608011940010380182014826103011481c90410040075406d0b101c1c45494440c0040e0f4404081806075055010308103588007644c04002c1500752404071a580d03203044600f5107200c043d028083c00142000302d07281c180d4082c14444d4015141c1003080600984800341c010070480c40c0e88030701d80b50620240e8041150a0b006032100d00c1c1c5182050941402107107154040e01e80900e0000d4040340140c050560710044c102c420300195031071940c40f4940303036440303003030071f0b22994031a04206000c0c0141c0100e00320701c2c42004e004501d01b4100b4170f600400039580003030000d00e000140740d510702c8001580c1d01c403051100d02d032610950320144441d16910740a085680050720703240c0101ca0040701400180c842301d4000e80c1050f0001031001000c120180120064413540c84070907054010303441403101a24507900700c41d028aa03691141c00c4413580f1400112498054507002602c0640300d80003184040c1504c1d400995400174850030180b82440c00f0380403800741d0f806240c20302905900060100f0030043ca540003d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 46208169 1250 46206919 46206961
    0x20109050c0907080601141327051006030e01060905150117150409050f070e01030c090c0804020603040311030f0406090807030309060f0207050a03060207060c0f020d03110904020301080303 83
    0x191060b403c000c0b81c01030188a00600c80d506010603614000341c81365400781611802103030110488020740c0c95101404c6c0068586002695100c0700e40000d10343e056080c0180f07442424088800b13951280340c41011809001c600c80c0c2243d0301d5686a00c0421849441e015662041c0140e401150407103811000042201054801e0701840d680181c06011180c004008441030b400011138000c28601c20500b401e030704107219080103060301c2c800c1c00b07400500e100c0c50814080c1224000c0100d402003d907242148001e8072151050310700000c0613140001c006280030b0015540007030191810141c00318500780c01a02c0d43d4046544040c0313101001c00d080000d540e1107010031000e09009005420031703a1850303801401c1d0182034065101848860f2080c0b840040c0308119110040100a003804000c079500e00345400294000c0609403689418030320032007501400388107440031000300c0d54020004140300e85003c400074410507403428025a010000300361140c0d1680042d40c00f910f0204080d41c0e82c2e081103a280b0050200e00031072 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 46209419 1250 46208169 46208179
    0xc050901110c0f06130b0309161d0a18022d03010b0306060d15051312081e090c03031c1808070b06060d09030c05121608070305120403020109050c 64
    0x2d010755912030381141c9440304016510f007620346018208190311004203802c204100341c40801081200100001ca1808118134020450740254840300f410281d01b081c03c4a50b08107012100c0456150441940421451018040c0b406034482a82d4001000e42011001d01e00b44000c80107249810100b10311142007513031104074020424000d0b0003010a07204c0100404035480340a03404413510134042c4003400307800f802c2101c150401c094582440d841580f030710008010751b242c603c09020a41c0e03050007109600d01640545c900b101100e10404070b07820207100004c100413658002d040c28211152003c00150a04686a8403124030f22440d16016000702d901c00489071540210344180d01313010440c0e0804503a590754000c00b904500b41c1e03943c40402c01d6407141c2000152001e28180899003819801a5000407451150302940c0244155003c42022400341c50f100c0c0011039003154400000501c0d003002400014401c0c10014108161200300e000d602400325000d5001d030b5141d03200c0004001042c04200c02c01c0030300300c039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 46210669 1250 46209419 46209433
    0x110102070308060d0c150503040308180a1211010207110907020c0907030506010e0907080a0c0305010b09090910020304050706090e072703080309010b010305010b0405010c0215070203010c05090111 86
    0x10001c11044002c0c2a003405241d41511308070501c03c0c0100203102400c2c90b2640d01c40340b004000c40040842e84201c8084d000614024081960700b4040a01d003a4408030950040443c0f0302d803130310342e180344410081281040c0729525102d4405001c081c00506001401400c481a450b46804140801c40c600145042c0454100d2000b101c66079071403414040d0400054600000d4960300c5074010389120998544407680002c0401c2004451071340071444038400c050545051211070a242010380640d0002e00901401d0402404201e06504299070482d50045104084880400304902003004990040d101680c20f508401030500101d80c00650440081007818110441c6141840c0010702c1c1c8a40903a4159564117541c1c2d9500030481c2c2d08007928081c2d504080782030b0b07403418114a65402407080409a17030202e410003000040305900d001c03c4d24101c0380306031155609041c10fa42000003590b000703080060560024040305025032400d00c2201c03003103049616041d9442c007042002501c003038490399600003207a21081c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 46211919 1250 46210669 46210673
    0x30b070207050406052b050c090f0702010f0902011407030302040e01170f03030106090e0405031e0307030606020604020a1710060f03020f0f0a03080c030705150709081227030a03030c11010207 84
    0x40442c019030302500d1101003c1007a502d0503c1c1488c0d2981c5a990b8444590010312041001245a4078003810903900200400d4018480d0707074041d1540894044e010640700e068034002548024000d01e4094400d280c01481c050710303004070492195003070b004450039a8007460515006002004196045e858840c000d505641c9890170003000c1405601038074007c00036481c041002c00000300185c484009000c090032010500d1440348550941044800c2d10019040c4080016a94000b05609001e80e80140803013021a04bc040c031100d2492a000082c0034078802c2c016607515500e003900c1a0700140030004034187d400762860041010b48030905c000e0a20500d910903400e10580d641d8035583c03080700d0748100025224003110304020306600607424042c00c0c90040c203616007035503032400300c4042c4540714075190605031984030710707505e41c1d50441181c01c8580300c0d404206904034484d20f6500c2a80a4100301c91303c4000c80f5503a4082828245401c80c1180804d441d090441c0bd84d035008844003541c030003d60021420000c0366 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 46213169 1250 46211919 46211959
    0xb040b0301050f0103020702030303130c171203040f081204030e12030a08070e1504090f05060a03031d040c2c0a0e0c04030b0f04050606090f0c030a06030b07020705040605 75
    0x6200e02c6214821080d4020030703d0340a501902c100b150020140c0fa180d140c40321506100c446010b408039065008550081060000e03c80364404034951030000302440c4081c6585105903074000b900c1500c400e40448150000514508000c01407280d000300050318509081c900a403418001e850124401c0190000340b464180d0000155903c5000d589014540f50300d40d0f510a65000328640090303a0040044015100300d841140020811204469010003050043d03500e080101d41b07003030b650107a1102e0030703e2080011900c500c1c1c0340111030410401030348200103220005030440c0c0041e00c0c0f1401003015804800440500d41490610354580522031000c17038420f00f0006404d0b100b1502a0b0404410f289002c03031811000d4506941c040c6a0040c5480741d28140b4100c5545820401c44044901d03100700000a60345040042589000308640410304e0b0540c1c880995001e06c81e0002480d0032189a41d4020000203d50310140107030141d500d58015020756410b100900051342d02c590030183c0189100000e49030b602c0c0c01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 46214419 1250 46213169 46213171
    0x80a050408030402210105090106051c0206090909010204090c080906060102120d0c0302070f1a010909050a06050402040b0a0f1a041d0403020f030f280801030b0a09020a030f0209010b040b03 83
    0x8110b805c2d44012060503000f502c140006512072003158a4001006175a10341540f10009480d000c40e00800403002500844500041c0a14001c0d0008001d00603208141440c04015400c5540d03140050704285d100c0d007201045908541031030300000c1808050142604003400350a82110081c40a459a03030341114000036584a131513011101265542803ca020303074480d50546011136400230b0000d2140145017400200714509181e9947c031090080000941c4c01030394032445069035840b00142c0f50300001350310303440003c1c8401401079030465110040c0c408159034690841014121030202071025034100400009002c01c2d0f6180c084005104002c00c0c040311095555418004a01c04400000303540d4034034003282000303803090640136036100102d0b110f4440c2e030f051009070a0038441445401c0e108010343c1801c2040c03450700850000030950420040c00802c224080266101000d0070000c100c84945a01040324095150703c1030b41c0c01c088960750b100071032a03e0301c0322500401851141504144c01c0c09919091484 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 46215669 1250 46214419 46214423
    0xf030503010f091a0906041401030807110604081f06050607050d09150c02040902030313090b03010f1e090c0503070f080c0a0501021e1f05070324050f0a09020703050a080a0504080304 80
    0x80560000781b600d9903035400440d4001c04000d40381c0d0303480d65030380340c8890740c0e41099600701d440c548014411845801e103102500c08482c0c41d0300062007146c180c0d00b000b201c180074009a044480c2d880e1600800c440e200d01e802043e640c2c2c0305030010071100d240b62000070100c41c22908600d5a480b003086441c0388299114a40d00d01e69138040314005102541480003d00d5482500000b10802c1c4501000007007001c01d03a4049a078240041c4d000384000501c0c20124011103c490100000c120741c01d003d100350618882e4000703070f02c41e80b06043d80c078041611500000c2c90039503694450541c420810900348000c030402e010355119010b064800318041e80c10000045d44442c603601000c5405644c21440d102900d0040024240070204402e01459803c011370340440a0102190788001084c20300328401d002d0780807406640c4c0701070702c100c0b8011903060420b010400400b42c4070303801660166180c500401c59105038030041071103d00c20b486842e9920100207026104020090100450614003410080130801d40c40031654429 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 46216919 1250 46215669 46215679
    0x30c0c0818040903051b0601060903110a0308040b2205211006062721030203040306020310030b0f010501120e0a0506101e080a11030a0f030503010f091a 67
    0x1e525006a8480404240040d9a110307041402c50818160060300804602c61007240688030441e8081d0b40d5555404203215000005a296030104003142c42010f594001e00030003022103403181e9803902c40f20000e4015410000905d1000602040130724258101c003100c010340ca00310035010519000000320303002d44926411b4010b81485900720755440090040302032030140d24804200c0c0d6a2580001007140c20700702c08400281080d0040711584040b600609402c4640c4060402075101002d14603032544c00f20880b0850540c070050001000292450002d50300c9800d044440b14400c600e14100070100b460003400700540103034104010700031139074030090000c039541d0b01c01d2010a00c0f00e07880100c2480c0ca01146c002030264001d0300300340182c00003400da1410403981c03000d480f0380050b221860030002c0c0b040301d0b10900100d680000c00c3c040000d5424a0b44985071031004013640d41007245510741c03051003c2084000c5000502c004010312080300d031200703094081c0c01d10080800c903480c0040405800103032154080d42c031807 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 46218169 1250 46216919 46216927
    0x9020a0513080102031603140a0b010207030b0c0a0e150a0309080403020d060b01020c0307050d11030114010e1e040f030804080f041220060307030213150509040507030c0c08 76
    0x95014004464075444140040c0e4015582c6201c454000e4000351100000300043c0c41c0300c1110b03e4880c0c0640c02584000045c01802626400003078401020700c800741d02e0650081700c0300007010429000c0b840b44a00c00d000c0d03800c0e0f43e500054000038070402c02c00c86218850002c60400640120b443c9040e980500050300b000103410705e0908214409020b1580020b6204410550b00c00c06c00081d43c2055190890030303001c888000260384209a00c458443c0500307a00091503005040104108032030310000b0b540c0c00b034000250f08191840c02c90780034909030403042e2441d05620a00001c0468021f600201440701d0340004007609084c0d594040b000c021400107000c0000c044045000e02008004903128091004441039a0765a00c00740348001c105140c90035030f40024000001c40032140e03460102124482c00402e4a0b15503130740d08034107034001c0d0404807014030b00c81004031020a800b14000740f03140e11009079494040e120604541044155040249408105410100c0b0b604425412504510120368004281616 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 46219419 1250 46218169 46218187
    0x503010e090303070921140d02010605270604090501180b0603060c03010618080601060e04051308040b0a0513031a090c100509040b1503060316080d0e010c0209090d110109020a0902 79
    0x41030300b0206c40500050a420a0100203c0c0d0024a070780e003140c001d80080c0070070b176078070020050140d6a04000032403200d140c1c02c64031045020703492650f60044008100086c10342003511240c0c21221110280313030700c0c0c0c0c01c004140000c0c0600d00120303030b138480c0c4224014140741c45e0142c0d0031400c0b40070610843d401e0140800c80354000e900b411a0800180030340c2c0045800c0c56030341d51402440e60900c2801c141c066454034010556400074040e0a060894100054a1400380381100e28080782d80002c1c020810040705100f009809004a140000118010305000d14419042046100000b0340034114002c3c03513001e02d420701d40e55240c0c0c0c005441038414600b012511040a04e010030040c003040c1180640c0026503d0500102394510400f5600031401542220004940460003907a60019801020071a500c01500e01c450a40300704c51000c039102040c034042082101c680d022842408095861010540005064104807644880d01110b0541000001d200c182100e8010039028240c034000d0a140071340025003000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 46220669 1250 46219419 46219469
    0x1802090c0d050405010213060203040503031213060501080606040b04092001030e01050c03010611030708040e04080909040b2401050906030a060b0f1905121305010608010c0503010e0903030709 84
    0x9022106000c0c040d5107090b04c0c02d14003d6118060700920b070344100c000031507290f10000c191000c1e100082c0084d40b40c0b800d201501c02c0c0e400d400070055100c0c0c0d029090184c0000b0058040c060080089400070a41340c106802004150b440490406c0c0c0224a060700302c102003504ac52152542e03413448002060280e030803100403005400007204e040815800c00c414414001e55820086040311045d6880000d01110b0766000341c0c60741715400c1d02074440c801c00c0c8024003084207204101a0481d00c542c044034600614503000c2481142c085078250303000c10741102082001418000e122202810008035030414000010000c0c0282c001c201d01180910408030000d40b4960752a0321407406024481c43d211b4840c2141d112a40c00350340006a142c0130001c20009540e00d440c098003d40315810303500c25160900b40e4542c409054142021300d02035880d503481d110006680b0600303218001a00200c0e42d1599a41e41c10701a8075048800081c000c8581c95008100b00300075507900c030180c079080e26020340541090000d1418102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 46221919 1250 46220669 46220677
    0xe0609060a1d0603040c06050d0b10120b040c02100b12060c2709011701090813030c050612060105031b0a0518090402150708040e090f101802090c 64
    0x580c1000002469a600035080445112200a00d000c42e1140458107428810386000540b0000c2c191410400e0900069000b032015101601074810005400c00300340c07001401440200488902140c4400302d800c0c026855809182c214401c02e642c180103c6400010080d6074451011015100507903610000071140e44442e401810700c6103800c00c071016800e14400303080d030980c41020300061781c03100d1a0b030040c8800035040101010600041081401d40c2c600565002c00700701076050b840b1955039441605000940440141481020581d11074075002d0031441c1c100074040c1d49801c014441c01c007d01041140d03a1030b91020940c064004c0c41c00c1512500e4a0740401512613100700790030007403440810000241580140500350340c10318104036a64030748542c41848460f113026140070f9007001040ca5100110010b0740000c03c0c403184100c0b13015242655440b00144141015940c1c0c8409801242062a43c400301300007010184080100820401880c111039441c800c0300f1100c000d01481e10900001e4403103000005803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 46223025 1106 46221919 46221937
    0x110d02061302030307060c0e030f0c100e060c060103030e040506040b0a0306020310080703060b010201060803031009050402060904051501020609030403020a2d0e06090708040f02010e06 81
    0x15414618541030183e0b0144010440400010414414084000e9040e5681c0110350b0140c01010b003045e46042e10440e0b03c0c0d0250060799116560005142000882400c00d50007400ea80004103042e0301442481e59614002c0d040000300b8941c2010070000500c2e4115000c000e50350b240010002115144035440c1d0700301015035800d1000984980c000c642007083e0340c0d014804107540f001114a080078a400445005442d13541c04105940c09001d60006440228091401c502d049120840c03600340c04e202d0032000f2600d44002c5003d549945048440c900320140c01404540340400e0741118140304030024600500c550300001d4010f20011042d0b03030980b6801021801038614010307001c000c0220181c003c2c44004000d00031030032010320828066004160b6003002e810f0516146d0300b04072075030400a01e21018004071104010008203100940b662040c1e090801d00d035100745100225085020351008 = true := by decide +kernel

theorem cover : BRFrame.Cov 46043169 46223025 := by
  have h0 := BRFrame.cov_init 46043169
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46043169 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 46043169 ≤ n) (h2 : n < 46223025) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
