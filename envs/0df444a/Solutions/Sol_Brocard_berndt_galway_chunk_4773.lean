-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4773
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:41:20.278616+00:00
-- url     : https://prove2.me/submissions/62f2bd64-ac97-4f89-85dd-9695d3927523

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 858273381 ≤ n < 858453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 858274631 1250 858273381 858273389
    0xc09121a060906010801090207020d15021e09100809030d0c020d080a05060d140c09150a08061012030314010b0405040f090519050a142506020604020609030a170301 72
    0xd180d0401140480c50015141442600160b58406180c0e0804042901039006501c0c2260009510595000041d1043c4510345209a14880041e100c50341d010044ca00707921461440d0704101010000400d09071200c00c418006035005040c0b5000039200d07000f0091840c032030100c2c0d1041c02c0b440d0421500c0402c0c0c0c04940a10860b80301e0366501c043d03440700980d05e01210b0003980d0302644a40460400e40003e2412282d414810417400d080d03a1006203a10085100c89004403400407038001c82043c07090031440c00f90455000b81000303800030101440c0540c01a14140000e000307480d41d18040c0e031020010940309130040503202014406005155075074401e040e20b960803501443d8841c07414104d110129200c1c1307214901c0000d41040040c06250000100c00001180301e1070283d50074007410010380b0215400c4c2e003c80c02d07011504001020031540b02c6842c0703400c21030109511002c0524644003000700c1c640c001140c6410030780440340c09580d68040000039242861010004010180546105400581201c040e41c121 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 858275881 1250 858274631 858274673
    0x30a0c0207060905030a0627060f0e0c0a05011103130f09050105030d21151503051806060108070903051b12070305100b030109240c0f050d0c0912 64
    0x80c5485000030b0701c241c6460700409030154040c420080c0030410f2230b04007229851035195400a2034281c000c0e81e015028030721800f0340d040e030744861000030305000c10701c507158403505810050103d00381140000f0305110340070b205071070410005100c1c800450800740105c0f44054404c0c031088920716601c90030125a100a4450904040d251400000361424041010f41103546503507101c040c070f07030104183c40c820450341a10b4050102d41e16104500e00081d020007800103049111079088000c0d1042200506844004054459000c00684035107000e090004480f500a0000d0070302090595502100b00c402ca0569840a05503204090a021110308102801e510360328007903901420003401c0100706d0355107080718130009090345e0041005075101290b990103030300f400c00001c0000c10302d6500c0d42c0b0b8800e90842014420300f042c181901803904400b9180c85500300400e103a0420382200140408050018000c240c99000c170591110154840c0e18407801501c0060100541c1c030700c01708402401c10030001c1c48881c0c640151 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 858277131 1250 858275881 858275893
    0x316020301050c0306010c0b0a0608010e0709050615030103030507022b210215040f050109030228020a0608040c09061514040f1707080a060f0c080405190512030a0c02 73
    0xf007210004582c031501c01078446051200c4242d40b01e007071458000300a0801190b4440b0041031400080c02401c420a01807401401181d051801090444001800c501d00c105619144120b00c0c03441c0c0d4065904503a01414910788a41181c00481c80e00468a0341006c2a482660f001800605480040381040c600848012000d1101c03544e87c0c0309904001061200940c0c440c20000300c42c0b6404500a5500c50710800d410b9a28986c0c558403107007980c00da00d1007200582c00880944aa26412070708941c0000b1100c084c036460610140c002c15001492805003000f003000380d4000030700b404009110f010007020303d400d027085510341c3d4010400d09850210815000034482044001c1d501c1d00400546007039802078803244124501d01707019134882c0308440c0d8900e07030309019540c400a8144405d1007424007282c0542e4012904030100107000c0125070162040d20305000b04001032001080c0001240d45002035070022a44a02206092552520080c5034540b10348070000010000e0700c111541000d4076050090b021205 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 858278381 1250 858277131 858277141
    0xc0c070e04061808070b1b0d1e02120f070c0f0210031b030b19150f090306021201150807080f13080309031210060e090c1227010605180711031602030105 67
    0x4085c0345105102a0b007c0e60a00030741c400010150700c041103071400c90200150101f070304906441a07030044603002c210f02a13904108940d21108152860307100020746880c4032080c00d960394241400211040207030295110356009003000b03009030300005901741c0318590844012419a00100607102809c442c902070742d401c025448010000c1021001030321054038501c440c0c049000c0d030444601314051091010403920140c00030204103648010312011000c481d4002e000e60400308007924404c01c0c500d0348404c1000d00c0c000c0281c084d9000a49503082000303010724402c40d0315100304d080c0700d02c0360385000504040ea00106006c0302800020042000e030792520014011a52480c2106c28400302611800000c2201221b03524075500c0c00070212079019030422035031410b00c0707100388900c0c101d20811104c240030014030b00408000381c000105400101421140240411810500816502800f000b01c2e2440b800d40e007400b10352520700030062a484d43c85100f003141d403203858503440c0da5040f50702c15406078040d510745070201e4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 858279631 1250 858278381 858278401
    0xc0703051011031603180f030905012c060417030d1515030509031209030309121312020402040305240109051506090109150207030b0c0c070e04061808070b 68
    0x45140107603a0b41a50459503145005003003221a0405201095a900030035a1000801c64001c0d414038001c0380800c40c00f81c801c1c54080c0040709150880c506100040d68244621480d0040b20300340c81584c0b01c031501c0c2c1100640e0200b040390180b07404c101600e00044d4107070302e01010000058203280504507814040701480211a04810403140980c4800e040025800302046000303030050b5821002440480e4900b00708410340c0b0b410100180c91001c2c454000000340000d15000300040b044211010482901c0c00680007810740038200d01c0c1c410b10a800403d800204107544d52941624002d640007002e960341a901075020301940c8283e2480030300c0c1c041c2c8440010030701242c0c612890b0b1203a0701c2d035442100090303040300c1007080c070ba00f003122218108101c40901084070079030b0a01d029144503464004100c1581136150480e030450703006281c480e0191043c40150f43c405800540700701215409006801c0e075468030305100c0c000d0010501070305c03c1ca80301001c484040120402c003c0c0303002c0e0301943c0721406d0750320740032444 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 858280881 1250 858279631 858279641
    0x803220302061e0403081201090c0801050913050f0105090303190506090106030b040e010615230702150f13090b0105210703091b03020307050901080a0308060105040b0c07030510 78
    0x1070b4100400b8480840301e80e184100c5070400080400034141400e503280e494040b10f0340203150100030f61800000402014031280100b1821251600300108158148008200702090080c006108581902228002e02c242400014000140b070f400a01c40e03458402500356a9034030542e9090308002c0c03841240359104104e482042d000341030040248403140d2900e00c0450140042411440c0e02c10b42e1120f454888400074400d06005011191002e614400307510f40c00b401003040a008500340d0100e01c00056401c1c86080d0807260750a504503804040000104079500c0c0c1d601415558282c0000c002800760180c503010000c10301103d0500400703016240008004681d540602d14800d42c40710100300c00c07104080c101c1c071107041c0c1c4100d840c64002140001920f6161a21207000c46440165031800b00500560a0a1100d0340c0607110558041005514100ca0503541350085d80000e0304014000010500340e0780700d0400c03500100140d80b00b040e00d80350383e43d24090b10b60203544400c556500c01c08021850300c284900134 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 858282131 1250 858280881 858280883
    0x40201140c010e0d1e0207090f3b0c03060c0c011b021c0e030606101806180f0608040b06010c0b04060f060906060203180301090b1810090f0609020f090108032203 71
    0x2907d41a880c110340503010b002846403980280e80c580c00560914a1641d82c0c6104a062402e1000d111441007002c890b030303241c1281010450b60300402c48403c5507031030000351260002281140d10307960b2601c02c0806401001d02c4101c42c0c20b162400703050510700ca0341c001071014460401c1d262145086ca422030040d544000116140380c5c050f045034000070040d240c02d1001ca680d4110909200340710000303007568040c840081d41c0140c8041409146040c002c042014094400386c400c030b420000c0b50b503040000160011500400003049410700b50001209a48a941c0701d4030300c6c6034800c40c00e042508052034800058034000f014282c03440e2505400240c103003058041c10086801c26005180f820342062422405e46a01c0601a0b070599281e00100c000266802021403152b148a00303013480740302c01495800d01340034000048800302420140c8580c0030401880082c1d1301a50b10032000160107600d8400704085000b002c20140c0c0c055044030000a02c0348000c002854030700c41900b2141e00e001002c1818028020007400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 858283381 1250 858282131 858282133
    0x20115030308040f050303101d0601090b070507030512030a0f0b0a0902070302010216061d07051309030e040504110315041a130807050307020103050c0c06040201140c010e0d1e02 78
    0x242000864040d1422507080383c0101201044c0040030349419165910a44444a108000c0384081000c000c0c034081586442c06954206119410b0101c00284148140e010381c24207003100143c12006c00000304101c40c010740d484401c0e03030400505580b4120b4150400c544020750b180c24000d200c161440c20b44190307540d07a20020b081c04409414207108900a410906c8120b0541d9420810800076605141041240c00e02c104808565000d50102142090a030212240950742c0543c10034081d540d1048a0020784901c03050000035846058181200d850782d00c101001d801614080c1408240075002ea400c1c00d4521041c1c044400d607803c4012070703404400b02210060b0040c0c203020b030381c0300034034112405080d04461202243c441c2d0071610386400c2413a0b808090100c9079644001045401c550701402550390003045d1a0034641012800212243c85100042c002410812090183e514803040c1c070003502c0003030481c40e000700441010000f06590b01c0501003400ca01140311341c25540310140c00520700d0001c007640c40d8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 858284631 1250 858283381 858283421
    0x15050304030e1c35030417120a0915091103191a06010e0310021804050910200d021e030402030a060507051e0a0908070506040519080105250201 63
    0x621141c4c1566420050759650641a10050f030101d4801c03800b4100300038240b020990b9905041ca44a400760f140402c0c400c0e15440148028130040d03004c40701c5543c1c45498a10041402813192801114045007a0a00230019141120307040601425140580c0610340a404440030135242d8440b00000b003000c080001c0603d200050b11803100c820089045401c007a040c10041070480034400003d042c02d0550400c0201e00307a01090080d55a007204203c0e4500360415101001107090107a1003640f648842242501400e44940041d01d58802d224103101c544100180e12540350444010900d010350b03c40c00c1031121012042041500880521040780d01950f030040041c8024941e50b56000c010709401004401402801c0c0000807660340918014034504800301e240b143e4401c0ca104010f0400b102a400002080e40504400d000c113464a00c201da00b40c86c01240d14009420348c88010100f40403407034000c01501d50a040500c907201507152007200d414160b40d14810500071032600128201c44c10340d142810455005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 858285881 1250 858284631 858284633
    0x406030213090e0a03030b091b1315030e100c0806090c0d0908032509060e03031309091e020d0f05030d0603050d09060c050606060c0715050304030e1c 66
    0x10354000d0020211440300c00d00103603968401c0c00c00b2601c40c6084603640743c100e40d2159040503414480e88a2180e411500105142021070207440d114100950500101e6000100c80d0a402440410341c4001c11b1600c2d4215a100040d4030000c0142c00d111411004900c41d80544511040050240302d0012020703548002c456600c410030410503c2000d000c40c5480082003021035400f200074060300d581c6500490740342d582c9042c40803d89401c00150601a1140001c00a441144d9540a000d4004440d000d2408055600030b01001a05521400c90307401c6601a05c16400120382d0300503080400d14078000d900b906a00882c0c4842c00d21020f0700504020f502c05900d00108000400d10030128130681c1c041d0048900f000700075010002118890381007561320398000c0380328211941c1d0102041d00505401e103008000400c480d5540c5644e41c101905e280d115003000319500070000001c0181c98010103a041c048040380c071040e01f010304107502c00d940c20340005000d8145d0900605001e2180c1c180e10340c01d01c020050104207 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 858287131 1250 858285881 858285887
    0x1101030e0102091c03051c0b09060f01020d030e0c090108011d0604120305041703040605061f0e1e031f0501050d110103110904060b0301170601030b0403121104120c17030406 76
    0x70341303002101030240c244030031f2020076401307020002c803003007203000005906034100d04200381440c0007054a4825a0f00d440c48a840343d07408030300410060014100458220300215501d03040031902401182c00584801c00061901c1d015084421899008800250158007040d1225200c40c0101c03405058401c0c2c0302c08080350944a54002644113014801445140b50400720200b402d610030781d0190344071034a85007405080e04d80784074904284004c16244c0f540240340000003030062140e5043d0740f882400c9002c5c00c8141501688601000d607031009060f40d600e0340c04850401001410b405a00c83c00c0c600c0c020001c2401c0c20003154415013a81c10410520005503040f0045002e84032507150080440010301c000782d442d40301c60082902516401303000303644a6040094680106040000e1909a54050340c0100003080c00b804070280c109805250000b815080d000398000640645500c244d920075000a000580560340d0782002510382c8100b502c64100356840007059000301b0040304020668004000030061a80 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 858288381 1250 858287131 858287179
    0x50f16050a1803140c06031b09040e12031501020304050109180608011506020c0a1d04050f07030f030818060112051006060305071101020a02060114040b0306041101030e010209 77
    0x341e464481003040c003001c03500302400025031040f6130608007041c010214007010b21030035003070001c00d030f4a4504500d444059079070002c2c1da2126082440c2e10024900407a5180e94204d8018004648101c031050b0b11058814a0a0350003201c3c01c100395400030720812000c0d031005c01200d0450380169118211982001c42d02107141146038044110300b9070365540007030580028000e01d11032600d101c5402040900d00140681041c580c00946403003000448000e00040e10072040765441508100707a0240c141d9198507003986404d120203045406445841e0300041000000c1100080305c500c0b03980d407d030303242d101d01010126118003804601e0460700101c006202c81c1440c609409000c41c010b501321214003850030021012901c0320341004000030344030000c100542c1e030880142e4403003240d4140210b1810700c031040001d480d104180105049030780008001d480682d00c64120f088012001400c1e503100781807501c0c1c228020701c030304c1c2d4003903003c01d007031076070007c2c4044040c0f0076262850b41c00350101361702058149650240b00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 858289631 1250 858288381 858288397
    0xf170c103005160801080703030804020a0e01030602030117010537020301030506060f060a02100c0521071e08010b160b01060914100509120106120b0a050f1605 70
    0x140c0c0404644520051804036120302107584100003841e080c4889600d0107102c50802100511401c2c100410004c4c0d0000341110840350103290003642600d447c03001032b103c405258030405080b0074090012040c090598001c5040b2400449108a000c2e0b0b40d02001d801c2e14400c0791400ca01065410303d070801003807000030381c070200c12001c01d8120b101c05e1840145000c80e0000e0304142d0301584074200b04805418000007200d06c500b030071201d0394184801e20320025034501c824804404880e44500421002c28083e4040e2456610764500d1860401d091807103091241408640e1080000c08000f500d8200f41819040b00c0c0b07140e500c0b565035184e0790307003411130310003060344980d6840289004050044002c202d050703140340d000e000590741c0c000504c5d180120103030080180b65940c030b21480b04a200c814000c0c0d0840d00721210305030706607030a01840c22001c21590040003284d11034046074440c40300c0c500c204089566901d1048100041c1000f150301e403c085c511a9480032901020700341300e88000c1c03c0c030742d500070409080f0380 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 858290881 1250 858289631 858289667
    0x903080904050402040f2a020a0f030e010903140c09010e0c2d0301030515070f080105120c0a0b04030b0a020a1704210f0f1d01120207050105010f170c10 67
    0x803111901d02d43e02118002d803040301c1d9424041000c0e07001d000c0c2d50320044205030007500c014400d43c0213070342b14040804981007000f003e00c80c01e4106181141d00480401c1e00458000c0101c0c5003031400d18044584cd424002c4d080c52064071020000704101c1c501c1c0c0141c6000e0700504001e41e041620300440440c1d002048040381d02c202c62055055041d085c61030f0001c6020314419000740181480c502d40589105102600650610851825244210798000f17412070460310101c034100c080d00801c04034213041010b800386094008104007804101c50420000402c100c901c10000c82e0620755410010408a02843d14a000003800807400c22071701030b1300310b0706042d0443e0281d8902420521079001e910b9a0380504000c070000720700c0b81c05012401607001043c0320050700b03403800c0449402c000d03844200007520107507425a0500c800c10480c0301e054011541500d0781ca90740131000b0040d6503180e682d0105800ca451190070803180e0222508024800c0c045441c1d101c1d1070020b4a1080c51000c0c4403000e950745034511184000c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 858292131 1250 858290881 858290891
    0xc12020402090a080d02100c0f0c11090c0c28080f040f06030b21060712020c120405040b01020a030507060b04020c010504110a060212070212120301080106080d090308090405040204 79
    0x65a600f03040e500080510b4401824940207222010f410900400200302c402482d2900d650b1000380c210200120b803148038600803203400307000d1070031603030803070081807034903000321010041040c0010100e0042011040341e0382103c000010701100395941d0319000303440150419a1501c0c1e01c00080b04080548814510507001c5824940c0341c41e1048850241030b404280000e41b01c600d14022401d05104c4901c410680307402070260005480361842d507800c4060a11010000c1401e4007410041c0168191440301030040103681c84c21148403451400307a0858080d80384214a00700488005600024040d80d10991540700d8034148003168a40100400d060142c1e1500550204203842100c0e00a102e070038400c038840c07602ca110605101040c8903440300b080d0031107025907000080c0d006170b296184042c0c40e0f441c3c0e41160300c4500000010211801c0441407155103404134004000422511010341069040d00c440c01c080710098280b4010880e2150030b00c1c40064490001080000c0a908040d045594418000384c03011031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 858293381 1250 858292131 858292147
    0x60108240a0207021203180901050f10050f040825081504020612090a11060310030f05100606020604030f03140a0f091b0f0909082d0304081809040c12020402 69
    0x3445c0b100100c00d41416400028034211b0454207020341900741c04040e1b0b842d503110340c140000306010090030001284105000c0150700c1d8080c1c0b2401c00c50b682078004118060b103881e95440b01c00d541e000d060f052000702001c10303d51480708449002501d02150b03c103900810540b07062446080f00013a002d00140d8100c041005030541d501003030704202e8000c203140700041c0959100380c1080101c0e9a80140454404c03001002070000c6200c100182509990300b00d0f9100c8a002d840d8a891032070401042c044030a2142006000141c2a801065071031049000b6118050100c45500040341241c102044411041c4142c00104d00c406505030b10800307034401075460018001e0160389400c241c48445080c82d20040d612000c0901c40c080390804010000c00c0340d02c4050020411541e508001801440d081140001800300700e00c0400d644510a080001d00c0908059540d0a103400c204840b03901000301400d40e443d4001c6da2150078280100b0b01031003150045106800b0704d00340107a4544900460030103a90003038081c80180 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 858294631 1250 858293381 858293389
    0x60f0405011110142706072105040309170624011701080c0109080f060117070b120703060509090607051804020d0209181302190b07060c02060108240a020702 69
    0x1942c2c04151048134a6502d040003445100030080e01c031002d00c0d0405a07001c005c4140e00091213070b40010090900b0116044000c07003540300c80c90490300c0901090b051205020625400030a004195032039180994000d0ba80385107002d94403c016610b0400a50754050b82c005140c07945400021180814540202e405c0115040007030015000e820082d02d03174000c0e403c50034142da04400f50b04010310700301010307080e5011003d8000d6120001440741500d5540c0c0801201c9156502f0f108281c05801948026501c5544480b0300da65803038070403503c0c0d1011030728183d4042814174014842038417543d01000204003a0340e0f40300044a15030001925150000c07150152030a4039550b03030000c0c03c00881700510060f200d49000c42080407807120a80580f0701124084207000b00b124000110403034a94040e01c641c0d4000900807207030f005042d0380c0c4d070020564680225044042142982020b01c0c004259421201186d03214400b5540b6130045600b586940c001003820045103c64561140394402042d0000504000c0d840d0085 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 858295881 1250 858294631 858294641
    0xb0d0e010c110d1809090f050f07051903050624030a050a0203060c03071d06070b0a0b03070801020406053009030301170102040b0d09150e1b060f0405011110 69
    0x5040070501c0011001d40d4018100b00481c2c4500b140e141c81c0003031014130b1586540c1a0300d180200d0001d6a141c8400200344858002d00c81d00d82580101141c03030100514085648a8509000303084c4104113004036005102c0c56116a4070a5a41103000703020103840d44a01d041500440050a0718014030116071881103a07424404101428000e2000d4040600d02c0e10405040050051210860120074001d020361107034020b04100014918045407103032801c1a10004103103018444004140051030700c01c2280112458000040690083d001c81d40401e4803a074040b400e0303001e1401098002081407080c22000030743e400651021032040809501900480c0c400c51054010845440300103510000c010086010461808003401703000c00004c50805041c8001850648210b56100c0d585c1515a04900140400480300c0e50b01c0c0d034100c003010044c1840c810382c059101d4010800d03d26078451a50b040d5044d5040034403c0f50014003161000c0c03881d05062000544031421091001411403040d41d59a40c5610300760300c24 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 858297131 1250 858295881 858295901
    0xf0e0f030105090705040e0a030f050a02010f020d061e0b0d0f09020a0603050910060602030304060504110409031e080c040b0f0d150302040b01020d090312050f120f0f100b0d0e01 78
    0xc4c0c130100341000f007403005440c01c0010100c4264801d003210341c00f00707074414100042420f0900e80700e580d4820920341207000d41258540c122046100003034591300c044d0390b07a1203442281d4003a0014801940c0c4410180050000c6104040c1080d00411005002100316444002d00742615030000610030b072981c0125001c10015009000481c3c6d80d8070600c110f004041140740081c2d00c52003021312540d800c01c40003e4480c0000340004000c10380340c602140400040c4c0c1e00c0804e076910041c2c420441c040041c2802814030b99065680e414140e00b1200084c0c295215a9160307215030384141c8464906841e1043c021070a91147e001c10622410500c1800c0ca001c11034060001d0811103110511501415401000300b00c03034041c0140f40c10b40d400724803c1780c5042d400144103001c0740d40144a42c1542c0c00018025100c600c2000950008204001b4001411904c80403640d400341c0d15001d0603103d155900022403140f910161076525030907280c100c0400601c0b400713000910800c80003141c04a458524010007509440641e10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 858298381 1250 858297131 858297133
    0x13020403060b011403040f11040b090709090c05040b0306151c0e07050405040203060708100f090204031202190b1f03060f0c080c070308040f051e06010501050a0f0e0f03010509 77
    0xc007000c2d0780c403891503513520302d54030102440c60401e130b65050103000f03172440c004100540c0041040035a13607541c1d00418000320041d105a95038502414000e000743c0c294041e0f00301d120714000b451802c5c640b080095900703031240094481d1a41e112042003010541e03d17100c1d00b4600d80c0b010490f90b00f000040301040c9030000c0800d0404540045098881410301c0100d40245018901c0c09042002680e0000303400e540206c10f03130500c0006038481c072440314108205074200140c0ba500043c00092a0907580d402041120702513421019940080107007241c503000e0091811418682101c43c45c00400d01001c1c045800a580781107401c1e4140c4402d0842c0804600d940c070681b03449135118204400c2207454040c05140d00e4251500110301c1c5800c1d03400401341d0007810406802c101c003410001c3c0410040c030031050003064206003140e042c0c506400814950b1004c01203213210a0144000014595002e0001e4810280b1942c480085402d0440c804641d4803c00f0b20304198000354010100c000f648003807056034000d4440e40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 858299631 1250 858298381 858298391
    0xc15062806120c1409040608030406020a02132d200c0f06010f140301060302120120121b091203090f18011715150f030a050c06091302040306 62
    0x100d0141c08490410421107516080401c41da000913413012151002c400f441c0000c680b1400d404020030001d09058012a1561000003008601c090b000110290f42503c00c030348030a00955030301c0c491401d40c0c4402046480500411403281800342204032116140e000583c1e0028400d0007542903144001d0030140503070340a8200203205100100c0074040c000310000441e008083d00d5140c400c0d80d40b00000688106003000a071a600700015640c20341181c0010368000340348a60384180d40c071009008050000c02307440b4041c5d07010050007aa0544200741d404103072215100e0b0f8219039414120300c04040b40c0440120380c0410411540006a840340c1945c29581e100e100110f44500081041c81880c07000340c0707241441807003174429122aa0851500741d5054071500404101010380c80381c2001d1409000c5a00503d0700380709c01081060030380400d540c000c54244225400e000c4507640038140340d214805190064555040785030408643d050460040c00b50980203050a0039107240d03140c0e80e10880c0c00c2500101d031420703110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 858300881 1250 858299631 858299639
    0x203210f0106020609071a040f0b0309070501230a1412071b17071b03080702010801060f05120c0d0c0302041403010c020706140f0406080702010f020c150628 69
    0xc9104a01401060000f45114145115455030740c2070315200d40508640c50f01d4908110880d05000e49004004800706928450b45034000310151360030454280b0114030502d0800a480d40c840c115030140c0500342000c1c1000c010528590440700d0348804014011b0042d201892900c03070f422000203025031982000c210740181030009008000742c0c001010010402040361491020a0100489401180707501240300e45d40c1d501807074402c000088208040b04070065221000044c00348200040009034800d903690441c582e02d414080e40c040500d0841240010400c1c0101500148407448183e0040b100300c41590914000c11521000d8a0003040402c00080d0086400c001c030802141c802c007003480048000740074465506000a5498003144108001c21400c050741d0440d00d40140101c1ea207400030070841c00c0c0d0761502c4080c050140081520007600541c609222210941c0c00b40c03003500d840c10096004ad00d103520f03400d941e50000742c0000d0b21095116880039038100020504046070300c86812170aa00070782d124a4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 858302131 1250 858300881 858300901
    0x26070b0603010b0310020304060b030f160902070c030609030c0b0a06061803081215060a11060f090303130203030c060106090e181e010b03060a0515060705070303080601020321 77
    0x1400d118002e078100700000e40a5038001c9040111004d007168010f85036a03940c1880c070702030080d2444007070701400385040300016042c1c04510301c030b0525840b16048030401d40e00d08a0900724843c2d00d07005840c00c812114280009003403078110400c4540240703014034984107035884091010000740c61580c0307510780e13800040051303035000907111452039000e81c4601100c07841d5403641c0b00244603203842d507802030410000048120604007149824090b010b080c45442d00303a800000707000480c030705407a5880c0784284400100e201c040900014884c24a6901450440c2c40e51000d601e03004461500407030341400309008460055130708012250003040c040d6210b8541310310b4604a08001200078200e102030000d12074040380c0c92900040d42259424003000360303000305c1c1b1035460f1080c01024841c4240307915000c1c0800b880a41c52058000f1802070921001107507003140d81c102009018880c858004001d600640000c00100780101c00c42c9910040c1801542d180130b14180e840e000c1088426041400c2490f45405d02c448444 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 858303381 1250 858302131 858302153
    0x1124181f05180418062003040f0b0a0c020a021021020403060605060703081b0702040905100515011d0a0f0306020315060a020a0219080102180f0103060b040905042607 73
    0x60588007007011041c91361848521302d03440b20019000589880703036102d046580004c0144c031000c4803801c0c59140d080c24504a40c0d8500c0c0c15209556445100c00031681d030842e2840365501850343c640061110f003090340d09201d5002c0c21480000280138603c05808000030b01d4114408284a4829006a840b070951810200b290000d070000782c0a074109021180010386c0041d0283c0d0040794200b14012400c40310015410948500e10b4002d403c207046c10000e00403c840054401810282e00d4000d002540c6c0f6240c50b42c042e4492804450700041840c46041c06403142d00c4106a0780d58400f030040e40c001603c1e40c1c3d0388030100c4100e5108451541c1c2c00410008a423540b0628541d6844040740c0d05841c1100c01e010096603005c3d9201d01a10035048000032101c49030051a03071ba802004034030001c2d0f40315001100401c5422801076078080c003410780b1120003c80c640c403920880c03059441500c7c40e142031904009a4a0007072500800880710007041e031101c038a00016488440aa0015620f8003503074540d00c40c6001041c1c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 858304631 1250 858303381 858303427
    0xc05120c100c080f04150603061b2d030509190302030307030c09030b0105090a1e0e190b070810030f080405120114070c050a0b01031124181f05 63
    0x401c1e1070f0240400c0d00d8001201c950041d820000781c002e0000e04621820040c81c017030303000400807403401100c0900c00408003000d803500003440d11400300700104217001e014a0346042e50189258a01d030018150050b020b603008682014440d4100c52941a04001500758155219001d03005a030022041250490741800f414440c40130354900026560720b50713600d964052906006040c481c05826002076400c0741c03035a2100529071208450308003c240b512a0300c100030449500400518040c080c444d0406402541c082c440c000d51060640c105641d82c00c50450303c610010786481c10601e200d401c000040340b110a1324011940c05100c9040d83c3c0d5181100700300700455402e09030f1515034141604000490802002c5a0f800b01c640d0800803400000c502d00b0504200c00400024025030300707500044140029001003444000054612199800d01031440d550b811010200c0a927520104002d018580f083d1828203131074280c4040c2104980b01190309045035803403070005911300002e00c082601910007000031101c942c95 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 858305881 1250 858304631 858304637
    0x9030b0c03180a080f1c1a010905030c03030306040c12090804090507020109030c11060702060d1a0307140139060f0204030b010509040812090a030801050a060f0c05120c100c 76
    0xd0109031350714481402040302c100c00100011032014181c880d441481102990000020001420b81a6141017141a600c00c4107000810956001c01c03e410001600b13184074000800450030355840804110191401440784420400f10442c5454044024080c86031000d11503003205440701d05141410040310801800c03182107a0525100c5004a900541800700c140c0d002041030804082d00c00210b0958410040002d40203000061084005a15940030750b80420441c80400443c801c11000c01d55503113068007901030400c945040c3e07146030390f00178041c001b80c458401210080d00c4074084510000a40d0320000c5a04c0b0032205800c1a0030001039200355000c295440700218105421500d4501c2d0011050082034010011040481c05100790034051700c1c03003082075240c4449a46001c0540c152908013a49040f00401d2040c40080303010300d0309046a0301510280e54803403115006000044402100707084064905000e0403503205005a14440202114a100402059407061081620084800496280c820 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 858307131 1250 858305881 858305893
    0x311030705030f0c04170c0a05040902060f0c012702030d14090103110705060c071505010b0706090606090501080c150a0f11100c030b19051f09030b0c0318 68
    0x400303402000380c82d0891086603d190b044d42e03807445891002d2141e50401d4940da07100101c96010002c0000b0700a000e9101500d0803143c2d65035407418081600c9007004020340c4450b06001c40c120001c0c07070002400d10301e1300c1c034800860441c10034050100c0841002c0c0c0d0aa07459000403124806604040100402111240c5800242c2c04c0300303026058072a0090314011030406864100e030350252072140c0181d50b50a504141a200c440c02e0001d80c080c019071110104032110592584480001a003e1065504a80071649410b14042c01c9070b98440050035a160112030240e500c072808207260400d4498030780a004020014010501608100203a1108140d5003001182c0f0030043d440007140c1c49103030407514100345c1c1001041240034404003810401407582d0f0b6002680b9000400490340c0e4140c2007001803844c05c0e0356412031f0400c42c1811003004441800342a0300405840c00481c8a0700d826013071030011441c6071802c2000c1988956684092150a682400d60b0f61000300c00e00041184203c2c42c409000d03086002041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 858308381 1250 858307131 858307141
    0x9040506011106180a12020d081e010509061306092c2508010c08040c24050f0c06041b0f030308070f120e011e020a0806060708120a0903031103 63
    0x3c0d85000080c1000340151109030524030410007000400302195008210307003001841403100941d00c021130b664a0380025035031000b08103041d60a000108d4a008403144030600c6a090a040c07040d003c1d8042c00158101e0000e0440540f560a54230410003e00403400000c201640322171058002120801c800c090440e2416001014007003000030f070200620741d00804d000a9000d41000404c51142c0c940c001a015400c040e6034444580e400011503200d188580b03c101d0b0000e4403520241590142c0142c1c583c01415030200d0184098090006081440d903e01d15603031826404001e000e080000c2030783e084841164100e09102000507244419019000b12911440e20328515103000341081005000c03d07040c0003501c0451100310384a0b85102d02545e02010042c003071910144103c17802403595201400d807594550441e00308102c0f1078000ca4030030618903a074540ca0b0340c85000401006600c440400c88030400204002c039203141441440301d2265882640000301000e41303003009003e480b0b084140300e06405040007004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 858309631 1250 858308381 858308383
    0x190e041e0f0b060306040507030209190f12080912010e03180a0909020d143c0303010f090f090c0b0c011109100f030e030c0a0303200a0f09120602090405060111 70
    0x185d480b050494001c070303254890000a80c003c1c0300312000b198001c0d00c0e50400307012405051400c1c0003210320014543c080c0d2507030b07090014484041100024501081000b02032050301d44a0f1032860310441c10b6000003460303212500c0842c5550b0005840340184c0040b206144010710748420702300000c082d50f090900040c19958005540005c032540c004040000007120141440020030444450350402c4003000700a1102c44041c901c090b005020306000740281d54202a0b1020010050f00e040390480510240300b9401c000c00c1c680500161802414841d1313640743c100010504030a002002010b040c40040d0340d03014004030303041c00d55800c1ca81d08104950108184042c41d00c880001000b12036280c90070340300e0501100b1003100540404100c00c01d50388030200c0c001d01c0e061000f04071441d03030900c41c1e2000c0000040c6000201e010f810401c48030400c0d00c01c140f0141425501a05840e001c90030580740214125403206024000800903480c251586075000c540e1640e84d0511340b040c0c68001c442400c1500402c45001440d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 858310881 1250 858309631 858309637
    0x7170304060810150302070209060f1539070609050a0302062203140d030510062105010305070f0b03040c031203020c0a05010e060106080c190e041e0f0b06 68
    0x50007086642c1c2d0000b0181100300c00c0c410007401a0200d490341040b400280100607410040c0300b03902c00e450141c0403031610714200c0204481d1100c09080c864501922001031603d5401035000103611140305103802030000c42e07046824500018040c8201030500251901c50718018a40d000f038003c0c000c80080c18422a034032081c01310220f80d41160744035506c195805c0d04000d11184c410466481c401400004410070281d003001c41c4422210002f220140c44c0c1070f2000f1010f891060f55060400f443e40350b000d2100c6403090002c1080e2007140b4800d416407801c94104002291000d074404d840c00d421000003030245008482103040200b50368030046065041c6900d506002542030303c00100541c4610342910304107400ba4051b90300c0c000c540002c1d01ca081109042040c0a0b00d0728509200c000d0141d0360020555501030000580140088914541400000303441c0c00c0c0e07070401da0b4030250b007032045498800916660301d0082c0142002c11241a262150b411803450064a480c00082c1820320b050183c416555100c0c001070f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 858312131 1250 858310881 858310889
    0x7030b0906151c150c110c130b0102010204030b040f0302100506011b0510110d0b04023f04050a120f0c0b130f0c030b010806040308012d0f050307170304 67
    0x110404100183d0b207030240740e400c3c0c0680282499070b03a1080f40c22405582c0e02c54400c6000b9521407000d04556405403a450707400aa6925074000c1c01c8003442c004141055001d180c80e080c040c000189440e44076100e01801e80000c6408030741c210042640e81c4109035044c48038003569504298180030381c0c00c1190010340503140101d00d203200305440e10402d1051010821485012050000c000c1190750f03040c40008030345601405d00041ea0300d05106040310303d8200b5108403038103840c412460507418244000b01001c99001701130203a000d0101c4510315250310210110881c0140e101c2c3c001080780c1c007040d00e0301281c00300d48000008240a041c03440250714507001102c0c000380c01d0b8030800040c1596100d0182c61580740300360708050820710780b680031181080f050004810030b40c1d0007942034113200da987e000b0385961134204803401000070700344200400550b0a480c00240114400c06100034141c1c03d942200500c580c407640c080c0e0b4021258010030056802d080c099240601514116120507a40252455641e8800e601c6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 858313381 1250 858312131 858312139
    0x160b18040902220f15211e0c080a020609061305131b0f0206070c08160c1a030606070209040503090306090304060f05030c0f0a1e05030712140f0c1b07030b090615 71
    0xd04582c0840e40a02d01e69403944210b0150ba1f558614101d040d000304042c0080360303102806040441d04a01c00560106d005034010001032a00f400081842016041545000c1c0a00e2100001056581c3c401c01e044190076106440008d807800c1000c0900d10001c10010540c040c89400440c40541c0d40d404140558095041e0801400301d258600d044a8907104414100765124040342c200004c114545600200320f40c02c00c9051a0800c60814084002c0d200a450499001c07008004410050030315030345640c0d0045c01681528281408400400d082403001c0b0b80c001200c2d080020203100054000d50114107000d01d41c5481419403800009080c0310340b292440715200f4a6000c03d8401d05184965407940d55440c8600b24918a03800380c00002d0b160f500150b0701603010440994000081c15142d2044c404c03000c600b050230214640700c84405801d0454064548084280e041020b89540d0a5440b00c9492041c5003000074040706180d4103006000510140249882e80c022409028045c100e43c0031010394500122 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 858314631 1250 858313381 858313409
    0xe06090105070507030c0806070203121b2a01050912030604050a110a0f0f0c12030e01241d190515150c160b18040902220f15 55
    0x900141e50758090a20024558401d801010082000e80d1441c1800c40d680c01044440e05c0d01e80c540103a8403401400360ba050304980030300001c0c04a480f505810b0098000d1074080078684600d010661003100f80c0e25690064040c45c030200b01c440800300744030301c070752048600000d4401c526101005100d1031002a0a952007542c448000c50209030881e0f00c03c0303025040b4215419960641c1c414050a42c00f030f40e40c000b4012805480365900c041c4c1c000e142041c1541d50000c4034262240c0d184074294000e10305c20b040c2c002d10b990b83d1a070340c0f11500e46249071462041c00c80c4880c0308074286801c1e0701914045070081e4240d0f81940560a0045441c581e03800050110000074000c6100c0c1c0c3d82d04801f542a241000c2d409510a0020200701c1c0225203010041403400e410b84203841f4901590403600340414003505c07491440e41000c110ba9882100b5008050004500044c000b281110454000030f203003c1c0c2c4040d551008040156000400501510408000074180101803020741805444400c001540341f042025000c0c03e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 858315881 1250 858314631 858314647
    0x1030209030d1d040c110105010f030803040308100f08010b0909120712110a062307080106031a04110a02060f04020303040303030924050114030307150b030a120507021f0e06 76
    0x1000e5984104031004c0c0c400c201c102c05501004141c00440550008107519100010540c00c500e0703e21442600d80001d581d52035a140e59030111150b5500034a4014210410380000c110394001c6240b171030052a05a001003a14031141c0c0c00c0041c5a08043e111a829034002c216002c95041c1660590301c080d0782006500b0318220320b51000f515450f40340c104a690074000e0145000400586600201c9188840c43c20119aa00b00305020b084400742920050f0200e0300c084010818184203030420203107020030798007142048100381c02240c203650000102c8119203201169030000c1680c100087da0740008804031840c05030600f80c010035268450b502003e01050f0311b0340c8210080c0480041200b1946c04240a0844142000200c4d000103100038092520100203d403655105450004145c940168101140b02c20000090540b003005044a000443d054056038900d10b022503040d0443d00098823550301c4803541c5101520402c000e55003020000030420401c05540c02c2e003a42d004043d0808120300792540c2daa41d00721 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 858317131 1250 858315881 858315917
    0x50307050a0302070906170705121002040e190c080c030615070515090a08070210050708030907090e030a2a0f0809030c06041409060a080733020a170f2701030209030d 73
    0x113001e10780800c24000580001c220940c40619803042c4024001a260185223f00203400e80f20218800c0000030840d0000c291082d41e460020742d04540024100240c4445101c2210b035a03800481003079907240c1044151031500756404041c3c81d40000b039080a4031a07413155a654682074000c03800040c3c003ca4100b0130030822035001e18100c40c0a2030b00043c0480d1246001c8440740d03520308280c09890702d030504000c40921001000000e0700c240e05029210500c04044c00f034409100c08130518010010791110901b01c50100307084104440c0a24051940c1310742d242034800c140351a10a0034030306503000f12401c00040092445402e1643c4041808544a03044c546600000503030059541e0059070746801040400204803003d0740d00030740724000001000c8410000d82000207841006200040096044400c030100003950b000074800380da00d4011441401d004000c0480d65413034100603098100c1d21614440030041c44540b41c030900030300c00b007442c0c19403078400d030f5201083e00ca640520f80c0c401400310360031404c1850b880c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 858318381 1250 858317131 858317143
    0x114130908090d0807061401063903050a030509070f2114030408011406030c0904050a0803181c0f0e010c17040509160516050307050a030207090617070512 68
    0x70441d07101c0e5402c0d81400c030201d60217104202c44043c41c0c0b140174007150f012000031504070360040d00c1d880c011191403a0520311a042d00101014074421b10000c0180b06030b5000d0f21005102d010350303941d9450760030298001d001c80744040d010320003e52100a003000000038481a440a0710300c480c464410954407131034001205d64814a0080c04450600c0e1000000d58001014008541c61a4020701005488024107516410700303940168140c5c111080c00d55880c208040c0742500948a5400c540c02c62849880d1907a0b02e40040d20116080550700082072500402023110107420240c260350f40c80c07903002d0310601074184858010b080c801c1c024689050fa0040e8000c41e10700343c201d40c0000004149110300807110420360702ca13010b898800d5004101040d50243d400182c490136143d60384505d80ba183c640d07440b06064045040c41110313540310030409280010b1040c440c25081c64030035001401d03207030f04003201700c3c0030303078680382c2005614000004210300e00c800000f0b2280100c42c016140204059403403201d29007442 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 858319631 1250 858318381 858318397
    0xc080105044e1e05130905010308160201051605010903030b010e0d060506060d090c050a060f0c330c080a0e07150207030b07051312020f0909070f060302120114130908 73
    0x401c02090340f0300c400390800b0080820b1024003c103008450307100d00c807413800c4540c03c1c0009800340c030080c0b1038002160206060341c200715005061040c2040e402d140c44072001000c0801c11075459468070041c00405415011710580e501090800802111807440803903281c00c85118068641a151000300740d40703449001c1104c4410480d15030a1080e1603850030500748a0159125030b600950340e040000400c1c0b8402c4140741c00c1401e4541d14002c002500b5101c2c4104800400030006c9040034081e502d191039204090340b10212181c500002c101c1d00280500a00003050041c0710b581004d0520740d0000b907100b4081039a1b021340703d01b903031440300310598000201e25000217908010080b586440078020380d0380c2c1000c0503150440d0341040a00041c2c4d190016160701d02030300307c00203401400c16444005a40342003590650700c411503000f01c482180c2e46440c1116110469441540400e0780080c16000c01200d910895001d842c0e48010100442e8100c400300303000743c4004a0698009039a003c4a070f04200862044030019 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 858320881 1250 858319631 858319667
    0x106080d3b041e09030201090b010b03060a0303120f02042405030c121815161d0d02130204140a05040606050412080c1203070f170c070c080105044e 65
    0x41079140203402018507200c03d0f1190009d1b00d000064a508007800c4030f1246801400340210f0500c0e581c0d007507075541304100c001350b0056100c0004220480807440580020310003442c1104075842421a20084040403180e02c00401104101300140e095103c0708440a140c085854021142c2e60181244c16000310403110403030358000c030b034100e222641c0c070340704654000c07140d6842010b56105100800e448019a850440701d01480e06030803106c076071504505400060b4000750a0500e0300030080807020803a40300390800c0e00c1406001142841c40c0c1409082c41000d024190b900300115404c20300c1c003034414003e40c4101d040c0005c0310307240401002699026102e083d0b40304001c90380f0b2040d2000610415402c21148680013403280c0c80d101d108a4403401d100e070154202e6640020340d9868101c03100090340d100000c00e17140c051407420000f598010920481d445175016000142e6030780c00d14003007020500d5248010250b1015005028a5403482c1100d4425403080c902500e0030b601d10a281054410306101041c0c0e0401f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 858322131 1250 858320881 858320891
    0x80415050d11190215061c0f080408010608030708032e09050103140a1a060303041a040503011b02061f0909030216080f0a060e0106080d3b041e 63
    0x40340c0c0c00030300500403a10226000481d50719103803600300d070f8517076070949494842901800403035a1820020041e0000780003000440b5a01611522440d491039038402084506c080009070405c2206020310482d8081e0030710001031450320300c40da21031044900000c1d00154400300c0b0180d11820940d1007003100b00c10f0001c0030381107404440d030f2028a10b004210900c02640c2040200b8064010b1400126960400756440303032011a982d0303180c440e01460a03400428240d0148070402001c54004c5d02d2250450b10b9a0410b0b110a80e2581000300313140c01d5840040c2e14501003c0d0141824491540210380103501018460220311840e000f11944a0b0381600d070380c051502c01d482c10280c0c0d01807590102c2c4515800c442150010300c0d06540b0030300307140d0b180891407115490780c2045443c00001900c68120a488038002070003c24031070b48136402d05080c9007401c400c080106044602d1200b081c004040d64801141c079a1652030894200505880303201e900010806200d00d6031888403132003036520340480e8420300b10b00b0181008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 858323381 1250 858322131 858322151
    0x100302032a180105130e1906020d15031401020307021b04140906040201030605190501030b03010e0609030a080f01050112020a090308030709030213050411011206120f060513080415050d 81
    0x1400b44081c0101409456130641e41480051540114085021290f000300380084c44900700940d00c806541044425640030052208101805e0080c5895000811403901600f880c500c2c0146496958100c403e00e00d90061040054081e00403034810b0507191490000c8000d0400702002400030701007074820b4012520040240041580e0000300948600e1007038800b00912a00e03507042040114900c0c1040070320031541c900500072940300c1d404c502c03010140078001060419104e07220a042290450300b400b0141d00100300c2e0b241d090350241449800200d50941d8050313550521000070103100c5111541c122140c0c00084810b43c80d807040741020000c0d608405402c2c1caa04004500400c0211303148403c0e03206105802624190329150321695008036405000712091040c000010b4030392807145c40d8001e6100d5524280011425204d0110f001503e10680d008108007543e4500802121406813072407141010a00700b61000520120403242500c401d841c186540c140c90410444148c85500030602a582c10164441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 858324631 1250 858323381 858323419
    0xe0d20030c060a1b030614040f110304060504150204030f080318010c110d020705090114150f0a1e08010e150d080403030f0c17030403050c010507090509100302032a 72
    0x2070700c0d43d01c80c1820304c54041ea12180841c01e449060091010380e0701b040c1c010035241d203041c0d0310040201c0c01901002ca1000001c091000703840e0012181911480d4032002044208180b100707000c400c0601a400443c01c00b410341e21040c100e90028000184000000004103509054503200c0d000031210103070090000910800e0018000c126443c0c01550324482c40b08000c1c0394600105980c0150303000a090b840003603107000199007108400080380c9401a4131078044583e142c1120000b08118648031032116503030045010010300c80e08407441d5403688105d030b0421200c01c0da40d00501060450305452440c0200e9250035600750404110354408503409040c509110041003c014003500807030b0302030340394440c1000007100300b580c0001520600a0450161040c400012104400650381060007450814100741d242544642101e0003502d0f8180400c3c02d1003000c100d42c0c80e0002c40207074040c4074a090b41c024107245901180d5181300343c100c3c0c120710600300580488031650204004490380c40081c44400704151a6800c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 858325881 1250 858324631 858324641
    0x81b030403110f0307080d050c09030d2d0e010c03200a052103010b071b061809061208160f031101141302040213180c030e0d20030c060a 60
    0x6401d0038003d54a1140300008080b0544031005c0c0c00c0708615160080c1e0320612002400000c003442e150701410300ca940603a440410200d003c00340580c40e140c5a10a00c041c1203062072001c10524100303401d6103001d200d056540a00d10750400d10742820600e21100140c41c050300d4070144003050103543c01d40024412032041000500040c0717240180c0656a14000b800f113a403840c09603000103110102070820040250341d0410000b0982c050040302c0c5484400d42d60418902c0060300e80e80110001100e03160240242d90368188400001c02e8620020443d0034941100e882c2140003407c009050010b0103c3d000c081481300c1e0044050182e8081000079402086140c050004464450303007004542c038110080701503a85003600a03014038042c002000c1e01145d40e0307082101135440040a007541210b500d1001420341107030030a5041c0803000000114850343e00b00700080441d071181c003015041d54800300b00419100c2d00200c105403411490308102c802c1d1500c1600c003914610a40302000b0092040904005103040e2642c81 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 858327131 1250 858325881 858325907
    0x60906280e0405150d020112090510050103060c020a1218090c02061806040308010306091a090d020d0201060b07060518100c0806030c01080a0c110a050a03031805070303081b030403 79
    0x80043d40c40e030039585044544c002d51415000020b0582600141d802080c020920010076800072424038661b0b5640c034105104528242403031501e5000510030030a10b401a407401c0c0142e8030003485219403a81321242100403041240c01400310290481c2a10341148105c0c0000d08107140b01402411000e1074025035031201160388140b200213140003a41e03e6072010411600543d095a134014050b421519500010444031100b02c5100001040381801050b107500914410000240900032070000c0c040040e05010781080c0d01c20840e45840003e1103410541010b60759260b4000100043d5544c440c5894142d007111000a160640701d0501850036401e9070390012850b405060341c41401a071035030b2003030682c1e4040300002240440c880d0300c000b0b080c2d034245600554a41a480c9000d140d2507000c041c9480c14990208801e03100c98000030704a00c240350b014040d40d1003070000305602090b5408540c44150301d4066a00004040107110008124801d11589a000f41c03110790211840e624105803401501c44811070507 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 858328381 1250 858327131 858327139
    0x13030b1905060a0602030a050a0306030b1f090e1f0e070311031504050613051c0305010819020a0b0a09091a01031a0a05151306020706120902060906280e 67
    0x80040c1c0c19007032004803e07007154283c0e0029400d0a803840e4061320182c1104c1d021108043d80c1300000070104140244490080c855400e00c044001448580658000c0031078021800c0c15040181036841c101000031688001203401c00000100d841111002016002d51303003070314885110b410030110920036801200407000200300c0c100d83ea0400080d02d0700404050484002e0b00c603800001c006401c1481181e00140300f40e00c01c1c800d654081031507114810326400c03c0fa40d0680004d40d510014014040d0410080d28103041c40035002c02c9031080c6500050141c03186000c1c0d03000c80302004c66030380c0c602d60184566002802200005204000c42c02c80706d820380602200c255400030341050703c0c4061003180c0c41c100781d08500020b45000640c80c00c00081c0802c07204110200460004100306d262a40542c51702140054078143c1d01a01c1000c2c64604020000c2003c00c1009002924150301580141c0d1200101e40c50311108ed0b0f43c0729220710b140d036001825018080000712030b0104c0081142d90750b81e0700240040070200c0440d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 858329631 1250 858328381 858328391
    0x3051f03150905060907060219150b03010902090a1a03300f0301060c1b030c090e0c04020c070518070906030b01031805241003020d0206071e02310213030b19 69
    0x40c0b5608861a544400342501903400c0103052b0681d102d4005102c11b000140001c00c140d4000e90100b86421001c130f600050740b0384d039681c0c1c21250f520900d83c8041500741c101d000b0141c520001a01ea034540b054400c40348117000b10a01d0038032071640c42005440051303070002c001c16140e694910003d8804813129100302c4a05800341e4101d42190103420560301640d070050310401c06e540c00c01d2502d200400904030038007100e128803040300165035105d0000b4651040c6480103000118a05000e1004401088200042c4600710310308001c031003503200304044c0440b20240b82c0824030a41450060300241400d284038042c802e01e07100b54006111000583c509803049004524100b00d039500c81c0308005801c2034801d100001e148400c1000589010f0801075103060004084904c5e000007a41d03803d901d80d60f10f40604002d0612001140c0c19417074800e0243c04103000030950034500101c2c181503900c1c0b600e452034030401441d0b408100301c20002600302c2400040c541c400d0301d994081c10003401c3c0c2e90420141001a02c2c45c0d50030b00c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 858330881 1250 858329631 858329653
    0xa320106030c050c06310807020906030d080705160206070507030b010602030c0307140c2211090303030a0905030c0a05010203010e01081203010303030f0b060f070303051f031509050609070602 84
    0x3d03400b1100c0030070071640580b08545034000c0c945a580c0e422158014030038800200615110950b00c542c07000c05200350141c559a131510f1051042050b0f0040c46240700f9000b205e0204995900440f400c0d61002240c80c015a07a800104441c0c0e0584e2040000603410000200300b0900700f01c00050191b00340ca01031180d03810a6aa42c1c6400c0307a507803048008203542c0f03030410300c4000009060351030101141000c02d0166031a401848001c42c502c080b031880c100b002e00d501c0240807207544000c1c2c4103540e0004a4808103500e420099004a5524030000e001c060b1425621f10841d400c2c0881441034503004c89104041c0c92102c80c442c24807038003070340007030107171500e07000d09500009111440000c03900c290172541d150940c00d40e0703e59202640103051a10402040c2501c2c0c9034051481d54421000740219109140c2d426210a01c60900508842c8010300240390b40c0b1940c0130764501c3c00090480748017280c5e4445e11103e84003003810700d91405010300ca1401486403040340c00b0701c88480008144142941c0079a400c65000f00341e9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 858332131 1250 858330881 858330887
    0x2103040f081213110f010504090f020d0c2c09010e06012717060405061f03061d150103080f0d020d0e01140c0f0301061d151309020f030a320106030c 65
    0x9580c01755020070070400081100610582003846255049034006081441194050f03058a01008411b000914841b0000180081000c0303101c1074071819500700d800350b40c05203000c15031412042c0103901002c6040f03000103e0a03072181c14211410150103003404d005501b4002da100c0c2d900140d003d040c1811500c0b000341d50008000094451050703820000503c415200d08106030f11030400145d60400805e002200031011803981e024481d02d000900442d4030340012054041c1e8203100c120144032804002001c01000419a0351064a002700c0401035000e0307a849107084000002c0c400d07595400c4500c0d0034441c541c0748007081075000f02ca80c402c2d880341001c0990b55103880e90752544030305403800382d800d1402d000600c881807090202242c54038490010700d05554240000130200040ba610400c401000040c155000020001e140c3c0e00030300303490f0070544c00c8c40340d20007078203255000041c8030040c80350307541c04075034218035a207000300c14007107401c0f840000c1504a0242501c10b21600740111404a801d00740b1300444c0c1d502c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 858333381 1250 858332131 858332149
    0x40605060c1518150a06050d050703020f010e180103030e03160608060a08010906060f21020d0317010b181816021218032103040f08121311 61
    0xa48500038054101c0b140002e210b4101c4040c1c150200001600e02801c1041400c000c0b4400d0161201c882c0d58542c50104940f100740c520340d8010a01030402c11722902c000078000694007050341d50413940b1411040e65900101c81408209107500d90040040a452000030006810305060701e001350703505080140e08006066a1f0b01d0165680a000c4040c1002044484d210701c0c403058010000078a500c03102d0782d80301074483c203540080c5400d44620303039200b000300080845110048001c00584108141b14803081c00d400d1900800c00401900032100b1031001400c1510501880500500c080800c2020f03513158214640707250840d40c2c40c2108500807400c0082c0c286429000010b5411180707001100d2503403060b43c5806007160480000065100345910480d101d211003001c0e007141d1075942203401402800d00201844c2c40e81d0701590960060011404551a600c90000c4a5000d03404c4440030702075000607e4005002d11402c180415031494020a200c940d01c140c0c003544816502807044154a80219010400909 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 858334631 1250 858333381 858333397
    0x90f0b0f040206160303060e0c03101410080a0b030d12050a1811010201152709050c120304031a0711160501030902010905032415060f0d2904060506 65
    0x3c00d03c40320308100d149003000c01c121842807a010800da5640c1031045000c3c04191818030415602108102d004800919500001c081ea641c601c101d80074070b4008148240b1501e4801340811200100203420780b401500b10031440d4001408407940c404481a0003441c01d0509402d082c03107281404042600e00e0011300030440590950400c200e501c1c90349030344d907210f042500c0c002c040c155500d070b188442c2c800c200c0015441c0206645110181b805c800e08400c0e8400c40001610320f80501c0c07a0803405008200b00043c034803030b40c09055800b12001c003040c055851460195600083c15500e02880200400c06081c084034003500541e16402d1024059841281d11900800d103640303800004c03000f08204940c46030708101c500724018141002869100c1000ca8100708168501149180c4041344c01007141d442d42c484141d0000104250300c111520540000b0910700c2101c54600308a80041028418108654403401c0f9201000403521134549490401e10000030b5800c4050344203914000000840703040003006c41d0104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 858335881 1250 858334631 858334639
    0x706020d1209031d030c0d0c0501020f06040f0b090307080a05040f1215151e030b06010c171e0d1e0b0604030611070506040503130914062101090f0b0f0402 68
    0x2c0000f2032244d00109134911220760307141c0b040100d400780070f4036040110111503002d081a41d030f0650030580007a203410315199440429510110400000c5441c2d04000d98080d0703442902044951541200d003403960142d100050405080042c6c030502664001c0001c000322040912011150b640c2d41e01507a20b00410f04102501d401040c200500d00d558080d40030400d005c4401e015421142c7d00c03413484031800703c00300c46120036511003500c00b4401d014144c03003010b6214509103814980c125103a80c450307141c0300700c00f030312a061440080f8109000100c100000030325002c0c0c24060b56110541440c01c28040c00d0340c0c0d400360415050200d0b0b000300c1c050140c002c4078170814001c0c000c980f606246a40d6107008100c9103105141d0840c0610040c0c1c00990144883c0d07003da03019500840d100c0c190885a0b021001840e40200c2c0c6e90380c6081c580108003554204d000d0b178048812642e81c03a42c6a218100c029070820240d600c1920341d4039200402c0c2c00c00c400c80000c0c01100307004d03424683d15507949800d0202515010b80380a540 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 858337131 1250 858335881 858335897
    0x105091b0d0204052115271b04020f040e04050307141b120c01080a180b04060608070f0b0702010e09070f090b04080604150f021209010b03060105150a0c02030706020d120903 76
    0x15505403104540d04482d0840f04e80607503880c40c07050014503024030302402004d500001c6008e030701ca00d4a16890101c40c00211801c6203003031142e111074445407090740b161080f0410b032070b0005400e220003481680c52294110b000d80e9079160201d5000c645486a11a1065041d111180300035942d0505c00b001c41c02200d071900007484a00201401966640d03401045110b00903160700560f4408400c0400c00b80c4010701c0790800c04400d080510f0202d05480e560782061050f40d01011040080c4150441d05500710345244010701d43e60309150004031400c09900305600c0c0c200861340140040c10f607110741d0104054045907101e0300c0781a100c4050040c540324502c036403c15680b00e0030208001c41c2c445030b001480c1c407103680000103401d4800d12254090741c0110681c04104200f660411400080a010b510707190b10301240030342083d43c10100010103101024046861280c00403888100c0580120706040801780c004003260041591804c00075034620316015803100180341d03288141c002082d1806400402503140d218207070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 858338381 1250 858337131 858337153
    0x130b0105010c0f020d0503121b04030609020409050d120e0a0b01151106090303010501110c220f02190e090f0408070c05060a03060f0b0708030105091b0d02040521 71
    0x68074074449003083c3c81c424404011000140ea4075092880074910a602554917a08d1021504104040c010310b01c0040d510b441d0f017a98108018041201c0c1529804040095502520b0012600400641e103008100c5d00c00c81c1422189075030003154000400071018000e110084858480e192540c2e1001390080c85d0030702e0750f801400b650f520085081044112882e01ca4032908240a2861130200f0a842d64005038100100501c00c5503409042601c044044100802c001d000d00400300d00d01d110842d074844410480c0104610300d40d031190308010948100c9100942d10b60281c80300c2045100360000b80f950200d541890140c2040c102146118403440c80d8001c10b601035034854540d0081640000821140148284404180741d40c80c00b0203002c00c29415600040c109007488107100030300741c02e60401500c040050010710700003820711007180c0c10b540080e940356926449070144020a803a08021601c0700b002d0210f100035282d07485038040c00480d1801c0310180080000080562800080621905150b03081008102 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 858339631 1250 858338381 858338387
    0x90b10030c0b0306060c0d080105011b1e02060409060303020c0405130b070e0a121104050114030a0305130e1f12120305072120040522020f03041109130b010501 70
    0x554800800303000d2510b800010311707016081c500220483d4000c45c0c3c0a000621003540d1001c1d022101d400b29903500c10168080c0d03106e040314155580348821370002c84560034030031900c40c207040d507000307001c8617100740300b40b540b00d14019440307080c45aa1140900c3c945030002e904803028141005005030001c04180d141d484050341156510000e02801d50440c8002c01c0024007203800b680d42c1100540143ca04030100c2251a0420003540c0e810b0340f1003482d05420700f1300c96099a40c04201c1e44149549420550740d2180340c0c85900001c1c1400783e228480083c1d1080810261001100da804c6904080f0030072880710781c5d1101c1040710b992040303007006041c4107600518084098000e601c25074000c2040d040c41024420450800306068541496071100070761514028000b0003905444200403250f04624a4141428000443c030140a690030420426481c0521401c2104481e4102d446400c8005e001c9503407880c280c2040410941c4503145a40607500c04000110a02e82000c01011610303405070b40c141c1305900c1d01d4011 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 858340881 1250 858339631 858339637
    0x30e071514040510050a020615150915040605041e0b0f03180a03120605010e091b190e0f010c0f06050601020f0115080d0c030906140d0f090b10030c0b 66
    0x10403141c4400b0031022070541d540d400da151513040107540c0c0680d6440c020314002c1c00d02c01c01420010410405060103290b5607034074800126444d0144240030317101c0514a000824101c040d540700e007500340c40000c000c181254024020819035140c0c1036070041e08140c0340700b00c1000c1c0a50344500d9400349401d06c070610309511150011074000802d44580803403490491552030826030300823803c601003a800040d842e200c40180c02000001c000c242048000c103201c00c404141c00080c001c0103030008201c000c8010314440b072074a06652032940c0501c000604040700020241c0420511010075104800b074814650342c542c456250055400d51161007840b0b01039140c0d0b04c604c094400501001c0c1907002e840c17103c540e001d07424401c1d80100600d4a10682903070f072500c0c12032410903407104d58640401c85542c188001190300141000c040b210b071454900100104841c0c1c1c5501d41c0501c075814400d550a02c5c820082d0103080f40c200303004083c01004e00f42034030703150b1218441611510707200040800e8210369003045084038540103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 858342131 1250 858340881 858340907
    0x609081902040f1422020303041716060c0b0a06080a0f0c150503150102010e1513021f0e030f190501020405040213140303090a21080316030e0715 64
    0x3043c6031014129140559000000801d040714000c3c00701706002100304810b440b010400203415088181a03004241c4a1040f40580c0000341c01c289510145160100200344005511b107040341c0c1c0741d5440c0d00000300b01048055065600c80c0c01d01c4041010305043e071180a003120815002465842150380cad41e8400144451800e903000100c81c000040c03207444c0c100d507045003090242e5446560f490300813814078200940440880c116031501141c20143c242c0004d5120381301c00f242c0d0300c14455070f6a0110a14018060010082d0401d14500501000ca401d5500c0284181030a85031411030010500a250361924410800030b40c6601c0302d807002041c4102481d500c42c006018a0015260540311004a4141c0c0d01c00c0013450f4012151010401440c2c00c5136100a00c0385104501840c9405181d800051075100d1602960110136001d091142c190150040c0110320309600031745403922131900d943c9201580b08035448100120f4244080c02018201c0428020300350351810301140412000950215500c404c5490 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 858343381 1250 858342131 858342139
    0x714030d0e30010603050f030f1e04030512030402240a051c061403060c040b040e1e18010605010509100806061c02091c110909150109150609081902 65
    0x150201540e01e03540802c40000100c81c008240586140b60003813605e0000c07030041200307400900c1b9014500c520703181141d0340c1c80801203030b400980050542200ba94441c0350b00c002c0c000c0c4252100c4104890304000a90f00c182c4c0200c07118070030344c0306142c1814241c591140015404c6802040202803440c0103201401c0b03880700c8490700d04020600040450200c8660350070503e01c0f940910b901034014901000410b42c46411030b00c0d0700f401c01d0310380066213241d0300503805003142107240040056418a40ca0b00310706000320700c04482c1c11560611045d10301504482036141010b9500381900441c180d40503004480000f074000c1d00c07490030906481c41c2200c1074031003c0e0000c1c0c1c0c07043c010020030b45064640c07038204159503008900103035200b41c8801001103450700c03d80d005000171200c0c2080008907843c03d141e07003e001c806070385002d0150346140c860360030055041220501000c500c00040b44180c820391004081007818140c4c05043e940b2020309940d41140c900c42c409466100c65111400607113640440c0040c40e01c058 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 858344631 1250 858343381 858343429
    0x3110c0d3504031b1410121805010b06040b03060609040e030301060909051008150a020906120114010e030613030e0618040b0609010c062304050714030d0e 68
    0x71900501e0820303a021201025802040600a0080710030035038a69102080007004190314200856030f0002042074100e20404031003140d080840d000d4030041903000030070001000b880700341262503022044841d509a40b15880e2209680d440d0400d0812582034401e0700700102e0031640d45c0c004101803a44642800c5401c5919842d081c800c00000f08041e502030000d03a00e510b8100c1d402c0407204811298010308001440320425410004440081011056883c6201201c407181c3e507046100300c003910039014801d030090400203500070303080c0222021506030f44800c074034501013201c07010044404103040b08140f0b80c1a0440800b05100c1d00b010204014824441d00303214000c19907040014455401c1085001c00302480e01c058601035140c02d1240e614080390844040b402e004101c4002481690320403030060500d5582d801c4080c2610314421031640c4c00c400301400c1e450b50707d0b062030041d89034900c9110740146082440e44101452401040419064141d50381c0c0154a10301759007001410340d094030305950f00c44141 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 858345881 1250 858344631 858344693
    0x1110d051506071a07030b0d0201051b1e010501080a0b060d0302010b1005031608071e0c05010603080c070e062b020306090714030703150b060d05100303110c0d 70
    0x1400151030024014003c50164600000104c00310460040640c4c04062030700304620019602c110a01c1c20f010b130280f0b48652601d440b06082000041901440074040c49031101c0d401948036185441c41070a01881c0003030065980e90403040b582d555021030010034010428002a03242d0920b05990246039002c0e02c0081500ca80c550702040d9101800f1110500040f4004200110001c2a002207602540b0034030340350810b460903403c01084518001120074048030340200401b1454440d01d600b40c25070360410000c0080aa4926007012316510480515002e402280c0000a4428841c1b0041d4801c01001c1c02058005211600e02d454200308103c0c201403032244440041c015840410019100e00340300001410f0050402482c48074440144050714480da011440c1440011490060005543c082240224441c9807844c00a00780d80150300c10000c6070b030310749002c110b811801e5113018000c0340d0080e110700709121190f1600365128920380350000c0c1c000d4420081080002c0d0b00028514400c04092100b00e080a40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 858347131 1250 858345881 858345889
    0x40c020129190b090411180934080127020f07061b02010605031603020f0102240f0c090f09040602091e04110a0c0b0901021209030a09050301110d0515 66
    0xc0f40c016066800d000b040120083c01c191245c61080d5103000f11032410004401401c07100307030340a0b0f40054040c18802010070f0a02c01c41003105d0654941e4402040c1a645003ca114242d84604482100006004500000e1034160f00c1400c0030106802203456281078081d41d440c440654042c104c02840407a040000401143c103600c1030464048441e0003043c10b650082c1c40090030754296820252007a081250350000b0420809000c6049a074140c884002c140300410060b428038044211394001303408205205042408880710a81c4100300305c2d42c203c80541c0b0780c0c11100c05c450041408543d000421020705285a02d0505402603209121f0705000d0b1400c5250400300c0c42e081c0b0341801401100c0030302c0840300040d03d400d000362041400400000c906001340d81100504000390102c0142502d00c005010592481c800c0d0110b4002c001036185c41c0895041145d2070654a07844003980c8000250722980105007441e040c0624019020fa851416040a0542280900404025210244090070300e0800c07030032522 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 858348381 1250 858347131 858347179
    0x1413260313020906151b0109080a050304053c0106031202030a0905120a02060304030c0813060e0433030c03030206070915121e1a040c020129 62
    0x198404403485100142d01c14425407820281071144110010154100d0108840c0b05840f4103d031440da0940e1288100031981d8010607240310f0103000150001150741d03d80350011b0055018030304c84c1013100d8410f030050001d200080c2c0321600c540c0705d8803a007080d0760002000303014001c21980d1010000054a5a0365580d640d8050364501406025800106505035182e4001e1144070040c035003502c10003440c5c2003840d100e0380c5803004800c000784641004004981418424401564525800032280d0343d03c0607040d0031410000704c10322486d80000e2501d91038400300d0804d400b68100340d10007001500091020000214046c80c14614280c1c2098040d00001021a200040c1c0d40011406600501801d080c4068014201c03480d81d007040030a5003c0d1a0a071900603032100d0311807800030b9007010018030840c03002c10f881c1c001e0b61400c14800342c9070b080501070b05008a2294021b090700f5012507040080300ca20030016400c1e0b400000011810b8a14003001007902a00c0b11402039510030024881094806d20819442042d2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 858349631 1250 858348381 858348391
    0x1302040e0a050618090105340507030c0b041a01050612041205070c090506030f0703050a021e060a02010506030607030e0a0b070306080708030a020d1d120c0a031514132603 75
    0x1030b4480041c000d0003034829000ca40c0c00500d0400070001c500c403c49032042d507544082381640c1040300000d00202414401e20030305103443e9000b40c04000c5410942441c0340741819600e0b13249804c085160000a0740e00e050402c4841d2115800300c5a2081d0741e0303d44072441e00c1d43d06290f1751001e103d410800ba2001501610441c0083d11507114001407a003000c0044c54035020707031202c604e04950b01824050000c6407002a0141040344e040310040401c507032155079900c000c400c410303c040e00301c1c1020800182c07160701074021a108180550444400c1c1c0d9a60740e04030107130b42d06208060403176001440340c0008103070210312231a8010034600700400e4850386c9403032903490014035030300000580d00007141415906505011003011400c00703243c00b40508031b00c00c504d049a000b00300406881070400307104040341d00e88180003040140e04002d0210303802551382e0178458440604d140c0c100c0d01e11b40ca0700e4100680780f40c1044000d07001e54801003007030744d0b010b000e5a1a2031014003074000003820390903410403400c0d2500c800d0006512079 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 858350881 1250 858349631 858349633
    0xb032401060903050709020307180605070308060105040f03030309050312160816093302071a0708070b1905010303170a050f0c0706020f070804051302040e0a05061809 73
    0x401440545501486040e04000e080201140e001c1011920008102e016180c088100590300d841d00e15098400303089110b07040346400c4400d000004c545800c10050304480b40a40c446402c0c0307945140045415114502850f014901203040520100744258483d1140c144a80c0071a807074540004c000140344841103c400c035513501400e0b844c10030300b607100c07031030b82c1d0440704d12034241c0c181d41c0b084840a0070502050140da803620380c480802010180c401c100da001e1003491002c0702c400c54140000025114201409042421680c5c1d04d0340880c0380901c20f086503c1c45800c000c03203909000d0715a903040e09821010307008000c20030a500b090402403415204860085110303403610348a250000e48104a0440d00a0610048629090030010080c1d04070480d079030f011902c406495034942031480e2010003402200860081400041401c400f0442c0c2c60001300141c0f1390450301c0174039060144281034160b2103240034010310803030725a0202e4080a11608810b800100003004005155902e02d10984000404c071408082 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 858352131 1250 858350881 858350923
    0x31509271905031b060705030f07121b03150509060607031e0f030f02090a1a0403152c0d031a04092f090103080304030905060406030608061608190b03 66
    0x20359000b600134401c080600f0014000c2450000000707800c1f404010000052a0b84c0c1c9800103490501c1030714036890248140804200e80c030700091100f45c03482100e4007040082480c100c849000101c00302102d00880300001c20701c1c50302d5546c100500082e40c004000450602140390600d030450a00e050001c0300c0030380c0701e50303801d2604101407400605440c141d50340365081610421403000c664880e50500c034261118041004008001a0010340c1c5601c11f50340041d1403d41000b9281020a82d60740110607401c181c0d0020113080055034404004c0d072030215a003104241d006070040700d1101e0098102500c00009441d02070440b0080001140584404800444810300c0035484d0300c0181c0d0f02c4076450340d03100e045810360060b0a409040072603018030043c00054100c08001c0001400c04d4032070741c03511001e4103010301016201c0c1d0380d580010340542581e001d600b4050007408002100701e400200c1c01805104117644801d0b00d903c60502d0114880c030300341e400d1840261031340c3c4188141c3e1020003401d03032130b060020b5007441 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 858353381 1250 858352131 858352147
    0x40305150109020705032d0a03050103111009180605180604050c0310061d12160e100302060d091205090f042d06080d030203150927190503 61
    0x40a040503080406420f106201e1400416400810f481e4808481e5200c02c2e2054040c250f41610711003155104003100c580080c0380301c2c60030303859040a4100c0f4030901c2c00c081129012420004000d103107010010004e502e4010822140500080c400080f0b941d0000014600b80c4940200715624201030b20041041c120809010325800c103881202c0d8001000380719030b411400c0030310054852000520583d01027141d90700f4106601c0f040c06821000d441c80040c400941102c1c070498498aa1408403000100e0f050002000150702d9450180320740b01d548d07500c81c2c1070200c508507401c12185400041440100541d40c103020700c005041c2e41000321110700316488541d11184003004112411f0750420032036005508000700d4900c461894580000c0c0c0c8020201d24002c41d498005203000288655800545c4a03c90750445c16030058065004601801c42c084503a48044030140074001100010344611450700114620341c00d01c001f0742860791105003500000e4405d1041e1141801c904214503a03003d86080c0c01c0064160 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 858354631 1250 858353381 858353413
    0x41407061119020f0607021815120102031509040813230607050703030c142415010c2a030818011701090203130b0702100b0d05061902040308040305 65
    0x41d10740d900c1c0e588402c200180310b074003150791040200c180c0c5001d14000b00c6c54408658803103105290004409100183c103140c01c080c408c0c020700d03d260f40390707004403080c3e00950626138040c000c40c1d214907910782100c4418104d840900805d4000200203031a910000d002c0d0211405800280c000241a4419072442844103108441620040c91000e64460401005544000380001c2411800c480c0c042c100506c901c25a800d000212250724000c1d40840d000c0d2002c100f0700b0380340002e6120082d0550407041201e650300e4548422400000c2c0e52803c0c082240070070b21070006802c0c05800c21102d680c140d203031603105580510b0012040c10ba9041102d0580b8003040d003d1140d2824141c0b84144082442e251122040c640301000291006003e8030450b0782c0c001000440c1c00101e08500e2015035440480e410562806180007074480d0300f41e40f06d2a2800341447ea500070031386001c1c12100c1c41c07075070841c001d00b41684880011909242600721844800c81e0203100000c0403d00d04000b400042d4002e002801704000c441602c6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 858355881 1250 858354631 858354643
    0x3080601020c06120a05040c030209040c0f090e15060105090a0b042c04080f13060c151e05130203060405340312170108010c080c120f0414070611 64
    0x200c1d000f00d50a1241001050310404980d4116030316074800174180d1207034201414032101075080070b50082301c0b0500703000410800b074500008545116100303401c0c407600e1301c0b034140c02c2d00e0311003024208a034054541c07100c0c2c2c2c800b070100c1a0b030030810504110389010b036841d010914800c9142c0c000c1c00b041e080424104484001c040700024080000c660348564007581d0b03004000310040190006e849a40045044820045000110781c10000c501c5928149295100b100404400c03c5140071140400204010021202d160064220481c8541d44c0d01c40c0d2030100340080b00c002c0c2402040c0310f001c0c01e000407800001d80c030244038603800b031030090004e0308550010b20400300061000d04c00704150080c4a101420030b040c00450039030184e9034072a4010b0b240c4c0b14140300c01c80f9406c0140c2158130301d00c60400b00014034200154012004201180c1710032a4985d071344c0d02e01c030000303015521000902d1011000000e00111028840e142c1c0301c0d1240030403013941722110301240e2130314000e900004085070b205180f07201c280d0740030014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 858357131 1250 858355881 858355903
    0x60b0d0b0301180b13060f050402030c0a0e06060f1e0c0706020703170c010e061513111210090f05011a0702151c021c0b0a0b12220308060102 62
    0x203120200401603e4025502d02c94005002200c0131000314910a0a29000038061034100c0d505100034080f00d000b01d0003d14003034034224400e01c02d5039a2001c1c17030b08000d0452800c803584581400419a1400c041c0b1046501612450b444658100070f17218989060b00400036011401154040e02d030b245081c07140d440e01001e508030805551100f80304100042d080d903000404150403d01c07113911002c1c004030382405041040300b1946c1318000d801c1081592105900030703d10000c1c044440d05030805000c07001e0310440d880d08072a0386100c4000c00607191800c1242c0451904009240103155080356070740040d00854100302c10342d4071900e407110010401484400103a4012401d444810703450100554002900c0d044a0301980103d403001103410f003d02c00d84134115403068402c80f0320135585c6544403140104500c1d941c600c03282c1c40c5440c00d0740c42071090415400c400180c3d52216441413034810a210000b0800000400780940e034400e14000e400c01640c0c07210501c0300349100303856407950360528400290510840303e030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 858358381 1250 858357131 858357133
    0x6060e0909060a150e3d12020f1302030402091b3403050403050d0806030a0f0f02120a210509040b0a051002030309010b06040b071b050301060b0d0b03 66
    0x207100d1810008144690055084900040c07400803105480c03840501590001018441040c00c203d0715044415440c4103000451680754502e110070315501c0e2064102004840034200c4c0c0d590305000480313000510103086c0e40020560200007414100050031403441074240c0c407000360084184011800c008219a4104040d50903400e00c40e0007600110039a07015202202d810300c5c40b00100311000c1c840d011324911581390110000440f8600506014080d0b81c01440225024031810880100491192200500400009000c1c218000c119140c01400f807a0503501075910301000712552005039694410381d90716108200140c1021229800c06c414031310f49a46000c41c10424880c8403199141d8010110f516801044500050031441c81d00410070b07070407954200d2500162440080241030740c001000c1c5100d500d100009010100100040c480d841c0603034454200840300a100b90340c00900b9010340c00012080d07208440082c40d69400000342034401d00d0707000003030400d40010040c107103030f029014041d03809505038 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 858359631 1250 858358381 858358399
    0xc1e080d050d05040c0807080309030f01090201050a1107050409030e09060f01120c090506030906010317070b0c0c01020d1b12090c060e061603021c2309030f070906060e 74
    0x10181452103120060b4400301d50b110005810090401d101c00302601030742e02287c02d1182c841d46010b42d00e500c00b0000030b21903c507281c0b501e20303c1c140500480d003071943d042e9902030070004181003d41c1c0300044010310f80014082d160003c90345483e14410400c0c0b4501940e24035500400f050180500d4001c050040c2d8040c3d0301741c800c05a12660002500c02d070000f03200600007014540564121440e00240d0800f51740128008144582c011000032820305a0b03003d00c000d4904180c10800f074155920444900810b42203801e000135071010801405407448114142c005880c001d603005400003101c2003219403101d01803e001c82007043c5a400048501c540c801204100940c581644542c0c42d031080340e09c035039410000010308948039500c81c2e40641d03200242c0c1c4c1140700040c848529000e5200e840303a031489031103418031a030f41411030317842400d000c3c41d070009040f00c0c1160311240f4000703030110348c1c4900c140d070f40c041c40340d61006c480d105000c02c040d9005100d41c15000a8140c00d00a0080441a80c4503100307214407540 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 858360881 1250 858359631 858359653
    0x70e0a0507201504060501090b0307030f080d091401150f120803091e0601050f010c0305090409030908030a1107120201171b04031203050a2d06030c1e08 67
    0x340d20740d100110014010b404401c01d40000c40d15141004000d0320790448480d00713000400c030954210605031903606506100d1088003805040d51109284406002c1c03070fa1401844001c0b8601e20010b0000c0c000d40040454461499205c403540c42c058060301040030380d542d548241072203d181b0b80d40d4000d45601c219072503078545407036502c0c0f4600c0e4a8400240150700300102081c100042001036801203076018200703070860b148021009854901c00d104250061228003407100103503124544600c070042c1d042e2a820305146520007403000419040004900788218820081008001000980750850180c0d40b40d6540c40301c40c906040c200140395100001d000381c0ca00c19080180e801440d03880c900261510202025030b2220b0284402e80504455012584400070b4044188011414985102d41194805000340d0312004d40c8102241c091181014100341e8070141944039100c0524800c0301040c6404010074480d840c0c0d10784844415803903104400310fa0581201d100050046280c41c8020401d00010b40500c4203e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 858362131 1250 858360881 858360887
    0x2030c012a14160813050603011805090f03160201260c0c0c1008041a060f010f0201110c070e091515060c0a2f0a150903050f070e0a0507 60
    0x155440101030110b02c070340410121844900352003418820030640001404281008105a0322a103143da01265502d4800b048504118085a0407074821800008014810b40035a07001810013512040c0c0d14010910080d1764145d00b0005002021000c82000303541d0811031001510b030f80281e40400305e42031030480c0c401e41100d448074076007070380601051403055a444412107114184028014541e42c040710602040d100c20340d00044051040e842200007030b01c03101a510040c802030744211246a4020348105280405510400410005440034000842c010360180700844242d041301d008100140c0c0840070810404c1c251902041e0000c01c10710103030204c0309030866904c0d45850010043c81e0a441480403c5000342c8801c800c031a2001c4c0c9a0301952110441e40c5800420030525240400d810b035826000700f48044903840f25295004d4006105080991070012004000035440c3c106038284101400c2c0000884c00900855510410040140c5446070030011400254500600019001d40ca858104441c980e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 858363381 1250 858362131 858362201
    0xc0a0609053a1a07020303040605280b010e0a08010b010314040b011a09121506040c1e05070f050606100804021c080c01020c031812151902070302030c01 67
    0x40b030819800c0c038242041c00c024900c1201041d003018014030729070800c03140701c1e800b04c09140940d2040c40140040e485030a000300c82030a4071202c0c091020b00d404096903825080d036000c0941c0790f07818107100c4840305907400090b84032806580a181c060b512074203441c04c507690600c18403103840152000700d805820582c5503034800310b205010b40740d401942c3d441a0814045040d0980700b01d4040200040101c1403021102e40c1c9074000c403c0013030554040d05002c40c000345000d00600b40d030884d8540d95621080520301c030f80a940c4d0200d01415061017002c10403c0e000c00c15202c0300c013010324080c600800712820b00b4800e001404d00c140c400e004c204804102480016929000240845020281e0490540d405030030a614640705d200c0c5600115032001030200c8c0342500c04030180080400c0d119401c840d9100a00a0240c49030b50031800c505d50381c010200241a804c40d28210075041000760301c484c203041162030200b000300c2c1d00c000f0302a400359001007000d0b466a142409520440404040032440d858000340031991250 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 858364631 1250 858363381 858363469
    0x1f18061a09190b040603021003200313060b1318030806010503010f030308041b1202030709020c120c120f18031b010e03010b0a03081207050313030c02030c0a060905 72
    0x640307411400f0a66550382d08403a01a5800030180d0b20003452001002d03006100904180d4503c0d0b0161003203450203204c07a01680c0c4940110003071207866080582d43e010062800d500751940c84107100c140c0d046210a14410701c0c000711321820540ca5036221780d003006054024000c1a060400000300018010394032402c0408080b00e903d030802207240d403100e2138084291110611110729a000840300055000e004581a468040c000e505861407a61101d071342d00180d110f03101268003150301002030b102465403a003004044400305d117800c0e104850308031000c003000b503401a000c1001c0c00102144054045100004401c000081240101001c2d84074041c4105525000740e080e50502140c0340b14121591000c2d00080b010380001401443c0c0c2c01d03101d03e0091641c2d001109d032116400341c00d60002c2c030b50501070802c4a00540360710b80f402c900520181d604450f4003003009022a09070203201c111094944685810001800c156260703070300c000c1d01305014888002e01c3c5c0d1500142e44908034400321012500304405c00031003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 858365881 1250 858364631 858364681
    0x70e1308070b1315021305121b0a030602030702010f060510020a03053702250e07090e070806100c0c0b0306060910081510021f18061a09 60
    0x582c1d521540203c2034402c100c40600b01a61440c044907445071a603006020405202244d11412500d407410722584e48010005034040340d2040410181c8150340c41000c15100030020586012141c0f41d542c4c00041ea081610040c0c00750391030300c100500703802d214000c1e500901010703100741041518070b19009641c3c505400001d01803003000600380d081c208000bc0d00c40b803144c07002412a4844109008502d40800d80704801d00014010382200c0f182402041948152642c2001d00000005052100107103080c1c00103880e010902103c0c401c005080b44401d00094801c034007549034270072103240c0041030004000e052001c01042001c42008000014900003041040d41c402e15040d40e05c0c0d58920b00891414468000280d80c46004482d1951090b5805004144030328645400b0b011100c18400510581c80c10422455000d80c01103070700070007407007048101d41054010441021541c0002c2e0000304a40c02030540c005d0340c010303440e10f00c103007245845c005003461390030f4054612800c3c52a01c0c500028523152408203074000c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 858367131 1250 858365881 858365903
    0x5031801030b060f130e090a080319090b040c0801150b0904020403052d01060f060c0302010f0c2007082806050a1a09040b06040b011709070e130807 65
    0x2a40c0d110780c0c0032201c465005000b0395656a00340c48404440d400540007140300262800f0007054000800d0a10b50180803000001e000e40e20742039540c0341031504001e02d000d40b80140c0c0d0700070380000398881c01038042c5103024002900481c282405c00d4070341044076400c096550f07810011494600b041c80c1c03d09100b2039584040c5182c40c0c0b0311700030024020744620343c0003a100d0702c2510541064a001141100e00716500c2c950130503000f5008a00180c00d8580b948940718183c128148100b09082c00f41703101400da94460300c000a10381e540074242c982225603c420700d0001030640c81d400c3c50200e41500c90b214645141da8024414030b490410a15907070011001010807044c0d800c80403500c1e00100105078051198841b02c00e00451801446c040028045152010446001b0310000c0b0864103181d65114002c82e088084050325688220602c00a44140720120781000000e540310340d00c689031031400d40e00070300c42c14002e40755143c5000c80560f0403100c0503054210304400d00074103000040d8054226443d0701d80c045c4244030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 858368381 1250 858367131 858367177
    0x1a0109090c0c05060708010e1005090112030c0f111305150609060c0f010b2b0b1003080d020c0607210c05040e090d08090114011206022a06130503 64
    0x5a107000380c00000e00c0380c0b14800074440101c6e0400c40003416070b2017a003140105030f0f449400500c50517105109041e00a0785110060112100150404003428000c3c00c0401c0c0c115104c0d80d030401800107a000550744078568030380d000403516203a0040849001454002c1c0040d0600f41c01080c0343ca095400c1c40d1f4030803040007441d0001d0f601e07144203072030001c50b00d20141c0e0204244094540d0107000d61003d46403054402519240e1500f40c040e45261411010007010725180c0d0a40e920000c40c5480908100e04042e8295400000030f0407520050402c040d1450004d41c0300d1242c0c0e40100e26144016011074288110007610000514800b0014060f18407014004210103121100560b61403103160004100300d03001ca010000301e40d07400515000f001d581e6641e0300941c5d07521101030302d00326203d28620f03102ca01020001004440b03840400000114050341c1300510340351125040106070304607122102d058505050200c100000c00380030465001066104481d070100742607807025100e1040c10f0030350b048030f0945000a0f03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 858369631 1250 858368381 858368387
    0x15030f010b01120b092e092a02030909040606050d030201090c0b0705061909060c021606020f031e162003031603030c0e030d11070503030708160614040c08011a0109090c 74
    0x98182d8014000d6894161a007d0200252400202c1165503810f008001e4685075200b1320210f000303200c03641c00b039420031101c00200319982c40090003e40d401c50f00e5040202d002d5803085010b081842c4641c000180c020020315040c040d00d0120340c48503070f060b501171040002042c00854032035404101d00303c000c0b0b05c42241c03100c2d00c0c005103000c0c0800740c4050301d440c5100917140d400144005040340c0002410b940280c0d603103012661388251052000c01741d00140909142d03000e940200c172412211128200d0b04203072000c03c1d0f0300e01d5000c1034142907a140c9060940310007000c0b0038941008903d5001e070041c600c1d241120701010401490b040005042580d222003000c505032188183d140c1c201c1005041d82c2000c20b140038010150302207180441a00c0c0901c4000241606e40001250a0142e004041d14100314800b02440d8140203181c50503100c0584441150940304e0580c003506100e84d1048203049606070410742e1036402c4894041d2000d095066558a9100a0ba0842400c038200c41c5400d5000c03580c80c022040c00c13 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 858370881 1250 858369631 858369691
    0xb120601060203521505010e10060f0e01030e0d080601170c090f0d150b030d03141314070803040303030e0d0806090903120f0f060a03030804030815030f010b01120b09 73
    0x6481300f0405c5c40c000041c90002c2d00320604035081c41031b41c032100751510074459201c091a44200000b158240217206881070282d884514810014140001c03144c4020300e0b41c9091241042042d0006100c0804010f00c640e00705006001458228021040b00d180c00c20f8010585e20400c0b20040c440e41401500c202d140d692204040c0d00d0781e5100311540d200d1041500e2030409455aa100c0c80e22034060070700001903503446031107032802000020299458070346441240405e40380d034142c400d592150b5000400e42c0d14140800c807030380003007003408015036513a0300d941801011200700700100c401d560094002c1c4010603a220161a41015080f2100c10460300ca0300315240c690b204015a500e210342c01c040800c00e21b02560400a4460089010702a840d551400d0810100031203a0000502140b00c103000b240c0468400d45a655100710391302100f040c504000e500092400c804d440380c4010a030b440d40300210311540d11039504c0075000da14480901000b4041000070f0320507040100026141c14142c250300117000401004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 858372131 1250 858370881 858370883
    0x1a280e030a09050f1002070e06030f0a03091e180c111b030d0c0302100b030c090c1b0606030c0f1c05070f0605090d03030b12060106020352 61
    0x4899585449a0010385000c100d032059a10a00740a07048003814140640185c21411459014080c202c0c01c146d406078a22a000d440d00b90180b050720950b00000c2000c100100f0514080d85802011034a020100c620140551082000100485408001c0f2040c003030315128480b00d01100210741c90349854070885180c0c1650b0300e103072194854180300100907040884031103c041015800e540010000c1d1800340c0303800020400090050b0f0040300d40d200c102a150303000300c000003c024103446a07800c0c00c00c0007420381e43e8242c503000416900050050402d5201402c5126420002c0307020308807e160910000391290062202603019400c1c2c0b0415661316a00c01030341440111510200c212510054103045076184100d000d12110791b01d00e0301e0042142c0e07009001355000303214000d01c050f03031419041d58118058100d040f8556003010b440345908000010600605d8060882540110f4561400d207a40b40700a0071410244a502422a004243d0220b005055600004162140c20210b030780142c0d4031559025503450 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 858373381 1250 858372131 858372133
    0x93204020103150b0702040b0604030b240a180b09040201271523131719030f1d090103060531020f09190e0a0501050f041a280e 56
    0x90f000c81d503040548060108a4002c0e181000103403800e41c1482680c1c400c81c00084d061609150000d0001c40246268141e400c90012900c00001040302c003140e1400203e81140c0001141e41d00040c2410220744901d05824a040342d4002c035608060700060000101100c1c0300551030b5101603003490301134102c05203000820540d01c0212904c83c9414005045004400c041c03410f01c0500c00030004859000410f0f611912000b42e031034076000b843c000d03d01881031414070240c001400f40c0c200c0c8800c80c562a00348030f07003964002e848882d1580380c0d0500c0142000d61810711040092040c0c02c0555540c1c031040034440c1908c2d4800800a0542c507001c0c60030500b8141c0368050b1004c90003a8501411400c1001d41601c040d034425502d14170560444010040f010710110703000040b5802140076103c462034103420581703080d100d560a503450920552511829601e044840144204846003071200704120f414041759122047c1c4101c3c5d00e2030a0480c12000201c00c074044859140ad6250801b001e00a000c8e880340b22b0f2011504 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 858374631 1250 858373381 858373421
    0x11120c090d05071523030a020901110604060b10030204030302030d0b120f031c09020d110f120c100206070203031303050405130f06060201020405151b03030c0301093204020103 77
    0x80482510740c1060340040005d244080c24603110b00395402119141451020a504690765880d9100094112400d190b042144515101181c0302c0113000c0039000e139003d01c00101c2c1d10120076060114610303591194108041c0704001c2040844e80c00b0090b1001c2003500480400c80c16516030020700c1d41c46061a040d04580191141c140b0780c504008000c112902c40c0d004040566401000100c04941d070b040c201035008201404580300088286001c00000c200c001e1266000c40705101c0415004c8441c0c4075a00010b5105c0380325059035103001a0040a003101920040c032141c0f070445002512400040e00041484210741102d03401c141c0158140c4018000181a002d540e19180c200c40001d461400aa01201440c100c1c010848501c18002c8a040d070f80040e003d500c214141c440d40c0503a503070000030b01c905101e040008440701c41205100450280241c1c00c15a0340f83e5050000000845140184036184080c07040c121400402e0ba070401402c400d000b602e41c0b903900ea503a41c001070380500700742850180414488 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 858375881 1250 858374631 858374639
    0x9030c060a1722020907031e090c050303072f0d0b011403070b031b0903100b030d03020c1c0c0b0a0c021510360504020411120c090d0507 60
    0x112118107901ca12003030b485803040e1501d515040550100c4900c1e60100600704810202500b0602e030b2071a0030006500d03000070203140010354400c901c80e15000d6001d41c40d48991640b0240151030507a04003800f4200d000d1858060195a00e5410311240d4120044113006101024165280c440094041031406004c03041d044941d8a8030700d001c09024099104010013204424815060008440003038a83c500d1341c851641d16500300c03e04080303900e0010b5120541003000144150b80341032200600000034a6001704040458a0070142881c1104044a00701031040c050005003900004003032020350210000d030f03546200410001c490315900400c02402c40109002440b400703108640c8501035108165096402c42c5400c01d46120540c48103882d1074404400c480014081d02440762035050402c0c90b44100c00002e00b480d400c481004490855030030300826640d40801056080600032210a04a410a01351828804908540484002500508065002044640c0d41e900c4006426a006820104032400c0f01d6803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 858377131 1250 858375881 858375887
    0x80106140315010c05250f060e012007030203190605090f030702060906090415030b060607320a03020d09140d0b04060b0d14010c080601020a08070303060b03151806060d0209030c060a 80
    0x11b00e100341080050b80d00e10015225102d001028402c140580d03038112190711208403c0306241c07100f540008203000702100040143c3c0c0c10040c2800402e00d02d148240802c0c00c0c2d06004080703540042c100a55600301314001d05100c0408012140400e03070484890b03407260b41c2d080202741c0b01d0084540300d5806c01c0c031304441542c6000c480311400702100e00c02d80a4200c0380d5100002d11100c0e0041c410700901031038210b0b0142203002c101c041d54a0080710303030480380003015007001c100d14900011008141c0240c0c0203c014203100c0c0e680494401b02400111449030450142c01c400309040c1200ba42002e000c100101c0003003810480603030040b45400341d00900710039520b0085c0c2007002c411014925154815171900e8a80d56445004504076485100140c020348a9010390740c45039100b50b8840001101095070782e080100d00c1c1800350002c0c500441041800d040c081030044203000e20b018000c0f0804100d403118034204619903523040101c403a51110340c0000350702c03040080086860a441c1e550030315840400840c6500005034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 858378381 1250 858377131 858377203
    0x4090e0c042307090515030603030f0f0a080105090106050a1b12030f1a0906011211040e010503152401020a05030f03071b110f0609040c080106140315010c05 69
    0xc0c2c2c03102110300c6501d0700b10058410203582d200b40d0b50010840030041000381502c0000e9540a800581928902103804103485e04e5035210903054620400040380d60103041f0b40c095a11405010291003004d12541890b9001c1d100d40190850401005051400b0701c240c603003070501000040e0ba1020441300106036007035020300a0020754a0300c40c2410318000c010081100c00c00111045000050403216150310703014011240150607400c801012038480b8060220b90040d41c00400080100050444995040c5810141410361003560038045071191024806558000c00702408608180d160f900e00c00348000005038180059000090454000460081001c002d030000031841100c0555440101030ba45004817003a0051010b806802c5010304101243c950a04600140e201e00000b8400b034108090722000a054400c00b03507a00d03001840340300040110540207040b85000030348c80e8070440c0c11407400c007030081e0651000303190690400001b001c1100038007609200750500174900310402080c001c8609440084c40c9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 858379631 1250 858378381 858378431
    0xf0604030f0f051309020703020a150207031d030d0f1704060b030708030705070312110d0c0b09032d07080408010515040e0303060d080c19020907020d0504090e0c04 72
    0xc40030b60700598428821001c4031000c401d500820300c12217080c0580e04000390007040e03040f02544541d0620303002044c4000400b803404443e80d0f00c090b80d5030185180c0244880c0c10262641030304002100b41100d1541d02090440d200c48540c80c20f58001c00071203104449402c401c0c900c0d800c112001c0400d100900205403c00c0ca00e80d0015000c6a000c1e80c4c0d501480c070b13903c0c40b03001070290207500300040a0002901b1481c40146c510f21915190384090302d02006141011504443c000100302c003800f0200030046800031031707540040608061824205803140c40441e081e6494043c004401042810300310844404003510441030b0050401e0b80c5590b2501e032803500801065840001d0361030342c46d04451840c40c103801802d0300c2005681c09107055071111001e0201111145804441c481014801e4104d203080800055050801b0460685192948d60050240110b000f0342280c046400280781525065017000803101111140b900024407c0d65120303002d410032000705000f507400b50400c00c082200f80911a8400c2500f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 858380881 1250 858379631 858379637
    0x6150207090b0306010803030106140403080c150609060d0303050405010e010501080d090503011a04020a03060302090901021c050c0306012a0308010e070905091303030216031e21020c0f0604030f 85
    0x9424030380100f40d40c80c0c000340b040c5a4603500410040c0110f40c0310342a8400c2401d00c4480a42c01c080d22030b690000c040e0400020508154003a4150040c01304d240421302d07400040c107036488140b609005010a403e200740d1383c4064141030b01c1d04040f0741085000d60100e0115519074008000c0d550b156500d41e504e031940e04071844000381000c10040341505c7c0610448402d0751818240d158444041020302010790000084801070640e501704c00005622481322081c07050034103000040e900e0120740800c194804800411806051401e404c200c91403011030100ca4100d402405d000740505c1101ca24400c2e0030b40314070413036504001d0300342c0d007081050b400c40000d50603551880322804507642d6600d0121034904062088907800150400411409040c5a2072904464000d00d40940790007240070392441c4101d8095000c600041c20074aa201082203044c0d42c1000380f1480b464902403190140302e448040280c00b0900d02c0d401c50340021011403012007080182232071340000d42910010310340b605010302100079198001000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 858382131 1250 858380881 858380891
    0xc1d031603080c15070e0d1506150f020106050604052b0807140a02030a0314120c0d0c0906050f2109010506090901090f08030a11030108100605060a0c060c030615020709 74
    0x22503180a1251403082005d0740c0e4003224002a48200303c01040042400d644420340d6490b8500f0850050140002500400401580040440c00c004003407600c840303041400c42e45090410f2089035540400c60701295811980710b032541011a520a6244074030703807440b540e0f07030000640701c00c200084503024140950099001c400b101000403d00ca80301c880001001354140c00c12124040020300800c4003000c0065610300385410311147c0c00004a06030702c2980c84801048001c0f414054280f503c0c015a91031050a183c2110b4203440c055019045000e01102d8041101004c588201141c070019024803021405030030203d0305003003041881d8002d16054520764024260322000460002c0140142440140d001c41c959a410b4500c0d203411400340c001400c080c080540350940c1000c40350108010350f010700481c401400056500001400032940f04e5440180a800306010711100140c1000350507542d641c00510216030450032000880040a55811181e484905100c0004003503900040034010b403054103a0402c0303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 858383381 1250 858382131 858382153
    0x3020a0501050a0e030a0c060e1608060627150405070e040501090e0c0f061e030709240e030c032508061b0705070506120702100c1d031603080c 63
    0x30303110726848013106540304000800c0e600788600c412006140c0960f0000403882c3c50294642d0a000700c07082c1c2441f914040b8a42804884010300c0215000740e0300710f54540200072021030203043e0826040b0f10804140313040b0005442c00500710390401d4940e1005100300928580300c078001c0c003191781d01d6407000c3c000c600e41000070889507800d100720035141000400501c06500c0281c20060744034103541030309401400901c50a17070b0754080d40a81c040d24440c0c5100e0b20341ca07403030800c1d80180031207810f911000c00e84158440908046030302102c00d043c02002813900c000d490480a010a2818080881c2c1e03c0e01407040400c0c0c00e0f030200381c030404641d402c440100003059a917540c6003059078443c400d90711a442e401420084141000510300200030301407040d400e4519060f640e0000501540110500300c0f200c4c410f1004000c00d695041c484a50540300d00c41c420014004d041c0d00051800c80056071740605403824903125100d985d401c2103d010342e10740c45500c41400540301d1402151a80112031902a02d218440c880c3e4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 858384631 1250 858383381 858383401
    0x60203190c0903052505030102031303021501060e010f170c09130515281806091424040608031305030a0308040609060b1309050c012115080a03020a050105 68
    0x2c802c59402c00e009101c007003000880c0c514442803085660b07000d54821800000c180d1400e001552092070301c602700c103040300d501d814041c0c20700a00c106865581401100140601c0d0b8000c400c03544442c2c001c1ca8030440140e584441500c01211444409540d210603104008141c1c0316000100036019040d50070a42d80200304903680306488060316859040300c0c5407200c035261420042d14010210940740c01100d116254260318488494054114010030800d030184902601064000d110040907054030811001448c05911602007401506001d00920500c000c2d40c1144482010009200c42c001e004016403a0341b084c40c599240d124841e0081360700b403010300010b0180f401241459903a909929050b0880e6515070f5500024110a08110b0b40f040c0c1c0c4e6011030981e901d0342400020301d04210840001d485040b0300b0514a00b80d12042803d04205005000401002000e0a0080c6c5c0640803c1d010401140c1c01300b00c44100502500a101e0a03c00d10003ca02030550002d00d19103114007504c000c1003603840b001c10350 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 858385881 1250 858384631 858384647
    0xb0412090f0504050705070209040f0308060a030503070311010b040608060402121903120204030807030509031006150e18100306110724110301090c120c09030f0c03060203190c 77
    0x3901d203a81640604225030f0800f41c00c4a5808041494403034a000002d50001350184415907040d2070340d100c00c40602c4205500040701c3c0380c21460442d010354085103195110703035a074400d500d03008003088180e03882000d4090094100c104007200080c8240b1840b0740340c4071040c0e03503905c044800760700c503d0141508040f42040030407481030410000d0142620783c0825101a58846022210120300316801c000000100c2c07000300c00f0b800100e210b66604c0d0341d1805143c080510301480c1003943e800c00c601c1c10804100300d40c5844c0c03080405141900300030a5270790040c000245400480c00c1d50314012150681007115190585800304180d0380b103120200304407502001c4c481118080c225005003074400303820a070750040d0359050b40802c034100e8402c00810a03650385c0401001c117420030b9000c1800d1a4440b10340b88450f580040322420308062100081000180c031031002800c01e02c03544000b5108100b000751000611454240c440d0140d500302009644d20b0902000303860b006540000f030320010070b01d000610b1000394464800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 858387131 1250 858385881 858385889
    0x30a020a030e0d1109040305071b05100201110d1a03060126010b06121f15020721020d1502070803040221060c1b010f09030311030f0f04080904090b041209 68
    0x35013041d1402ca400d101c41444042c1c41a41803180078450b480021350300c09c440e0000451044402c040e024941803d10010a0004c0500720075a414004d98000ca00c5880040d41c442e00d50040c00810503008075140040e4050110340c034550140581c40011588100240d1aa02a5001c000d1210b40c0b084151120500301c407039409007164405010400945040203107800300e5041200040132010505280b030ba140340540f142d41c0800524405001140801601480148001d0040d03040b400c2c0108403038020301d8042c3d08158802407081010412500501c035011802444040419904656591140c100811107402c1202c04903c1120112804600c044001c00303402d50300e04140c1c00070246615652403003002c54110011a008007410400a40780010090040d4481c444010f0300c00141c4014038240102902d034030f031201c0110f400c010800e20115051415006900040c0703031784001c1e11900c803864545214481c2491140c0e1007070418440c801070000303071501030f409a4130807100b0744441180400700b0340e06e030811845 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 858388381 1250 858387131 858387143
    0x10e07090b0f0301140f030f0607021606090b0f070f08030a0c050901080621070f0e01060801030213050901020d0f140108010c2708070f08071e0521030a020a030e0d 72
    0x4000407640e03116178030202c890050070920312142039800700e450318401082010b0a0340c85003041c8090b4075018483e0740d1030104c5003000815964204400034040e020f42c1d103e8850b410304000344507002100102d064446d0315a0000e00307429005001d0410004a4000b0340300301d00310519060900000d00c0c01001100d0586d1410b03126007519940e0001042540c1c40c044891160a401006900790f402c1000c0c00b8200c0541465502850868280042d40d104200160404014001c04030014030240c0e0710900c418411101418001c1426583c941103140a401561504440c00703003001b0481d2008400c60300700903403803d1440141d0900341c0c0c0e0f8a486c0c500342c0d00e244403542d010840144869a80d5080c4070f84000b40401d8172040c0586030742e59144020700c3e103e0154040b10006503030900c1880120300c14440c10004252051020b0304003d00f00000342c904114074800c25209480c400c0c100402d070729031400c5203903c50242000750b035101d0549640c040d4459401010407000a10401c09110644c9800b0b00340a0741160021 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 858389631 1250 858388381 858388387
    0x51006050306030f010e0d23090d03020c1f0f090b0912030f130302030d0e01021c02010e0a03020d020d0305010819050a0602030702070f0608071d010e09010e07090b0f 73
    0x240050314a5440905107540602031054403900d41c1e1800d00521035021404001404120400034008000144803456400c003021214103409101ca0040c09548502c0d40846032405d8105e0203150680c07a201c0000411504010660380d800102e451135195481c0c0000903840b51120560300000403a8400418000c13142c00b40c03402d00411105003840a800d0001021580807a49480718001352648903803c44040038441c861079400900c11810281708603001029141065038070042601d0010352101c00801d550b10f5001203046200b01035500c02d4200000061106041d550b91414900300252220203002060000d0700c034114084103407500ca4494103049900300e101501c41c111703150300503854040c400107090ba0984500786402c004101d8900c000c40c050203071034005004403441e00440c06481c26142d031142e02407140e020f0402c9052a040030000c000c10401402c980b004040c9580180e44400c05581c003607400c030110340300104400420309400c901500d05921041c00a5503070b122122450711603101c078605954414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 858390881 1250 858389631 858389639
    0x103121e0504150f020a11040609151514270d23280c0b040906050108010501050307050a20100e0f030705100c051209030a030c0e0f0d06150b030405010b040510 70
    0x400d60201400b0f00040000c6000e560740c2c02054103554404280c0c418950b1901000c000040cce42e42c1c4c01c6d685060301030801c1135880070b41180d0829240180c0d090801210140f4a908925091031101c00044810050a00f04030b000e5a06040f044208140050049004c0440740e1035a03940c00041c03002640c1d130a0410000d040740504911040c222140d0034102c1d03014802c00d1001c0b45200b64140904040d000480d03002621500c1c0c2400100300e50010781c42a41841710410500402e40c0d885401c9403809045818500c0c10380350b003840c640f01e07003800d0251008243d0113010f450054148664101050103803a850864007408142c85140f0384a10805000401a9112034061110640c19800052038090307a420100e042580c402c00040c8134440c00c45000600b078100181b1101141e425104030f0665613068078159415107003840208810b840354880c000d00c00c101c141030800412000c0d4209800d00301e41d04800309241a61601c1c80c681603002580e0031111542410720311001410702e803246600c0356038009203005900e440c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 858392131 1250 858390881 858390893
    0x14060702012d050a0f030501051507050a06290604120b0709231309020604120503070c082118040207050309191d0408030103121e0504150f020a 63
    0x148020a08600510920b16855040c02411902041054a80b150741d05500d0308024524800b116101c001c1c10f14000c0140003580312040c0d000070301209292010756905190a0052030000c0d11003006180d07504261000c1810440034252950781d0264604104240c0154010812680154020348040c081d0600001c0d0201d80d500314031542249450402a40090b21111800741c0d0405000450061503111a07000c03029052241c422082d451501d4000c1103000050390000d80e4511540c0724544440b6103070303001202030200520403500e8042d40040044401666400700300c1c0c0394003407161409030030410401e40c0f858008147c0b00300d8603103c1800741320b1000681c00404100080d080b581c4195200d20082c0300d51110760321150803001d0380c00104201101c01500d0030340a68940c0c104840c0a2451030800414400042ca001040d24103495000c02010001015018221003c24100103698504088902012203a6070444000c1003520795643d84010040030040081e00d89200d102045001a4020400000170841e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 858393381 1250 858392131 858392147
    0x8010c0c050d030221240405040c0515090a120c05120d031d010903020601081b03060f0a1103011716050108070e03030408030f1801080c0313050c090f101406070201 72
    0x140710380c044a08620900c0105d400303041c049611a0a203051002c99a2011003038440300520151b04480c140105d01e0141d503510490390151041601504005004810501c50101626034200300030302003000322540e500e00328010645241081d110659240c1c400306890411800002106030310600078103115400d14801c42c000d020346c05d05001e0350101c504030f1682848080c068100107a000c6c0e4000c1680c2d5061007001d505018100c1004010b90403030b149002c65540b0302149580e8010400e80450b062075803120150f2000e44104054111040300020010640ca41315420000041c100c0b90100d07458a0b80b1810600100400c41c02a0380c08903548900003030240b4032a5071582d034813050180680341056178400c1c01c645140c000a040c0441410041068041b04042c40c0354000164000d02e8542014103242c520f00d000d034400900082280a00035040c0c1c0700f404020407041c407602801808425961030141900c5070b003540c0c103a96500e604000604c1c00a0140f103a40c1e0b0b507503207111000785168900741041d40191f840c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 858394631 1250 858393381 858393397
    0xc1b030203092101111903051b0a0c17030c040b0c01090501020a02150901112a0601030c0e0f06061b19110312030c07030f030f110408010c0c050d0302 66
    0xc071040182004039114003980c0945866051002c61000350040e00c030900350307200700080b482650b106000310001c10441303071000310200045040014103034550030241c07d001c09900e80040c0d040c03407000411196940c0c0c04003441d00c060340541c0661207902554150341c000752100f9100380391248003d000a2050122801c0185540c900450000aa200d2180d48407800d903004800c80038056000310603200e242c9110305000300c1c1c0c40f410700c5008201740e9464030103c215038094207010401201c40315003086a5a005203150103a0011110100ca03020341e507a15108003588017034000c00d68150821400326003607411a528090095030002c011074100135800e100001c02c00c0c6251442440c522444000007038031110715000041d26802449800034044a80d0181803a0186880154000d03140401c2080f54008141c419a90b0383ea5140c9030411011412500850261030301c4214230403424a010b03000e030502c3c000880140200e0f85148024000c0720f0300d010040c2ca400140d4030700909107410a00d604a101e61003980100203074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 858395881 1250 858394631 858394633
    0xe1608150d0809060d060e0a06090e06040b06030712080d0c030c0804111801180b030a0c15050d0e0f0118172113020102060f010302010c0201110f190c08010c1b0302 72
    0x17000c000014030050341d45070782c0f16a80c1001c41c0c00034450001d459005140c05000d102c80705100900030b030078080b03a88000040001c0d2480c0702c0c0c6004030700f691742d081c4001c030000e02000c26889141c240904040010381d005a1841c0941c614140302400828004d018500000d800c0740c40c0c0309969600ca8403111030010b03c2d02e103032135449164000d0041c5100f10001200e4060502c0c4404900c07080f032280c00d50003c8401013800b0520039404030601000007400401e1040075640d101550780302c03c400b4080c0c142d0b268060b00c200307d400d840c1451001e4416010005030501010b00346002401180b0441c200c3d0140d0395aa110b0240041d54444c080c0001009000001c1181540c6444141200000b02e0320400c604c1c1020346801248010050f002002e40d82d040040c0c0e40c01c040040d01c6001294910750000c3c017204640034000707052000e0400c1c0180304170b800784958603000343e40c002a224031207202c51410302e40480d01102100c0c41d502152020928031014821500d440440d0344607001001000d210300078110074082411411 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 858397131 1250 858395881 858395887
    0x80705071202030c030a030b090c16082a1f061d0402190e07090503060c04150e0306270304080606010c060609020f0309011808090111070e1608150d080906 68
    0x4203290410042050414030b40c0c0000c0c10000c1082046420302700948081900c00c0144064590020b085403104083c40e40104036580d2040d1000d040880301500f02c05240d051216483e034225000c001140403010759284850820039100100c40c8801103410500030a501e882c051031440c4e10100540c889031f900b09000903c00c40c90140000d03443c480402c100e40103016190103035400d00248941100d0290b0152908a01420b5a89040a200c0c5000e0040748070f006051002d00382101903490046241580c4000c02405680183c90101840017038104800d056048220019044c00618440401641c00362501c50018028686842004617003095120340300341c44650340c41b403000508101c944000d102040981c0800c68680c0780c01e41225085550f1410100043c00040512800060100d01111010300707090816642e12541c0c40317039041c540401500a0038960300a1014082c9100c4503110b4810b02c00d000e5503031084242c0c1c580b203c0201c86040c02d01360036040f944d07854400c000a490b0b08040c2c16003000107820700f81 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 858398381 1250 858397131 858397147
    0x70504020409290108060f1909061d01030f0b0903120a050717060d06021812010e071a1905190306080c01021207060e12030c180108070507120203 64
    0x20407684542c0c032000c0801c1d5a0f4800444001d1038401e4100d00708040c80b929600d0200380000600300351401482c480c410303001c07042c060000723694085c1d41c1c0307081d070012040080704551100c000200500c0b10b40900855400c20500031003607240003507940c906980d4400c610004006180c0d0f965140c0743c0000d00050003d0206001042040090190f280e00c503641d0804007140303d003013140f805042c4550200040c007086e1030207020440740b0344174a01c075282a16846540160368030b211500d034601c5e95031040c91203a40040c2c0d41003082e42e11070701500600c034002003540c19202a43c1c5e0320540031091480c1c40c00b2036110b8660510454440c3c040101c42c1c4800f9034007134101a0300c0e0809424403d031070f6008071441080425035440040c407800b9001c02044a0006082c001061421000031070040c642c012810020643d40c2c4500c52000f5140040c080f102040c0303a2042c0068407410160300c8904242c021036603c416000074050034114035072203610b02601400550f00c07240e1500c1c02945545d02c002da207000400e015031004001d040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 858399631 1250 858398381 858398389
    0x90c0c1b0d1b050a1203021903050c030a02070e0109020c07060c05011805030d110a021b040b0a06050d050901020f070f06060305120c1905031207020127120305071b02030705 76
    0x40d010b80c191902c0c41601820300c401c100310001c040c5c0100c1800910300b484040082d80001d1b14007410101a0220001700c1024030b0112004d00c51103800c1c00c814000405c02d05581900000d0034003c2e220401c0685003141c0e2a47d00e10002c90041805841640d80009801c0113260b00a0400c080c1c1203000b50004264088032000000ca0b80d07600340c0f002c4950358000a40048800924892000a0845011824641840340b038000359140c003c4440020448552030003444e0f036035602e5202d030005c024007400340c00c0d1041e075954028000740c10130b0140c5841c084c103040000f621001d0610807034402ea036940012a040c4035040d2602c451070150040119045030b0746280c0440814000c1100596045d0743d0903c1c01e076207640281e000f40c2031a0850300030490009c00a0300320f03400243c003c4140d9060f1414990444400d58450b0000c9016110000b416a52104104410071405248044070150342c0c0c080d01c1003403404404403004604841f000c480340d6000400d05030700701c240a4620b07450800100e00080031502c00544170030002d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 858400881 1250 858399631 858399653
    0x81905090d03080f0a0501030c140a080f0d110303090a08070203031b0d0e040b090c03101203031b17061c050f060702010c020a03020601033806090c0c1b0d 68
    0x2d6021892101c1040035010220060030350040707140314180404e501d107940b010310305159401200c4e202c0c80e8840c0c00c100742e0349a4510010080c1079082c115041c40e55158001c580350000014581d0001e0410b4103403400c4540e0000440c0d020701024801855000b50a440d018001d400102040384e042c0010004804d111078081c0c4181740d41e000b980e002d09158584810043c002d01c2e6140b403c54013860610681c00d00c65a00d2113290b07680501404401307035407952080c00104e0701100c00e8020710101840f010100f0145039040e44404821114803c0c003211201c41500d0585031062215101c2405058440000703406081488001d003c3c40314442000040303100c070743d80d1103050085038244031920350720010400150b01d50901034800e800545001030900e02189881c02921030405000c09030003140350300c0120a2408828416007240c00314801102e040c03d40c0c4107a02d600080e800d4446511a452540100c1c82c004c002c0c004442140b07144070020180d40951540f8200503d20508c80346030b000e103401d280c2038041a034507445 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 858402131 1250 858400881 858400883
    0xf053c0a090e0615070f0201021908040302090f01210303022a010b010305010b0316090b0c0607120b0303070b06150408030a02060109181112100b03060105040207081905090d 76
    0x40c0c518a0381081c5154481d1807000709524803030241c0010444403040d131081210031031500268403031510303500c5000603407800142c5c610481c1c018200221540034016558041c10a581c0708035181c0d040358a442414104c40744003801501ca21030b040c032245440c1160020f14040d1074034443d00380541030203400703580004170003480b44684001510083c10a002c3d00c00a2090241103417003400c081000c1d5040002c00703081ca020003050052005c49408500000f03900441d0304000038841c07040101e5480d4000142240c44442c01d440083c00701e015801041d80328000ca01030301106440240044d41440f8494941e12000440a454030350440912480d40601c4250107005001922030039004541e28031100a00034507002c416448020564503000200507004200c0c1082d003602a0815000807130400100c2c002541d000526000190500c0b8014208000d5030440e0400a500e4004400ba600e20380e90320380511059104522004181c0307d000c1160b00182d00d0b9240301850800124501681441e4800d40415844201144 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 858403381 1250 858402131 858402137
    0x8030a0605190b03181c1e020d080703021c1515030c140304060e011509061d010608091603030309020a120b0105061602041a010f053c0a 60
    0xa414042418610061800c100d42034450b215420310300320043c1043c0c04040e00401d0201c1c1d0304407502050707082c10041100c04d83c1c05041080083c91400388040c00b00c040d1106540a86030030800620401400420314101c0232085803195002581c8240c001c400a6024800350149440f007910582d112080c40d00c500442e0403243c1c01640102d60820a0310101c0e04450302c0c954080500300001c8040d45070340000540d058a202c80d18150700ca072594030b801000344c0816141400258a098a000401521040300104446102030200062a1981c611480c0d98403d00314041e820a10100100441403080a0a0754000168404c0d90700090105051440340d1059a00550000e13403540c400030300b9071a25103640c0c402001f0158041c0e102210a6440a0b41719005209180c411400410b605038140c03c41030310b00f4851076009200b04003010449130118a0301071000b040da40058400681c20710018001c8048492110002c02d00c2e00190f1903811710842e510590b0400003c81c1a11040045070b0402d041001c0c00d00100c0a032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 858404631 1250 858403381 858403391
    0x10c031406090f131b170d0c030c0c050402070b0103020f2403070905060703030e07051c030809030f0c070807080105040f1410020415020c0307140103020f04050d030c2108010e060d08030a 82
    0x111400c034034a41c161ba00c00751345420812030320000b06d0b0000116401c0b660b0601b031031503001700b95050031000e40c2195842690441e00000d2074000b080783c5c41915034140c92003280d42950501d00d007020300080d0b25981074001800c06212015044c1021800d0146900000078600070101701d444001050a0b070304041412804252608120783d142d42046c441917003d8601911148001100c43d083e0b040000341c1c0303640140038000000701041104209108951011504404c0250f03640c8094001c0b03540d401051080308400e0007091b2002c148900f041c0510b42c0a1a006900b85d440c030341541c1c9550500c140001e212111920400b42c064a00c0e01c5280041c00c014011100c801000000740b180c082c8c1810701d41014540300350030102c400e22203076042c0b005501c9090001c3c40c0043c0c42d641d500031800c9a5101e107410040e03011210b940c42008042d0300107404100c4500c1408441c02100d0003602c3c48410000d14061100450200001840112481440d1a078003000040102180310304540316500ca0b41c6c800d07100003200503190 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 858405881 1250 858404631 858404639
    0x406060503011b050c07051216090209090f090a020312070b1e0c0a0207090f02211005010f0e0d030e030c0a150f050409020c010c031406090f131b 64
    0x244180002400103a00a0007854480c5091014041401c10948180040440e08955060007006080040d100c06421344d641003110f001c0456417118880d0010102e0344442d50f001c00c12680318002e96600e1080078004101d07588a074031034800c400c0c3d4001d244000034400c1c01c9804001d65000c0014020801c018521165034140f030b42010456072400a000411800e00700c03081036410514100080d40c8101d00103202500c400c41c43c2e00890900101e50700c1541c0710750800341d2421601072140c3c01131031078901c50310070b102c040b420802101c0c002c040304643c0704d02075010050003040194001d518040d100d07425490000e440501c41070004154070012a0142c0005102c10104540e03401d042019900900c0c04075004801d42c3d1910361654115103141000b40200b008020030000c4a0f80270720b050760b0203072140f10815900c5003001d114a500134880400700d100020304080000a86a94100045010b040e018201e00360990362180c40824144c1e000e040001c07400000705500c80852a80e02c240c4403e0708040d00200c40940c50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 858407131 1250 858405881 858405893
    0x150a060e090d12050a060308070b22030e09062701030308090a020906040b01170106030f0f0204150c03090803040f05030d02161701110a0e01020d18091e021204 70
    0xc028507448840e800440c01490a50300302c0400c00f200504044080b03001d54070b00c1008030190200307a00042c4801d1340412203030200031503a00303403d2144c0b928031301142c0300704203080c0c0c00f944100321503102801003810350b82c2070a280d0820340c01940d401359010742a841c20f01c0c1c80340703468a070441040072a2010056164014010542e0001e401c42e00100d120006102004580d00001c03480680036100390301c00c944d07580001005902030314034003841074803001600c002580c0d507031400380103850424030305800e4610b050500b48600e0080d209035001c1d1410130750034a20301c0071511804c0d036040351812816001c0c0800200c0c00a03285004000401c041c121031400700f400685020203143c0340c07903007403414841503404c60300e20114170100e0885076400300c0f0700c80021901850046c003080e5004041c6d03295451035183c000030b20b503404143c000b94800070b848000e900b203400700c511840c012141c409401030080c40b201e109800030040d0788515003002c8004091480090f43c001000c19480007264001d00b081200b805004080005100d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 858408381 1250 858407131 858407159
    0x509190b030607050f0306041b180605070b07030f1b0c030905040513020d14031206030c010c030f030f0e01020406180b070210031802100801050312040e0c0c150a06 72
    0x5800400030780c02d1103c0301400d24014074000d103121400c044006001640c468111010ba110580c100403000a0714007002006c0001c1030394001c803a2121800700151507881001103524181e003100e0110010342315810200c001d800c0980340e00d90455141c500fa45d05540303400b12004100803041d150040e80d07607403a24028100351920341c0010b00c554640820407014a400c5a0800c1c4030540c101c0b0b5030848000d00303280900c1c6200b40d01300c48080c20b21000c1071120701490014a400e0041000b10211001600c4a400454081004180040029405406203040107019400c440d6003d00d00d070f5404943e2403d107600d85400c9070419409100041d69012101883c01c00b0680007001404101c0d000c607150203801c0d0041080300c41c00c4080981010340e1201501607448a0549420155500501004003a000c4440041800b8000e009243c445d004001041909042100c110741c00c0701e0307881403c03c1141d914541039114542082d600c4055500452100b2110a10085e01d04c5104030b0514800041641c108100128288 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 858409631 1250 858408381 858408401
    0xf030309100920010c1a01030204060801230c160c05103009050f060105090601050406090b0c0141010e0f040602040b0c150906040b0a090606050919 65
    0x20b1612507900d0200f10303c64540e0101560b928140702510080c0401244c48641c01c10001d008141c0c00107082e0580c015008455040700d0003120140112a02c0340002822500b20160a44034810303511101c010107601c2e40c0a0b103a100f08404992400e00c800041290240d902c3c0110494680304a45028001850b050100a4600180d40340912482c0b468200d0801000700541010001c043c000c030140300a51281d0308103030707041a840b0064548820b0f0034401207039148803c2c000d40748500d8002001400321f510620641d0101c0b81c0c0c82d03030394030001d6144c0408094540c1c40032010310744654a0750440c02e1040721907203074010a1312481d5110452201018400c928410b00780e1188141c00011000412450b81003140c6d01d90012020480d8524503203480c644034000f40714036402003954102c08214680c00090110795014444440c4509040559030310044544610f0304650041221800001052084003d907010640d21403140d40009225500c1d01d00107070748902c04032200c160b5064803024440300ca1a0780d005000c121 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 858410881 1250 858409631 858409663
    0x8010c0507080d051302040905010506010f030b0f0603090a020907021b010903170c0a061a010806120703080705030c01050414100608030915120c13081b010f020c030f030309 76
    0x700441d642d68141c1d0b403103803084901e025904c440104040042d000c4019400c00d600800c01c1245c010586000d5010303000c1100c0090101d010503216190160190040414503c4010f00d10070341140d203101044200c0d00040e00c141c8140c85174103c204010385074030600901170719150300104a0410480b80044d00d426802c4011410407040890800000e100007110b004a03c14640030240c450000001e07542c502807542d8000360980b82005441d00c02066654121901044213aa40c016140d4558003408013140740d0345041141c0da4012403040001c18030a00c00f40502500c500e05903031030010301048060035140103070b9007a00c0e01020032011180801007008500c2d07401d01c01d02c6081c0f100782d242a038025228040e4690043c060400c4035076000703004404000b00c1d01403079103100080c11a4184295610a01c3d0004d05024400912150b0040303035405000603c0c0503101d48040c4441525024000110b0708502e244030280c080d0f20a040b24030f003150750b0500807a00030000c440700940d180c0c03401c070300d04c030b49458064000c003102 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 858412131 1250 858410881 858410887
    0x717070503030115050c061014121b010c0507090f0c1d01050306121605030c0d05030d0207080408061303020105010f060206010b0703051209030903060a050f040f03120e030408010c05 80
    0x1503004030649045072031496034070003060038100d400e03609446202c1403629a4002c52041001c41d040da00f102c4016120304030104060b210180052084070441c0c150b400c61640e10954031031400718003040706001c1c07002e810700d00411005010f64482d40340101542100a0254071082240d240b040c079071003010848181450b024410030100111901d42021054205040220000c00a01140c07201810b00c0c00c51f80c8034800b2240492800030840513014a50300405210b0702a0040030f100b01e240c91f1803402c80d999082030103585810351000081009610294040318109010711000650300c0c014000c0500c02c10500c1980c514480341031038000d085a5058221f00c00e060043e89042c05550b80c0040c0315410340e440c1105040d074504060406503501d000d0083c0022407001e401042021410f004000340811781c5c010780032036081c3d88402c140507003582e60840b550820801c446000a02007041035040e540c10304e0190400c0b02a113000350380035200b07880070821044030a42c000101008014000d2141000030070b002d20700a41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 858413381 1250 858412131 858412133
    0x5012306070b06030c0a030b06090c04083003070513080105010f0b0d0b091602010e0c1c03210204170307120c060e1f0b031f0e0c120102071707 63
    0xc018060400c014294102d503100060b51910100100d0300c020310010800c05069580b454515031103403089803442c0c01020360300003090681e500300081e1400d441548016080c5902d0400d01e241400380c03e0610b42a41041c038130764103605042144000c501030401950354030342c1c07481110840b0b07002500507030101d20103038541401001050000785031035003501c01c80e4040e82c3c0e46000c81c0c41040085c042c014103840d400100f070014010705031903401708a100b41034290024090000003010113602d400308503e00702d0308000c0c0c4e19034000c080424070f610307885e0325442420480c440e40080c000c04d0038085c580100380c1e083c03141c1c0000d0074001c4c0804080c44142c41d651b034800443ca4200c039551541c6010f24009000800e01c030b5011000d0003040001d40009031485404012a81054102d0b15105440b01416003c02043b13071806695401c41e003008502a12070503014420079849041103240d0303100820312802220214050261ba19440d96141c91034804001c00ca01c2c00584c48298070b00b0a5031100b50345100400c1c46841c1004100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 858414631 1250 858413381 858413389
    0x1e050d03020a29061e0f1915020610030308010e0421050a020c060702030c0f0315160f1e110f1c08071d04020f0408100911150d0506010e030709050123 66
    0x30060041d961744074004031120100e1044c0703101458605403990359010224041900315a060b42523143c2c1d074220b0b51141c0f11815801700d50740d854000503002420708001844080487c038106a040707441346480004170391101c116441c481c88010380c0f03a40005c0d0300095680c02258100300000341c2c0c000031a0140e150454950009a4415000308160f000c2d0160510090700c07650123220a41c80800ca0391035558031403903da8207018402c018410020081546150054121480780301c0c4c800520500b490f00d4110a950300d402034405403400d2081e070350340381f15155085c1034241040c0030322220024408a212801842c80201502502009101204110783c089010841c060600b415105000c015030300140d031940c003901d05c820316114541214640e407042251000b40d03442d80e6486038500c180100c1d4031900c01446001003180c0d50000b209041980c0f4030a100004c10740c2ca151344170a030801030504105c40542c04200100e0b007401e18943c41144013a42d00c0300100507045400142c035032102c00303103100241420030140c009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 858415881 1250 858414631 858414679
    0x2e0f090501020304080303061e060a02030a080c1204030c020307050418020307061817032b0f0b06071b0f170105091f0c03060e011e1e050d03020a2906 66
    0x109112700761030215a00031408060a00c0e5440d00c001d0141e0b5515060120060342da030744001107400004e841c400c00507080801d04020f82c0d03e0884403024003001c54071517480484154040d100309a034580a400c0e0001030340e5443e445210118210240040020509401018145501580100d0034805a03220b2400d1075401c0f260900700340d40501000340c030f07854510902c2c2031550203000c80fa505110f0100c803108040c05200303030f80c5510000419406000c0105400340e4201595090740395a07411070002d110305000144e4000b480b000340034601a14194440d82e039040c45041c600940e104800805556002c0d000043c2d0038007500c0e9104841100401502c1da03080a602078032a103100000c105980e81d40c201c5040c1c18400d400c0702004001103000401c2e41e5845115040c41c0c49265044042c5e0429016000104004150101a240c0850720b061200c41c621300710a00c80c560300340d5003044085000e80e000400000f210507009404a101e01502c01107006151402c40400200c0544600d101d4242c400044514602c24008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 858417131 1250 858415881 858415891
    0x10b0315040b0112030207080313091b02120d090602030f04120918020304140601031202070e0c19090e43110f01110a080606070b062e0f090501020304080303 69
    0x12940c130148103401c049003040c0c40d80d04009080d01002560880e500ba5003000d20044c7c5903d031200f00025049060220000c108580c10280541c0101c0010149a00f480004d85084403c1c14404141c645540d5030b600300f00c1e4001c584d8130080b0846402400140b0517680a90040c1e0b00250402400c043c0c2401440100044a0002c00c040260004009420803005203800803e1544100450f0280d50f100d250220080000301c5e807023401031003900000550004039002490040e640202c4c0b052519802c0300641c0d0814440842c03480a128142c50000b5508010402c040c1c400e50454808404468a0f110344000b800601d00002d030000010400e0280160749400440d0a000214104007448030502d02d10903050600009402c48203520380648440040c810400905041c100ba5540c015241d031840e00f002290702a92101034205009100020100d0802000c0380d4160940b241c07681c0302168180707580c9200000500c6c0080006208084a03034803035030300151910081c1c5000d00141d8145802d00211325500d0100900b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 858418381 1250 858417131 858417149
    0x5061312110d1218050d060f09020a140a06050a17042d1101110307031d09010801020d110c03070615030b090f0606010903020906090402010e060c010b0315040b01 71
    0xc1101000461003011211800180c28a41c0040440c20800d0803104180710080115540410758440041800100429204014a0340c51081e40341d444540060005000281d10070b65036154041c05a6a40028070008020180f2544411603040052043c0800c082e2321000c00d2200603c010300c12141c2281800c114024039441019507907485003880182d146070039110032011207600d00c0318003645040c031580303180050148208200d030350104001122113041400c070b0100550014040d14000a11a040350400f6000b8030001078540c07004040041c181b090280c0c081d2605a50004540c1c0030901d45000760b402c0c03280c242040c241405045802d080d101d11034443c006200c556504198503050366005107500145400414100381c03880c00740c002d00c0d40c85880d000c0380d0002e44220800120300e980b02343c150300103982d80509044466110f02051001840b40540224148600e500352070084d500c07400c01600310107414400115207600000c0902d41048444181d4000f50303440303441000046940c1000040c11152150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 858419631 1250 858418381 858418409
    0x50d031b170a02061008031209151003150501030c12031403131a13080901030b0d06060f09090f0311120301150912050c090a0b0a0b030709050613 64
    0x24051a5505001000809058641d1031607201002440042e00700c00300540c00700c440c0c03601c0707154031342c07a9403040b61003591601d91081000300580c001e0b90a01a0700440b80d40c041318403803661100044084541281e00e2a40914005401c0080c0840c190302110340c401d4a00c02040036506580310075800c04124040d5104c00c0d82850a660304052180015a0703a1344450b00b5825200d0600750f00110403440051000e0301c007003002c5c0b03100c61080c00300708141038007581c0e4881a101007154540e80d030042030b0b0440030700541410303170311240a07100740c0303640940c0500140310f0100005c04038180303400c4041514042d00a6601e40345051350400010310038115402c0311071303014104100788002c0e01c1d00ea1883c04518490042c0ea40c2c81c04800002c0800b5000402561801161200c40c02c440d1603001310360320503403c1d00001c2c280b03902c94407001c2d00c98140103490a401442c00340d070128040380440085010300503e80d0000b041d480c0c00100f0481c4e6a07a01002e1800074101c21180c96141841c401c800480c2620b4a0080a950780315032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 858420881 1250 858419631 858419657
    0xb0a03021005040b0409060905060a140f180403020d020f0304060207051c08040905060414060603150f0d030e0f0a06120507091508070f050a020a0809131416020106050d03 75
    0x49003a940113212842c1183d40d1180c40c0d000b040d001d8012031050301c0e40141441c01140151811203046016258009002907403020b100080156181c1c0c40c3e40c1c0d80340c010101080d4894002c40032103540c0e100b0303400f0f134008001c01c0d022408000e1500d60078500329002034205000c148051540400c1d140202c41c0115004040040c2c00141000d080958207002081c1c49000100010300820a0308071512800c001c5808100000b0f156601c030b14100800c03034486a00c014200f000542c104400320070700c001418058000400825120003141e850010b40d00c040d400b2410045000d005c526200b00a580d02c4001a64501100c80c94041c014085030744580c0380d40c03281074a0314009103a280c4a101d403c001840a505c070180442d49048016260702c0081d510880011801c840c041c40d00da001e1400c0321100861580286100b8445846510f40c82e000b50300c0320380d4404c0344121a1803c041c07440c0981c0c4074641c100022103103581010940c03400340e10007061950041d0790400c00e04016954440044408040d0182401e01e20307480c803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 858422131 1250 858420881 858420887
    0x715140414011503152d2316140a03060302040509070f0e07110d05210c0d1d10140703060602060604180f03020106090f022d04031e02130b0a030210 65
    0xc00d003904400c00c151403040c2e00c1b0074a90401080002504000d0401104003aa142c0010702e400740741c5c480d10a100310801050200380441c4154030b0300340040c0340c103a802484010696810b030f44845404000261104024420b6103080d04c140390300065618000e040c134510b230824290034000e10344280c0c003c040316440041c98042c00760400406081000c0d040d186c0602c2100784c058955000701044180f0039900511641d80e840006e60740c14040e81c440d060150500100b000c05001410410304141c0c600035050130307441445401004071000301d600d214800325510b9400a9203202c0b400c2c00800400806041c203074200710f19a004156280c0140050b180032448503140c001b10007460404d94401002d01c00d200344030800b4507038198080e80c2512407180c2d0a00020411070040c1050b0301034800303242d0590880c641328000210348461155039407800864a103042a55230303140c543c0c00f4020121484049240154000110b1811020101d400702540c40100141080a80840c1102c455400000d00504140513500c0620780 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 858423381 1250 858422131 858422141
    0x60418090c0b030c030114030d091a09041d0c0315070305060f0628030204030c050609040b27060a06020d0f021c110c03060c030408071514041401150315 67
    0x20b5003840d80f03980f4146000103141d5640240f0680c14405422a410080740c0340c04514011602e08580d11180424140402c16404080d481e00640003080304005120b21501c1e18040c0f01c05e0507120700701c0200102c802c04a01270900e06144100c40c400e802c80e118104804011449151f00302a0502d0002119540c15021611412090000c194031110105882c0c802d46456040c16100c0b000f00c248007042040c40a40a4003070340039a005c02014014034207024090780c14110060324068078001d10124550424001251811444598600500032080500d5076000d100c1480c42d0340181054078118812890020000c1d2140404c60702c00f81002814400e911a6900c01c100c841c80d110300394a005543c0d06484500641070009003041d2042034000e0340082009481c0100c0d155108001492000d461a5500e907100e80300383e44444030459150024a0980c4c80148030740c45600c100e801910f80d14012800c160500204000305460103d00340d82c108450305020040760500356085030f1b4405500c80d4000c280d08550340c0601 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 858424631 1250 858423381 858423389
    0x2406050a1d060d0b0f1317180102160b03060a03080406080a150e01030f03020a0b1806130b0712140c0714010506130c0507120e011106061c0f0215090f060418090c 71
    0x79031000040e40d010590401401182c2e00075002350346c100c810000590714bd40406c41480011100482c04001c0320081d04000c5a0192004048040c0c00f0f07100e82d515000c0381c119820140010380b0180402040b5002c611460039018407081c00902007072302e41a0914060501400000d0101c0454940f500030140200070940009900a00c0a102c5251603444203a040d01121440e0a41c0c0c403605000c241201c075003078850300d50240c0010100030943e50b298bd00340c0c1c250b00418512616207039500701c1765100c45510114140540c0c100400355560300706a00b000100001940c510040d280d2400c0184030301640c940d5140c0007261411070300890740c9556240c00351000c3c01a82405005d0034500b00e407006c07142e5848840e21a2410003622140308102d005450203036510300072244030f0b80150854218900c11544032117503e9440c1e10a68010400c9003c6a01082980d50000e00c003441480002c40c402d0341e240740010b811000d070130b0203403481c0c1d040c04c6c5089403071030419982c81c40808029554600500a0040402014010f0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 858425881 1250 858424631 858424643
    0x140d032106030b10060c08090103150e0103030e010e011704150905060901050901052530090c0b0a1403060d0b042d2406050a1d060d0b0f13 61
    0x1c0c659909043d603c0240c01c5500d582c0460000a01184843c060740d0441c2c1000e1300070380400e0034040580c0041d0000d2407001c0d0110015206c0700c00c009040c2842044003800b81d0302c42e5540800584c0e4030310000d04410702d6040c1d040d041c0b01c0c081000352449031140c2ea20660058006d00506d1700e61302c441e0209001000880c7c0041c01d20f00418042140380305054011600400c1c000e8002c010740c4c1e4503106600805054a00d014442c0003941024842c2d0034402c2655074803424842c0c00417065564048400d82445004001c02d188464075a415035051120110800000b0a92032119070320301401c1081c003c060407640c1700206465000440407580d10303100c000f500c0c03902650001d40341c40c10341820b0401002c26040201458441e0604040051070030000c1440c0400e040d9100c5242000d41c0640d4a110140b0318045400c10107181d5603000000c0c1e90b03524000900010105c138010006800c495241100703402500429040c0603010b0848103100044807000700603485582c00c05071030400d86801b010325400d40142640138003c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 858427131 1250 858425881 858425891
    0xf150321051b030405030712050d3506100201270507050301050f010905060a0b04050405040f0605130302010509010b0d020d081306050c1501080607030e0106050325140d0321 76
    0x10482d0004010010340f03c0c118221341e0420354881e4030740310b02403a880b0002d0003500f201c01d0000d1031034006d08034005241d8845803075490110340000600c5010078a040140700e40320801c014882c15003440c1510f071000e14900d100a21149200740348d110700207141e414150001c9441e2000a005000f0180075240103040010028400c40c00c080c03201741d840c00c40030701451116500d0000031681074548a0300d4441110442600d860400d4513090802004000080056482c20104403004000488502c01c076407290580d40000e4003074983c02d0400a0071240300030425070b0203030300d00b00d000d10b01642c13500600c0d06a1513040700d00c1c90f080940c0c0e01d086802801401c5041c1e0b82c0c0c140d030a0000c41c4180e00080908041c8080301c086401001c03240d610610740c00000e21402949403c19404900040e00c2074011040d84071503500040f501f250b461001c03e2510404240901121045140491490600340700303c2000300008a0780310420044080000e12070114800d0040510885007401a0950f41c114420780c010100e8103802c01c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 858428381 1250 858427131 858427177
    0x181606020c03070b120a0506011209060c1d1c030c0c0b0712030b0a0b03061504090b190f0b0a121e050603030a120c11030a030f15032105 60
    0x1559000385062644070f4002c1e200d01007408000503040d50b14102e16104011910345503048040002c6c0b8000e08030b00e0400c03054014000325a0694001d43c003400d840b683c000520542c84540081122004100b05074810000344444101c91b80c4540703443e5510311003844000030014403813a050310011a5007500070f0581e0f52107000007925003244405000709a010388408041c03030032015400c4007144c1c00c0c030150f154000d03000e803424000b419880000e55404030000d00980c401d2407a407207401103075401035485020242d45a105902c0c2d20b00305031701030400004102d11031101c107d00700305d900e1103802510300820704403e10101d00320b1603003885484030f051400c1b0a45d004000e02c451108031840e004104c00c1c1c0c948081e90a0001080c40360034004121140b440055481da0580c1c040c504042016103030003105102007006503822980711100c1480209035620454400040d80c1c00c8a161090a96501d01c00704a04400c201504001003825145804401a01d18030603040520006200780c1d070600400322056083d800c80d44100d2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 858429631 1250 858428381 858428383
    0x10c02101205010b0412200a080d0e04021c1109040f02031e01060c0609020406171006080607020a11040b0301140a1802010509131d0106062304030f050709050a020a1d060318160602 79
    0x1a07504007640e500c8803a601c03014401c0c4020780c03099a40310100c4003001440603404c40d003280d00fc3c09041c10005c2c8900e2070300840d1070000d0217480e00c030314180034469400001e100310384003402c0c0e00004040c0c940401580640c0740110207410468a180080c2c4480e4490140400b1941d5660040001e810004543d851103921326180c190b039180218801c82d0183d15054000c0703407407d80001d085110740b140c1c0e4000c0240e11034554171503e1340c0b4811a10550459161021000680d40070301643c041044501603000316841d1611405090350f980f41d6117030803220750b40d48000025036440b4088800b8050f00b40d07061903d0a401507880030042405442c1070203a0b24240350241d4999206400c1442240c0f91170343c0c0c3c070b43c9104d140740105060721120080501006410801040007a50203020b004405000c4e1056400c0d1540d038201042c240c41007140c2c02018503034005070b845880c80e044100000c27500c010f4542648819070070408078209102c054110001004600a8080c903107030200566030070200740f28410300b0000cbc5e0754040a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 858430881 1250 858429631 858429643
    0x60127020a0302071202010b0a0501050c070b0c0f072405220308090f0102280312020409060312020a23070302031204051c0f030e010c02101205010b0412200a08 70
    0x48a584c0841e01444e10220306c140100012004003c00c13007081c403845c1100545e1998003014803600f0f00c0c010340c2000644605914041c24043c0011006000f40d034940180321400e0020a0708049203540e49100450002803c0705100d8103100b0180c14800c0da2180000c4148040d184001b1045540345005500401049031041c00390102e0201500d10f820100d034000016601c803158216100302c800c0c00c404001031032012000c241c244060082c00d040c4030360712050b800c150a076400341e000a0813603501c1e100108108504400107a40e611801c0c8080c004010083c3d6681c80f2004034081d000415020078248800001000e01105000303542c003c0844540114664105071190844e2007114810b800c0001c1c09082240031280e1107511175485030800c404142183e809a41015040c2003442c100b0550b421101c0c01030711000142101e040b4540c0340e5180d1101402422001d40c0e5050f00700c0c1c0304200052100300429070381007039040a41035010145a50592084426800c0c4880540c50343d603000340604000940c4503804039007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 858432131 1250 858430881 858430883
    0x60403020a0b100311040b210616110616110a0605090601050a05030d18030803040b15010e060406031e02070b24010c030c0c0e0108010f05150102060127020a030207 72
    0x48280c6a82c035640d00383c0c1c6000305844044e10610600358101da00d80742545c842210a038000740f217000b89844c03a4817440e0002d4010480807295600c980d0a102c280e0184501c818002c88140c6003014003014550b00e8a9203980300a40300300c0c110040c540d410500c10f4007401010382c10a0f05031089907000507107820100e020b05001d4401c240b640c0501c9001041c9400d14085142c00e4900c0a401841c0c140810b0204880105000380e0700c00403080f000c00b0100c0025900c0300250300450103641d07054000d040282202e43c0102c503007a000c5040c0544125000c00c142c503400d017500d00321072640c100044c1544117074655085442140d0f60229010b03200044480401a501000d50b0141e4074803070115000d00c549018070524003001c0e0708a40d000c1540c407010100001d104a140001441c03180c10501e003034594500c0301c0e9050360000c0e0090546a51074800080e000f0311148a01c943c00001002d03500c0c0070703280100000c2c1d114401805100300e2000c0f140142c03c413400c0c0108074149404607030300085541d00a490360080c0250000c001c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 858433381 1250 858432131 858432143
    0x80f070201180b1225030c030c020109030905060c1c0c0c0b0403020105091201020c0f0607030c050301050901150216030503030703230a1d0a060e120a020c0d0c08060403020a 76
    0x40004109040d01c0b20640542d82e005600c14a0003110075051100311800078914504100c00165141402c41303044c100401c401e480340c43c00300c2c21604996014094454912070308045a26000000c0e01007948400c85408a40003a22000d41e43d05036030429a04003403a00c0b1526450350f4230b54100da1202540a50b640240c00d001e142883c24103038035041d41c10060722580c84040d0015400b48035586803490481c1e0104070a8003283c000603d00201d2084817814402a400c0a50942d0800003c0011454042c00b0b2a607403000180b030003034655810314002907102041802404056201400300180003402000f440b0848510200074442d43c590f40e103082ca680b82d00c11110360b400203003440d03504038501d4842c000c454000c0401c00c3e01070f40117650b01d00005000306852006c14420080d100d820315518107040c0100c1c00c00d0b0380100c0d808100c8540c10011203107090041c050143d20761101700b00b04a001039003c544201c0191085909290303640d554140514030b210319070080d0032680202c4060000301a0001180c8140c107200301 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 858434631 1250 858433381 858433397
    0x114152b030f050c10020a030204082505272a0712030c020307060906021b070f050108045c1210090f12050403060b03030306100516080f070201 63
    0x21404441d0b5000c1c4480c802200e45c0981240890000260090071402110b445c00605003075951021134500410318440f0750050925030403241a002c030441da0b40b80501019150058441e0034241d0340c00c268442402078084000801010840040209c854441e0000280140810424a444041e4929070041404480955030700e000104a0b500900403292082d41a4001c5e6040100315111040030b05030095007140c07920b6007005a01003111030804080d00d211030380c4004045071030414080443c4440d0a411003814000080100300020320a00014200c20010341003055102003840c044454008018400e0b840010354810101100c2220101958200080b5105060320380090700c00d02908c0c030604a60b2440c00e8000c64102200400250461003429109400c1c4d8403c60f17a980c0c851041c40c0e40e46c000d140000440c002000c1007030044500603d00641800ca02451550030b01000180444084100d5502404008122080480a04144040401c7d0011501550703440211080341c40b60f84540c0b42280460812 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 858435881 1250 858434631 858434657
    0x1911031612020c04060e010308030403020f010e0d030b03191b05130209091003051c110f07081528020904050702060105180c030c1303050a0b06010305090114152b03 72
    0x42c050305c001c4840c1c51300400500d9085449204550340000d10580070340c480c0001c1590401400d02c62120340101d210041c011074004820001e05a80903070742e01078804c0d0700807402209003c1c00c0200b405a1181d10800601c00007101141c0c020030070071282d2041d9481058080607041c1c0c800250020a041701c8c0c00c071400d0f0310560300c1c0e540c000c3c140c20725404090000d0780043c00c00c101c41032015951030b0b500c0c0c616007440c1d240d0380d28503007405241c4030403206d00f00d001c1e4001e10340070003a80004100c04ca60f0107900d07c0c0c20240b149130050024040c001d010120040107440340d002c0070401d030882e50449402002c064418021481c00484c041e5445600784200e0303005442680003130307031a00402070f031a600603132150740041d1541d164031800c8401900503c01c04000c41c082e400c400800503c0800203c00300300c0c800e00700c1010602d003410001d02110030040c02c009560f4140405111a40309000c2903a5120042c6820a0071041501c00860807201d81c520b01e403915501c00f50074010381d0840d070307404003444a842581e51008180031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 858437131 1250 858435881 858435889
    0x10b1914120406061d0f09010b03030d15060219030302090d0f05010507020f0c01020303010e040302120403030306081c0c021003150f08011506090b030910050a0e0c061911031612020c 80
    0x21000c004402d85c0020400e12074213210305c560404802000412450982800682550710494072030700c21541d0b4240d01c40a1240b80b40c45400141303d140090300812204070442040c1002e402c100408050340001c03240001e545045402501c0740c1c20500b04602c4015a103480c5000384030a840500141c810300c550000980390001c0c00e6159a001039004d54156440c2030b43c48c0b042c0500c060b0044003075005000f03400c00001f00441c01b400080d4029036001c2031091038000000d04161012160000704007450310000c9819411000c4160003a0f415142c0040707104020b40c04070010312690030820480a40c460b000520603440f5507034501a201140c0c020071480d0f213241d04540070400e00d1702c1294086480c2c0d003810400b001204018560000128094603021040401d00c2812240c0c1200d100c0205661420790301c011172410841d4102d07140007a070b1158504600080c10a22031141c03015080200078444220804282d014810313500300c0c881c0d00007401e2030001c0501d080b070a0403841e00c4112006106504040c0504d2030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 858438381 1250 858437131 858437159
    0x515011806140d0828050703080c040302060301180f0608030c010b0609031c050d09030c030809060c03162a1b0506031909050607020d090e010b191412040606 69
    0x42c028440d4a4880059441100541000c4203000700d121018006003071401401c0d1090102c80d00f156070b040c0e5614003e2401a04d4040040c118551600041c03200f8801a110301c0c086905440581c08000c60070494040558003078540450103242490400c040010391103030002c041c110310382100e4000d120054019052000c40c1c003c803010158998007003407001c0c004d10304041010303001d042071307240403803038441c04500807819241242001c900040091300c0040901d82c0c024155a04445c1d00c0000c1d00d0300c0e060400032140d06002c098900d10035100f6403902107205500801a440445070b01d00c10010107031007044006490305007102000e4410042061911031a502c020f20342000b5928018011401c507182d414210084002e1454018200d582e2296460080b0b8020007039035205181603801011a044007100040c4030080542c41000c2d2114690014032101c1c039518141c81200d4000040c0b405071890300d03c4104c4444141c0328a8141c80140000c003200c40c1c064988625204074041d00341400440d5a03866038100600c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 858439631 1250 858438381 858438419
    0x60f0e040203061c020a090623010201020705070e180a0501020307020105060d030504060507060209061812030901091e03150204050a0f0303021504050705060c06040203061806070c0515011806 84
    0x155480004c0f60080d00c91109441140098400781610391100030b22011100190040d10080301c182d2903042c401d40c003008059803401400e03c0294103001099840d5543c90740380307015030000d41010b06e00151010b017591070040300c099160412902da0607442d0170994000e50054400c88015420071000807000c0c1043d405003200e0507070544d0380500d0075240030411101600004002c5490319002c004104183d983e60001e0310141111305180e0304030140b64070402410507040005604250410703c2100811780e04a11007400301e0318007000170900540230700c00340003041085800003484803040614200c404519a4040c00a691095404482e100d48031078900800e60f40c94840180183c0c13010100c2c60940584828054110b4801d40444004545800001c0c5094002c0c08105006034441c01c200029407500b000020f810910340242c00303c421034688142e40e15000010031a00601ca1034101403400c11101704050103022510f180b07030700082d5840740c4100d05e0f08031100480381c1a0380d0404074003040c80c25007018881126 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 858440881 1250 858439631 858439639
    0x5070e011d01091d09010507030e0c0d0f02030a0f030215161b02060406021b120a0201051b19060c031b0323010303110601060801080a060209030f07060f0e04020306 72
    0x6030005401e24100401a80045410800d00520008910244940c01c043d00c00f064114001140307403842c44542120340040691007014100503219034244004268a003461000361001081e140b42400d20509100e0852002505807064200c0481031000c4000c040c05118801e600351034900d03104850306a00c1d1002030f00c400e00c00d0f10b002c4501a02d081c0c0101010010a02c0700c40807d5a9010315400141d2143c01c55070201000d41c109100088207046551800ca8034241c08443c40200107c100714000d80e039680307400c0b000f0f06008002829a40504800341505500894035080f1030340d80404103040c0c4100b82211710100c9940d410310a080d000b5601034000e800440454288074030200804517000c0f00580340d22043c510821a5009501503a119118401d034040c40c043d440b540300c0b41c0d9010743c0c00c1e4a000c070168829800c2015842c0180700c25440464082c0e802504810003503119581200000e042c42020340e040300140c4240c1c4400030303450f600424270307074101041d54803030303003c1c070590b64060100303920085454580c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 858442131 1250 858440881 858440897
    0xc040312031e09020d050d02010f0c0216050d1401050412080901050912030a06030b0901051f080304180b0405070f0f0f080a050702070e040507051003090f240c09030605070e01 77
    0x102180c2c9900100415000512a2401c082c00c0d446141c1000780303d040c1c1c0b03401030751144901131020200c0c0c010f00038104a03510051140126524018054038140d001d40ba11844908032510f091000c400d00740012a8507080081080b4201403800c070b00d201201e44901e50108000310001402804107115492282402001420724507100620408035544014002c0d64425508d07200440440d985258140c82100c0d008000242403c20207001c40481c4a103c581300079200802d0400e002004000c001c2e501260084d09080d808007681c1c02c0c88002902c00002300d9078100d440c05e810094120340c043e0b500b2070388410035254013070b25444181044500004804141d40807603005004200c0325403040e44000d510103110301c15605502c1d00d40310200a41d1409135000c0ea00d9a000711801d10207072400d0030490300d854543d401c040111007031555405504841f88a006090001510f421003c2850b8880a40300d48034062981082501748c84100506038920710b00003980d60902d044001980306015142c45142c020050b103590710 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 858443381 1250 858442131 858442181
    0x1a0921070c052736060a1e0b0301060b0d0506041116020904020d0215040303080f0f06190e010f141203091003180b093702010c0206030c04031203 64
    0xa04440291501d4032113640a00c0c0c0460340c2c030590b45445943d540004545014195500c169858010b028003100c20312444d03d40b030095104181c40141c41c000420950100344900c40c4030000c0d00500d000e42c0015020b0308001102c0382800c820b030740107500c2413600319000c0180c06814501d00d803076409104440020040c6001e440005403410480540e4001d02c014070310b407074481d043d41c080784039540b005140307010030a0007240520416400202d16075100c40c00d00d40e072807a00c0c40c1030360341900c110340c0113046180160b6a402c0107948449210340c6450203001e11001c11342c0203503941d00040610f0300d05403007800011001032503103144516100130410764154260004504200100c0e0401021450300b110000c180750f510304491a5801080c400806014003c05072810307a0b241c01c0c13507400c1c1010b6200000b03840d0180d44550305002d03800c404040403800c091095a0b401d040d0000e10060380ca400e201000079511850110400c20400881001001a2031045032a400d103044401410340581c0c0404c500400d403143c401030810 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 858444631 1250 858443381 858443449
    0xa0c02030d020906090a06080403020d0203070b06100507061d1e030405040b18070f08060909070308030907080304030f03030605100c06020a270f0609031a0921070c05 73
    0x101e003e0040a007407038030803103d000034850102c84e804100410040070401c810b15805121418440c2c0088c000786185c01c4440d81c4000c0e03e0b4070002d101c1d0384540c20108203a0704951044040e580d0099024400b0401c101108006040d07112180e801a100ca00c150300702040664461510052070140c0f505c020360609040c1001c1002900c1c1403000990001c603038140b40010040c81c90149030141c00d068840721000c0a03202002008640000c0813103004051410500c600e4100020fa880c007280c5c2c1015603151a5181c1950041c10a8016031009040c1c5c8000b0030040140024404002d00e000d00c40d8038200442a520418891540805800540441e400102c1000404e440b0b400520080c609444d140342d48881400b0600180f04800d0381140480b80810424002c41400300010005803036981002803c0d04e1856882950100c5400c8105003040744000100e400540700700241c3c01c4140614506031440c1900207034001c030039001070000761070000506d8030002c0d841c200b286411214100c1c6101c1ca58540031007103030710 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 858445881 1250 858444631 858444637
    0x30706031512022403010306050c0408061603061d060325120f0803010b09040606020708120d06030c2d0f05091009021305040b2e021501030b07080a0c02030d02 70
    0x140c0c0c11803000400f1802c070f613035a4440d00080d694a501925102d504601785841107a10080116244100400040c020203400040e000e51180402c41c00300744162440c4011806044268064520000842103800c1c21264080d0014440c0c201501140c8018800d41c8044200e102000c1803404044501a4280a1320721030324000c01d5014000c0001104003182c82e07446103000d6009078400740e0002408580304089203002c0c0180b2005195500c002e12a1508040b052074440c11001030800e00c3c0180003801580301c0c42203410010086412100040d07007079540765020000a502ca07030b440145005801e40c035100c01c4c0c0310400d80c042500c5c90351001c40f8803141004203109002034081d00d10351188840704030000362160030340010710501c42c683c00c142d000e1034a030400707200c26078070044801445058403906031110751501078a040902c0480c215945400c80241805a09100c151900d406030041b568001009200910700c0075402450715a65003041075440000402c11a5031000c0700c240140c0040240045405140e006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 858447131 1250 858445881 858445883
    0x5040c03120908070f061e3203070309030206010806040816080c07090b040e12030a021303150c0f0203161b0504150509011a0301030618050607030b030706031512 71
    0x2082e000c0307588402101d464602070345e100c9610381c9045002400301c0c039481a00341d10f801c1c4074002400e01c1411403040c080c107281005440d0003d202e01116081141142c0b146000c03440101e108203080d42e904240034001d0140c200e03441c003500944101000001c28000c0007924502c220303009501c840c1403d0f800440021000f510300810307111944148060407103413001740120f500038102d1020005201d0b1138501444281d84805112009607080b01440324042580355003142d60080501c1c00040e0b9904007444259014040d68002034250140800280b010380082d601204621000751141440c1100d000c004030b0b0b0700c0c85250700f00119043c10302c0b0100d0001d028500394060420743c3c031103480030381c0381c0700c202040803a644442c0b907040c0700030415002c02c50340c28261891405401245846182c1404412941e40740d840180700080000b80e4440742088002d05102d00060600c0d8020309031403180c144210001c01070201014058824001c246000074060f0007440340004103405010f141c80c2003440c0007040303858050342d588 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 858448381 1250 858447131 858447137
    0x1205030c0d15031214040311031507050705100509031801091706010906080a170d060b0403060218060c070614040806070906080a0209130507230c1005040c0312 70
    0x1001003402030a0150b03410001c9604000d6003407a2a50800c00305020b8880b0669050241490900e100c1100315030842c1c080d66000b004503c514080c20300032a00d484080780e000e9005080d00402d110803240e02c031004000c605e019000b101c503a200130802e110200c1e1005e981154043d401000742a220b06642481d011820b001410840300c400d55811042c0c00070180c4404c0346c4c0c01c0e90001c0c0010302801c0f40500c101c0010300152001415001c010396550010014080e4490802d01d90115443d18800102d402c01d60203006094200c6407155981d180c81d0000e504800402c007d0384582809040b0716080074000d9421f000807100050101d2841d115061b40d0031840044040c5080c48104400314a1290400400d80601060303520007074218500ba10050102001800c2110224010808005166218034503510500c03c40b0000203840e89521031700752441c0c1008403000b80c0300382020006014440300c1e8000317051050008029034043d4140c494401080b1482118024aa00003404060001c41d207520009040250b080c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 858449631 1250 858448381 858448387
    0x1050703120e190302102d022a06150105090d0201050d05040809090c030c121f091b030603080706020a1101020301240c0c0504020a0912051b0a031205030c 68
    0x11103800c3c1008104000240320307102c0000c0300010150b04201040e0601540c900400148006038445a44040d40d284080c001e024100301c0c8403c0b0076920760440d0700d400c801c1d02020030300707030540f1803517030080082c01c1047c88290141000103002d100e507508032114414016901d5a1526a80f0401c0003540031843c031050f8100002405070000b0490b140c41898040c40c0110031158540c0e400c0420041c0e80071303009009048505050041c8500022020b040d160302c61586403528540340e403840c0030500e0b01c94102070041035078024000d00080d00241540640075080c02e00b981c500c1c001c640c1003401d81c140d640c10b120040181c041001544c0206805030f024001884072464040301920700e03c1d207000d0984e0405c0c3c0081180d200442e040d1441007000d0f403080e550183c01824403e82c00d920944480313104040d0380c89072500071031300041c1c080f14041c810300110020f8408482e1f40b821404c1941405d039a618034100c101c2003040402c6003121a80d262101c4a2022030392301001c006e2040e20712580840b0302d40c20103002d00d10102c1040c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 858450881 1250 858449631 858449651
    0x718061d030102030a05180a050d0c03032a020f28110a0314060f0f07030903090b0a03050f0705040b0301061b0209240a050f0909030d050c0301140a050105070312 71
    0xf800114061440c40b8400715240c140018841041d1402c01802d00e06070380058207080000328082404030105520303051211811410b400d0036006481c01c0c0703140c11003e01944030f12446100a500c00d200ea0880580c3c229200f000c0780304401542c40305200d5184a01240450b07060a07210b1503c0420b481d01c5200d203075120150f8041d45e01040c03c0303504c150001c4901d8050fa05000044080400640d544100580400380190508440121560340084c01e003508160b12880c3e0340041c107004045090042801480c660b5442e41013140040c010007042e503d2180405910010030b10140c4a4800e440a4481d481c0c440f510b10707460303e03009850142c1c041500385007184c00d20a91001580e01c1e521024820300d91400038400c5a100b07201425240501d01c140d0070302c81c82824109100e1500c5507903048124160036a0301c0380258840003d054514022408044480c908010030404410b40f098041c0d412140742c4541c800c2d04000c103a00308a000c51060003039500250042c00b14202003031086d003500d0840e00008000084100395 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 858452131 1250 858450881 858450883
    0x120031005090709080d050f19090b030c12011e1701090c0617240d0809061612020127020d050607030c1719020912060108150718061d03 60
    0x3c4441c2004030700d0142041080e0704043c0000b010800c50791501c3c074034040030341182101c103000703d20340820f805140f0040c008006009841007005811503038074103500ca2a18020140c1950301c2000c151050414200001414000a45000380d02c1301c8100310403180c1d181000c0e0820054101c26500c2c44c0c00d0764844015001050a52034904040c02c0e06036101621140c0e8410038880c2d02c00c0281148090144461482c03070104a9070f4591070801c101120751801144140c2003c044900414403070386c1c4d000000003801c0c2e008025021007141c0d080d00c100d000015641043d001030742243d14610204602d01c1c6c08507401c903040840290b40310000c0c2e10052002074081c9058a8007450a1740880b4080080b84e0781e60a2a103c0e03640007490200850540310b6088607901d071a107d606a90003240b42d031010255000721300241250b07030741320a50342ca0807440c9040301c50a680d02c0c9005541e07040300240c2115901440008544854401c1d5985171341c2c0f40a85440341c04a03440d0142c111403040d10b030b41004241a25550095843c1d0f54 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 858453237 1106 858452131 858452149
    0x70f05270a02130e090c091003030f0c15050603070b040b122e0509070804050604030f140d05100f030b24040e1e0120031005 55
    0x541400850180c040c2110341c0004031034024000c10138505816045105102c40b170226420400502c007441020315003a83c0c07103003a10b440d4540c04c0c804a400b80300c400c0107201c0c461411482414094503404c10380340031824a110041d84035401d02c00c0c04d00d4200144800361840061662400d0306c0c1401c900d400740b05201b000010b4030341180004454140d41d01414041401e58a881c0311150360400340341c00d1141d25400350303030f20030000d58000c1078030140301d150814400c4c4da00000034030007a03c0d50381382581c000d103500031160100441e401d05650648881009041444140e09000c01c031400c00005d80d0318100c4042d001400da2085034001000031417405042203400610050810b41106417051407010040c140c1003040d40c201d4109140e090f07520600240040501404098058182c25191002c0b400e82e80b5403c10a004441d4002c1c00035a440690002035421491150130502e50650350004180d4072a = true := by decide +kernel

theorem cover : BRFrame.Cov 858273381 858453237 := by
  have h0 := BRFrame.cov_init 858273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 858273381 ≤ n) (h2 : n < 858453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
