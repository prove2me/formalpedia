-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1651
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:03:31.31112+00:00
-- url     : https://prove2.me/submissions/4a674575-bdef-4338-a7c6-23b233846923

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 296762589 ≤ n < 296942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 296763839 1250 296762589 296762611
    0x9030a0212010c0207211214030f091c0801090f020c10061e0806070f030f05011503180b072109060504060506182703040801151505030c030c0c0303 65
    0x203c000d0740044d003030803410b80c08441e8410380103141522110f81160104100b43d800308102c5080f000b0345000300e6060035900418140380d8400401d105520f441e89040c1e51140c6802c104984006624086281d4007a2081094002240c06080180b264041d1500300100c3c070000044c0050404407006e03800740c40c000c0c26050394401140c0d510400d01c104002e00180500c1d020301400035400d024a0301c044265220b0006150074100b0210f1414240c13202d107e41c002d00343c0c51a0910f414005540c40d58416400e6820705041640401d01d402240200c4510003c4042e00c92a0004000b01d07447c0d0f42c200040e22908240c4204500680f4503140030782002030540320f0204030300d0289a000401d0b152a250410440e8009045144603000c03000040547e402007480c1d0036071080e8800c050801d41d1040c0c90b040350562880a080491a01004c500881c0346441580628061552004501c0180344c0c0d4203501145c914041520703400050b82040040d016000940003541c015100c058180e107040b00788001603007036400a54104540c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 296765089 1250 296763839 296763851
    0xd2303040e100608090309010509040f050709081009050c0904020a080703050109020f09090d030b0415030321020a141c0612050705010f1205040218010f06020d0f0504050609030a021201 81
    0x10b14605529002400c0d06042c0f8000340d0804102003582c030700175180800e0400c0400914044103840b01d804c5081c0343c4d003000d0400e20490500203000380600805001c0d0085920030415208180031503401684203a45d0008060701030b04e441d00c0244900b2490040042e82c01c070302e041c0000078440d0400c00080d0000c5000307800000700003410b481003001d148003102055201d906083e00f40883c1c010702007100910f110060800140741c0e00c4480202e0088d0030b101c03036003c844500059000003450b400c16200c40c421003540c0462170060042050b2501240a24010440003030701e14401005681c400d640100741c18802003101180c40e24441c052801a40c042e50850070b410403104216508104041100d90090442403c011a00b480704031001001e031a40f19400540c5151150086015902c4041302d0050040031015604055a15580403140540351441200e00520030413410071001c40c030a208000342029107995962505240c00200310458205010340d90b40f50150300781e0800180d1b43d240302c1c4840d00304024000b04071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 296766339 1250 296765089 296765101
    0x90d0306090903050316092c10031a07111606110a08090607080c0105090102130801060602030d0e010e010c020d1b08070f05070b07030905040605010e0d2303040e 71
    0xe568599200803101070030011100002500407054079440711560b10004006841407038115a48117145e444030910302d8a40d00341c00c205036008001c8600c0300300f940b144500d0f15140c2c0c18810740710b41c9440c44040c080d1091204508030f9520054040c40d0811113610349400034407001d07561281041118107100c02d51012100041005076005010040d51140d01d1007d007002114a440351072107841824244c41c400c0000280c00700030001c0c0b50013560000709100b00200403030300d84080640d000798071911690740c000ca034103080050381d41c00501440d03007982c505602441c107010201c01210050010342e100b40ba0710b9502c5048800b2004000d110b1050b41d400e15038001e05116031000006000e0603207280041f542c2c070140805400108080c80300320307454590b001400300c07091036050070070a041c17143d142c00100b07a84038001140c2c0d09055201c0341a9090b910300701c60400c181581c680056074003210a1201c81c0e0860340300c0c000700e404141d80c00007180203002406180380070500c045405a06651280d049010100501000d100c0c8d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 296767589 1250 296766339 296766341
    0x111c020c011205071d03010f0e012a020a11040905010c08010f060306050108041209050303030109090606050a060206070c020102120403080d0c0309020303070b0406090611270d2603090d03 82
    0x14022400c002c03c0080e402d102400421510144900d400301c82c8184044000c02d8800354007a03400744841020401c52008154845070181042c0141c400d000401840003800d0304e0141807070340b0303403010894008140e112800da4910035182d5800084650080d134480346000411000e0048042194150303071105180c0d07041042c08c0fa41d8201c103401810801d481c2660a10032a47c120300a250000d40050700c400c0301201c5040211812000c0750031540c0c143c040031000052514041c1c0052100612070700303061002035220402e20491a815100703800060707000740d0100c1c418034001d01184074100c5c018815a00070b1000190f5112240d4816401100d00c031500180342e00a1001c1881610b11050180c0303002d0010001a0300002e42c0c1b4021400d01030810361014011070200409075000354105d650207a006d0010001d003640303040043d00300e99901507021540401c41c0c51129042030b2007070400e0000902c0c11080d6121a19010440002829500358200128030000348500800014501c5101c00d800202010188140018 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 296768839 1250 296767589 296767607
    0x9020306070302030106090b1303051e01110a0f0503180321100b0406050c01060f06030c08090a170a170a090512040b040b0306030a0210020609120f0703111c020c01 72
    0x11040603c18001407002c558050181000c4030304605d10281c071511241031212455119900080c841c1c07003140b6482c1d40507281e4800784501100c00000170480304008802c0c0da20503205654090b4000b803801000ca400c214010070145801c0380c11034a404c00c1010f40c0703102c1c00e840c6a101c500b1340c80840703c40164035540341c01000da4966204d800394103407070b0065103406c0401d0103a000d140a4503051190200c3c0f908408042580484010403c01078444d0100b0f0303842d000540108501942400081d00da80005000140005054541d0075488205100300465034240c440864024241000030040c021001e605844000c40f0920301806503000300103061083e40c902146031400052107a03200010900c41009128002c0d001d0390200c601600e0a941d881d502c01e40028180560002d00a5109028451028004da0300040051052900c2c500700d03144009a0741658500340074500f10903a124230100411070000e48220b044101169005040b00d2001c811042c10000070380418903840d006130704c40203100d400b66074000164 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 296770089 1250 296768839 296768851
    0x905010608101820060706060b040510030e061b09040618050112240e03072a08100f02070213020c0c010305090a060510081605090a0b090412140d09020306 68
    0x403945851041d519a0640c100d5407040026203103584000b540396071202e004840c0d4840c1c2c804000c2003400c2e01e0321100302c05070304036000cbc2900841c0c44000d07882116020384103c0c0600340c4d02c1d0006001543c5e400072003035545101c025040c24031039014000d902140d00e440c083e803006018405010307404100c0d1040c9010840d0700c140c0c005498008051013071008518005e03a07580c030a04000c01c00d5010301c8000d01001000d80a0407800c556240710007e81a000c2c054403031200b040b0030340080c000c2d040144124010b0082c04080c1d02551446801044141c81c924020b503006900d80303040d860000d8201889900000e4003480c040c060101c501c0d8000600c2081c100c5c040c000300060340000d090410107820101d445030356038040d2200c0286803a5552000c01c0001030200d003200c001380102030468410300742d03681005101130703060f1280500032541c580215601c000c0038011030481e120040c081078480e03a1151200014403034001d0040e0240310718400d40c00c052020319001440610303284500030416010610616140c118003c040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 296771339 1250 296770089 296770121
    0x12130504111201030b040813030f0201020d08010b04060809150c040305060a020f090f150c0307020108010510050a1206030f0c180e121803071e090615050d090501060810 74
    0x801e400c81c00c2d000401030642e0b4004400b4140c0782c6d01c501c0c102041d03108010700321500c0c0d00c640c007000041003a5490b03030250042c802c0c2d09641d045815030909a54030300c03080c002c034500c50300180410f102d028803170890954021303039041c00c07220000740040203400e82a4041d1110300b03030180001030038414004200710b40764100b02100411071030541c1c070280c010303400c3c000c0c184c129110b07014840b6523504550780c94103542c00309000e80900179075506210203034603901e6015000c00c80c0412214000000d080c600081c42142007121070b182d003072a10340380c0c8204035114410a4102e040c4540e039840044003103180c4007440d5500314403406d0800115410441c0002a44801e11418210581400c0c2c079481003401c04100070f0300601c0c14130b2103141c6a074801000c49210307010100003180c0500c50a00002407252214441c0d0340c00d4419410148219502e85800c00181c1c0c80358043c2890349181503a0341d90030a40301d0740081003a00c484580002d10011160f50726825184030b5409224542e02180350001c01d42080e1064103c02540d000e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 296772589 1250 296771339 296771347
    0x103020a0803090a06210c0e041116030507030207030b0403030f1406030a06020d0f020d05040c05011b0209040c050405090105090c010905010e06031b030c030a051003030c0f051213050411 82
    0x8001401d1800300d001383e6080240c076104d45415030b032440240c00c06e0401e01d03500a001800b59a0b10080190365200c03205842103042022601e040c82c0c090085603445201c005081d44c413248140c800b03960a0740071301021411841104400000b00b03030441c4145010700e20995021890010f403402000039100140d4108020600e2001440340780c0c0d44c0005d101c0d51440e8000400b580702c409000301400100392107902600c0131800000d0b900503025480e40207a1250f07100780302e0080142e8440c40111103030f540308185c003501070340c940c0300c000003601d085d02009900c00d00c61240c0340b6100b80c440780440d007a19001e0743d1600d010b0391502d09104400005010702d8842c61420320b810582540b400300000d04d00141c0a410900820000001c910345294200b004901c096143c0281c6641e8100089021290b40c0704561901200b480c000c08100680c1980b200300044a0b010b50381da00c0b607112282c4800c00010725204080314244998425180c0744c3e444e60014003461003000c3c4031464500e18010601080d12803c2c1d40c10884004100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 296773839 1250 296772589 296772607
    0xc0321010608070f081009021b0706020109030c11130c0203130e060102120d0b0d0309080d03111206040e06130308060405010602031c0204050619030e01060303050316030f140103020a0803 82
    0x20304c2540152151420b4060360b280d2917800b5400200a402c214109400042c00f80541092403040c40c920065600c200d588041e0307942d40403406c071103000708000c00140c40300070600046050640088000e840003062801402d40d4447c00d401101d070111541c0000d600701081d20b00e07003010729144510041101e40030050291402d04c00017500c418004032050403040001c1090b41c002034440d400194a0340004c0e20400c0407011504003d8510f100520458210384580f0112440e103a110b4010354190750038604c402420000d8003e10118014001040117400c20b68610501c44440002c03c54107010f4007400d070000d291606103050041c21803200400c072a000b54100001040180c2e40081150f001d03a4600301c01401016400304400d001e4071540d8401648880d021680c030040f40140c420121820555840c20842c0000815503203003a20160701c800741c007061092001038901c0245000c0342403003488a203000103480400036201022956840f4081030464080001071045060080800d4081c05107030f002035050100749 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 296775089 1250 296773839 296773847
    0x905010506040c0f0c0c0f09050118091e030215010306061a0708160c0b0703030c110c0d080a09081005061914060a110d0305040c120c05060309030c032101060807 71
    0x2e41001004170044c11036041c0500300c00c00340c020305160032603210070542d0340c80c44002924081c060074918220a20800604182a100e5110310301c3e801450012003608101200c031160b160b08600743d00394081d03100d20444180803000f2180c041c42c89400001002400d0810010b041d03101c2064046202404001c090081402c20080c1e4503540703a90b500f221070070101d91610100000c6241d108044400000c90311004258041d0070411001e5403640e58171142c090010700c1d05a0b9078151070b4044d034002c0c0c4849140d00208440c01c0040c221a1440d003000e83c0f0f1141e490b50318510b8103800c80088130400755140288084d500d043c2041001400c0c2e03000030030894030f007051256400c01903c1c100741072003035500103209c40d0041d0241140c2900c080408054238643c40142d10301401a11040394121290f200c1501302080c02c82a00d42960314098011804031000f900344001e000b003590020301040300c0381c44203001300130f8151010401026104403444941c010480ca404c98000c120760180c01c182c003030080e80001c22401540c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 296776339 1250 296775089 296775107
    0x1030b011710080f0105070f170a110906040305030405030d030203091c020c0607050c15180108041401150f1418100f0f1a0306010e010c05030909010303030905010506040c 75
    0x1041000002616030035044011000540e203c0e42c0c42e0701425018506007001941301921525413912011511489140100d45a80300d002ca01c244101d01c1c000850140c020a0388010413550803845210b00d845030b1200050b0399508503600448240e40006028407a501302031154408094050a0075402c40c28540240d0b6150040e4015603140f0904034030141c071626208201c0410ac04101400c1ca43c0d0311450340c14070325140e00d00c500c030150042403050a403914200001c82142e2703840084004984560324038500445e50040f02500903211020000303c5074201c20303028864809803059685410005e14680980c0d09485c5007546d02411880d003e0300604441900d800c509044545801c131912a0725075200e5940c1e00c00301e01240c206201540202401041d192404034581090304c517100811131150248070714440c0b082c441150b48900246086450f40070365402380174000c2c0c0d014842e9090740e0400c0320f144089085000b0991040e000a621011a030080c0902889043e821250035075080c03066084014014006180e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 296777589 1250 296776339 296776367
    0x609020c0a0f03021207060b1804050606210d0e0108100e06090402040905060906061206040218092404140d02060417090d08070b1f030611280e01030b01 67
    0x1241e80342e400405109004051032040061403042c0c03580c03400d05003107009042c00c0b030f00e150052021401109594168041032031285500c00001e1030707242d8072401070281c918040c24409045070b000b041351040c83c001c00e11040024078910340d04d0028503200c62000401c005c4015103d10103401c0c40d09414000396101e140b4107640b20f0b1060344c0d030394032540700e601c00306004218010029049014a41c14883d002402203915405084115142c0d0800c0d402465207544030b00c802d540080d8484071244964400c9442c409206038042c81d80170544a40481e070302044044400000c4180e011007040804010402a8a440b006c2d07844000000400300c0794440b80700070b582d6a0001c0c0000d40402003209844d9081e10200c002c03242c11520180c041c105840d22071514054070b030040c0c0c1c012200301010000180c0300c0c5481000220314003040312000b810707882c03458844c0c2c00101031088025000c2801008040e0251004d0265908241c400b842e201c0180b01c0800801444030786804035550401d03051044001c0c45ea03230701c0b0b02e160800c29 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 296778839 1250 296777589 296777603
    0x40305060430021b061201050f04020c0d0f080a0908091e0409080d05060607081c09060c0507020102060c13030201120608012d0b0d080904060e09030408010609020c0a 73
    0xd02101e644104041d1442e0960399200036181001a14a07404501000d90006100010188410107800c0010324011100110591002c0c48010002480c00c50602518210301078001446c25014604a5062116459142001c2035110707024070032403030380200d9490f88120020300c00c1141d07070055a5034600903c14050b201380700d605840010b520b11400103040700441440213004000074441440e08802c143c01036002d40d0b041c41d03e40400140241040e0301102c042903800303080c107840c02c0305000740e000ca00317108248800c090650f181d6451002440612072801c01d15019290643c45280500c002850100b0003028074892280611207945d0400e428850241600e0342400d003241c0060007600c850000300780c036511210140d03092845441000d1005181440031140454030401c002451006000c1070b20782450055400c000341c44041404039450301e014180b8210010702c0800e54035921586501c050764280c50681c1c1c02d40002904228180d0240f0501004140560042d814021000d044a8850009680180240f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 296780089 1250 296778839 296778863
    0x608060f06061c09030905090109060f050301110a0c15020307121820060c071509080c010c0f0204021303030e01090819060213090504030513080303061525050f01110403050604 77
    0x600541b031510103480d0241050a15694540705000a80b00502c00c1c0b414010200c600402e09040c107000e000070003031010404526068641d1022038207150080350139100880d6050212a20400e80d000445c050101070f0380d00640c01da2400080011102c1c0390101c4d48030700800c10f1007603000420b030308030b0080c02861062100c901c105940d404a1303964461401c00000900400d04085500c401005c000e14201c0380301d944100c1106d413503000142e96040c3c0300c0252408504065000c2c0001440182d0003628184054805410241d45e4403051612401a030000c03008100100f42030481542d01c140c103403008100c2e080051006030741d00c516080801c80041130142c90301d500002c040c0804042c0c0385125004198404003004070780b23400d09000f0700340d4104c440d5402e106a0340b01c03070010b44060f00005403800740714001e0a4029285d100401101d155100c070a0b48658501103e940450301266500300030a42c5e130041000c3d10250f40454440c03800c54142c181c010081090a0100380086030f400224140c0c01076000d0410120303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 296781339 1250 296780089 296780093
    0x103050901020f0304320c040f091a2a0f07030c0b09030c01050f072708010609050603010606020616111204060c03020d030c050706020d0b040608060f06061c09 70
    0x29110305142d00c1c2c2029000010300c420010000714281c0c40780da01e00380c0c0c000750f0038000c000106d03040c00c81d40c0040002d900c81c0c0021b10080c90240c3c130220a07491480400900d0f0042075a0703d241e045051000c0b85000245c3e002041003240d51010701e0101816004c100002114647ca229181c80c0540c0140340404980481c4607420035001d03a8200020315005002111140741030403181d03649601c5090001030302d5007820041000300c07494241039809142152150303000000349602a40c61225119843c43c0400000d0300d000520510030701c03a0001402d84a40d0118151800c0d00525003520b0b41c40d0b005100315402181040881d81010b01005001002072902440e203102ca40b40c074510344800bc141c140851388000030000364542e001030300005803a00c00d40980d244048881d20950171510400711070300c0491420400c1d100043c09640c000c08070380c0b80590001814012a9000c00d0803150640c020300c03031139032011051010b00a51080010f41c4450110340c0d052404422191207000e9003442100f40241c0e985442620f41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 296782589 1250 296781339 296781341
    0x403030806040b03010e24150d150e03040906140a18061a09030f0a1101050c07080601080c010210050709090203091912110313061b06020a0509010e040504110103050901 74
    0xf1105900038000d011100e40410071984815071100e4510302441e401221703407212a88505141c0c030580c1110718203110a1074a4041c1311003024203180480c1d521070311494140d503403043ca00c501c841d000002d070b00070b5032a6070505200008441c12500483c0508a00100321002540c078414032200f900c00200503c00c042c0320055848024200d19008001c801304890ba09200840c84074020f4018010700300c0c201e80d00100841080394603085120406480000700e13007540c0920b0b5001c1c200401c0300403504012102c21a070781d00c1c07281e0304011003070b000f0000e940c001007044100d40d0b030b04120301d03040d4400550041182e4103014002030038001040c8195802e542d0040005107184001780001003c000e004003841801c001d80d4a0000b81c100d11401e0107401145e03d030040e02c54922000429206002121102c507424075080c000c0590300340c4403c80c850350568005e0680500010300600245c021a541921019192650300d03002403c9e85000811550290385000100404a0304407140c00003a118207090000e444e0300d40644080c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 296783839 1250 296782589 296782601
    0x25050c0613020d060203040809011403060a060f051e0403050f0706021902010309080a030501050a080f06180708030f0c1b031b0118030b10080105190e0312041b1a040303080604 77
    0xe813009101104000501060100403c0c0c803200981c2d80003011404145c14102c076010076510103400425080d010f004413401161035800d804000d003426400c01ba100700400844514800709025801c001003402c20401c4001c0120006140045024041c22402c0840c02581c0d8003069a00c0c802140c0b0000b40c00c4150390123030b8032081c001385d0000200d55035042018170203005003100f80704082c066010000e0024890b040810510703404031a0001410f410780320f00014100f9400c0786a00d004160140c1c20f000214054208020f00d4603040c24203d10362120500c04091781401c042d512210ae05a96240903840782d944d000c6011229514070f00075406142050ba00126410b120f58207002d0704820003510b0100501040005c0d1130b1180350f10f40c403400c0800c0c0d150410385003070300c005a032048e21554401c113022202c10100d80200640440c06011242060504e00818021180a8606842e4a080d034840111f480984541e130300d01038400e26a500c02c420109125101e0307548554440070303040141000200702c1981d0b0310b41040d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 296785089 1250 296783839 296783843
    0x2041a0306060f030c09030f06090307110f0d03020a060b0103200703030609050a0605090907050f060a03110d0c02060609040507090213080706030c020d0c05030a08091525050c0613020d 81
    0x3c16143e14001500750701d41d520803914a4864481c000100c9041900002c010784600030520107136003448050707620001021000100c0301da0040000c002c826141d12805510f400e80342c025402451800141e00748182251010b40ca07040c10942400d81c000c0c0036030080d210900c00c40c001015200c2d5180d00360f050840090034181c1082c2003071818038003032000c0070101d80c10500648604441c03a42454440d000415a1201c1600c5a41c2d0810a5039150f10210b207040c00144c1070807860f506000c45c0d61207510401d035520b40d00c050360554040707503500c180e840c10304d5040140690084c6d041c0c07000342c003030304154443c3d9035201018400c00070b00a800280d1400c0d0b141d040f82040340140580000c5849443d03c40c040500680b0310580510010300c2550144813843e441039849104282d002809540340401440f030032600c6c2540180b2f4208544034030344455010341100c07980c203441070300d00d0388400708800c076408000030180b002c07010b80000304042031081010702d40d000f00340b4503000301001c0300e001c6a4442503c00305050f48422000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 296786339 1250 296785089 296785117
    0x3070b0d180c170c030d030209120a06090b010605120c03070e120a0314030103150504080702121605032a030f07030605010510050f0703030f11210a02041a030606 71
    0x841d0030002c030358800e44291410a00004880915101d0740c90b5149502030071983c1c158000b03481d526505029500425113840042d08100181e002c02001500d00086810100c81d06a6180604420300500030780c0540035004500e000c600e403854048142c0a01c2401a160752102000000031a04a80c002c9900044100002c0d00d01c41000c0440e0300765a46a810740401500410001452040180085000c683c10303070344e00140e0304c0c1308030f0805212400102001001110541c1c41080700b100503179612444002402d407481d0003007240c001c4810852440c8500c2e54050b43c040c1c0e02c03810b040d0701d00380009030340020703921542181880304860002c000382c42c2401e5140300290340e004025020003486403582140313041c1c0e0420303101e8403028000341c5d008460503c00d070107420341d17490001c1c030150300024426000302c10f61416011004c80c024062009100b8250f0001650a000281800140c01031110310382c0d601341d000d01d010b442103080174541180c3c000280c0c100c2180001003100000004c000e81c1c0c444069940074801504 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 296787589 1250 296786339 296786381
    0x181b03070804060c080603150c1e0c06060d0302060a020c030d0f02090f06030112060b06091f0905010504050901170a05100221060607081b030313050c19062307061e090203070b0d 78
    0x400c03909940cbc09801044d4480c06103c0000f101401c0c03900e84810080d0340759004058598402c0b0900e8000d4000340003031001c034081081046d174801e07464022100c4108058400581d20180102081401001c00050501038003090004100d003607600412481000e810000108580c01d450002030554400c1042c05036105a511401800c3e0908510166a00086039107030403209549800c01551503000ba8428698010164001440041083e54003403407940c030140d044030081072044d56002d0500074000c10303282c0c2e0b5950100301c410011564090003104d91100e10b052003094105071011500c50721030f048000c0e166000000b01d81030043e0940c0c40e0111308009110580c0d8907030500b034545003400e85203d481940e00784104140d18041c0d2512402035074012200c08038403040a864808107880411707445690304191704046030049008001c6400401079613205010006102c0100000d16846208028a050740180f90481000048e01c0000e204400d4500c2180c03056124403283c24800007514045001003002d9120360 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 296788839 1250 296787589 296787637
    0x5250e04140c04050907030908250c1e090b0a050108060105040b04090504170a0905040c0c080708191106070c061803080403020c010e181b03070804060c080603150c 72
    0x210140c400e680b421905c584940d00d41141c101d064a0b0010800752480004104812112440020092681040100c088030304162620380c100f8904056100855201d032111100407081d400040c410081e10354804104541502c02c07021034000d80880c0645814017440e4404a40641c1c0201b040e94010016010281d5840b5210034600000d4002034500303c2d182c644038040059030501c91000c3d14120f10b01e03552414440c0c1d15100812020f4500314131020305201543e00980085000e0200500025014600700d603510402c00d08050382084181401c1e0080000c02040d40040d60f60104680750014000e190142c00600309007455402012028001246009404070303110405801c410594802e034000d800395000e44910500656201c1d40420b2580e43c40640703e0004488449140c10494001101007403003912080e001e20450041d0f8019030304030f40402d202200300020010580a8291100700e64035103810f0034185440801e503038008190000001c0c00e210400511119880380556109a4000654480054500f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 296790089 1250 296788839 296788861
    0xe010e0d0c02011d011d060f070c0f1a0720060a0c05010c0e1827210406080601030c210903030e060c090105030403020c0301060f0905250e0414 63
    0x1c1c1e02240441c0c1c0101324407400c1e004810402e0540c09060710752500035030000b0f0700707851386001c000250303507001c9003c0c003240003040426800f8200c180c1c443d1000750841412b01c0403200b1140540c1e440420302000b6040081421410300c1d0603946156840b000d400c0c4028140804081d1901d00c00c06104d40002e0003150100010b41d1000b03499180300d001d04020040083c0c04041100e20034040c0c01900d8020f03418410303070380e40002e0780381805030301110000c010112218003e4050000c81440381c45802c041d8002e13881900000c03800b140c024107035524290150b19052038042c2c094500c000c01030103c2d06141d038602e40302d04003c2c081c05803079000300c00008021030500c09255174038006040d5914180c00280c9040d103107004603480020304502840204001e942040c4040700111504c0e030000300110118002c03010b001d2580d440034098600075004d50303550b0040450500850740c1c103c950080111224080c85046025440650300c03000c06071540d5841c0207403902c1000d401040140c06100d1506404c0300311041000032481ea4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 296791339 1250 296790089 296790107
    0x5191106131d0106120e1c0306050612011805061806030c040e100627020a051308150c0306100e0406180615020708060a0f0603060e1b03070e0a0e010e0d 67
    0x403d480395000c5125a49016003242c0c12101c29085030750000b40c2036184440e1f64965410010990314010404513224004106582c01280300c0c03151034822803005001c445d9424200c02c95100e9003103800c208501d42000011001000d504880801300109800f080c06514107100040c0702c4100600240b10480c00d14403c47d036502c2d0b0341110300b5801d07072810340c0c045010401e8600300b0080604180422f610349031200190f03002544203120190601c6802c2003d90306411846018400a21400d4043e111810070222107600ba030301c00400a0300d41c0203040042010369651128044070f095010b1502003107080c0740b000860000c3c40c01d07400c000464803032180160303910744690704440184c440e040d41c0803006240e0808160780c4c40703040740541c03c200d030000b400150500c00181c2c00400c59459040b000f041c1e1079030b60346a460440e01c412961045542112640f545110100c50100003044400d8000f410038528000320020b503e075000d090a904180c40b83c0806c085032009401c0401c0c506400303070694080a003900405008503030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 296792589 1250 296791339 296791349
    0x110304031704020607021002060609060f1318020d050105070e0607050d032004121b060f120906020c010f1d0c01031e0507020304060909020307080610090807060c05191106131d01 78
    0x11681c00180c1d41d07040003040016100b0018003100e0001d400d2580800c0504950400d0103f20700041c0c10710005070b0340707404198259901074400040c103410160301c010801d5419503030440c003402081112200040002172202d203030aa0515002550789980804d4298030301d00b0402204202e107000c41c2c00f150060340403000094081c816000a040c0f02d1030304000084c83da03941c1c4038007404030740c0080956070603c0c06045880d1443c01c03100d03000514000701d03035a9881280c0100101e896240e42d21605810601c0c3c0f18410341d038902203060009001c1e18500d1000982d207480e6a240e0904054486600d46810203400b0b00720050340203640010310491a085000a40e07030b4005209040000b10f0001c40064030381310b140b0880303000700103036a110183c0780c1c1c60400740003031905481c00ca0020403140d5100000d80c0e81d02402000040c14180c2d8400f40141d6950800d1481d01e0ba07002c505002c0300d40319841040014049214854030301ea8142c440740d4132031030207001321150921250b11001e0707100031070b01c0b03602e0055044100060583c0c2c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 296793839 1250 296792589 296792599
    0x609060c011d0d080105102313031a060117060d0303020706060b1e0901090e04051f0501080c1e1c0c0b1b012c03040b040f0305011103040317040206070210020606 71
    0x180c0d81e1010007008041c110714040116801103030818918804e10619071111040c008c102e40b41807611284082503145070b0f442584c1882e40081d02d01401c00c6800043c1e0f810240c24070348215201100b40221500403005040e2511412025a6103030801d4000d805650140350004420450140c2c0d42d100c0443c00e41c05082168600b0b140d507007508036916403440c1a00c1001c041071752080202030400740c440b80b035110003901c190340034854404044c3d541b515407881c1840340c0010fa000410154901840203242000c2d50a80c2d910800303401c03900000310700a0220520502400b12006c5c3d0070a480c1a1120824001482c0041d0002c098500b0102e91114034000400300009100d406603010026051b5240c22500c262a0007170852804e1203880010f01c45155150300c046400c5026640390070340c0c6607034105c0c89038030681c41010340340e801c8102007040c410700384201518850303580c450900c0c61400b43d4005142e4644581480c010711010400700f400d6454a50075070b0200b580c05000181c0081c01a08040d5603400e0484641c3e11070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 296795089 1250 296793839 296793841
    0x2030901060f0b04030b130f050a021f0e04091e0305070c051806190f080a0c1a0301180603020a0b070b010807140405060321030702120301050609060c011d0d08 70
    0x42d00035581050308450300048110f00b09800d46d518007072422800b5028503e0300458a160b40c0204290407400200c0910500040031000030900c140640172003105803041c00750000d0082c04003419004040c07800b444034115030010b50b81d03000e0b241c002746079030340b0b100c8a00490211101103010540c00c08010100c0d68026142144850741c1c036020002c02c1003481000c0e178440300241e03000c40d125060030080244004c40740d100d5526822385401840902c1e1009511002950780b2031004003060060280c01c18002c0c0540c0704403505040c0d140ca0041d130301072106105008901c500b01e012800c54460980c004006584c2c000c208211441d03070f940d00e000341c1307400007441901c03210712150000869a00c0056040c1c01c407000c40440c0c4c05c0e00d103032078820440100f000901e11074240c001e002103480070308580b10000054143c000c514613103904050000a181c5a03d050004200d002d00b0801170009075070b03c0041d14200c00c021240b0720f0f501c4103420b01c6503000d00101c071041e41d58940c10304d0003154101700100c3c03010307441202ca81c0c85a40d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 296796339 1250 296795089 296795099
    0x121807060206070e0a03080406030c09081f05090705010212130e0c0306011206060207050103021b0607030903081012020909010f1109100504051e0d080a02060109240b0c0a150203090106 81
    0x212650f200041034007e0400040103024081e4000052506541c184428816a9012698100f181d0003258080d00c640074036864841c03031214841d075608445802d00034600c0354107000011751340d4518003114000c1280b010552003001402c043c03000028085807110143c081c1004141d110290b00183d410901081ca080b000039005040c1c0e00c40e8001310740d03066005102603880c20340190300950202074498a000c0c1000d41c250045081040701a0051080c0e68000810004d1030a00820302480a495809201da82180411201a84a400b0700010707170104c0d540705039601d681d254180100071034040c0080c041c0c104202034034500720302c1015000c2d00100ba10744d01d500da035014400f00e5a40c811802580d501c000f4103008000100394860701540d89004c0034080c04641d078002d0300d840c6402c0d003200d0506001a401000107000c448424080c0c0401547c2c0c081c014004040d07880071419844150b40110b0300708620100342048009010401c80c91641d802400c80304000f12410b0105021354000c1342ca00450f9070a00b000090 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 296797589 1250 296796339 296796349
    0x14032203120305040c06030b06161a0f0702060a050a091b060f02010209090103080f041e0519050d0b0a0b06070b0a0e0a0302071701111602091b121807060206070e 71
    0x1104d80d42c0300c00880109403c00d00160028019180103d420000503c80300242d041c004c11510400340c0a10000118121400303c404081000103001c030010807001020320900c25000564250080c4001002280503075420744d140f0001c1027aa64060304100020020b0205003c00f4203070402070340d651341c2e11f040140c400d1000590030303842060380d0307540c01c81c0c1c461b0010404920b0440c091302100305046140d504c1c043d034501d40ca42c1901030301040c3c41c0345441c000b5410002031503d0644d5900044469141c101003502d4000012040084040050241e08400b000140c0f443c07900d5004010905c80101103589402480c201140001c2d812600c05031050700c0c1000040c040d90700014105203283d450b500810320103087c00750a1461101c44000d4100fa9900d0b68803500412141c40003800c010b0407910241d900399011401008a141d01c040c040e44103070300000318a0b074280140401200d034180910b103040002c0d522041125000b00c0c960540307003a10342c0600c1e2000720b00107901064841c0070300880e42e148241034070383c201041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 296798839 1250 296797589 296797591
    0x1e03020a120c0207120c0b0f0a02070501020c06070818030d03090203011d03031b0904110702030c0a0b182b0b07091203030b130f0c0f08010806010314032203120305 72
    0x2c0980c0c00b90030200480030b0b00201540449105282c0340c1041d603a00e443e40d20326500700007401e4100400210b450444940d040001c40000c003424070003080902d9a5a01081c6544208540504504c13000500c156a841a42490840c80b80018048840500031603900400a0a01070803c904c25402d2184104141c5000c00c00c5001d9020341c10065403650b2585030020750078460059061600c50300903c2150a83c0e50b6a2082c003c54612409445503030320320700c0c41018149403031030049a20400346030f0400d02240e510300c0d00b501c041140082034034065001030300008021440e100c0b040b01044000a003500b0041e0300030301100174034510850104003642c4480005403116039007805003048070001d0208040100b442500050090325014101031001100d0402240507a0f03203000405060546845900900c0769010400e4180f10100c1d03d844551035041049064441c078040c44080c1c03c00006050300d50b22101d080c0203d80c040d08181002c0c401d80452040141c1d1003030120702c01540e10200298040c030007113000380111 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 296800089 1250 296798839 296798861
    0xa2006030f06010c02031608030d0f051b180d0f0203012304030309020a030b071e02010905070306150b070c06120504020f090403020705040204031505100501050f03071e03020a12 78
    0x255580741d40300d02c0111002032828406990500c1014241d00c0444258101c003005846450050b5a0b6012146c511009691005203407100207403505042144403500c1000d000b240102c800d580c196500403072079412405840883d19a030b4440d030492420000c002541d08440e485a109500034044102030041c008803070006000c4c03000000c6850400900001c2c441e0344190417007032004180c02c030f641d9181d0300e400300c9440342201d01001140c0f14146010300c01c403404039058040b101601c02030103100066a100341e151210b5100040407a5180e0820b1503402c251403d094028002c4204d149072a8003040c140100d00548511074400454000190640080018000c2601c034039006002c01044003504c2091202e4048010803e6045019103c4082010b0395a40024002507010303100402401c0c1800c09824121803015040600c00c4241c07500c1089a40d8002c000c0d10092075043e10030645076a00d0318016140000408080214110b2001111045070780507809040c1d0300c43d40b56030380c0d401c40e000b01201d602111240142 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 296801339 1250 296800089 296800111
    0x403020a18110703030b01120e070b0d0b15070c050301050714070203120c010609050906040b1605040801020d020309011d030d0e010b03060f0103120203121602010902030a200603 78
    0x24024102240c4800240031520400028840711640c460992500a00c1e4203e00190710b5005140642d03a0044280308c450920480400040f01d680382a03540d500250300c2400c0b1541c0011900c07541c050590360140000b0300303014006501000d85060050015031082008880008904e5004951030405110340d40c42400e998454050501400e21014200c0d00508400c0744e052007039019050002220720302502d0304864003000460001e06140041003a5600105403155076840a010000482c0245681c2608030100119440c81011800030480d40e074821a040480300d58000105000020025030003140714001c0b580003049001e015075442c11099a80140c1d810700ca0340144050700da4040300b5800b258203030f00c00c40300002c1d41040d8240468109103040f1031090b1103403140801007007404004103806200f10703001d201031031900c1c12010320201150740c050187e841160140700f03080d200341d00035402030802c02c0c0c0003070440e1803582441c902640036064034440d01980800020b40c0002c01c1c10901d003074034020796501b64 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 296802589 1250 296801339 296801359
    0x806060405060d0f090c090c0507020f1009030803090a06050c130509220b0912030f0109200711100908121303080301180b01110604120212161205040302 67
    0x10030030625400012002c1c94a503a100364031307089aa802d1107104000742c400c40d40050050301d45000d00b4100c490101035182401420020000144e40f001d5412000c0310003100e05252640001d01c046800d8291904010300e000c400000f40429400c0000e9660900c83c4600001d00682e41c5004004403507004020350714030360315171400c0184194030308804081c3d408864a0001810b01c4c00c0031090b100007407065232041d44e24084541c24001816400c0c40f00000100080300960700d0b6041103181d00c030100d41e0510802e2012951038000b0088100070012030b0707440c2841186003e843d0001410060417030050015198841d480900c070701c28145024100240c2162162006448101d280d5070b16488079130300c52101203800c840050303800310008400700e02440c081c19032420544000c14543c80071004545007212150b0600004820351151218005412503200794440d10498120f85686016032802280c020b42d103102c1100400c44001040403495400c503d98001c0d02e410007882c07034140c8107072854816808040e4104003440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 296803839 1250 296802589 296802599
    0x1a030f3304021e100c0203070e060a450b030d050d021303050703031d0d0b0112150f0e100c05042706060f11010b030303060f1906090509010608060604 66
    0x1d00b1500c4942040e04070fa40c0c15105520004014014140500c004514542c01d890290b0908004075405000148050080b505044000030341c0d03400e0a00c1404200c0d00c64a1a070b99032241c1111f2401140c0d4030302151443e0040401d20301d180100000b210300300d00c0c90b00e0003400d040c00c0d02c0d0001c1c4114a40105488051802014030a004044d500000c81c0c1720b0300c40303050303c000400039400b0404000154001e60310034080003140703031000800c40d0f100803030316105d0010014210046404014090b0443c3c02081c100c1e890301805217825000103044101e20140d60349802820074074448179030400f1540000c0003003a80c200c2143c481d9040300700d41c00e03200f00300f0003d1428071052000130901b8031541040d41040c0d182080312100004404c00f5280c440d041100080c4808240b111542c0e080740e400c851030915100240490f0111402180e601c2c000246010700c42d92407000e52200c943c69860529229244a0408410741501e03903201030720000940c031a442c041c030580030001902c9440b95900030700442000741000c0c0b501c0c2c506 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 296805089 1250 296803839 296803849
    0xa0504021003020c120a020307051005010819031209050102040614070f030c05100e0c090c0c0d0e06040e100e06090f1321090801060501020a05030d1a030f330402 71
    0x1c000915035100311126a18030210260161144581d61f90003190345641c03a1500c1820071b00ca020b0958492810701d130051203610400b003810b40a4020000c41c00b0040c61281c03c1c11205040340d01801c00c2c4540ca4170582e001805010740080c000e58446459a4520082d140e0b02140d4030321841201800100c405c20444001a101d0a80300b0422030141084481c0c0c403102c2503480045814101038200c1d079a100404104c51421b281640b030341d20000301d1005601f04081c0000060311022a90999000c0000c07800f5414180d640361010b44000e003001c6010b08040d440c0c0120800e1060625010302c507441c1c034085002078081d10305110b00d24418890303c100642d05894920100f14001c002035030072903100c40008002410084040f01d65820700e1413583d07a11300158a04060790742107071000d420950440d04007401e41404141700000320b8070888143c14001407402441d4a4002a071050303c505998140100448020703d8480002d8000040154200c030000c5080c1c00107041e080b1200250440c0000c015000c0020094500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 296806339 1250 296805089 296805097
    0x9051c0503090306090705040501060f120c05130306050f0f1605090103110705010c17070e0f0f090106051309050f01150e1c0b01230d0507030c0e010e0a050402100302 73
    0x10a108072401c040d901c500003410322034200d44c8181c0a42c4010010001450140204c80c0108543d0600105d00e5180a10083c0b5a101c030002d81d007016912556800b014030f1043c001c030b82400c0c0f01d1203080340e0119101d2500c000501002c0e903a9607080181c090101e500300c00d42d2113695008041141c9000050310348020203507160780001c415075050660b02c510169413051802d001b052810b2140c0000604818074060242110302080e43c080c250790300c41c10400a1081d00003000c00e20101044035446c110082c0f03000024010840082a0340c3c100d44050b00009031b1a4206000d00300380754040d0b40680701c0f5511aa030303160480d40d0444801c05401180401005941450522600b035005145040c081c0308840f60046060342e92400855014032240d0f820f20380500881c0a2400e025202030040e462510360300801c10100b092080841d40c2c804c04c80009080100f003020041400255441421603400c0303996406611110340c000d10910b41c2030710364100060f89130001407045500c5030754000c04001038000092812002504 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 296807589 1250 296806339 296806343
    0x20a030c0512132402100e0f011103010608012907020103020c1b1005030103050601030b3111030129031911040e0d020d051e03070c0b0709051c 63
    0x160b0b8604502c040c01140007403400d40c0c0811029046a03103040c0783c56440319503d03403e00c5940040c034866040059400302d2068030340c03070b0040c0000c42c107221074501007810300d49220320000c559840d061203401c01800e208091812900c0c00c1d103404c1203517a03842040c1043c030b200da008203124032000c90040140905003080540707200b80c01850010b050090448ae0f041c0303423042517004083c0a042d601112002c51500c2c410b441030b06d21543c6841400c2d54516a94559150707018007000748a1f407070380c42c0050403c0c44000800380d1125500e0404440c01180b402900080c00310107138083e140b500c540728503031106050500130b0303102c0040200030000480700c8480c0785a010010454000342e150183c2142401e80140d4000b402803a40d01072444840410010b00800086174222000002035800c03d0b0300b000d10300b070b070007088180f00d940c80350820640e40c10480541d031411303d80884440103240808002d02a1440d484059014810b104416001ca151200308003690300800340d2290340d0b40182040c0c0034401d2900310010750704031a4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 296808839 1250 296807589 296807593
    0x10905010906050a0503190905060406050105150405060706020f0a09031b261c020c0415080706030c03090b190e06011203030914060708040c050405060d06020702030a1506030302120901020a030c05 86
    0x42c47c0500310500341d070680e4909031990350102c4e013448180456442041e00401c0c044a0380b41032483c01d40d00f40102070040344240e40c468000481c009013400840c0e011540300041c41d070f1401d99600703452240640554a240800e8172820030400e13601c0300f40b045416030082518114500b500640c0819a039141400a1511035a405401400c07220241c11584422591f000e100507005000d0380103940c024070007182c10005042480e149004800c10107a01c012403035009a491070b00c0c02045010081106401802c3d41c00002000445c03042c0401101c1480d601445407604d000400034050255900b0240c1d64801c428000c1c052134205694109002034020340c00703040703441c0c422114001b8900a44151a08000e0200c82c00000b00780414200304c104040c14615a002d05030441d0304004600b403640c0400ca082007203c1c8010851a400144079056550410400750b40c41d42c080e82820061f051002580302900d00ea100443c0544900c0398084a16401403054030044101a4014074511240751802c50700f0a00a0384140c1340c82c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 296810089 1250 296808839 296808871
    0x305071a181201060b1209160e0709030b0f010e0708040c060c0c0b040602030c19050d080901090506091b040506060327030309030403030f0305040b0105060d0f1505010905010906050a0503 82
    0xb15000e0098200400c222410142c40350000c038003c1196620007070003032400e40c01c07e83c0e540d54100407251058007610314650b8a020b5542c0c8e50350b4213a0b0090040e03000509021b01040800030541d81080103030303058408000200c01c19464011041d0781242e01520020880082c1410910401d48a00350400c0c4640c0a078105801960f51903000c8401a44030fa003215005800029200005400401c10001c640c0e1420340d40144030b12a90b1960754442c240c140c0101c0400014401240c100781c1c094100c003214a400400351080b81c04c1ca48c00c0c0caa40c0720b04107840d01c48429480411401540340520400d0b00c56403001c0d01c000e01d03658480d000120203200c10418040218020000000c0304001000598400c030351480046980b1400c2d07040203000c05902c2002a03003094140300400c800101d0000c0900d04440068403a140c42d901d4000c9040c0140142040d40c00443e86070108080c9c4c0d03000407010807411640280c845e9116a61244011141c0d0405070142402281c2c0400021a2442c0708000542c0e100e03040d84095521 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 296811339 1250 296810089 296810119
    0x81f0911060a03180b160f021015080105070806090105030313090e0f070806010603050c16030e01030b040906021803060f131b060314090d090504050402040b06040e010305071a18 78
    0x4c4030b9640c90554001040c04204014000e940c1e03009081c081c1a81006400c40d920440300a51f110001d03c0c0da10811510b03043e111130484040314078070001d8000140240308500d403c25004181e8a41144c49501c44c0c3c010b900006602e04021080341e9080005080040d000ca0403c40f156010704005640003c40784034894059420718400d010150107028100080d24042d40f41034402000d0301c0000e014848012000c00c02c10030840c5088d000d2002440e8107041c00c4400c40e2611005070018502514001c0e0454100004002084540d5005004c0401001d1140c0031107642041815515903040b0780640c0803202c10408900492281c2c0864844c280c030404c800500c150045440151100765030740070101003a12144807481c400710003d403a0b50701c031400c440240003d0014000041540200744205405250381d03038042425500c41d60404040018042c0c007055403160b40d0800081520801d102c02e881500401001040c074072684400c080c07903159000c0006040c2841116030703003030400d00e80821980c000780030401552 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 296812589 1250 296811339 296811371
    0xe030d03111e0c010e101523150c0a021302030705070201051602060f03042907120605031b13140a0506030a060f020c070608010e0f1f081f0911060a03 66
    0x1900c11008001d0000900002091800e45040c5c10620141031f0a0040c01d1000c0c402400c58002c01c0800203a4480459000b0400309800e0039214015a001e2400021040200340b4005540341e8218802c0c3d9019403d4405102d6000803030106030340c4a40007074010028800590310440260105180700d0f00140c03d041c0041d40040c0b0300345e00c42c0040450142000c000c0109018050801d0111940e40484981d0000078818884070301b00310051046050220b04c0f090600034984580c005805020042c0072110007201c06225521011f00070f980e5948141000c0303000043c210510b0040f10020030403000302d842640c50b2840c1c42c1024080c0102000d4151241001020104843c0e0207004d1030038820b0031005035600c2c588a140381c200234080d048401803124000041012403441155180d0024102d04602d40310f4407080ea00400c1c18021440525400c4280c1c900446c1144010a18036011000e10051882c1c28641c2c0700e40c64242c82040324090700d8040e811a60305840c0c240780e4020100c0ca9001e190014600d00d0f0010550 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 296813839 1250 296812589 296812601
    0xf0604021e160b060f0d030516050601140910060e1e0d110a06090b030c0a0201090b090d0f031107020f04061703070b0f1918060203070e030d03111e0c01 67
    0x145940b10481c10907410b000701509035580105056401a6041408201082004091b0407000b410045c0015184c000d6850455100000952000c1950403e50303452100280c040405c5100074814803c05012800020b0200740420031907411341c0380e0009803120b140802c84031501503540b2208801ca80740300400c155076408c2c000c0c0c4c1c44c1481480d848001c52103440a0201000094111070203002c0e03540400e10242c01d8090583e68000411000e280c0e59042e0400c00700e01410403194000d064036002c7c1c1c00c2c0102e190010511415801060703440c54850300f0385503800c40c11345209209042c03000a0811014000d4201481d00200503400500701003190303959901140800c0071021072121064102094550805c041310bc84a900b111a000004a082c1410100350f40000404105030020759038802903008002c0441001c00714440c0c011f0303800c40d1a07140902c030103442d0505c140386061190080c0309200808038003070312a80042029800c030302c5040c848040c04100703940424440328049042e0600c003208550400340582 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 296815089 1250 296813839 296813857
    0x30804030306181a01020c150c0a210e0a03020d060903031d010b03060c030615070311030a030504032d0f0201020405030109050f071a191718150f0604021e 68
    0x41c0d0490384250104d43c07525468103941c1150031058040510340c1c4e520103140201009444e086564a291420070f6240440b201001048101038240d03a0003038852441c0d441c024010a6265016800a00c0042020710724680c08000d511071510310040e80440c80340e50041180c140b10b8240000c50364002c1c4800003d5002440d0342d50b03490782d11000291101d060900050b41c0100d0990121070550401e07600141c120a8440c0310012101d00115804c024140706040c4083c1d40107541c03090380d580b0210075a006002e00411941500801c441d50450420f03512201640545912041c00606018000c803004548840500c580001159000e01005c0b83e60390302032203100d40f868410740060410510140c411400c02d00c09604c02c0d02d8803401090350b84120070004040760a41030401c20303940b4000b8011142070b030f00c021848404074818a400001c00801a441091049030f070070811341101c034552106410240404012950703006140780710b601203802404c0580203002d424892030721106103100d0302c549002d5107030403010b40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 296816339 1250 296815089 296815091
    0xb060d060515150405100c051006030c030c0b160b06030a020a0e010603140c07080a03110c010507021209030712080f0c0601061b0b0f07030609021c0e010507080403080403030618 78
    0x20b00d81e103880e0040070400404100d0741c00c0303030902d490080000d410402c0b07441e0740801c7c800e2900c280c008100041c4815100050080070401155450342401041680c0c00e000444c0d00104011020074070000c00000d540c81c0307000c6070140d424404295920000c961101410094040c8903880c040c00043c1d40c0c140e80507020b404094015079066240072801410b880040303000700440710701f41090000e80030444e4100d0300c00f181c00c03031801c582d600f401000440c01008210720501c1628000f2461040c8140103410003802000c0c2a0b080310030810f060006000d441c8241d00150358194046002000b12610500820007c64041c0c06054285401410106160303032007120845000c0c0c0003400184400c1e0f41040f010080000322055181e54109070303a0301e001c1d0440d0040d180810b01e10948000031984c0d482a00000081c0082413400d5448400b1061003006036000400e414040c90304040d1070703000303c0c1014410036218400660740c1c94603a03100c50301c0a0320629400782c41502019122980801c144003004503580c0185a0000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 296817589 1250 296816339 296816371
    0x7032a060e10060e0f040515041b0902091809070b070b0708010e040803070503090709020d0905100902031c0c020d11030f070303023a0309020a0b03010f030b060d0605 73
    0x1d1100c0c00c1c481e2841540400074036112042c041c60914018880d0300000c00310302851192603500707025180140700a545442109400d0400c4201303c0f400e982000001c00780000d5050240e121188041680503d4904035045403a41c44a107001c80c05000c81941c02c61b000806440708507880b904000002e40c44010b00ba160072911006100001d90302424507401489204504800d60626545103001d034800039010f00304001c004404a0241e040900c4204002c1c000d02c981156200702088010000d030407080419201c6010321520402c040d011400303100ca006074010302401c40e1403004c0010601c0500102105010070114401a10040e101c2207150144180214008928105070b40b08052400040c0e0740341314900c1e081600100b001070380001c1c0303c1d80030b044d401040542d5030410b901d00c99910201c403004000d200e4102004185031a0701507005143c01d90003901c503001404d40f196480d00046c4402e03c10950a08811082000400c001050b0543c0158004040c020016503a40f5082c094030001e07601e032040741401175 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 296818839 1250 296817589 296817611
    0x60f09030f010e0d050a11060a0e10020c0c06070305070f1104060b070203100c0203090402030115090501020f070e15040f0507080a2c1c020102040501090b0f07032a06 73
    0xc1c1c001409807090090000d03072200410251a403043c08000405d1290210308081c1c3c0368043c480905e21140d00504590b80352a10302020340140c00c0c03401e000340603401130001c0080b01c1d0109008480c400d0702568001c0000e02c203094280301d46c03644000c2c8160300300300080c4101400600941c00c0111035a00810079041e10f010041c04120856560343d0004548403c100404401604e02141307001070700103000301c0015000245441a130640c45004840ca030b120b4070000000c03940d0038420050050900036a520028000d454000690342c504540101682c280d000306800c21040c00e4104500b80c0c010801280c1c5140c908200c4e0110b0300703941000080101042c0c03120204034030f4070f230f00c0401d03251300000501d01801044000a290946007032840741d81e1041050b0340303058410850701001780c80811002031051138024034003410000d000303410500486000883e60701002658081c01015204a403550502081c45c0c20a2603600340c40040c00000c0d0710f8968001c09410360100c0a40c8030404410900074400130816120b1a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 296820089 1250 296818839 296818843
    0xe190b18030a0323041505070912080c0106060203120a05070e0d0807060b0109050d06180803010815090109031209022809060803031e0c07051f200d110405060f0903 72
    0x6405101346102c3c8100710100d031880c40013000d01204450700048544030000304580084040c4c10240d40040d03018810410003403040010800c0110304002040540d0700e42408030303280c0c8144001640202401c1000c6480015241e21940e000f400b5410003031628801200454900c88c04039100b40c44403d0081042018001c240c01443d078445000d2a0840410b8140030000351000c05500700540b0701a51a040341090030f00003d0441c5495402c006426200d41c5d444401e80d41e10188454025000c00309440843c00032881402074200850345038548500001e802d249002c024149d030310050764030000c080020f01d01c109581081d0001001014074000320503042401c154150340c1a9070202403141d20402c10071003007600180300b602c0115012084950544c03140c10f08021a40926030011341140920001c90070b000c40032001012040840420600c804842421951030001441d0341c4400414010000d000c003c1d07060354403618030b000c040a10241060303200c1c1e0200c0c00c150450318484e1000c00b000252040c02c1c1c602 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 296821339 1250 296820089 296820131
    0x433050a1404080a050c0703021903030f080c030117150106020c030118050a0210050d0608010501030308061f0e040e070902130b04061205100503010e0d030e190b18030a03 75
    0x2115241603081d0405603034403d00da100341001c810404c50301046507003540c0c0060004c2402076400510020303003d803400c4200b03400c0d005184001c80224041c0703444614000d0092501c240715040f120404d80c1980e02c1e240c440030703260040035049181d500580a0034404d65200e9028039010b0803d50340108241c0c02c0f400241401c44402d101b02010000d400580c1d0400103000160701d00708e19506440006952a80301c405450500911000e14825400e00c84003040350041544014101d0780207940f06441511614244010128658804000142907103010307a685c5020314100e181542c0d0140000629680041d031140c20402e5581080500507000034803440c0f450a25940780c3d0141060042d254035041c80d161024115175004d03d100504a034070f41000600c4107209082410090002030020f0182903c000c0ca5140c80342190110035020a241c1140103000c0e01002400500905500c0d4100f075030f40000362258012540000d0131800924000300e12801d6518090001d060281d1882c5c070080368001051a4030381c40d40700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 296822589 1250 296821339 296821361
    0x806010611070b09060702060a0c03120509150601050903030c161a0d090309091103070809070b0a03050402062206081e010306180606062a03080433050a 67
    0x3a08004803420341c200812008100c81e5408043c1c1c3d039030903116000c01c01c540030700c91000c0d40c08600803841180c066005004002c816100c1e9540b05c3e000d00d00c28000ca41221400d40d00d02005903c4100003145001504242076080f00c1c0c1410103508280010001034034650000320041c1e80d64000c0d44103240459524141100035080000d090408400301304c0342d8541a008501881ca2a9070311200d00b40c043c0b40c025030b556400f1703003076141c01841103150300c0e075a4018070381c4107880c5d84000407480780029402d0030001c14150240c419543d041440c10396840d104501030301020b03206030391180d01000410a4081c0d800910080210340070810380a541c500315000e000e07075030002c1200c03402017083e605011124002c040e00304d041d01d502101c00031700d5007000c015880d160311961200a001e981307442c00c0030558681119103260342034140f0025180c507042d07602c00760300b0144d00d00b0001130218980c40e01160000d9171804034800400805140d10340117904000716901400c0c00c00c50120700480d9180244943c103445030160250503e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 296823839 1250 296822589 296822597
    0x902091f05121e1503062a0717071419020109050d151401050f03150f2d0412020c090c0a0e03070f09060e01122004020c01050108060106 60
    0x1400500020700188680c0e6940b00c4561110000280e54a040990101c81c14a004480d1101458404881040355003913043c2903200e4441c4200054074400d06102d42c0c03c1d00b040710061448144480b014180329a00980700880307240c240e52604000080b0310201400300c41c0e0042042c80b440300145284c035030070040d0103850700080da0315503811500942d82185129084403c01d50341e0000115031410880744c000100f441c40342e001400d00365011105450741709580c3c1a204101c0710445680b4141307040559441c0441d020410410b22070380021624015418044e6128260f10070304c0d900c802001c11003000d4850081258041503c0800900c403c1c454411032100502c0102c1c0000c114490b4483d000801c00b45006207440011440094011250740c0306241c1c0d0111034402a040301c1c50a910362040603e842c119002d03003038005203842c8000403003000b40f4240a04844c0c01d41807808a005e119100c00f0610410051084101580402980610340716072000b01040880f1800020300d9504050015050620681c000b034104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 296825089 1250 296823839 296823889
    0x30e191217150d02010c080a080106020601092a091203050a12050702060f06040605150c010c030b100311160b090d110d030e071a130506160f05070e01090209 69
    0xd0741c4000601d00349004200c5000f070503c2094401242d811542981c0100800c5021a51229468000817030318161501d980a0f00c110342c0c0c0b2150100211070080300030380400301c00500380144039021400c0e030900001c060f141c951091912052003800c1d0f0385800404400150300055103622241d4032000000b8050101e1005011600341400003d54880000e003541c0b80340804000400c08541c6d43d0b600038802040050b094040100c5c2d01d203011051600040300e000c0e000d5003499612200c41e44284204000b14600600081641c2c00c60102100103000740c0d490404100c00420110120200c074041454410380304460b28100b503d4040e01c210305241103580c25105000e5400aa0b408108000c0381500804400b0300e000107103400c070f8101291406000e40e201c41c0c1c000c0545105080701c1e205000081c00000391504d00e42540302c0da29400d2000c7e0744100c0c001d80c00000603d0341c2d50000101e40043c2481000d000e1000c43e51111384402d150302d1030013800ea0000c41100e038001214403050412000d00030203490080e90f01010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 296826339 1250 296825089 296825101
    0x1060506030402192105010b0f031e01020c011b020c0306061e030c06040e040209070f0903080f1e040f06031e0507050f0f1b03070f03030e191217 64
    0x703020160000344165024400b003206503092511060007400401d41c4150481030185d0003028240c21020f080c4c40c10f500700104d800d00e03810007185081410001400504030f10020036210b8840b5078a0020740c1100795003c210810170042d0074024418030300ba00101911043d80d1b81000607180a0f480c808042c040d4020100b0886569141e2a640d080d1084844400320643c0e01040024240084158110350100700481c0c04900c00181e1031409104078802d881c02c3d01107846000c401d480500358842c0c4140041c0603e041800041c080030041d02c03440030032084c0d443c00c00001916048030070044e280d140f281c201d40458200903007007010b4409802800e10341010003000681000c08451001248058140c20340c135180407c590710701c00e400719201101e0000125494071000160101540d01c0785002d290b405400c0c0300e08960682c004000c44480d41e80c0840b20f00a566110303035003034002d4920041004114040c02c000c244072a4921403207242d0192144da2503011000f61400c000d441c88422034582c4c0f844200c80c10400c20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 296827589 1250 296826339 296826349
    0x605090c0a270e03120f07110f0613230607120c090b0a05040515030619240e03030703120f05041203090203030405130207141f11121006020f010605 65
    0x2042ca81e440c500403a01c2d00710080c0e06440c51041484151054041031300f0010b021549250302030241e16246e1b601081072070507803181682d9509105441c0d40941004001c44c0d071140e185000214214403500000d0101e9070440021116032021011001d566084030041010340e40c0d108402440ca281e2240e802c2110f0281c001005020070f100f405002040b140c00160320030b807540a8029039000307040060002c6548400c24688a8064009454650003080c075070807101012040800a4019a084a52804d101609500540f1041c141c0e0014031070502c900c0c04607140d59600e040c401481078900030740356280b00302e8400359204120b80d405084641e0240c900400d12000580702c0040580081c0d03140703008541c0c03000b40d00001c2d0851080398841d69100000e000c1c060841391081d00941a0680070b100d001c0440c03009071510300d440e4151448108000300c050214540f5020ba5603001e04444c141c03850340c4d1340c24840c0140301e0087c0c040c41034884a004103110300080202641c1003001054080310100203016551801303010035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 296828839 1250 296827589 296827649
    0x1090201030e071d0915010602030c150705160c0f091e0e07030201200d030c11060403081b04030210020102030f0709050a0e06060c07030305133f0605090c0a 69
    0x36070310802c10010411703040741008507076054000141c0544017565600c0e0017039942c1c1d0001c03c08450600514000c41c0c100d02045950b10b22841140d15554074103103500411204400400c54211480703103040700b002c20355000f8000c840001e05a01e50000030010850f80d0307c102e00079204104508030f01e050a49200402d007000c41c410f02107030f5080c02c01440f6022450902000046100150342541c4038135011095481ea03d81c111000e881203d4403000d601202c80a505625030004072000740201c0c3d00d400c00b050080782d0a513840350b00290502081410301e9165400184608491b100010060b034000c400d01c519000300c094950f42220007410480500d5180c0008200c562403a80f02e02c0b10340d19102c1d80014901d8545d40e0840740081c0411040c0d40703a068492601503d00d800c1019801c1c00c1244240d030200e0407140140340300032980b803001c1c11101c440c040399200f40d141051107001c49210162180d00384000030004d003e90341c011f07403680015000081082c0280602c81c041c0764400d034844080c0d080070641d0218410030030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 296830089 1250 296828839 296828879
    0x91503020f0f0109090c0c060501080105060d021c0b0c04030c0501090e060d1406040c0f0609240314040c05010e0103090809040507020f03180a051f0e13020c01090201030e07 76
    0x49010081c5500507280100b895003d03411072810710907060341d0540d001c3e07c43c00c003c40c4505420050b503603c03089140d088401c2100c0c9941c006c40340448420151030001280541010a80e011801d12000c640c0c03101703030a40084e10001c20591020505204201d0407440c1c1c02e000c0c01003880c0030003a41d454101c017111103140103802d8134042c40c1c104100c1c03010311034a4102090082144003c44072241864075142d503000c407151040d900c01d90000c05d800305641e485a6545401c89400000d0844024030021001c2c0d0800c0110350b880040c550b540c8000703428042c4152003140b01d28000c419400510f4542030015201c07112288101c0c0c105450004c00c080020340070000d81d41c650b901901c00041e82e94802c642a46011203405600d12244800320700150101e8814902045181041e52880346e0b042d501c00601c28446c002e0200c20702000940e4010760826032080901400d00c8070014281204c6602941c411030407603200f0030181150f65101d00e908000d42d6003500501c14015400001401c0452400042c0905030300d92000d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 296831339 1250 296830089 296830099
    0x7020604080f09040e06090c0109080705010302210c0415080402010504031407051c0501141b0d230717090607050f12010807150903120806061c06091503020f 69
    0x1004516810107425900301c0b401c080c0040001c070b005e502e540b543d240002c840602c024490208000300951190b0020811102440e00801800d820600198042d41081003c48a0f0f05960218040c0005e070040e08107005881c2c0d027a1481d640c901f040c04000401091082031414130101000703000c0141d80c09001c44040380e070000304541040c104990181d041640582c422544640e064000c4010145904401000300b032081000700141c0360a40080410224200c40000031041402001076031502c0e0400200f0516102e0140010070122019070590311903480b0000003000b034200c400f000310307040d004000344c05942020ba507850414548843ca00c0d5039804010100320411401095105a01c0d1441c402d030740c040c0700b1100d1640304d02d6031543c90481c2c0c0d407a50f0303105450b03c0e06a2020312541180c0101c100d8020380e0741020b2603031901411564240c0d0b041c000a0004c982004082041c0c428020498055604c3d21412000120b010b915094010301070740c10f40c1003045e801c10300c004810001030f959049500300a20041c1c170 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 296832589 1250 296831339 296831347
    0x50910050c0c1012060b03010815010302030a0b0615030423031602121f0c030605011103030f0408040915060e0307061b060b090703050106021606020a0212281401050702060408 77
    0x4110b078500300d130b000c07403442080c14040080395206003807000e5811b0790b118900710390420340481e0001c80c880a080c44081d41603000600c2c0100401d910030055a4402c0d8068544043c0000310000c11090380e000315002e0390154032440c00007040f6003204140c0503100031810021404c04c149401001522081d004c0000c0c071807a02121000e14100c1c00341710107102401950000c20141c0d0340088072001801201901720002407400318049460740c0652602e40d4800198002582107949030707125100c0c1e140d030190066400400a0000142c40c00f007600401c601c038000d1850304000381e45402c5028107840e8000015903c03a800444040c00b01c982d1103403480c44070610314112140851360364100300d4000e0510302c40b510341141c2c2d20783c1002070329070b010b40041d41241e40960803107801100320015450066130f01e004000040e00301f44c0b040005440c00d100c120718100298804c5c0d0784819082204402c0c412090718000444803840d25642080c0301056003038445e112480d40080c8018940514003d44544d00104014016503000c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 296833839 1250 296832589 296832619
    0x40302070f03050c19030c0b0f040302090a0207030e030c181b0a091a07020918120a0c050f12041502010e060130020102060a0c12050106050910050c0c 66
    0x280001003240c03081101080b900c07030500c1500c8007000d800460056a0b148042000a00401200c004a0760841110a5424208101c090550340411305418007a201400044003680d603848446000d440460030060356a5924038003e84840c003400c400b10700c240c1060b680302502d500d0362030419207000d0f1412207095a80d5200094188e541e0940f5104041c0c008021030750051694010300000151038505d4a00e21414a410250145030b10071504000c0d006041c0d400421910441d188140034000f00000c150f81201100180720741c0d142d008550b001002071645144601400414030080085000c4040541100c0c40c190421000318400c40c40350111204410746c504100610039802094291051030503107909503502c0f038004188200c807800303101d203c111046566084041d4a05500c450941c10f8014107040d56441140c030340109280414031050000041d1000044511841142d01901207600c070262614080302c20f20590601d04001041031000c100541d070031140000482000d011f0b000c03503920124102c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 296835089 1250 296833839 296833843
    0x605130b01030e0d08010e0f041a1e190f020f03130206190210051302010c082a0325030e0d0c08060f010312090b0301120f05060103030e03010f090317040302 69
    0x10842010385002e4118007540031948050300504885d62044001d47c140c0300e031038a0030046c40081d1001000000705000020802100300c5540754041c040582c40d0610f07088449081944c0c4070202c030b117640039000f81c8042e019040f145206080100f03100440442c103108140b00240c446200140c0a0301e945c00030a030100c4115601c00c2d048940311860001d00a43d8981c035100b004e56924a041100603c980c01d000024402e2104450440c0c0f1541d0140d40b0045580440e072600840da5111022000742c0c0400e200c1c01c40a640a003007228030411102c04001c42c4c4e910105506014601f8071100d2a50603190114481c5000c240e20489800b82588211245140c0c080365140140c04590558040c10003401a0300800c4003940e2800d0300181280d000341700040c0004d03006c0b40c04959180440c0941000714106000503c803000100d0244454644109c0080603440c1490702e490789030480c240d00440c00a4108107080085040a00400791030160300d070002e01c0b1101d05a9005043ca190a0100201c801c0909000506043c42 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 296836339 1250 296835089 296835101
    0x9060301020c0a0605060913020612060112060f031127190507081506040b0a0c060906020c0709060905010f0e041506120b1501020703081804060e01080d030605130b0103 74
    0x9000c2203d0094a407403030902d0141c241161414410b613002400101010000489405141d50040510b4540342c05680c00700c81004010342501d0421843c20b10382806140c4a00c80c400150010b0066051003d1641c600300414000310220380c3e00515042c01d0400389484e114070f2500d01c04064000403013456617241c440080e5100260701052486050a05004419420031041400340440902000c0012a50000d00c64944a030b481094209282042204120b03482070200f89840ca204040214505d101503e40368240d0b040100070302c240c0e4022a400f004400800d1040c08000d140ca00c00c10300066142c22981d10310200c09116a010002d19440000c04010310001410904d0040c0740c42084a02d81b00c0f1881d00d00e180103944101c4044a0300c01c0450100951140c90b00a5200164018040c41e8195522401c05401a00c2011300045c004115060640d5890042d14094040c4105140b41580342881407850004440400301c00c0c14a4040f050140383c07170300042a041e103c9981c10209101400100480003042c0e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 296837589 1250 296836339 296836357
    0x3110d0609020a0f05130b030309010c0f0204141008150601141b07080d05071e02060408060702010506100c0b04110d02060301080a11191203030b0904051005070302180906030102 78
    0x300940b00400c11404c80421181500c805845c0e01d0301a0a48440c03000448816221681c0d055005000b020000d41c440da040c0b90410303100301c0f907005410806601040c00d071a01c0d0800c1d5000780303103610304110400403100c0e0108000c001480c000c00d070143d26102c0b0001c081101a10746410000a80b0128001c83d40c1c107030031654031028159500103520070394103409803035684c0707401468110700403031455054ad40c1c41003058505054101100d2442d516054a21005c059100c1701c0884c0c00000c00c0c040081c00726400d000c610300c5081d0b40d40001c505490004100003414000c01440310038843c9a012407004a0200c440703080d48580d1046d0104056640540090701d040000980294491000030010410301c90200f05010542d1048164802407041901000502c031400003404030303036054000741041407840d550241203509000e800c0c0040e01840c80c101017002010100c0f0166000da101c00c100000840d101d00c203259114a130b501c0c045040200e13201044280100d1a0451403007028800c001c80d0342030303400307504880540f6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 296838839 1250 296837589 296837599
    0xe0d0f050109020a0b3f04050114010501030e030d0903090b040311190b030a0f1508060601020d0201020405030705010509032e0f02030403050904020a0903170c0c030703110d060902 79
    0x58203494018081d0011a0381280501c10380440000c40ca0380b440281c600102821940b441c617002200d503032001913507800d030450340108076000c4050014616481800d008902480010651443c2000c110040040c1a40000d040500d0104203400c1d80f42d000c010354450540072070010469042500701103802100329048052160f00c00100041042900d420100410105a800c0450388424401c02a1171004511034405500f03c02c000040f030340c014542c04501042c40d64007001661414070401e00d01c0444054000001d42c3c0d0001040c02401d43c2c041040d24442140303840290300d800d007440040b9403562618441c07281407020104a07491fa6603001e02c4084546109201c00ca040390010102c141402d8a05881000b8581c0c94414800b1519449001301e03807141e0741584034103261030440c500b400b000794003900c4040100141924040000784400344101281541580d146803120840c081c11030520303159025241c400e90201d803007007000580325a003124241e80112264074400030b0381d007000b801070102c80400079480 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 296840089 1250 296838839 296838863
    0x504060804170d1d0307020102030f130306050c1c06080c0613081203070906090f0e061206010e10081506190b0d0c0f0c230a051c080f040c03030e0d 65
    0x40390481e40040390013112032002c3e001443c0013040c159220303c10b454021340140c0007046025442103403580184416640950081011545c9440d44011075200350340d0f031400800b000600744400c1e25414942001303509941e2041240c070b0700d4280142c0e503444030f0001141c021640811b803c98002410b416982c0100107640503151241000e110450059004031032440c0440c1c21003401143d01445003441d981525000c0003012501c6080c401d014a00040051400e544040c030944104d0340d80c030381440b00c2402082c244415455500305242c06601c420960741014005034082d40c01ca800f042070205043c1e400c6417094035840385c002080f01c0c4442194065402401022500285464524280f9403010401040030fa035809403250505804949483c1d404030094a008031442011051000c054400e07544050182e00322804640e80d50345040c20a00c40e000d48400c4417640328800c80c42750341c120002d162300031104110b03400a45000d940750700900a240c08003804001c080111400300d80c0310403841c45401e58100000480c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 296841339 1250 296840089 296840107
    0x705070602131a07050705130603050d09090b0d17030901090b010b040f060f02030913150915050901150c1e061d03030603070308090315090f011b050406080417 70
    0x10382d4001c1c41038503c0705407024128044908004240c1d0700d03169100000d40388492412080001c9416800d480c2c0d481c0a56400c00080002d20401441071000c50b5502c0b2090400e1404148104450908545600800c62a0a010001601c1d44166003d01c4580000c198490700c0d400c41650040080c03840052a042885001080b0002c07100054412030300f071340481c4016641c6454080f5401c0f80103160740d0b0056401400419041d00c0c00c915644681004140002100002d4442501c0a4946e9900000e0040d44da400c1003900700441030100c0025050075a4104079035450316035121070545c00c140f103200400281840e28010810003a42d003001c0f00e84001402c0e804403113181842d00c0100b010204108010034005048021840d01005692080500070b029143d0513184d07442c0c04c030785548a1052a5130600420500080e0010302e1502c82d8044d08400c00144403110313401d0308a50071a40d40f40140d412442852480e0f12140c0d078031000320707416038915103820040c2d0384880c0307880061b06d03800220075000d00e1408110040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 296842589 1250 296841339 296841367
    0x130806011401020a1109130b1609090204080312091009060e0613020a15210902130501050d020f01031e0506010912020303181c06020904060e090606090705070602 71
    0xc16118510207071900809030200580c1da4107007444004010001e10380c00f503120307803801c04a01548001c46c0c1072000000d915035541d02c00d00400031946000c120380040350318108a43e025213028080d00c10719108502e01400c159206a0380d0103580a885514141e03640000d25140c4103101e8980381b0800b006060248004918100c0050310b1000c000005a01c50040010510a0740740744078042540c01601e0710103c0ca05100032840340811303003811902440300350640361111007001c100c003040030070380890300082c8a9401d204200e950700780f0000081c60b450804005000c581c0d1282c2601440b00c0c0c1c1254000c506025590042e406800d5616001c0b021241c007803482a1401c8c0b00d0f8211a20603642641d90203a01e907100c003c4507082c94007500e0043d40541c000e111007101c20151413101c2c510325200407e800000405403003140300e07203000b00300f049034110b80110350b10303c09051a02590000d00003002a0411619020005540e69000109841d201e020100041200c10f8090380c01c84103240d0b00403205540d80c0960806005c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 296843839 1250 296842589 296842591
    0x61d07032d08181f080103060b0111060f0115081005010e1203030f040b0a090519051c0f20100f0b060f040e0f10231e010306052211130806 61
    0xb03008401504050070070424944d400e02ca01c81c100d4030742c1a09030f401c54413004024003a604549044c0084c8040e00501010308012481c0718000f01d4002c00a5503040000c000f18414410802109100108040c80702001c199609481a2602031912390441002400042c4a51070b0035407462515000001c10701036104450341401e4800c80c05442c1d100031a07119403034400d048488880001d4896046070f07070a90b0b000c0322083d000c007606901a40803100c2c5440344046026180e0380c06900d05011a1042034200300e69500001e03210340e650004804c41da002c201c040c604c543c817044a82d14501400d641c410350615040e2283d48070a183c00d40c054860350310303007083c01d140c1c0c0010b0b4440c0c02640e05145c000c1300044d42c20007001e542d00e40b003882c0c10859255507528148082c265845d000c184034204803440d0a0300c484035143d10b294001004040c140b14010100c0e4403001604544140d0882402850303081940070070381c18024507210541d600c1010001d0f00e07404040f02d6024a00480443e14010801c8007800940004000360103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 296845089 1250 296843839 296843887
    0x405070b0d0c0e01080108030403020d02210a060b0d03051b150106020304060905041109060f09090406020706140402031b030a1202070303080a06050904030c110409061d07032d08 78
    0x603d845140e800040d1149642440703501c600703500c100300034001400e0a178002034403c0c1c030250101c034507109420011460440b011030450780541c48000800d0511200e802120003401040d15540790074000307034800030003a208410207a08c080307460411081c0d100504124015400000e254a40100c3d6146c62009490340c0c0941310f2400003030b80840000c642440c19204610001080a1406141801c002e05106d08c0f90458010030350720003424844132002e512051100c1c5e128a114110060f902c01c5980b4214040302c1c0790070b502c550082d01450030080180c60001300d10202e103030101d8420034246080c80c00640352107044a40180761945860700c07110400d40000e00c0900752840380e2280059555000018422182c80c0d01c50f50b58000711308400f040202c1d0085088404083c02801c1e52000707046040041420343d45081d204443e40c1c1e90b0381039034540360581d4140314403038000304201804083d4a140c441300108103000f18072901d0341c0c08154080054119441d08005626030042080780c40321040402c40c40c0c0b10800c4001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 296846339 1250 296845089 296845097
    0x40603060602031207200106141e01170a0917190f0903060f02070803040506240904140f0d02070e1b122d0a0c080f0f0405070b0d0c 58
    0x481c10030300110680348510159500383c826a13403030751011601812070480180006400c207486114501c42800b034a00a00240c0c80c3c83d1991201050900400350a4090300400c160080f40c00c002031030ba03000c4000d0440620151070610076443c1c600d0000c00900d0300d1000103000d1600d40548540900c48030005e00400d42880818800d010031840060300c0c1c200d048161400000c041000070700c001611540006040c5c07188030001030030b180840e0703611110744d4004e0714103403100c2d440700d130410900d50700c2d09044110f0482c107400260702c800319200c04509030000c00b8000400303642010b40804102141008000482c000b102d0442d80f1200d80c0c101c001c0d4850b10907000d007113205a501c0c000108910704040111490880440203036181040c090602603080b40301510b0002109091b0200a01181809540c0603030203940d42040341590070100d203004211002d11401000780141c401c2008000e208418250340d1126500c2808040c070fa8492500c28140034154000000f25280031980095007806d5078000c072102c40380c03512 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 296847589 1250 296846339 296846351
    0x11120a1a0903040b030903040f1e060203251e14010b060304031202030a110f21100303050703020309030610050f0307080712050f01061e120b01050405040f0c0b040603 73
    0x24011806000403214041c15500c100700030001038200500943e070089030b00b010789060507100c1400c0140c1504542c410420407200618400c8801a16454400105040e0006510300044107082040000306403050034100c0443c280b50400b0700a09150014510142c40918810900f16241905c1a414000d00f1140c4a6280c510745141030701700203040300c5c0a00d03090b44400f525150310108480181d4030040407900c00315120503200340c0801030311020b040d0404080442a40310400c101901441d00d05c00300306d03911558111403e002c01209076298900c241c9405192965a500301c5080c00d074070314400c907810550140f02da5010400b41000a0141e60291102295402d02c08501c12080540d940c0e2580910100d41e00045800c10001d4a80724614101700c0c403910a5500700c2940249060841e0204e0340509110f0513407203a004000c0042d142c4003805448681041c441d04a80d0b910f442d00d5402050191074003881da0f4ac00440c050200503509182e1895110b03c032034010540316005002107402921400b1301181c00c1c29 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 296848839 1250 296847589 296847623
    0x30203010c11100b0f09150d0303020d0b010216050f0105120a021801050901120507090504020c0c01020d020304210807140109030e060a0c290a09031d031911120a 71
    0x1000b0112046401130491240c881d21804021b00da8a018007841c4403041c4600740002e070354949102448019001e900c006846420340300700c14080d10400401e179411500320070440c601464481c040002a140240c1e0f11003201d00f907010061340c9520410404003100d986510822041141da9001032031a002c0748003003202e100d00d51074010340b00d42c00344099540c00b00e0202c100100349100703158071060303001d070301858a05281036441021500700d03407120000c0591500720480d081010358042117011451a914402140707018070703040c4401c101c0d00e81060041d044c514408031901c02d1080910075125440e0700710886954094071008814002e0040182c201c002c00d00821140080c1c0c40c105c07043d52801280b40d160310042403003590b1045030040307540b800e85843c00c85da02c2204e10302c14600b0b02020700c14001d0850019050300d00d820301a0444040200d901c2940281d040d04440a4401040703202460006030318000c040e13441c03440d1071030204416210350b80d0020180d602c1c5680d40e003030008008803c02c1c0103483c0389941e45200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 296850089 1250 296848839 296848841
    0x90306091e2004060311130b04110d05010f060512130c06030b0907050c070b0f1218120a0519031d0a0209060315011707031e0218060901090b010306030203010c1110 72
    0x145c40003034030300100c0038240e00c443d00f00a413584490340e13603d000002da13041000c0006021142c400c56080c02390a40454101170000302c910525000d08940748051103c1803070300e0760041c058840c0342e8407680000680000301d100250341d070101411056200c51540c10750394890034010b0041c410384031070074403999418010902507401001110300281084028240d031a05004010309103500007004814a0380040003255420000c0701d140d40e002d18410441010300c117003420141860034080b0040360710000d07800c0008041c1a0b0f0000201da401c90a6a6100700d011030b050340003a0000c107400100c1c1e00c03003054000c08007a855600481c608840510840780c40046480d414103066460004c0784401c17400098440060000d1011a06002000a03c103012282019100c2d583c0f44811411400030010303069070121400c6c1140780c000c00d800d00c009012084070040d0700d0a0400218509810312038081d401e0b81d50842d4444e0740e482500f0000140d9005030082c0002e04401100800c500c0c0d514003c0d01c86e501600540d00055189 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 296851339 1250 296850089 296850101
    0x16020c0a030809042d15080318040513050616030609180602090a030c0806040b0c0a1d01170c030405010e030a020c0f18040f061b090306091e2004 64
    0x20102c00d080c0b02d646000c0c013000f022488104408080f0444134050000d4418001c0c101c400407600c00852140d0914a244803d0003141d01702900540060051030040d0440b0104801c180d00115004191510b510085180c12124620058a14014241040314051104245c1e80d139441040d90100003d6680f00070314070884000c2c856070781040c1c0c1c983c01880e021400c150043e00f55100c000740240080c030750300c7e40d4034a00120f007688200d080b9003001080105200300d07144000d07480000c441d050b030310b016088c00e002041d011301003610150148440b640c4655591040d19840482d102022440c3c16500b03000c150f00c1d00c580c00031581100c45600340786501c02d02850101c15a00e031070f0309580040100280250400403000c900240007a005540d141c2c0e5090b03d8100e080d16036009d5070143c441400c07201110b080002c103603007400010201040e019118420300d00ea02000c174500b2070383c002900158000c43c5103090104500700b0250411000080d4514a0910480080d5002c010907002c1c60000403246010910080c1d800d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 296852589 1250 296851339 296851343
    0x307030f021612171605091e1503010302062a070303110c04090b010e0703091a0a1d0d080c04030506040302060106030e061501050c0a051902210307030f1716020c0a03 73
    0x1c04011034a01c0c00411176490441915043c100c0c2030030350403004102009000000c1c940380029004800046040031054030b00e01502c0000342d28507540c1942c002c24070074881e010361949002d040100d5822502c0d2085074004c1c110107030310300360340c0c0a42e903d0800a003800c0403030b02c5101141c050100b1801c080d25140c4201e8258a40c803503120b45440e031030710036906403c03503008080c24203040c6c45c3c04806000074024031100c04031100600881441c1d041c102e080074219021400621417004030300c003c0b0841000c001034100d400c8851442d20507015036600040407514051540010100d10640d0244000c040d004100c40381a180d45940412043d6402c400803603843c0c00c00c1ea80b00e0003481440e041c2c07240c40e511075001441180c41e00022100c0341d0200e503172410315206000d905103c40d2240000040e0031442d026424600d10403000c400e4040c0c5078428405076480340b01d042c600605000b045e801b482070711030090a122159041c90f240b0000e07c0e18045002c2d0f44043c000c40c8511005006401c2c0d603032000d00d015407295040d25 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 296853839 1250 296852589 296852627
    0x80123040209070c140304090204080616050409020d090f0f1b140906011e0302030106031503050d0302070f0c0806040b0603150115020f2a0a0b030406020307030f021612 74
    0x207240c0c000e007522424000e400941c0d1600c000050442c041700200020001000d405000680c2c079032401d50b68a04110f80684240c844906203545c1e9540c1aa101040d1800c0d180543c000580c1c40f00c1e1218610010040781200400541004180105010314002313040700860080100e845001e4036105140100625030007040750801c044152540f0500300980100d40c01801070410030070041304160031a900303030450030000000070340000c0103015603607040c001c0c0ea100f0b940150040c0c0c4c0c218110380e1129203491440c0e102c001090f03030209501007408080b1710340300010750b0481c01c91300403180c60712246070711a0b800300ca040c0c030a80c80120101c0e006007000a142818040d00e90a0040760382d09000310000f0b00e11101d40042c003188038841c901d00c106101481040400044040030036800400a01c6805403000076544280c82488104d0080019083d41001c0ba94416804000180d40ea61410000d400420340b85400907946440400c0c441c2d400000f203050034200c0d5005003034545040282c003100b150302e0b24000340d07010446 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 296855089 1250 296853839 296853841
    0xe0309011704050a0818280b0f04090b0a0506070b0f0f0103080915040816030605070302160609170301091514100c06060b19080703020a050a0e031501080123040209 72
    0x82071740b110250140d0000d400d441400c54401d000051061002c2c1d602d008421502c0c220300828000003181c4000050902520712824880c03000c13640380c0207000b070340714540341c19480316210205a5940c0e26890041d0100a100503141d101600b0702d40c0c040e4a080b2580b4100462507408103242c020a03441c038604880d4812080c52808420800b44038508000b140c0c0701342110b005100c0401c50403014401007007859040c0d81590800d83c61400d203802501c1002c2d1600040c50f04c1000704c2040852071404007007000390403010229626000f484e003841e06014241d01d02c01c038000040004119039920341c1041404070481c600d070080d00707501c540c602c9540c00983e800b002c0d03000440c110010b0b0002d0041c8281c00155000b01000250150b58680b1211641d100b4520007406102d0030100303c400c1600912942d4020b003980c501141060f43c41e0401802d68460f60600d50240008951503c0d03159030108101020100307240c1444059503541c041c0e66020303024001d00e10700456140c0c07043c0720201460b00e00e41d5210f150014024409 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 296856339 1250 296855089 296855093
    0x1090b060f090d05010606030b0439050f040b0a11121611030304060302032d0105040f0e010e1c0c15111b07060908030703081f05040e0309011704050a 66
    0x402d60100b482950444090348407080459400c0c0306080080070320fa28086034580d001001c000c2110642800064994034800e220304001c02c044801a50041134004c1580e0000c0c40c4240c259040e0203031a41e00c01c007021000901050212600340034103005851515000c00d0a091181013540782c583c040c1d040c40350000b06100d032504000e1603030006601203000d04040340401808501182c11a8459045040420f8001003400307405841e00e05882d1500c4405140c01000740d0102c0b0814489040621403644155211000d41074841e0140e400456078500001c003c00c0f078840c030705e26483c3d01c030b401e280c207001080142c8590f1018454000d0060307000740da03400618088440f00180704003000302450003219404420501c1801d03110481400701408080d15000280901850715000401842081d0400c03203c5810034401c1000103a0041141d40d00030202505403a441c5400407482070405400b90301c001e61007402c00b04e0f9111f02c0d41d07020000303182c2c0c12020790700c1400c3c55442540f82c001540c800c0e00c006046d640407002c5040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 296857589 1250 296856339 296856367
    0x31d030c0c01051c0e0c01081e010e0403030f0903020601031b0f030f0c05060403112b030c290411010c030c030309080904113f0c07050601080303090601090b06 70
    0x2084c81c0c04901c045500040c003900116500001040c109a202c403900364010342e048010310380d202d510402140c80e1070040680300281204180300348a000c000c030201140406010750800d851042810b030b410000320501e4240203684541c203100a482e0054031255190141c005403219a05a5246c078041442c0300d8510360f075850500d00e50040c1900c00744400700001c101559000b0060000b14080c1140148483c01d00040062813035044025904003241510000341c1c200c2e40c01910320020380c143c2401810f00c1010304244032150452814030b04200c200292800001150b454801c2c000da029600d04d4024200344801500d0340240b440000c2d02040c0038161400009200e600079040720b1b031050450b50306200c4e903500401c0c150350082103600c5c46803a02240f030111458940c0d00031000e1100340c0500011102c8002d000c00350040b40d1207227220442c2d00d41c1c030025011034410400c03204030070f80c08000c0b02c070250b80d9400d8480c0c40741c00c15111402603000303000000030140c64900440100500050203103181000c40c018802c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 296858839 1250 296857589 296857597
    0x50306060c07080d030b040504030c0807020a0522180218070306051c1e0c090b0102070b0c0d080108070602030a0318050a031206090515060903030712031d030c0c0105 73
    0x69031100c01000001299101480880c0062103403600070181031900c4c400c05010b8500600200b4011842c040801020a032f1005058018a0f044040d050b84e6082900200305405002c0d0080ea4000e08041003007c074040b070000e054103003090300510420404401054400302040080800303548a03030960107a040d420394180b01203800241504000800591f10800708540d4441555054805400304803444140581e4400c00c01003c06401503001d0200004c2d0381d080000300c01c60248070040c03682d5000c2301d030441c2d0080002c00050103040c04200d03190441494070640c0c450545542e0b00000344100000661103400051210580d11590051030600702000012401841c0309888283c03401802c2c80344801140013801070300000c0b4029501c418a0319008180f2005841c40c0354491480540780608015201e40340460400720584229810b039614829a00040c0c914001d50740090070348101c0500740c00031140c050340f084003a0030001100010a82041c11200e4490140c12007042d81d5811048400c101d5600c500010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 296860089 1250 296858839 296858851
    0xf1a0708070201181d01170c010c060c03020d050c030901060b1608031b0a0801080105010f030804050913080f07050d0507020d02040b060c03040b0315060712050a030b1e0108070503090a030503 84
    0x4884d031680c80c00500a00d0000765605039005a0840060203880c0c8541c1d80c4801642c525001811860722050000f0280c052494014052a5075034038906481c512940460b00c04070403000b000d220908245c281c03004694000c0e24185400c4d032038540c001684554200a0758100342c10b0042080fa0302805e500d68640715800244000d5214001011291a00045801500404949955a61840d030400040e142110b40680041042001d00740c82000003507110400ca41c2035a6060701c1d150302c240c0b100707080c154003051180c40003005405d000c030381070b003000da907200c046e0006c6070040c406c4a040c5a550380003a519449907040294006030011104001340c2030903004030380400c5014090601d0440c030003d42d41c0c21174101e0341050b880d0680010510100c01500c1101300400750302100c2c168905180c5585c2d16103903501008626090000103e44c3c01038541c0668004620380740043d201105404142241d09219064460114007261091000c6105140700d071058a10500c4507200038118800551000c1e103241c1c00003058 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 296861339 1250 296860089 296860127
    0x6032304030801061b0b01030602030601030e0105010f0524040303020a0605060a140d03020a021f0306051c031101110d0606020d110c01210c0e09070206090304061b0c0f1a0708070201 80
    0x180300e0000300d40e9940c1c6c0d402180980001030b207a050030b0f8001410747ea000f034a080c0d200d0b818840103000c118280058403003110380855124504140e840241c1c1645a00000800e1342818041400024107401182e84003d02e40325800c02c00080e6901e40070400c16201d54050110345100c80305145009083c801c4810740300c640280119148030509074005040901c00c0c00c491903003042020443c4200765018042c40001e00310803540401c61608180000c10704124218024040005010040d82a46800e41c4050074140304005515a50001d001d00f0002030103c0d03114400040c480e50b0328600c541d0344202c0706501003500f401d01500100c0c000000441d035180420684180c400c00d40c02d000c2c0300c02107051240c0c42e814203047d04d511820101ca141007003c2e030f020042c52901503401003020025440804401c5074141d882ca07003050448191500c45410350002421001002c2100120012810802c00715016088810300c3c2d4a40d0204012003464841074050b0090060400005010f04001903000d40008800340c812420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 296862589 1250 296861339 296861387
    0x1030f0213111c18030e040e150411010c0b041a0703020a0c03032c1c020a050712030903020d110405010b13140d1203061404020328020f040603230403080106 69
    0x2140c94111307203107000114080b48140107404441e0070240605000551030b00302519480c020045414040e0b000108010149020809105d070940c4c060351002410603084006c2030700b00d16007481c250781c41c04102e10054041040103c00140503600c01d008030340b1440d02035941d001102403180c1c0c00b9009071500100801c41c424842070b030068010520f40c425040807428200503ca403916030092058110b541d07482c0f44007190040c0c072886000c542d0004c6c2040c11903800c4c00f4080c942c0515410100d406a56540000354080750400042e41071000b00001070f80c810f0303c00c40d82000701e41d990342074650301031080c1400c140c4521042541003150103101e000c60108000060300d4450303080903d0b0390b05540c03040c3c503100b80304c0440d6540009000c8400c05581244248200f56800c40c55400c107250220080c1e030b030801c3c0000b40399800015082c6000b1841d0103840c40214800c04141d1200e0311aa030280192882c1e4101c0b00203084205481d000320f000e00140607001d140c05448405c0d031039091400444030b048403080805000a6103203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 296863839 1250 296862589 296862611
    0xf2406031f0209060c010615020d170a0f0f05060f091b0d020f130806060103060b0f0702040e01020408010b010212070308010501050c0f0718140402151305040501030f0213111c 77
    0x44005c102501456000140817401c180c0440802d00c68146400d0465101142021072030360002c6454490101c20100410750360740705032020001c0c0c80301018840b01c0e242010380e580d0b25020640c01c03850107038108460145140c1c13910410305c004404100c1d090111490100c6c0004000704c09400106202d01c1011000342c030300fa480344001c00340c40d40000c03643e503903002c911303403041101003000d100350340c4c200780c0902e0705020003841d00110411074026140c003124506000600b40c021981c0da07901c806441d00c10b940c025500c0f2690382036100c0c000c1030020070340c40c00350144000000e00d40440b0301c112982c0940c5900d6441483c0d00b480c00446094020f1a00307140184101c030000000080b08211550090510500e851403011a10711450150303100c40742c040014050403014031005070780e29103c41401e2200c441800c0d8440090390900148016190300c5603410601d000004414400140100e1580f14001c1e100401c0302d4088951200403a04038000310414080140860740c80c030001302c41d812401842600d00418140490 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 296865089 1250 296863839 296863849
    0x30509060a02130e161704170c01021c0b0f010c02060717390d020a021c0206030a0e012f0901030608160612110d050402030f0f2406031f0209 62
    0x10f540358441c0c00794054040c00d4441e841000b09001c410072090720740c52418280d0302c194411f05c000380140c15003400400d032989c880c40d095040d03a01e01c10f0401c010251015030001c5000c02402445c40c414040c080c900e6603c0c849500840c142d00301c00b82e0241200c1c1c582407198a03003149514140701504505042081003800d41070544000201180c3d00c221400c0c0e4611a50039642410903134060304d041c064101052200c03120381c012400d42a03a540680300600c3c1c08504103d01c03074803203141c441c00a40c42200401401302060450317100c4820b6200d04c9000b000007000030005030b02e43c842d840450482025404200b515420a484084c040710700b0181400314109407aa0081400c042020400c18054158454100304103503011589480c541564641080f0a02404100540d5441030310310040308152202c1c04207046407000c01010881d5034440f0151040f2031441708026823507a440440d4210840340c0c42c60400c0820b01c000d81032501034100100203101e601036881d5131241c1001448000c02c80b4039424000b984c0c440c1c40d8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 296866339 1250 296865089 296865091
    0x4081204120f0e24090a17060c0903100f0b121b0613090b1302040e180d050301170106231203040e1801020705010906020904050601030509060a02130e 66
    0x218454404100549400c018110099030841104100103603541609545a51031420381400c40c111301520400d070200f45074040e52140e0203a180e0002c0c8261170014000f80885091802c007050344045d43d0040d120201d82c01d10700c1c05507250043d8580c000b5000c090015200381c2c03061451013007411000c034940300090b002500900820a140c503480c0c000b1502c0801c0320b50101105420f413032041394201e04148500c00c4c40440305140e4064940a50380c0c4d040c0a07440d584d96501c00b010750481c1d241c0305540e101d803210f0b60070740400401d54018100c00341ca03401038180f041000ca01030083d220709a403030f43c0c15a8a0400c0c00a622400442440115503031800f01242031800e19400c2000707001c4150b07034a65209081014407650709040070910026400c240400d10038503e1301004643c100b04c8141701903e401004800d0107009102d000c10041c40e661819010608009113900a041d216804850400081d91500010b400303a0b01c0444404a143d04410f0000d6661003076903000c4e2050b6149204d40709640c90f190341c03c40c844094 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 296867589 1250 296866339 296866343
    0xb2a2404020405070305070210110708071b1d0402040f09050d080613090f0f0201021c03051e0709030b09100204091d19031214150a05220504081204 65
    0x514a0800c825410300f40580380c2c0000461500b0031042c07404000013515403c0b01c1036400e01c02e075100e01c210b4070848051010340c3c040b10b82003a10507650302003510707003a803446440490406041050440008040b4001d0b400c5a41000c0f4481d02d009127640c2d242d08100c010304011124020305682c0742549400b1420410040c0c0c1054100d840e040314908096080144c460f0318404081074040c05e012102002640c4c0380d9001c04031a900208c18014104207200507030400c25891f800e6002c020346114060040c941c10742092380a298103000040c03100c1740095000003c03401c00c6a001c0003060810324108006405502080d0340324900341d06946007604100403590136030380135070301400c4502c0d11804a501d034900013020284c0c2d0000b040c00203004000010001c00d070000fa41c510b0140078800800c00207180002c071074000032150f8501c0c429031a6140f8000c44e2204801080f000070074060805500003003014100315003107202103007440c49001c401c00000c040c0710015110090045a44000030702c840c00c001c07180d8000e040d000d14 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 296868839 1250 296867589 296867653
    0xb03150c0a1e0f081b0d0209030a0b0403030b090711060f0402060d140612010501080a12120603030c05010509160302060d110f0706050903030c0904020d1b020102070c0b2a 75
    0x10f200340400805501014022240707641505100802d01c406074011240c901100c0308000d85c03681c25460002c1d081c00540300010b40902e460303074208410154943d10101541a04940f91071207511040e0088850b40444100f295030fa90000740855119203508003001d0b44244001d000510380f030080d0300701c9000d45038039076001c60a034807010042c000c3c02c0c94810307080244815210020041589412051907644c502944080e150190403000c044c8800c1c031820460842c030207440024825955640b4005009084025059609510300404214440740114074001c613072002c1d82c1101041402c503003c004060707001e00d04140d007041d50381d0343c0b1410417403814000d407001c0c1d6101d0000c1c0c0d4465440342040025100001c000031b01c6600f082081151403041642500c16088094a00503207409810420300300400c0100902d8040c0c0d61075400000109038150028004184a84a00c05041341d965070080041e009440c2180c04800075492004d50440c020302d4a0762410300e40504943c0424640301c000200ac8049944100d02c0e2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 296870089 1250 296868839 296868857
    0x7032001090504020901080c0d090203150411010306060e1201021b03040f060203030f04030c050c030105010b0904150510140d060618050f0a051306030209090d030b03150c0a1e 77
    0x15a0484503010050000f40d8056107090381240000b005120014116580103201003026625905a64030807400c86501a0480320300e03001036001201c881d076003100c045a00070746070050240c1c07039403190061600b25241600d4081d5611448000c20240c070403512070603842c42d94203002d0680312514900d40e901003d01003201a6586c0c50800c4c04121000e69190000c405543c420400d1000c21003041e044c8580c0140c051511580014280c58040e09040d0b8070b1040d2607141d800c060010460642110050281da0001c8030100581001844503912a466034071800798403596581c2c855610360f005442e0703030b07100041350004140b0702a1182e41040450f1129001880003c44d1080004025a000740710040a4038044900010f210241400030302c4207042805018060100c000b00300c00d000c095030f0021320107940c0c0240b00b0603092605010050b5686960311060002900b400c8242c1c285007000f00e019460449040c00040440d40c2c0e81a88040581c400301e044800c02488440d00400003410480c07841000301d0350380e944882 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 296871339 1250 296870089 296870153
    0x20901062a0b06090c0403080d02030627060415030b010306090f0c0b1309020f07121e03021201050a06080a0903090b030f040506060603060d0b040f170c0601080105060904030e030703 80
    0x50813000900442c8034a60400c010b20205100c2010f40b4039450403c100540d503599001e0115540c91000d1200c20010b1940b0750525800540700005203214103020750b03041080c403400b4014805000e1203880050070319031050380140045101c0382c000f2a545070003400c0b4010800d00c01d41d0380790034612051340b000d00950030200b401c2e102034060681e41401002c4085d020350070841c1000d150340700c0d480740540040a41d840c890144004a0180594141290610080c1d000400c00d41c0c10280103588080c050038880e440042c0080740c0751500d05c80c004240c911954440c00c1550300c0d4030f40f410042c11400c0c025024840c1941d0001104071600004510800803080c0381030b65030916243c0170b0b1420801a010500c1181c046c810004076807074082c1d82d0300035150000003541075a1614104503544d42c0d0b0108015040309203c0c0303460082103e802c0b004000605c4228100c4203980e80c1d07080c0003800c8a030140c1d00d20f9803004a100c0400c0110380300c3c60040c001140010165061559a55544141c40031320303c4400710380e00340c0100c0103c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 296872589 1250 296871339 296871349
    0x1080606010518090a060f0609290406110106120f12020609030d0f0b0406090c0206010b030402060418020c0f10060e010e07030e250302040513020901062a0b06 70
    0x140000c42820300506001c0700300c402400040300d4010f818010328400001032a81c41158114800500504196951090329044001d0034203507503021381d0b00034405162a5020004103469107030441211224458182814580110340071085120280059902d0f0540415126580101418464810190a500c0c928107250109000f03003c06200800d5401002c10040071100110440d07002d64080040012641030310400f9000804030810900c1e0410714024010900c4205503208004450040d02225004d0b1391321425140740d480110340003904160306000c1007242824482043c05002c0b0340605c090300300080c5012480c41c01001c011002e034a0360120741c80b4154402c2922500e030140c841c2c45120303042c075810070358039480c480d0024116404240d038401c240701c20703208203000704020079001060301d0184441c0120601956140c43c0801c2c1e20952500340850050892420f400b80c04a5016004103210703071032700000341c0c2d40064242035040b2620741200d0088401484040c09403a007072003418140b03030354200041400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 296873839 1250 296872589 296872591
    0x2030f0607030507270501052a0c21030f07060212040615060f0e100c140304030b07110d2304080714221517061503190605040206040302090c03010806 66
    0x700c0044c84603c2c5c1c5000c61102040000a859082c02d1040c1d0b41c40340c00044080c00c41e03202c1c0e481d4034071000d40001059007420114001500c900116102c0d4001c5400724180600388030804800445a030040044100550083c4080e01540d406000b00508015010311000171112003100d0803521a59607258000c1d421040c2035030365000d480140741c918850240c44201510100c60254072074411580c000f01d42080500c07074002d401913954460b81c504880c40038480c070140d41e038100d03000803aa000d08150004546a10402c11420a40403500047c2046040c1c41c4050300d1140b0f000c0f03c04060750a0385155090211030810003400184522002402014609500b88a040c401502c00b280b007145032010703a59440d0148103458002035a10038001590b0024001b030b166541c1e441e640201407841101424680000303001c10320512070000503124440400640041640703c60f070700044017000c0703403044038801d0128031568081a4460b102621607440c180c0c8076000200404411140d07980016800801884142800e11080d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 296875089 1250 296873839 296873867
    0x1021504170c061e10060e0a05040606050307110d080a0c020708010501080d020f03030705041a0d0c0c020102010e0a021e06070c0308040302011803020d0803060402070f050c150705071202030f0607030507 89
    0x2181060620184204455841c6e00c0740d1010400340c0307200d1121640d15004640000c00d8020b1040012720741d15240680240c10890380e550102d8206140850401004100d16040385260b9658400c00d0341c51510b1900104210114401148111034002c03402c91802d2040c0381c041c0103008001c0c00c01500841c0000e00e06205024142104e81040c02841303002d0382c00000f91000d903240d554980b0002000c40c40d114229000345d03031040c80d0760f5042c00382c4d40a406800810400800d8004e07402444408402200310b5514151580000c1d00030160f001020005101d040b00b05025201c000c0c241890202d10b51030b400e0700020290010b07112000002002c004540e0801008003201e082c0c1625190403e01c0c54001490413128010054181000007000500e99039460303049407941a480210402070700c40c207080080d41d0302c020704000c0d07028200304034000c00703c1e1780d1343c03010b8a1459503c100101401414410f01c04441d03001c4540490705031159803a4440015000e1001504c14402070307900107810324229100405130b007110220 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 296876339 1250 296875089 296875141
    0x50f2a07090b03030a230703080115050c0d0503091f060602061006020d050a030908030f040309050402120a1512060e07140105070b0601050c0f03090306100501021504170c06 76
    0x882d034001d4402209440103031885060407605003144007403c2d200b0441e05550740c0c8180c480001d01604154018144034160b070301100e52000b40d20041001519248507074507501946a0081c0b25540d40703a0b20820055600844420949040f0b0b0a145900400c0c00700c0059a400c0c8180c5408007808610707030412119a115000d000f0f40803519181400203510b9050305801c0349c08000001a25040e03103070190700003540c06580f101045949140061008410407402d0b41c080b00007480c41d400003d0945041d0003030f128665001070088459482d18000000103203428030440c1e440e403104010001d64030012880001070700d40250408904040a5001c0d030b400d1100d984c00104040142070b0028542e030340e000080e29010303a4800f01911481e228900140c07a5402000c120b11180e104080d00300b860002d011020b0031541d0000e90455241c0d0300c03040307064a0581402c1c0036181c01640705d16100c1c2001e00003203182070b401c140154402c0450301c0907050039420a83c44211100b03a254402024044074040c1091000b80045c3c0100d2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 296877589 1250 296876339 296876351
    0x11406010f1209110a03150609050c12040203011d0303160f080a0203070c02030f07050102100902060a050f072003060604050103150f060b040e01030c0909050607050f2a0709 76
    0x103010b000c0300c10542c41902c2ea0740d514900314041091104201a185400420004104e80d80703140040c0110041780c102c0006038101000019880306030b01500340607100d2068003c0c200034420703000d4841d05174010404d90303040d9219500100409007916035510300a00444c040d5030b0b00d18004c0300c05503000547c1a00d070400c01c47c603180841080c0740e000100680044e0100400340c0e403a16100412284902c40c190040d6040c01410070184c4400300c0014001c049460a07001da94480c1e035065181400c54104a40c0039401c4101009900e018621600081045143e8403501900300949600d8210442c1c143c2541c0800b185151a000c000e6031404014a80e800b10048605105070b41c199542d065656200021280702661031f082c000d42021040d0300042d007d0070703004a41503103c640d80c800c00b240d110000e200940d0528030b2488085880c81c0c00c2e000340e06015030400020301017602d69000c2210316601110320740019450078801148406000326921550000b003c02443c1e80001e4104240d081400c2d6901100c180c03480e1030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 296878839 1250 296877589 296877617
    0x14030708100807031a06030c030d0305011a0f0a11031605010209012d08061c05060f070f020c0f041116030e0f031b0120030705074b0801140601 63
    0x1d2805c00702803200c1540f80c0c200f621010701092409130f1040265a0500540410420403685648501c0c102c2d4140c0120b1940700b6070541c4c14000600c200300880b0308001042140600c0240550385011005030407108580c9080c2c107036202c10201b0074203078008030f8140c2d40006e484400303580d000c100740100001c0301078040b003600800310009074503014000140f014171800c0e1001480a948082506c2540b6542080a1072001840d103421500c4510407145040342c0640000810003080c0300308440e0151030110780007492991002410007001108016085034040c1d1180c4880c00700c1940d0f200541405201128141480000c500d4064074070340542448a005408a50320005a6500066092155460448800400036007600102c82110205078178400360710109030f00083c2c1c02400001050398600403026221420f45801a0b0b4819041c0c1601d29018502d42001a100414580c5000c032200038425844e08028039054a85c0280840035074401c0f1016556132414170b103407140c0b40104650042c0c00346020700e111310f00380b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 296880089 1250 296878839 296878853
    0x4030c0e1b03130809191d01260304090e0a2d0f11031e060601080717061f09030c09020c060c130504061502010c0306060210020a1403070810080703 65
    0x7032043c240a000d02c1821000e200c0b820049405154020305828a40780e86a480c59000d04800e1144030680c40c42c080300040100405d0441c00d042e100b0000403c072910740311a5414010390f0b440d02e404081c501013080001900a0184201c1121f54403100103032010780c40070b0402404c9401c58010f00c10303044080d03c210300d000003900440084030680c0300400c5503111149050080408100c003200d00e405210b103c100590b00400d0110342c0e0f40e9082100100c0d002642d90000440e040c1c803080d9010004100034000040300064030401541e413112001d0041c0540b06807080b031840790300c401e00d0f4889010500449007481407140d0b074081403000d05441d10095140c140486025941c50740000e05035003040c40701042110011401c043c9a100802c0020014420305071280e0200e1989a19040c01c03034055860105844441406402003c0466081d43c0152011021988502e07020790710640714102002070340028072000075031000241d40261020b98640c205407510110381c0e02001102e800144060303122000400c005010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 296881339 1250 296880089 296880091
    0x40e0309010f0507060f09020a1a070b1503070b0d0f0e0304140a030b070203091215060907030207060f1d030f0a140c0f0f010c0908030d0c02070b04030c0e1b03 70
    0xa2030708000c20342d80400100e4003409070030030081803503050000f81213008200ea040072003140e00840701c10140640d078090103c42c100c00d022001c3c05e01ba401b8070854010030070110b42e0780d5004100f000c80e80b200d9208840081d0910b0302d182c00004800c8804500c84000ca0480d116400c8983d031010340030400140c820b100d25943c2e001e0b03071050480031445012891803d807501c3c0602801154040843c0043d810702075006500c0341c00c00280e00d030040f20890f10303d14074540000349800361801186805a01c40d02d9010a100422100421400c01c0c56020001640010128070038041c131a802541c0010b02e52121069001c0720024501207901907a00600240070b107050020201c400006050810302e00e41c4c0703541e4140c0001401510319810fa0b900804e0002c1881450102e2543c0704103084031f00800c516401c00a0503600480103000c0e40c210b80d4001d10030026174481d294854002176a40d070040700c5145550321122803441c0d00a030000c503031003c01c6400c20032211740d10113241034006a1980d19602000d102408641e02804 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 296882589 1250 296881339 296881357
    0x41206020c0c13020301050102060f040f170c030d0915060b0d050901060306061806150203042304060810110f090d0c0e012306090102120d1820040e03 66
    0x15000407480c0c80c1000c02c2144100c1010080c200c010b46120038800000290030901c12140540200000140c0e01c0e4014210305228550040d100d103810645900c81d2a03021080309410b80c070185040119001c0484200040c00e5900209030020422650310320304101030030034241c1e0141c204c03030920405001800300002950100140307200c000030b40e0790f51150800e014000d40e500c081c290a00c0c01c603003c6500e110b040ea5055000729643c9090042c190b449142c09840507118210f480181c0040c80103200d501e100000362680e01c66006000747c003540d0110009000c480c142d90048100754040000e400205949010320021884952002e03824068040c003120258802d801d5400c1c440e904044031402000900030b8900003070141302c07100051070b40e1248072a43d0007003091445100c6035542d90b0240c030300f03501c0c0901c11200c0c0c452041e40a00354480c942d2882c9803850b00078401074000c141c4c9450843c2e1f00c502d00c0c90070203403041d1300801100400000e9000580100c81900d0780042c002c90610860005000300002203401c020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 296883839 1250 296882589 296882591
    0x20c0a12170a050316090e0a0203071806020d0c030c080a030207170a020c010807020a06050f060a080303100b030402031e0d0306090b01080106050a0314040c050301141003380714041206 81
    0x1005021700b1125051950850210801100d09000e80052140d0146224180a80301c03042140041012000071004920444005070300240c0340140301841a0546008a8070a090503801d00c00c2c5681d808030a50401d84281c4c00003640401c4400910803e205d00740d64004900390b6407490101ca043c0025258151700043c1c41c1070007840008a0711b0144200550810240c00c2a001c022504060300e09418004065a4091084103583d40105440c00007104507400707401d2103903180505501d403c0344550103400050013640e25004d031003400c0b103561035240c0d11000302c4e03001800a08018411018064203c503480d030403030004945003042d042056600002c1d401d040d41d010342000d0307884140d0003c1c1103014000707545800d5004019102880b04010700510b0308000e4072401c80086c0f02000840d840d01d0100c03001102c076404106400703181000403899031001050b03111101130500d000150302640705c10004802c0440742c1c0301100842c0030800810340c80b44401045a9001e0b001a14252901260700c8101c0901d590140040b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 296885089 1250 296883839 296883871
    0x8061905011b050d0305070206060102070b0313060605031902180402010f03050621061b0f07030c0213060e06031209180618010303080406180213020a020c0a12170a0503 74
    0x1035110000b0000c19603901004551103100d0380200180030300300544e4040c01610800f00420415800070034520180c9941815003810340d9100c2d00f0044500740c8101007502d00035603611010419407000e000080c0b0039950400300948800c20780c0306004414090100701d6841141400c00e120040c4c0c1d00c000d210b41c1d191a43e140100b09600d8800010b541d0320210440891b00c851182901e0b40d084a021070110710809014540710001c1110103060015881220a40c0c3c031120070400c0b9a000181c0600212000180082c00c4c3c3c3d01c041c02007a1191007102c0d0981c21825000c00090108455450200054809a4800c03901390381080d0001c004034036410b00519844a64108040c00290b03c2d482d82200078402c446c0380514000c240d6981d0401800c200e1042e101a99040e081c841800303c00090700c2c802400040d400f0b80b0900d80591040c80e408000c0d08031006000450040740c00d005031955600b8036446c003520041440803803014462130081d59a8581d1510b00311f440c0d80a001580c00b154000040d20740c41411140c000b651 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 296886339 1250 296885089 296885117
    0x11403060d1703011409090606150c0312013203060105062104030503060310090c06051b0f030a0207120c0b0f0d0908120c120103200616030806190501 66
    0x1104070810b001d0404400044000548180c000820b640714000940300360302c690f100d08802c16180c040445445400c2441c8e5070b00070026140130303001030200701401c0c0300b602d00f0b0613800700101d40030a200303900072091801c24818841d002c070b01d0028a0401417404483c0342c0c8107260084003188e1602c00c1480748038406c0c1c80110743c0291581c040013004075168440c0c40e903102c407840c2a207400b805681080d14054001c0c8500702045503185498401c0c041503582110903010b44030300d405002c0b1340ca94410071480a2480c602c0c4080034119100704084c00f00920143c0181d0749441041070000e103032605941c807a0382d2030328210030810049030300922200142c5007055074850303a802049100c07a4151041403a1500d84a2800040100f0b204080010b4001c1c025401c00016098480400c008a180203d0381c505080c480340b040100f0004100c4c075040f0300c4240c10f01d1901107c101d030b960000340b0240c00196943c000b0800c0810000209540040c400d54013500884031030340c4201c0f10400d500785011550040c203051010000000c06 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 296887589 1250 296886339 296886353
    0x2030c07050616080309150c070b0406050606210403141e0702010c02060d140606030601080609060a0803070609060501050616060b0310060b0a021b030a110a15110705011403060d 78
    0xb14094100411960b81d08106203956520110030002d080d600b1414800b00b5232200354a81158034007508034140100985450300d903032000b4500a402c542e40b069041210701580c10094400c581c0d10624003204040c5441c19050107013010482c1004008041402c003c40074840b07845a80c0110300101024085444103d1440107a83d0b0110004001c0d500040101e520408420300e6040b51500e22520b01c3c84842c15120b220503c48580000e841d21170106113072000080c058203041e9003103640300c0300007040d0f005455690001c4034103650181c142510f0194a8440c0f45003402500d02a19004244c00c1e6401890314003121f001c0e0342e0860341c0c044020002901c4000400c03495404009001e004441898208905a0f540d8640e01165000050200160184910325140c8601c09004810b55020103009040a02c5032030341c541d01c014401d200700a40c85284081c011524503520304c1e00e1078000c220341c1c5400000110892080e8584003150b030150341084600c4020000d05070000301503c0d0020020703562807402121500e0010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 296888839 1250 296887589 296887627
    0x50408070315140108031b010603020d0b19020334080403080c19030204080c04090804050f060403060e061b09101b0f032a05150c1c061502030c070506 66
    0x10741100180f0008169001c01100801c240e410b0745401110014542014900b40c070034900c0041e5200c14038014090109041e1403a2603417015165110025043c0084205002c9030815035070303000e0020001241082c8031000c03146010702024060054480c0710440c1d0401405004020300003400c004c82180800c02c0ca003080001c2c0c0d02440d09490800e40e210301c0081c0d0040080d0858400c0102620030f0b008040040d00f0030b44642504140c00c122114907003401d02d001d101c181c240d005d5240781c2001013080000080303903035841203101e06a040f00242c074060400c0e2000d4219122030000f5210107101c1041420341d40e0b0303203035001140c082e0f5007400c10314800d5402d1443c082e10740444100c050640d4100c405010101640034038030501031030029040b084000352440509603544032200000340a50700c50a0b0400c082903d01c6415030384865045000d03460324940386c00c0540381c2c40f103580c2c25610032500c1342800d01100d804404403440f8040c1510045083c4904190990782d02e6245214030b50140c0800100390000c0c0c07000100130 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 296890089 1250 296888839 296888861
    0x31501110a050c040501090c021b030703020a0902120105060301060512040c17070f150914041d0c0102010f0902060d0b01020309031f0c090305070603020f07170c0d050408070315 78
    0x510324140c46401e02c00d496807800c194451107180750a0000c50020b2091203507140c48281c0b030b4011322441d0a00242c401720b110f180401140d1510804100200507520a01018040d02c0d0b0414050380360107420300000e80c40081a00001d03c0f41009000510941d40d00401361a0160460984100301d038681c1e09110030080c0d4036401c050300152441100303540f6a1030024040741198114808140100ea50b041158411008100450b0018203000b904000c13507103007600003548000c0002e10004d00040c180b503c8914030360304013a01d402c1036004204130000a40c0c080c8034000d00d200c040b00042c0130003034842d40042c42e907100f040e02e0304e82420340d95022102141d100304290f480d403004c05000c5039902030060343c651720003180b9010065092800d10802a2120380f14141210480317500c04001c0600360f0900006070041d4002080080f0349690034010b08000c07451683e50220205001d1401550311100500080e0905018110301d03070501004200800c582613001031403508a90300071940c0c0303800d142004c0480015240003801 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 296891339 1250 296890089 296890093
    0x14010b1e0f0a05070c050306070215150429040b011205070e090a02071707030507120e0a090c17060a090e010e010e010c110a08090f060903060405010c170c03150111 72
    0xe890b003494024000340882030041c444880031710740c1c80b4109139844604494500c010f1300008600d5042c1003c10300f500780c0010f11852030f89440340703200700800c04495141c05900281c51580c070700340d440c5150340010200385100581e4140b00d4017409000280811000e0701c1021038070741d44c2d0700019168512464082849041c02003c0d00094203101e0220350180d040282c007501c4140c0060412403141c5441012036201a074591103150070050700f078640050703a903100090041400110006a000340e61003102090207041c007a84000fa06609012005010303c0100080d60320400044c014441c0f181d84070180841161031076200424114281a080b40c050004030103291a5582000c06058407080f0640060103201801e695030303812034184070709040e07584480c030a018143c0181001403050381e003012280266103241c0601040d180c2039440001c00d20f4004100d400b80d0b600d95465030a540c0460303100d075100c80c03402d404100c0742034581420942500c5a1002510402030045a003005075050303401040384104d90354990003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 296892589 1250 296891339 296891347
    0x11120906091b010521011401090e04021c0c030305181009051302131202011e0504050904030908030304060614010e030613060608060414120c0a1202280614010b1e0f 72
    0x390f0005c0980c00c0c010b40300d14aa0f00351250100c2d5100b01c104d0400c40304451a0000203032a41c3c0c0034072a0b400310000c3e000c120450b1050350300d07011458102c03902c0000c5110780d403000e988024802c00c0603658140c01030b18601c98030319042d40c91511a484506001070300d5044032400d1081d84c240b030540009106500100342c1c0d041c40c01ca400507888081c0f4070f81460940c000e032160542d14400d06120075540d929210090040f4005020074041828a02b0000ba440752003401e041603015100c0880b03c0c615041118203c0c0d45940f607510034007000b0300c184001030410b1402c0c2040d4421090a1b0000fa1f250303a8000c00da510b096178011500b2041c800c2e60380002e40205090020340e50141803e00300742c03820480f41c42e066281446284041f545041859003101c00400865020304070340800c1d40e6440c3c0d880041060a00118420ac0200c2e40c02c1956400802441c5600750721120f40c3d202444c50b198080e50f044c107040388460105000100080311110b400c503110800d201c2c01c40d26000c0d0f0b121140354054041c07124040d4400384c0c041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 296893839 1250 296892589 296892637
    0x20304051c0c060e09040605060a030f060b0a06050f0d02090402040504090311010c050423030f0712031e0905060c150c0a0e0a050604050d030306050411120906091b0105 74
    0x180c40040c118040c824203440780f91111002d84240d940d005516400c280c1c0c50b00083d01152050b4859504520010035044d25150740741c6030201d4480000e442500d0480c1d580c001d089052400c0a10500180b4250a1050400a5800d13a0400728041c000e025500c40b900082c030590b00d036840d5030443d03000d080b0007003082000d25001c0c00d0042000d013441412503031640c81c4c44030700c0203180c0c0144107540c200c2c2ca400e88600300b4501d600d58a00030032005c1203402c40c1c26101d034042800c0c0b028002c2c48080c02406002d02803043d150350300d080092643c000e10321010400c100084115020641c0b001e5a002a204141c035425503a0703052200103031400301d001da420b18009000e1818014820303a114020718800915a41d40e10841880034200a040c00d01845880d078807003400c0004000300d0814000d0344401a000e802c0000c0c0040c1d80c0c0011130103580b00144000c444103070000f08210b16501a03010305403c2003882004280078501030408a03a03c0b400e08100400c10311034409514681e81c07056044500c04108010122407240e015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 296895089 1250 296893839 296893879
    0x3071503020c0708030903070506090f220b04020702030d1103040b04080610140904030f0306050402070503072108060d021f081b0703050714010207020d080a0905040e0d080702030405 80
    0x4824100e00b0f8012481e0004071070b6400010358a81d6a401006080000e2418040100690001d6a11a0031138680c10725580543c3d07803800004590548652a584240101c10040b41141c2000081c0d81c801e038814000400075880c00070381e0483d03041d0035060020b00c1100d022607451850003554417030591504001408202d2050100f0703860301401c08001d0440c1c2140e100c1d445050081c0d17558079940e410221020005001c02d04c524500d0f080540b1600700002c40c5521200814283d81c410041078483d40e100113500c0003007000350040142c84859080010311100881040200a4000a0043d501c180011120702c4250355458000240d50099442d9503030110320002000b500202044503105941042c1070034a000010325801129804c2d0303807595640d454044144d41d600082441601c401c6050340d0700303020580040c8c07076040c0403008d86c0e401030150381d03142c0001c0c003401010081d00d6000140a2410300760000c10311140007490f40200b00440c14203130780301c0e922648100c0c41c41c019079000e07a40c0b049842c444040c10100c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 296896339 1250 296895089 296895097
    0x30b060d0204020f27010519030b0f0a0305011a0f060d0902131803020706090612020d020c15101d04020d02040f05070c0611030c0a050703021006170609010b0f0f0307150302 76
    0xc3d03c250f5404415645c0c005407018040c0a0342e100407007a11001103041c3d60300c80e61080f001c5071030080c444500c0900711400f05203030f01169001201daaa64400c0c14111107202510300078040501105e01c4003d000a00f0045249070240c00c4403034040c3c1d40c481c1d0144c0115035529841c00701880c2c5100c810025040d0010426180c0c903164001a0054014a0310101d1040e10461440c01650659100c241a0f4103900c116440254016821001007d50901c50b900c100c45044c4841140d020722039510110500f402c92564550201640c03201c00307084812402c10101c030b40002d48069102d5011a02003842a29500208001d001840c082c65002d170310381010401e00a81042809600300c0c0105020001c000000115215910050307801030b4082e0002c0c492001c0e90740c0300e4402401c00c1c81c03103403050b0b850120041506406403003082d004448000410403107040050800c00507a540a00070000034800c0c401a200401e4903405c0264040b402640d03041c1111b10b1070f4800b040940001c0621b90030000c14400c291b42c0c010005c0d04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 296897589 1250 296896339 296896387
    0x5011b023114181207140609030910030b010c020a15120b0d12090806010e04060b031b04150b040b07020102161404091104020318060c04030b060d0204020f 68
    0x3608040d00c0a0900780c400c1410108200c000c04030561201092240e8105469060428500c222407409440b410088090448948103620500101c80c00200701c40c1041c50061000886920a00615171190786001c8810703407845039400c001031311880c00c100480f059070f5480030107904031508400000b008a018500444034a0140d038403142d544544525210030f8034100360f50320b0303485146c01e00b035600440d0f000c07079220790640c0480c00d022203099035455090741081400d80c80383c5030048810041100348800c50080c0c4001d51401c42c0902a00d900303028240d083c01d10382074031150040d03613900104120907002d960190043c01c1d4401506490b0707170740e880c0078050b240e00840c000c0f801402031284518442d40420b004005688a82d600b045411815034140001040d00d0042070301c3e000b0840701880125210317480214011603007103180c0c1c0e030840c0d2007200c050b00d400d20180150020392000c00040000c41c40f03120185c0d030008021035102d0b8401120307000080c01f03405190b0b407444103203200081304036400400032400040b0107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 296898839 1250 296897589 296897659
    0x31201091104240e0a0303020c03150103032304080313090f090b0c0f09040c05030f07020d1202071a010f0f06050a050f2b0e010f020301050a05011b02 66
    0x204200415100c0c1c00b8030700c201030700d00d004a50071030300080c10855070011000f07035442d0032940782d8080c000040c0361080c0c544c8150090b80210461742d00d241070910920000c035100e90407041c0c0b1545140d5000304000b4540d541c58034003000008140310b99020850427034006210b001c00b1031351030715107020500300c0d038281c00c3c422207201520b04030f10110419128092a081c40380c0141700e81100780d6444103402c03a10f510503c80860b0480003004003c135039603650301c114801c880b42d44e5159922441c01c4020800c1d1030078040c000078150b6224610f40c0c107815507c204c17000c81c800454003016071104594505282544444003201681e882e02d01c002240c100075030f070b111404a441041c0300c0c90740c00f90703242010384261080911100c00a00108003e14401014a00134041d20503403007194400e9425240380300b2008018132084c04201c03910303004a0050200240941c0502c03101c5580c1c114a507503d014006460034042c2d20036241846043c40c005604825000020440c564010f01130161181c00303c1e561042100740d0000c0c0c2c40c050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 296900089 1250 296898839 296898851
    0x20406260a0209060d060e0709050f0f0405071401090305010c020c1005130303030203220b060102070f0e06010f020304090614010f0206040b060906060f390a120302040803120109 78
    0x404400120034030070a4000e4a40b0030785403208002e0040c1c2c03a1200b242030341e4441d1030354038490340040c0c01c000e0742e0700900e40b1010001c0c941c103216115270f609840240c4000e912004000921011030004103081c0201e03491056860104040f180c01a40d544e0345640c0040c2c0030f03500c3d001162003034540115a890800900725081008101542410b6a440c0198103110080d07400e00c0100b803001078040c0e40156004099603050320301200544441140b82c40100008541d03540d040028000b903541c040002c100a0300c1c19210704441ca6062003503101181e0f8000b490f450401c040c490405011500900495000d414030002c1404002d40381c1e2914004100c850030064001402600d0341c5102e2480440c01034040d83d80001d01c18071589602e001c2010f1100058516980803070104201d04460209100418080030203030a0303010f4206a0086c1c440f021641442d035948400c0c400c03c050040218003040c100403c95200300100003d901143c2c1c1280240035640103d400f6200c000340c5038000114500ca11030490324023000c00d0103c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 296901339 1250 296900089 296900159
    0x140603030408030301120618050106030c0b0403020f1003020c0a080c1e0a060c09051009080105090606011b05151f080d0903030e0f0612040507080321070c020406 71
    0x62031241c0d10a040e81030b00b00b0700c010301030717940c0c003c0c0308850450103001d011a00018007052820314038215281120240c5d50398070100200103030b52990070001c141340c80d03045042514580114101c1841c52010074403400703440a080303103500d001c0d90664010700150f504403a4132400324a0032402a0b445084c81d2841c0c0e01c079118901e0a07881e603514454152024140151a2000d880e66820b0040d080840b070010911403074141c0411039071144a0300314031900442e83c07003940303036498080c08500f1280041e020300c0594002900f000403a0742c101104a60800800d0850340e03040b10309003420341c1011a401d4000b65030030b03041c8007070021003924a2103152010f525001d40d1a00b0130703640c858440d5100c4040110801140c0c000c0010404039010704141d803043c15000e4800001c1803405030000d05180d004e03e00c00e102000c0c0c0c02d03050105220082184038007405818004618218924013440202c4040c0102d45036603c2d00351700043c034503601c1404c0d10503500e6401f40040c007005448030b8008107265030107015485100c40c0c810500c04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 296902589 1250 296901339 296901343
    0x1030b1302010903020d020a0801110904060b0a02030301050d140102070317070c0b010909060b04110705070f06081303110a030503090c01022409030c121305011d270a140603 76
    0x11030a60503122407101c1807869081c00070001a04a00740d0344200400c00002d04090f081c040c1028465031421a1a554055101040100c83d80c1c1c0c3c0204008007001e00016100540000440c3e0540c0d40860b04040c86000500d0603884d81050307402940c0da2540041400c03800c1540040c00303a07014011504100c410b590f60100c040b50461918403020f003000818030300412040b42107504c50304845002c1c50003c5160f00f600c1c4040b0307064501200c00c1c0b04d2480000602d40c810b010080c44054007403c0300c1800c010010b843c1400c02400c003c1c000d8505e103d141c107007600d04810940112171092104954800b030301c4400002c0c4c01c02038026007048401128034002d50b50994035075840482c0c001301c048100d14a04080c3d110a0101808140006090300d14511040142040414040001030070104c00d21a119986002000c09542151403d504c0103041c0003460032400c2440040c215046001e07c826280b407289035501c005e1100c10b0340210144044810007030350511001d070f800b03900a444260710100c2508480e8540d041815 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 296903839 1250 296902589 296902621
    0x90501051c0605060f030f0c0406150f050d06120b010f0501050c03250b090a170c0c09040203030d020d06090501080c011205061807030c09240302070c0f0305030301030b 74
    0xc800700c00c0801c44180001d0306503000325000140503000344410603031000800c0c9080e1940c050500b0581c4000c0e0155494a4680a81b501070642c0c442c410043d44070a40b00a819001601040c400348500400e45d620450000d61060008100c052042c00340b05e50503007045142010280505039000c00081c5c030110b0b03a94000c0c07003210030b41c0f000c03c1c00a500c0c19121400342e0700410854501107203c80c0d000740180001c2844404800d020360102070281c00e800441c0d01d841e440d113098015100c415000d040c0640700305030b8001f01d01c5154404050fa0301f10788559540c40007038117612400c4441c3e40002c1c80413910800c1a07440358014801e450800b5004c1102d039880b551299900c4c440007240c107001510030710b0748403003921a60700416005800600b150040070f404821a01004130101e0340d580000b40e81d60003034800707142e0203540003004002c001d443c42e0140641d0656104800c0305004500245a0006401340402010012400c020a00c3c400710b166030039101c0c44d0080c6c503070748280701c140c40d0705e00c5020105540e400c03091100c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 296905089 1250 296903839 296903869
    0xa061107060f1116050c150a03051f0501030507020c1504030302010b09062206051f0305100e2205030706050405070b0309070603110705010507030e1504231c050409050105 75
    0x25082000c15000d0300310307040740510304179954001c02441008648130031954031080c0d0443d028240c3c80b903154400003011520018000e002201d82840d0814103031100014001c2a40d80c01e10b0b006c60543d07280703c0203038a4410f00252541c0c22802e070103504a00b000e509000f80c02501e10a40c020321600e4410400c00c1750700c203829203800354080510006135060741c183e010183d012101641001c01c40c1c039511000a2000c5802d0030b00d09480b0080da01c507100c5010b038140f084030390105003090b18000483c240401105840002401844202c3d16041000d6110701000e0052143c0d66000c4101d80d035a60651a000d0068a802e660407281c92041d00c801144481c40d61066070310a494100080c640c840c5000422070240c90030310100301e1401c5003000380c607021500a0041c4c0b0f12802d0303075880202d843c08d0b0802c04540340c5020505034921400e1500103000003d881c205008070484500c0050f4030a501c11104200d0401d109015000c1044120b81c603495100742d0064054400c03500314500802a40e03131303980300b4410310300040005d03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 296906339 1250 296905089 296905121
    0x10609090e2e06060903060c03051302010513030b0414070b0408480a0801020f03010e1518071d1003110d15030b060609030a11030a061107060f 63
    0xb0b0250750640c4010145000300c8044050600d90b81201403420881d40a0f13003010300081e03280b1505105000042c002c01d4000c00203850104414540000035071003007150920001d040080c005210380300403040219810107590000c1ca080c03944e041c0752030031b0410407510030481001405030000008000000c2010b9030119000100a400c040f40f140801c8000a60340c2171059004050a20100c0a0302c3c0303101c010907008090800a0510380ca00301c1d41080309011843d4050036850b0f00400a5000e04500003065a045070b01030300300c54440e911040d4111070711455005500d9040180c800100007100d01c10b52841c0e00135026501c80d0f0b403200104000c402380d02000b01108030342000e0020315031201030748603510066030b00c250040003505101c4000c01c181c081e260140d04004005102c1003050081c01078008a02e6040002180c02c01d03d40030880001c05c1e10340798124000380001041011213030700350b1024808100d074198080c0c8108042c07520083c0301e030300c95003007450251900f81c41d00f17800103025162403040c41041218840 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 296907589 1250 296906339 296906353
    0x60f152209050118020d0f09030512010f06120b04090b070f0306050924120715030f09050706080916090c230d150e04030309020112020f0d0b0102190b010609090e 71
    0xa42d41c8060742c01451246e01641d61034909405030b000710b1054030032051287c2d4600e03907130351203070945214022010f0f0080351652801c0d500070401c07150041e00e000380c41140f1602c0803520030020340010340103024048000d0f201e41e6102081082c4554002c021000021a07510100001c0d610765003400b24016045680c1c2d4112070950080e900c2c10101440e106101c034034000c1803950480060450b50f400d00703a0580c00303001c40c842035001c10102150035000e5648007a5280754104039103007103501c96a50702c0d2081e100342c600f84218400401d000034000e00c1000d651007039180c40108200c1c0d690030313030b02e00504c040d00c500750014001060050b420003400b85029404804125214141202e4088500c020f181e81411840300e03145904001800340c1c01d0503103142c4a140a910002810078040c000507281c0601c9003010946980704002c03080070b010351401a01c3c0c00040e454000103039007002c100140e00d8400001541601c21007404147c00801c03410329000c0c1d06a88060307803030f40a80b694407401c403000c0e42c503100003030802900042 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 296908839 1250 296907589 296907629
    0x30503040c0b04180e010e100f180f03030207170c0303040c151e020712050105090f16060518060304050c01110c03120d02070b010602070312080f060f1522090501 71
    0xb80003217104040101c000140142c201080d43c1c982140c4010011b01f041c0c031444491034802d014884c11404c40c01c41040900c65600315912618800756503c0002c0502d44c0c00701d444401e1194407000e503480104200480395071107032250001c660b00d0700225411103004c090380d000820310504110030b19038a032946844072500d2444007800030030b1000c501d900060441c452000d00280d101e40d40b0413403501e02e0b4058400040c89040c012038560801c6800c10036044503511131080303aa005491081e00b80122281c074a402d40c0c880d0110481414100d11001c40c8507488080802448103000c0c01256840540300b0980300c81590742c003059041c0b072300c81400ba02100e5240e00a43c14003545101b54030018070380401400c00061a06405540700d050b0000283c01500040e03100301e0b07050007049128050210303021250300389000b4514000042a05400c0d0042c40c2c180030342403108048002d40c03240c03102c00e55440cc0650309103440785121800c401d4410140c00404441c000504000584c1140c14455203041e6550440c801103014041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 296910089 1250 296908839 296908841
    0xc030c080a0f020c0a060603050d021f050a09020a03140706080c09010507150c090602120301030c0512010b09091513032a020307121208010509011a04050d030503040c0b0418 76
    0x7080b51040d12507020406003408032002d0100701010780c86a48005999803d5040c203511308a681c2c89400d00790742c48a030b458582411103c0007404080042280401c0039134820181d0800350501440094020a4003c004410402e8800c01c50103e40381000c1240c000b1070341ca81c0c00303e403107120070b80d5103c05034001006501010b5100d00b008180c0d2500076030035981d0920020f400d5000301d405a01310f0000161a00385c00b0b00480e541401389540351044880b09509550560b01c44680b032100e984a150320891001e030003500000402e42101045a000402a0201c4d05e0440315031074030341806416405254030140009101051800d4001820f50780640d589a101103040c54100005c08080d03d80c600090040000280165003c00c1880c0113444551592003040c0054a0011104904441441709001c00c4c20300600598580765511030445500360401503103041e40d582d46500900c02e50b080a504403000802100a05421100460045219038010140071b43d03100c02007181401180102d00c0e0700307100502088400c00003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 296911339 1250 296910089 296910101
    0x60c3c020102040e040b06090c0906180f0409060b150415030504030c05010516030b0306160503060604030503120402010905100203030106050702060d0914010c0309020a230a0b0c010c030c080a 84
    0x91800014030341600c0e040301007990700003110308031070045110382007191508083c5003913a004059001603a00300004080003c1c0d15003d41d043c11010400420a811600d40d24034400b0358501c41d02400c00c20006440d070501070050401ca094050082100130b10704940b440140c011201100c1203000001c80340341e04580101c025103c050019410005503203182c42c0030803800e104280c01510a51040e03a405140c4100150035a11040082d5109801c8038042101c0e44480b04101980000141b0304a40d4035a6010005030303003401035400141082c032005c41c01d003056a11354200f00380200c1c000d898030403034a95034004003c901d20245204400580003032004008407400f4102400901c6c1c40100903600340100198100116548034606a64032140126601469002823103509510840e034981802020b00a0300451b44002003482442c0c4400300c1c0c0640540700e042d102941c0c071003000c8003c0c4141841561400d0070001c0303400140080d83d440d441d26080d10040341c003038466075402c0c054a1311590307581c0c1c0d20310345801c0040c04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 296912589 1250 296911339 296911457
    0xc0d020c030f120a020304150e1005070b040b040312020409090b011a0f0c0705060a031e02160b0a020d141f0e0112030c0203100f0e0d17070c020607060c 67
    0x6c014007010400039081103640c0022291030343c50311400314030f4104101884001da82c5071414002c04000b1040880c5240d032809038040d0700540c00f00b8607a1164502180c1c0305d0101c0341b049400c10310202c0c011480d12056001941014004c5150b1030540e40c030340c000d03540350b0b43d4041c0040c01f95207003c0041a45110b0840d014000445900003540c098582d1031000c100d4952003201c1c103400003540d8000840b41c01c0d4400d181c0f0400b000c5580011030400e868864030000400c50500c015103083d4600000a090003410b404079003404203031060034040c036410100c58035020441900d0803524a01d60403106004030040805d0141140c03240a076540c16a4070f024040030a200b040701c4150100706e4004280c1c405a01c04200c0018410160540080c00702600f201040407103200d00c1103841590003003a41e20308a15402403c08540c0a15008041d5a07600c030010103488844007844000c1d0440400314800090014590201480500703030346903030340007200940d80c06034404100103001712a4125401c9289241940300ad40010000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 296913839 1250 296912589 296912593
    0xe1e061e010825050d0c020a08041a0706020f040503061608010e0612060106090f0611071413050115170603070e0702070e0108010f0b0a0e04110f060c0d020c030f120a02 74
    0x759000d58094502001d0381c203000101300000303a903810310251440342c60001106440a0000403150b5610b1014920862152400e202c080500701807038001503608685076581d2001e0704660303804400a001f645030300140320301446405264000b07038240b6a08030094803407032803075502c12000d43c0c20f004130b00ca038405c0040c010312340221040143e6141100208061070203840035071941000c6519143c004801b4000d01d8100d00c0400c00381d00080034851200059107000c2c2d0310301d40e00500c59403406c000814081c43c3c54a0752402c200d4107000001031040742c0b508c8090b041c070f4560342d40d00ca24000c001c0e00520003007100b591101e415a005040810118540c40800303900984540306803100b90769500416800b842c0b081e0850050f5035540c6102059110044c031844516400540700004180d01d0015052a15540108050454051803481000c0c540e07030b44401c0c910b02d06d4000d1881c0c0c2c64198203048207503100c441110480141c815110300d00502e28001908142c2110980018200d403058030034032003810742040c190341080d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 296915089 1250 296913839 296913871
    0x6011a0702030312091c09050d060e0a06020306180408071b080d120e060708070f0e04060b1e030606070807140703030203030f1003030c0605060a0e1e061e0108 70
    0x160b81c280010110301e13a0080350507400b42020102035060014008250303003d03084600c0340780001d60b00003003102c048481c21107004150030038506110b005810806a031194034080c00004000b0001607901440c020301c410740b440d036a4041403c0702180c52403400e031000b628145c418000500095801c145415000d484a002c07114483d940d0324265281c46a05070100300850340f400010b8584190070f02c0740c0351808050a0003440641000ba20103082440f02800150420401080b00c0a62a000d561688092103026000b0045c0c1075507075002c1046070b0004200c2c105000c090300c11a89400c1c182c241668082da000800710b0745803060341e556104a903403207210103c0740c1d007111540054094405100c0140114025006940c3c1c0e1301d0040d456080d1500001c00f0300748194600c40040c40842d034090403194145034409030010b00368641000045224100c3c5d40007444030800b00d010008400c0f0300c1519205000764a8002150585600c02006000e0b6042c0d5070208032921415507900b901d42c41800c0898024003102811404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 296916339 1250 296915089 296915093
    0x101a060a1e0201020405040b03061611250501120506210c0a0b12010e070507080d0f050c0406020c01080606030619120f020f090603060f0a180c0e01051206011a07 71
    0x740c074801c0c040600075135808a0200943c0c1858001e0000c20101203003d44a00d28107001844130b6510405940230420bc81151076242d4007a0410040002107250b10b0b5504141c139032503201a03050400c0740a100e0000e4000d005400f19100c06009203400707000014180515120403c40380500c100c00c1e0303014200d052107001d01d484265140c412a140141920b81d02480d0b8a204503218500b12400680c00002c12102040810070800d91082c2a100b10380e600041255603003000d80c01c00c802502100f001c000340d81d8684801c0c0850180c900c0300a10072903240d9001d40340205d25460056031015000c581d0541c1003e070030000682189010040d07513469143e82590400308a880303204205803c03120400840304482ea940720202580b40141310b0042c121070803175440b2410b29080d00881c1c0c031048081c2400b4858900040031940c6044107411003854208030b9664083ca060007414a100300c10124072034081c40200001c000304c1e082c101411790300185001d1200500a903440c0268100f03220002070207103a0f44c0310003400303c540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 296917589 1250 296916339 296916377
    0x210b0a09051302120a0c030206070c0e1501080106050c0a060e120406030b190b0d0c0207080d0201050406050604060506070308040c0308030f0a060e160c02031518101a060a 75
    0x1c01000051900d41c05240b10344184108891a02c20740016039203c1028400007407850301030501525416500075885025a2404085400c0b10f500886600980030703040000f10740c403900b5101840b0f6000d0307032010102d0340d80300002e840303c0c071038440408840e4202d110341c0d001040c02c0350007500d0380c42403200407151510304100d224142c0d038020b0b802c0f120010740c42d13940e082c040d031400500d40004004180541030b9130303e140080914851258006507182142ca4080c0248207e00a0100348020711110307040d518000c0709114028000c24046604a503110320303020208801e414144207406c1610b0018ac0007515156150b06c046d80c10b0a0b0003003040750003040d0610301000103031160001d50700a5940b410900d40d9801c0601981007540c20750307000541001c03424000c00c00c0e040f0f00c1001c050710f140140d040c40c803400c0c01c103400440e0500d181122030f4601d80d15000c0078000001c080314a026505002c1c5425628500704610001040d1380c1e2110800180031118003100140307251a900a0260300100d040040d2001e0310b40d48010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 296918839 1250 296917589 296917591
    0x30f02010f0e0a241b02010c0504050604030b090715120509060622020904060609030201020c010c0c09110c030304030903030801080606030d0f1b080309010605040b0604060302090d210f210b0a0905 86
    0x7410000950303205a05c40307409011b690101881401e185007010300b450082620303805140300c05013800c0e0750200462203040e400d211074405011604461406000004c0014011051a8154203040ca2410000a0503481c001c030b91a4003e0200a2102103200c87c07004139235400310311462100c00d0065003088040116555441103c005004039201c800100d8594000a81080900c2d044036041c003c040a8041c0000c100d022030a042e01c803004000032b0300200c10240c1114902808210144901c0b0000600c81850781010100c021a4442d565503038544c0c1e02e03402040d890310401d40b42190503600503420500c11502807005420310307600c0d62a00c1c40d1a002c3c6042c41d04c624046400e03055a8046000043c0040040c0a0080001600c41620244200c0440c1000300b0250f210358402c4108256010a8461a580c1c90b00000441140c204c42d10400f8ac504a0704202c042880c189005c002081c2071a00350301d80d203400750603a1b01040c0f401205d04560105840c40b513002500039002051380c080c4500300b0204840b141c5114a03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 296920089 1250 296918839 296918861
    0x270c060711180921032a0408010f02030405190503030a0c030905061906090204060e09060a030b0f070306120b0a09020111011d010b030304050604090b010c0f030f02010f0e0a24 77
    0x300b41c0329003030790b1040700c1d001426050444d40090400030410300710550240c100c005064040c40229282c0810302600003401107400285103542840d210300c0b01c0c901c251b0083c0d4040c501a900351031250420b003d42c0074600c084404028500e41040c0006061150154400040100e090801288004e280e075242814aa401c8940c90001d41c80000c40318040078091041d0300c0a0241e9a01c11440e2600b050300c081c0652005250441c4101580d0340020714a1300c808904900465002c0014a140d0911a05070341840c00c0480e82c5200192800c0070000c5c09075889041c162900e03030001c0d01c080980d2120700540c800350659260036814440741d2110f84038000400d20620b5080141c0143c051804900f19401500352051034030964401e034020301041c0b286980c1e9400f183c04464011200140f1000c06030010794140c0020310025020441414400040c55000741100081e07000d6603000b000b282078840090001c8a01c0003040c0401940700c1c112502c005160382007460a28000007000114982c40710104e00c0c00d40b80313039000e1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 296921339 1250 296920089 296920093
    0x91204060201020a020601050103050106050403020d1a01063b090a06230411090306010b0d110f071514070f0e0a0602150a0603030503130204090605270c0607111809 72
    0x85543c613640c103020081c0502400d103014000340d450004014045d018900003e440751038580c40e041c0c10804000f003880f1400c0c1030104218015a03660001504e01c4800c00e00150b081e2a50010f8042c0c00c2e1005400301000c0c19501c04020f006100c18404d0041e0000001c3c1a2a40140ea502022640d881c01d40001d000b041d400741e0a1070941c00055092006030348900d0802103404a06001c00c005175940420481d05507a5000c4041d9112078100e4000800740c8110803112520550028006d10480001c500400d0003c1c022880030304c400b40d000390340ca02115100c0c2c2150207d0309000d404921920702c80d80b0308590701489440c00540904261000600100c495400140540e015400421840503822a0300d40d005a0b051800c00000348bc44d20042d219200040410200c520500b091008658803039010202198000c0300802151a12441600d01544d901c100310001942c001a810f850003800500c402c0c070f200300a0402400c0c08000e03500c81c0500d48100030120750002c64800d90042c8070301d94100d00c500c01c910b2000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 296922589 1250 296921339 296921347
    0x203041a0c0610260303060d170403051b01020f10020a030b060c07060f05030403020714060c03120a15030512070804120501020a1b0b27010c1805040603120809120406020102 76
    0x13410050079040880720503210054804c60b9841d031002000f603a80c005030640380e440307142442c0e02c2d0451031070300f00c80b005035081d900228011060101c0010824001000160b020508011200040e0f903102d407140c0c03540000f03520082c54040c482d10f0a0700640101d01080c10042840502140001d1144d000606c205856a10040c010486568412581d14907031000341003180c51801c040c1c03402500c40c070080c0104089040389000310020f5450b510202d5000c14a9032091f41d446409a500d004040301080d51400000c504100150712107a515103e04001c682d40603000b00004030a000c0c80c0c0342203400c244c4082c0e59800040c00005003c1d2400c082107801039105000060341c2ea1003040c40a881c140d40400900305641200340070b400003c0c25000300a400a5003051801c148440350803018800d40e44d40540841c25500b496010b04100740c20034808500c41c088424400c006603212400e00080f140e55204c0503088445070303603072084d18038065400030b9000800c0905a410000c103009111000e98003607448200141e41c001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 296923839 1250 296922589 296922599
    0x90f03170a0b090604090320011b05070201140307090306110306150306030307060b0409061d0d39290f07020c061602030318130501061e02030903070e16050405010203041a0c0610 78
    0x482650303040314ad5007449800c104154000034a085640542c25000503800008070340910b020308488802103500010034001e1441001442d40b042c2c0003520341074002e0f000c1c0680290a0380c004d10a407845120301500031403e01c4a10b0301c5180107003100b142025003107550f07140c074500031610710302403455104400e0162007000082c600480746410040c040480400400c10090801d65603020803034440c03c1085116008100c44010340440d4400640710028085a5400e0754100e01e03040070003a06461040038400c100407a030b252a00403c40d00d1044171404c0041c1c00c014459a81c0d4500580980344440d0040b0100381c403c01c16034007113861540b01041540480341c5d4510f40b95100c0c41d115a109690b880c03602c0303003880035514125003d0215200c0d2181182110302c509800b1341410301c20010b032144e0290080440d4074039540e504c102030241d00140c03072034005181901c00480c0341500410480f0304680060740254505858801c1d980550502002080d225080411140400750010042d06000c1c840c03032945071258611300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 296925089 1250 296923839 296923871
    0x120703030503190209130e010b2808150106030504080c070e0a0b010e030d12020d090f060c090806061011010218190f09050a090f03170a0b09060409032001 68
    0x900c2ca102050b500400517000fa6483c3e160010307000700744628002c03c4019001d101c290140c6407000004d038000640240d40d04101c039070b1519881000320800000424580c484c110b02e038848410541c8548501d60343d4004000481c842d9104660181c040e2034080d080c8143c0d1b030155403c5c109198407011042203502c003030041040d5544101d4494590901f40b910368080e8170004680c940602400c0102800041030b8060403c0301d0359012148000e91089003007060301403604e01914880007600c000c0d501e02d0b2508891141f030b1400381d40701c1025904028028245561614200704041c0d00f428080170411681760010111044240050248400e500001c400d240c2100d00a12001b112840f041e000700d040a41000c00034425004121004c0e20001c2c900441d4a95503000080041d00c2040801050140080070120a242e4008445c014003070031488205c1450b00c1d0103c82c00c095403814215030781d0144124003c5419031032300d50b000601461080c100044c003400b860310f181d6110f0011107444800d613516804041408000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 296926339 1250 296925089 296925121
    0xf27070c0605010b1c0c140a080a06120b0114010507060204090b10090605042102102a0201120c09030b010b1e0f0a180f0f09053102120703030503 64
    0x1122805c002e1580d000c0400c0300060300c00140402e0303482192055084c0307e0204812150b00294219a6403080d18600801e149021680e109840d490032034089420180500c46100aa4108039145120303400d09003107070611400100b18a05200040280070002030990001d04010101080c000425021940a00040c80a450304107010402d09180a1020941040c140c42c00e4840f62801d840b02c414101280443c00c200e0550043c0d8401485100c18009a41c00f96811648110144110070700d1791000084000255218800a01180b0314680c11030214500f83d200c0080b0010a280038500c02c2d50300d0f21190041542a00006000070740055540c1c2100e582c0d0255105070384c40d90407140e20f05106d0340f011891a0046081c2c00d03040080c207178074007084400e420110704080e08094182540103692107000500341c0343d0902c5041032503410900013804c01940300a01c2c0406000c1c401103040498620350301ca420001961204036406041c107840720750100300070465000910300c40d40384d050356800c02c0fa51203484250 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 296927589 1250 296926339 296926349
    0x1003060c03050601020303150109180507020d03020403030e010f0c0b070206060312030f010b1308070b03160c0308010e1b0f090906150706020304170706090303050108010207020f27070c060501 84
    0x20801c0b080c04290b0364000226030f0302c8480d4080c2d00c007000485c4001202d482c015032380000800010745a10244411050b032040d40650b0190b021601440381040b000d130164050388c440034001c01d210f050041c5041d40150140f28034641e079807030f11421400a40e6104c800030030f4240c0d40702c401039200320100010360070100108007000051000700c038118503100403003900041c41405514039038440400c454034182541c005100c050510b620644400903141d404000d030540040391541c01c480801008090b00d01d008080b0f41c0388558160341c1d0301c0101e84c02e145c619903401c00042c1c00c00c86440000e0811000540404016003400c540449119a03202464001c100410f01b018021a109122030030755a82110351034070890b0100c0750302c120090788030354035410b040c07420f0f010a6007194a401c000050710020000c455200281d00d51103510100502c0c1d8070380294a080f805082002034024078aa8885800c514210410701c00703141c084000c030b4580c2900300040d1441007009692035408100d48500c0401000094000c4902602c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 296928839 1250 296927589 296927591
    0xa020601030c050d021c06140106030e0709090320030915041404020c1c050d05010e0402030f010204060c0201030f090807031119020906100315060c05060108061509130b1003060c03 79
    0x8141c54000400310400000c2404846c00b0014105041089541150382d148009280c0d10003a9a034401e0b010b400307010f41859860040c0225200413598910034410440d155807d640c4004841c42441c0038105c0080c2c41c15621200b500c41880030401c1662800d0409000240d0042c91603150391a01c0c00c60420560100da03401d100c0d80c01071003204140880028038180b5a1403a000c801c000c0c5800340002e03200c52040035002203003582003100100e481445a02041d01651086d0211043c40c1d04a03907000d4202c0c000c074043c105c002454003460320095031107074002c903114900400e000a03244140743e80f50100d541c41713008200e000c104000683d440c480c1d000e00890001080b005001140e00e03205074001504a8170040040d44141c0352100000940343c8241d01c80214407034500060f00e415525000c0c0540320f00e0306e040040383d41d40700d10800030400d15001f1854070301654501d000c1754168190380042001e00e01004112a90001d01e03030b041da202144c2a0b83c90300d03005010303010b5101009030031402d10b071082e2070700c1c40780d140700341 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 296930089 1250 296928839 296928859
    0xe072705060f090a170607050f070204050f16090f050d0302030d0f05090f0606060403060203040f0b0a0b0a050102010e060408031803030412030f0b010e04051e100905010f03030507260a020601030c05 87
    0x317030328040361035a844409464000c1c1d8404040f0009500b6006a200c041e400c24035000401102c2c243c0c000b0f0880c01b8051030500300c0c81c5218101c078110707030042c1b4602030803049030000c0708108101d0a201a0010040e407007401682d060051a54000307080b034a40d000c280d0401c541303c03000d0000101090048101040c0300e6800f400081c0f821070041951131140f8031009080a60000025046c0656a1829242070754895004030003410144410000740440680543c85003e590302e0010312980144100800d1198080103084039a070745840e41c0003140c00042c4031071107100d00c1341030007080b07840c051008500c20341c400c203216040c07184207003001000c4a641c507550503803580c40e09100d00b4040c1c2c0c01c9005071051850407034000c2100c1d0345400403045008001c0080c124207020280500c03400e0340c0351a206a095507098402044148e80e204c0c101c4508084e540f1000d40411420407040cbd01141e500c3c1844810407030300001b0300008220712074081d0020b50102c07040c0001070300700e00014801c0200c02403450000b08411a5100c0003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 296931339 1250 296930089 296930129
    0x1051302090a05061e0c07140d2a3204021206061614060106020709050f060f030f0109030c0605070e1e0f0d032f0c040f0f02030c130e072705060f090a 66
    0x52202580c450525190409443e6911300c074020f1000c60107403001c000c4050b00034030091295512f12002440d0b554240b40b640714600c150341014402c0e5403d05c500714945c1032054407144140f000e43d07400408400c82002d1144050804120724040d030415000c0c0ca100107008d1985841d0009050070000d0304500c415078201381c18088042012140150040c400710350340c030315180c06040040d103808084d4400c01c400d5401e01c0800d405064001c0030301b5010071701400d030a120310b55850004844030000e60300c10a84c000300c41420040e0b4211003000442d0038080c05061603e40781c0c030060028403200c0380520101d0002d510031440324032684180c6d01e1442c04501900ca03c501184900111546480a03410f440c2d0041c2e0f034900c00c102803210796030810101d80c481101d04641e281051039400e03000d0760012035080c40c6040c25000000d03d4442d01c4c86254401c00c44d5580c2e803240307629500405c84583d032a0801b1000d04840b460008030b05983e60758000c0240508010f240b035070702d095150920040c1c9405038016080018a0100004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 296932589 1250 296931339 296931353
    0x50a0902011e18080f010b190e0405030c010f0207020f0a03030509040f06090f0b1c031713051c030c0203030103020303030403030b190e01051302090a05061e0c07140d 73
    0x2a800c1c544181c920b4040b180c44500700c0d040c0e03101d5944002000079100c0e00182407100420000181076100c0001c0c07000a454109001d6480ca2010119040d10340c600390410a280f090305081ea0050700c26000d80b843c141d4583e15150960301025221206160b00103200004c44c6841d0b0040c01607140309690406441d0318540340500140922413589014a03100c000c12142c491940e070100c005448020f10400c04480c03041307207441c001c2c41e940c1c4038103000c0c4607010610542d43c51084117502102d80d040c2e82e0064070b608000710b80a00200090000f10070460f81a81d0361001038000e011038484151407581c828103440781094000c0076203242154900942d0420401403016840c08421694416003604010a03160389080c04150f07012039040305840032010468000c94541103032100b40341203442c00c4400b00c44010042c140f0038224895064810b03030284170510100f14500300344002d84002001c1036880d11160000c0d003603210103584034007080b000a030030000c0c0902c00d6400010700c1081c1d14030150390401c03034141070b035640c24 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 296933839 1250 296932589 296932607
    0x210204230f010f03050c0d0e1c1b081c021b0d03021c0e0705030609010207030905041b0c02030102160c0509070503090d140f0403030201050f01080309150711030d080109050a090201 79
    0xc3d00301601c0d140056125803c40003103603613000359010100084007107484496102c50780d100d64040e90b40c03c3c0c0d60750703d05494440e141c7c00c080034031034400c1c40200c403505540302c0d08141e01c04140505512140140c1c0341d031441103480940080ea546071240c1810410304155070741001c1e01d1010b00f0040c03510512060a0b0102100d40380c02c409a0014400152090410a0a480c121103684035560600c100000c201c2c4018040d0080c182c85803007601da11406603142c0c0d040005407958a03415081154030b0f02d104000f1030344541c0b035680030140054001031034580c0c0401c00d00e00c210158802521064400c036420440c0c1e0030080035080d400325003440c00c2415810074210050b2503080c0000b1203010000ba000c1c019400ca008001182e01913a071107c007c50351680c3d6850040d002c2e00e411a8604a01030a400001800c0e100100845544640007420399500780d00e10309c9000b00941110b001511050365015210803541c8081100e0b80c40b04845483c0d500d160740c03401c9a0002518002005002d0320f40c184001000182d030000701030717 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 296935089 1250 296933839 296933867
    0xb01030c090302060c3a020114040602130509070309021807090e040c050405041a0f0403140d1d010905190c030b060f0a030c06020d0507080406210204230f01 69
    0x20544c5d80021300c1c00a803800e03082d444018101c0210700008460503003103003800b022610718001c0c40d941c0c140400b6026422100703000440c49085044900141c00181181e00801f041c402000f2040c03802612a0085000201c0407035503600820750303e0403888198900907417007540340e40d0340ba41074651514003407100411502640c8521000180b00742c000c1010880307a000780c440030b000003030070030132480c5454104070515030b842c07072410880a0b00043c0030030004402c2d440910310403a01601e80d501c40c420b2081c9085000c0d8401491074600d190344001c0c84489003075a071180c0407805200c400100d800d0995040103800c11084c03105c0c004140b0b400103894000540f221044804990b00104070701e040c0c0d41c1c2c1c000410001ca40000303150b9884140e0060100800c805c01c180c080590b00140d003212001c240f2490240c2d16441506406400c83c041403008015840c40380a81c04400a28400e4030b0b041d038000169014140c1e080303604814504141350401c071425541240051030b04c99811201c9041c0e4030141000601418020516 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 296936339 1250 296935089 296935099
    0xf090c0e070212190e030f1002090915030a02190b0c071e03050c010806060d022a0d050315010c151a061620120106080d0c031d130e03030a0b01030c090302 68
    0x200d030300340d42d011f12003240c1d109110801d032031088624504240c0254000e10000d48140e0341d110207d2000900000310030709188001d401809050100e4007081f0600300340007410b03a5031642880b400724145a00c11701030030070700c62144000d03e41c490409031070140d007010042401d104100e020b48104003241d00011400a514400c1c00c204240e900c5010200d03101e4030500212240c1c1c6400020310307107114039010200c0b294124182c0d00740b60018590000d50764403089a102c10100091060000c0b80312690300d164111003990050510380110000c42e6203140d0281c98030300400400c503584003401412403241c2d14203001c0c141000c0700ca0914020b0141c203000c0040603903600192800f00360144600386507602e54181d291702d51006050440165002840310302070001401450168007404000050300c0c0d010700d841c000b501b07515444201c4040180044d254030004842c4825034481d0300010085001c10462254640d20600c11020303564928046003d00309449209900504161800702c0000c1c829070301c0040a4190381d41260 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 296937589 1250 296936339 296936357
    0x3080714150c0706110f0a0908060112060f0603020306100e15130b0102210a17090303060108070203070f0b073b130501141207180f090c0e07021219 65
    0x18880000c01c5c2d44204035100901c00a0405202c18050000c3c00c600c0d1081e640d5a80d01c1070300c1d20042e80c2c40d035000303101d602c041c010028440c000240c0745070080494a45100c20000b965560ba03000640f8103001070b1038124294900e05414803956486c0303400d095103c0400100b514031150490b000c94080070080c1c560700b118a540340322040040c0e1003800740f1044080c1c404010160700c1001410000c0c1a806004e100340840c888010b0341c105140d401500500c94110300001d98110b903114001500c60072b200806000841c042040000d001800ca0076002d10581e00444154049107885080603002941001078050740c00b8001c0440f2008034110b26074425114000070100160400440c00308064002c2803032265240350409002041c1c44030110307150203014004840701c15007000352040c3c0c40d44500311402038500c0c800b4110007240b8096019006045107000f840070001d004400d607218505d00340b249070424821010044240400c1d40e03410003801141074180c88900b46807414040c10680d10821000d801c2c01072080d614 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 296938839 1250 296937589 296937593
    0x61e060c0f020f0d0803240a0918210806030604050a29010801050a0c110a0201050a050405121c0e011b0201020109080c0109030f0c020609040902040f0603080714150c07 74
    0x483d401c01c0c80083c00d15800c0300400e1900003034070b030022955410f1320300a0000845540703403003e41a10303080030041d01c0e40021509000c100780240c4921607070412000400000c1c580026000400c01200b40c4902d0708107210070710103007002452860068903540c801d51000080c040412030101e2810083c070703841fa150f4055020072420b0304070318000703030180e079104c1c20165000014441c8064111a12500e80c102c0100283c000581c400c0d1045450101594010340c004040c08005500480041c1002c550034185541442c0d500e50004694001c0c0b5230806034650050380d000c83c2c446030f000044280307044260421264400c44a40000c02c40c0385105489a00024200c0004095900030341c81a64002e80241009588504100304c99000c1d195150045002420720322910250710b200c3c00d184014664010012442c018008003004050300c1c80700c070140c1e2712a40c1d07070000324800300003403141000551240e0031103a203aa00f18100030100c02048520a4000d40002e8042800028018186640072a002e2030890700d5030b02d14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 296940089 1250 296938839 296938849
    0x1d0601110f0a051e0619060b0d02070506010b04180207060f09050706090b1813110d0c14040f0b0705071a041e08070b09030c13061e060c0f02 62
    0x1a464029090041220800c040078001c10150b0100d070040084814400c0b030403403002c0d841040640c084c0c0280e0440d00100780c07506180c411010850454885c041881900e480b50940240e101e4560442096800120741003005030601070580100003800303045040c02d00c0c141d210b80c0c0e10500c00e0300d1a0045903000a51004228175603200c059008291401000003c0d07561901c1d59459409003c1d21020945070180000d00f0311041089a00b100c8400311424520440f810901c545601d07503a2890514a031a00c0300c01d2108074580000e41410960301d00027082500352020050711003144001c00081007901040180017910b501c0c1340f480b048a4031081600e658103400e0402d9800c0030700301d800500c0a0706504c0800480c2c2c032a900007070f005540030300380c90500840c050810f01d210039000f8810814140c21182c0f01700410340c00c2c00c000c0d29001002600751072220041e0307400261040d59500301c40880715590002803100490300181c407e02044031400a4528504101c030241c65040207146c003c101d01d0120403070408540721 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 296941339 1250 296940089 296940107
    0x3090b0a0e072d1e170c04090f0f030801060e15030601050f0f04090c080601020a050d11030d11040306060608041e1a090c0324010e0406060e01060c02090606041d0601 73
    0x3030b002c5880c40494035410280b12040c0030500b007803130b841240c0c1c070040744201c40c01d0020100454480018081c3d07400c02810300000d0f028102c4181e600032004841840810445060041d0040c400d6564803010741c142180a04140840500c0c2d0340603500c20048000c2d4a10042c0031250070007000d00b04940c495944002132622407140400c0c0701e000160219000641d071850341c0001d044200c0704e450761880b0380d650030012a951603440e1000f9240327070f10143c8800d524500554000c2c1d20040d0341c40940c0d20f00300280304140f0640f40c42c60464590904001420000d012880c0b1440b0013900e09407030711f00c07154182605c84100003010f40400010390400e1700180010004100c0f512a508850a010034007603103050a081074079200d030196918082d01580542c0c030340381c118415101000082c00e4400030801e90030000c0d0a104003078010404c46103d5074075800030441043c2410198000c081d41d5844100c13105151050040425000c2c10190040303001744414400e803086055811200001e150844145555801c012105900 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 296942446 1107 296941339 296941409
    0x20f091801090b06030f0417090a03110a0602011e0c030204090c21050603070e060a050a0b03101d0c0a025805070c0503030a03090b0a0e07 61
    0xc40941c0320303c002608c3d00302c28034200600700c1c021680400440c3c005840200503146900c816103401da108801420709807009001b01d541181444103901c0d10200603440060719000c00c6500d4500c80c0d0f059070014400550300b84401204000050320f900701110850190000504074642d07010040d009180c001d01000d0700510f207044c6015038010100d00d001e88001d502038884480000d407550303115203103c040c0001e0698036540f0f0500224115050b80590300010401d075900c0700c02d91031030300c1c2c001d46035030700204801c0201d9850307a50301c1c801c0341413200b5410008a000b40f07003407248403000c2c2d043c194244440d0a040842d110801001807d00400c180d00d01c40041000d8110100702c00680b043c07000c0e042091081c140b41145130b4440300028250f402001e05400041d80d151403a000b408455600c40307422400850080180e0520b10785850b0716100280255801d07440451103103440c0c2c1c1c4c81e2000c1000301070 = true := by decide +kernel

theorem cover : BRFrame.Cov 296762589 296942446 := by
  have h0 := BRFrame.cov_init 296762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 296762589 ≤ n) (h2 : n < 296942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
