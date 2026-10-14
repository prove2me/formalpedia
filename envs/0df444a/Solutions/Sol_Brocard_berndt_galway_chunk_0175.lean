-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0175
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:15:45.999299+00:00
-- url     : https://prove2.me/submissions/87145c15-fde2-4ffb-a093-9c5fb1f68e81

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 31294969 ≤ n < 31474825 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 31296219 1250 31294969 31294999
    0x605030d021c180f0305010e010903090b0a030f0911120309180603100912020c0406050a0e10090608030307030b0108130209060a03050f010b010e0a0b12060406050907020c030c030a02 80
    0x601181c2030050411580e41d0010f100001484404000b6044c10101c620302d40c0c1c40c608065094a030040a07186281c0d1500c8015400207400030130103002c0f0f519440e003143e2101135003e000d600400303850302e880c0300c01c0e0b092003046010000003e04540c0d114008a45403c02c0d80481c8039034a6480c0961820290803588445e4071381d00040140a126511540003001c658680103403140f00025921061390441d03448003444904200d02e90144043d4506500645040018500c0c0c0400035020000c1440343d0704150101102003506017202210720f00c00340002c55800d102c901d0f510740406913660b204541100000349003108010640d8440d513417190143c403840c030030801e0740f160a408204e06040d02421310b582c4802036000000025800f4083c0108403041000001340c1c0e17550b03a40000d0443c13600502c4140c4144032586060200b003074001c050721030007103c1d400c5244440e65100081002400d0309d4005951158040e0100010a540020100c1220700190f05849501380e01c0d00a140c0d648600110003507102c0c101c864a0706e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 31297469 1250 31296219 31296253
    0x70e06090c07080a0c02010905240a0e03160f0501030504021f0302130e01080c03031318060902072f0f0402031504090f03020601060e01050403060216020901060e040605030d02 77
    0x2801680e81c41d840c40c0750681030755580c40a94400c6401d000480c481401000540da0171401110080005a981004001407a401203080a03c410b401c0950b1080100740724030030310310035422007180c101d001c0c044604500300d4803581c80440f01c0500c00c1010190401501040f2544240034940c041da40c00341c450491203030300c6803488440440020054040503800c4c0039200030301300c0c000000030041008043c802002c1d41410301140c20b0440941e41103010b503008006510900001c107120b0411282450100e40d44038840c1c1e08442d020740b44540c4040039403400440ca82c2c082c440e0060b81000034421454102e00109080a005007490460306402a40320600301d4140340386040540086a1142400c14003522000d60040042c0490f60140410354600c55006803807001c064042054502514aa003400710413143d038480021304501ca1400000c000c6030300450b1920b1008a01150340d0400c6034028000340b020740c0c686100520b4050450944c3e482035043c48170010b42d500f00498800042c00841c0d02070703c120505c54030681 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 31298719 1250 31297469 31297471
    0x18080405060313021509130e0307031803150507021c0203030703020a0e060a051917150102010f0c05031905131e05031c140f0103150b21010608070e0609 67
    0x326400e4070f2007501001a0b4034801c03540a118000d045682d00d03608a0402c3c0030195940c20840313400d0391320f0040c1110401ca03000040c3d487d450342c5450f10000214151004800d0f4190503030005050041c5501810b0b40b003007464001d00c3c801c41990b8211611444040c54103200d006041d145000076170010404100c0582c8640c0003800c60400074104400035401c40c0c0c020818584c0000f11040c00100042900032540b0b596a42c00c0d941c000c07252420103180d00002034448a0b184018059440f003410442c036001c1c1590003900011100000c0043c100031030640c000b00580a540100e6209103201c441d054140728840304d5210b028000c403900c410103619160f880e0340309400e9912015a510128511080d01400076904000424000140740c44005010070704026032030030b4540d4580007107044900384081160081031503804504494001c0c207c44900241d0700d100000030b064140030b2a03000144614111409001c01c411142d4860b2a50000c03c48544c0d02c3c81a187c640c002401001d9100085102162003441c08802c1a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 31299969 1250 31298719 31298731
    0x403050d02070f06050108060705130e071416050607020307030504090f140412170402130902011b0b010f08010b010504180209040f0e010c0504120209130c030f06180804050603 77
    0x10300e0600c1c60b80b5081c5018500107004c40c1c00580721801400311a1051140380c0d004641030900c80d081c040d0405640c488000103000341c0000403070410001e040284640340182040219408580e501c03010400800d044109464040d1782c0e41c490751010461a03031001003260b40454069030740604140c2007404140280160501c1000300300c0e01e0721102c00002a00615a030b0080c0c1c4104040508448005070240c002020320f82c0e5100745421103c00c00000d61540c00d2001c1e0855424032001a482d071041c8010b03901d8121184140280a640299400400500407030300d0781680c011039200000d1550726400203083c0c0e050310140c90b00240c014001009582c009580c002d01c0401c3c0f41f0000340c2407444c0c2c1400710b01141c8517008121156919130555045464082c40b034a503400300c041c907025181508140454a4213000b4900c028042d640e81400180401c44052010740400c2c0d000515040d41d6036241045410301c038800d1000d90b50035207006207001c4603000c2c614170001b000d80d010074040d080c83d26060400030180c100600d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 31301219 1250 31299969 31299971
    0xc0304050f150a02030a031506080601120914030a030509010504020f1201020c01020d0b0f010207030302060c07020d0c0b03190504020a0303080403230a0306081506060c030c0105090c04050601170403050d 89
    0x142c03403040024005403160200d81d90003103845542d6804010107564030f141c1e008001c404085014401c0e03990009040340d00210a0030500c0c22440d986e2103040c014580204042c00300326214080d00e1003008040001d080207140c07507138140b00c01c0c0c4440300341508840007a2402540000601c6030001ca070301b840c1e0001081203004100040c01d11140107071403826a44102c80040c0200c0d07503294102001c0c40c00100750b0180074802e100515071941195806562100081d2a03c43c410601203170f15011981d4140c00c2050203a4000001c25150b6a03c942c0304070950003d40d00b43d11001c4051f640746162401c2882946e10484d0000c00500b00503142d034809541c0158094070640030460803c0820b0315000c107115200b104001c20f0889075541e0000668014125034030754118580700d420034007404001c1c8004480c080d4004c107040b82e0701e554440c106402c044c654481c00204c44125401c04007040003030720307000c140e0700042030050750180942d1341d8640044035412141000350100900d41808107011912036000380411602c26a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 31302469 1250 31301219 31301239
    0xf050c0d0c140a0b070509030703080d0204030309150801030206090607050a0c0312030b01050d0b01020f06040c0302030606120a030f0e0d08030121020102031b0a020a03060902150c0304050f 83
    0x42203041115160504021036451040c000401110920742048005640040c102242c05075980114054003d0100d00030040f003c40c81c03030413665003403120310025a8004111503444403400b8000002c1d420920098000c5502d10704001594240f80c07020480d00010756443c40026030865003040b000e03802100c01c0c550841c405011540015004100901025000b07100b50340b0520721314540b4130040c00822103001d0030581402d0b080301050340c01000791008260398413004252180480c0040b450130b4a01441440c10b44124070921003401003080c80841076a00942c00e0712000e50b90328051114130322a0114050996015072100404284102d132171b440980042d00c2e00029034005200010402031020b401911b0440c800001000326803000101c03022240121106400360710300303c2d00042c0d100c0c050030426040030404400b2240010300280080d0184690040003240038030744908100b0001d0603101d0b030890041d816110b80301a60503c640550300030754070880056203000e0410301841669504003c0c09500400220 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 31303719 1250 31302469 31302487
    0x20a030902040509010b090a020a020706050f070b0708041101020102030f0f04020a03050d1812020607030c0501060906090c020610050a090903050c0f031e03010e010b180307080610050a0f060f05 85
    0x4042c2c83e000c0d50301301d400400d2800b070060421040a0014001d82411441000840042034012802004541a9050481e10355808000d840c0032881544001840200c1440c10010069044a441809903018003007041c0c80114160040e800c1340710a0380d8076410003024030f000509400c250600c182e030061020309000503181d500c1da101e51034448440801800300301640803a0400159501100b001496010800e8005003004e80205016100707090307000d4200000940f09805015003504084000c3c002041d0411103250f90b40810307001000b9801c4c00b070005001e001c0c04651442102d508220950700700908082c0904e240c0390285004101004007101444428012001e0000c0d091103030b100c030403c5c20005590307180003060f0071843d006a4140043c0c54940103100621010341030300f98440c1526102e048150396204501c41c64040c12603905a0a603040c400d0000120f000e4034040751484c00360f854001c409031100e454004019058066001d48030300090603000c20000d080c4101c11087c80d0710304c2820201e01c1e0007140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 31304969 1250 31303719 31303721
    0x20409050106080c1c08030604020a0507140309040e0f0c04020a03060504060b0904110f0703081b03040501060e0a0b060d0b0a1a270d110a0909030201060e090102070f06020a03090204 80
    0xa521110040e00422070300003842c05c00342c41c018004203080410900c106090b5480c10f200e800301030140d50046a006c191515410b006008403010943c100844010040f4104d0005640781d0100451902407810b100c1002240e600004804641d1264079014180811000c001d0000079003200f90443c08058446030000380c9902d60744a001c002d4100b50021aa4075444c44e020f00080d12002100c00c280322204002100e110240c0300300f9614415814984000380d5101d551105040e1000a03144140d2100000306010030440305610170002c03102c400000c0613160f522000240111044070990303e070406e10402c421070351211a60302c00700b444e910040c40c00e04c0403525941035a102c04582c1d81c950000300000106130900404c46a0f40170602c0034130030740c0c5029503020200811a00d1020300d01c0140882e00036010307000309581c2d0917248406000d11100c20805e1011901f0000d0203014a80304411102c43d2150100e265160103008403071407a5040050080480340507941d04000394801c0351201c0030550b8500721400140e0316 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 31306219 1250 31304969 31304981
    0x4170102130602030403030503040b0c07061d010b190611011d0d080a1e0f0905010e01060608090a02010203040e1902040603050618090c0d02010c02040c08071b030503010b03040204090501 82
    0x40040016226414078000d030464050a8010200b0340d0300910040001941c45002c6a511036440346115a0a40701c42e000c44c066401003c10041c03282d030410414146070304240c90008850241c00d802803011500f01030500120240f10101210504c4031858144001c1e4040c0c441400c0c00341050000180b4003804150b400d8082c2c2a01440035566044500603c0307201b6449a0384070340109059a082101c140d4034900c021001c00c150b1402c0040c5511041c180400710b00700c3d400500f0325a0450000c0c00800c000b04013590090030140600c0011820000c003182e5065800910880310310380c1078000b5480c3c6030034015003403481c1c0340c002c01e808040001e00001481c411310382d002130002008151008141e604040c0c08010410075000985441a1480c00400005081c002890b1690b1070059801003042c2e501070004a0b0a9103c02502a4120b41001500007407590f021103c14030500d9650380b50b107100c0c8524080442076078440c10300500050f00501c01800b0504044c0011600035100500c00a0320f440b081d13407080d0075150 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 31307469 1250 31306219 31306259
    0x5090a090203070503150403110304120f020612071e0201050c030a0b0a0b0a0909050705270d08032409090d030c110d0e01030501060e0306010b031308030109020c0114011d090304 78
    0x846c0030a0008040e0465810314040810202030740c01c15040c0010385140c14284d40c8041c103804481c20640c0159243d01e8100d80e6440380050540c3c5003072038030314400341007000f41181000342c400c2d1050003075032500e00c1842002d0250b07101480591854803a41582000b40c18444650b03907100d264620700003120510350008051030f19882d203900c110b10346402d00c0c0c8001c0380c20080c4084c040c8142084854658181d90550030300040c9243d80c40030000e84143c012600710075428500a0002400205100400341c0070201d8000c418500c4001d0442141a1024420000e2003503a010000c2c0e48580c0228000741d002e500040c402105600d480d4600007903402c1078501d00b51040040f0404642a008042c000e961b040c080c0038094021800d240004140541c0801da84010502c00c18140080100124038045281114440f222340c2105995899503103901c10003000350f1111108250302c5d81b0300222040201400c074041c60480d03201d05000e083c0d0f8181480c0341458007000820383d0740903000800c004254208a0f041c8900300304 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 31308719 1250 31307469 31307503
    0x50402132303060115020d0f020f030f07050d020304061b080d0c0c0201030b060c030d150914070305060f0d02090402040f020d090b090a1707030e0301020d05150a05090a090203070503 80
    0x8090500b490b050543c181c0000080d840024039441c9503603000900d01024500c1c07032401550603410104201c0c14041c0740c07113110650b8040041e881c00e0071640c050152541d2030149d02640d81e013004040042e039481c41944160340210f0300c0b010b4541411909a4101c00c2080e0083c4441c1c1c3c5085005c01c03407002100d46503250500800d440324000c10039964507118001481e8801c1e82c07902d15010302d03200150b65030300818203880c1c4200c0e10390002e0001c0248044604d002130120080601c90085d050340300ba40c5a80c4220789050001c2c1c68440020014074113845001d5401d00d02a01d03080c40c4003000e030207018860000410603070b0031545950400069418502c020001088521400507686ca1a031030b0604640d1009040105a0741c0004040c00200d00c0d400d15400300a0380340350841d1369030320756881c0540740aa00b68114642c154400700d50603044680b140c020502c91990711640346048034180c4200480e070f1125014050f00202040d0000390100010751010440302d00040446903580c1d0707940700003882c00e40c1c81d4002c0c0040b5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 31309969 1250 31308719 31308779
    0x30408030405010b090421090503070905010806070219121b0606080f0303040507050103051b03040b07030605010512040803070c0b09030901081003050d0f0302040801020307020f0d0c0305030105040213 88
    0x302c00e0030302c280c40d1640412a2225480c1c105500c9080a610680c0c3c6103a10f103912601406504a001d100300d1401043d000d000e0358403080d611006c0c1401040240310f045124050703900041e80e2244086908a0008610100b01d50070312181c2c3c039148c4600e01910710700d000b804884051548120701031000216003d200e280046182401d0100c00c50404000c0105070a195100348144400507034041000c4058410078603000400340d6801d1001c400104103500000c00c84003000040c07105009409c020244200000d880a101d803c0d80c0b03400458103480f03841e55200e001c0141c04085000501c4041c01107070800020320300020401d0040c0c031042482001603941c50100da000040b0030a007940c0016009034000d00a03080c400440d03203141c0381d00d910781c001030600c001001182d95441c18028003c0d415074014001d0325000715264904180043d40e218a0002401041c2c800c4462500106110f2003844c03a0305645903480b01d08603464002030001a400000c40f100b45440e000e400030540660b00255144030a40d003424041c92 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 31311219 1250 31309969 31309973
    0x715020c010e0d03020708070605040204090f0c090b0f0303120702010b0a180c0306080303070c03020102130e0402010806030105100506030a0b0603130308011a09060307120e0709050c18150f0304080304 88
    0x1d4451140361034000d041c014810710007c40c00344400d4a05003030f00054007180303568407480018003c0036609030080011060791088814400c900c480346050302c501d00c3c01081520301407800c04c841d004200030303260760552007000303100c0f1144541c40401d070300080140004500c3c2c042500015105561540221100c000b02011520003419640100c401817900b40c20108522401d00c0c101c1030320b0748002800c00061205400380281018401d41c1225111621803101d0400035494091041504800741e031b00703a0001d8026000318a4600d0180300701c50282e110418616404c900d084148205030300b000380f619607041d0f5512603061990b1502c8004502c915134415001c40e0412251070043c020b1a81a000242c003982140b01e00282908003404031200c0712000c46001303031240e0b02c00004031060740119103a508014248901100d084d00d000500d40152003407800240b00325076440c01820070074007400f43c004c1095000c4045008450510740da407140580d1840a07164079044203040d460f0781d16402501c048a03c49400400c002c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 31312469 1250 31311219 31311223
    0xb0a0b07170301030507030b09120d0c020f0c011b0311030a0302030f0106020d05040302131806020306100315050d1401060e06010f0c0201140c010e01060305010c030501060804080f0715020c010e 85
    0x21050701400003141154115110241e45444a0100034969002c540110385c005d00100200c016038002020703207a55585c42c9000a1001c0c117441d80707010700544070741c890303081e150000440d9643c0d001c241a514000c00e21044a00f08a012800d08402d905101d404080c06616000c01d10007403c00c003802c1c4c0c4015940f424000c1c0c10011049050340203e0464010201010003580c1c0030341154222501100e1903045900e00301c80640040c4801c030000c100b5050410070703003004c0000725000355104210848100c000c040c0c1041081d8160b96044041200301d0f01c200c1e0040c040e0386000c407007545c001c0b8090b0100c4484142061b14440c211072032a00654103070407240f000c0181542c1c1c001e8403410004e00302d1415000303200c61580080c04180b0f12640e8280c0b00c100c08134a10405902c2540a01c2030211448002d01c15a40c0e030b82040c50080050740000c4002034188400460024010604580141c0d0b0122003030b0301e003546c1d8010300b42d00c80e00011000c44d440149450540c208028500142c48100060b40001405100055000d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 31313719 1250 31312469 31312493
    0x902030609060702150c090607030201050106030b0a050d200607061b0302040602030909071e0309021302030c03010b090d060606080601020609010c0c1b080102070b1021080901030b0a0b07 82
    0x20007164844020004416404035050070420700520303c8100c1c035191503110300154028480d134141c00c40f20216496051540c150403590403110786840c1002000840b00a01481044502407143c024940048110000d07400800b00310803109080d0880c0202c0c0201c900040720fa070f000c001e0684511780c0301c8a80c3e4038020313080200040c0460960808503e030900d41140a92203015a55205104805010001c2c8a85000350180078107401e50545070305400311a0310029000701710b045003ea000d00406951550844c2113442120b020f030700d44100e03240c2140c3c43d04030a402180e000010303041d0000d0f000c01c0031000282280c001e003000751002d44c560201601d000400286400b2004144016a030305181100074401d400c2400344040d1501b0481d0909400103100719800009556030054015600c0010f800d03090290784200c003402401c0c44000f0321101a9500403c520000901c03540503070501480710701c0800100550b004003511441810301091000c84400000c02c1146640e003d0000302000003100e800b00b1844414031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 31314969 1250 31313719 31313731
    0x905010309030806040c0e03010507021006050616020d03050403021903020405090601210819050c15060102100509011b1e02010e0604030513080a0602180402091810051309020306 78
    0x300000c20158900403c0c03003078080c22142c000c660ba00080c000300c030311800d481c1542110280003804103090004009545d201c0c0310000c41515480d188000c070b0035150000c1100c456011f58502504010a60f8080014411000750220140041080f000006859250f0b00e2108641000107100d0000d107580180416180002d0401c8101c0e0030001c010301201107200300424190f043c011801c0341034111803414000511a084070354520301d00c180d034002c1c00715500100500721503000d403007680c401036840e041c0101d620000340c42050268100518420040c0c0d00c603400a64071140500020604820030700715a080c4016000260b800180e01c0c07240d020b1402d940b42029042602c85100801111285036001c035100e81001e0001030401138002070b1200c00c04c0d891382d441c4000d00034400c00e0300e66000305450000020b52190500c0c406400450403202d0300d914103442521101c02c000ba0081c1482c409038400035500e5503000b410352010b51059000230880f52a03950b01840c0c240d100030000619040c4900400d49040c00c01020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 31316219 1250 31314969 31314971
    0x40309120203120d0f0906060f12050615010507060207030807080907030507140d02030f033a0b040204120308090f06011a0703021507080f010f120206030907051c0309050103 76
    0x20080050310001050b69101c55801211074640044c940f24601510b05070541e115803130b080c0740340d607018015180e00c00c00465500c1d00704800c0555a640c1d200d00005124800501140c02c80000203660044010780b050b00d07100b051620314a003000d00e94484003260818007013a000902d549003040241c5410040d92900300300004018002d9902d1035036510b940c4c450901400013141d910b04140d0b005030300d0f045801038405030300400340c550b41480c501130240d40340c01054800040712284003c01d03001c05034813001d005404401c42e0385e0380d0b1070001c9000c41c030003c2c142c1164110742055003040b0000d40103400e03590390030985119550340940d50400380d800901d08041d29822100503041300b0010454403040c884c51941e00809c401010380ca4007420b0609a050800d0307801c030000308001283c1000040c0307601c00000d81c030407401116401141d036214040703181400e00c1405880e14024128404001516080025544c06a1001c048801c619201c20104038a03080804075803c9004c030f070540c000704058101c12010701a050a1170 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 31317469 1250 31316219 31316249
    0xb0c0d020c06090103021c0204170c0901060c020d030c080d06050307050f2101020c12120a060305030301050d11120706021005061806060702040c11070501020a050d030b01110106030605040309 84
    0x80018102c0c0700c2c081c8828141640000e000300c40b244038000c0c7c0f481a003203810046440340e0341e400c044882c080b141d110040781c0f03008407140c690081c07500c003e100d030584445942c0c5002141c500d50078804440c41e118400e405001050401da000508004001e26a41e040e40001060042c5450103040c03a2100f1904120f03c10b0078060302c901032540300c2c078034248590440d101000f03907000c10140c25180207120304000c2c03a046000701d412100c28905c1d21170003880c1903905546ca40303500c0e555022401c411103600c4d00000702184c00c100b004100629110103c8a9840d001f13407001c0075800780301d100007003040b4210800440c2079000018108800c1d60140066005025411001d11292500100081041403041a0f01400c1103082c40414a9a1181400e0700c013500d80c054410000c951070003101410310b00c44181120b0592094000201c3d0715440400c41c608955440402400c046100640030380150000c0c2440034100840f6008012401c0740074000e032030003140140000a03003400e00303003070061071401d20350020b10703040c84105 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 31318719 1250 31317469 31317493
    0x7350c030d23090a0b060301020310230901080601030303061a031617070e0f010c050309090403020109050a030c0b0a050115030e03130e0f090105040c03060c050d05010b0c0d02 77
    0x8811203001030403000c030006210362102c404141c8080e509103001060b144800402142a50024400340e8072402607030182600e07074036001010700b41e12045801e100070301029803041103960328420136925107841381e00a00e2014000ea00110310074240c264000680d59025030010000d160b0140b0518016001c0c42c0c40d80c000140b21002c40750080c0c0320150041c40c0017030b450216150128450700451100d18040710f66110313a03041a01c1c0040102014111452050307c07c0c44031064298014000b0042c91540701c0051402c0c589580704200492070000e01c00e030700755500c50610b4400a14140f000c05202e81c0320780c5450007401e9042c00d081804c0740e80106500b00301c0385040010300005800150b03601e07a003c620710300881c14450350301c003440c11401480c001d40340c020420070020640d0490520710301d11034100c10090010729600d0b91200c038242c41e41902c0140c00d4242400d0144046031040d0081c0c00742c004181400b5107030403030524842d02150402d81c011f00d8010004500342c00e010006100f00440d00030244010040e002d484 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 31319969 1250 31318719 31318723
    0x20a0207030305090109030611070317010f05120109050304030503071e030e09040c05030d030f0f06051809151302120c0a090f0e010908091309120c030507350c 70
    0x680000360901101080c0c000302a881100c0e80005158889024840300309c0c9001d4803403443e0003da404901203094212200d8180c0c00c6600014100c2c0c000060348207070f040c0b030305090094451651203071650329501c4e500050302103102000104019803081c00110759406103424483d400070078040241c0840c0203030700e21050100b613100b0000788101380221508070075a02e8900c0c000700031401550000d501800723030881c0c201a00d0341591041221204060090240b5400307144d020084030441e0113220f038484040c12050203004600c0017201d50100e480300c100c071202414044044d80300041203a07502084104880e950013107050400f96440c28600d900c004200c1c0d41c0303a5100080001e2402c1c06144001c642c0d42994550464098100b6009400792034000c01495095040513410343c1d008008150007440d000d003001c15402e1049c0320300f5502d19008000540781c0d6601c020308880185035a103080e410042d05000a002060202a0081c1030544e0061078680c0e078085004d80c907116050000c07030741d13072550802e00881c4e190080c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 31321219 1250 31319969 31319983
    0x803090604051c060903091a04080a080a02030f030114120c150901020a020d06020a030b03030a090614040b0d090605130b16051c020306040b060c0a200d0501050402040f020a02 77
    0x2040340c8040c4801405540c004240003d070384080c10316814490000d043c5a081003001c401e542c0510b03801341c07c01d80c1103ca881010300c6036100f1003c6580c0300b11880780c00b188403200941240591441581c0c41c111900d529010141c00030b07004442140c01130280c862280c50040f841e0b21769200080054003580304840c0000f190030604c0c4400c00e420070800a8056003a0f8401d010041039240d00514001000d405030030907000075000040707594086440c24400d60818075000060f945010f21030750356602c25908004084404c403a10b102d00e4203a600f003d010104444152401903c02c030b500603031b80050b04240506280c2e0a4403c040d103901d40844040c981e50005c101100038203580411780d040e10b01e009100031182210715100b03602d00b04003e0048655080840d2107207030002c5004800840c1c0900c002425135040058520030354400001c00e91100d405503001444000206600541d40391140048042240100706050080001260607035550307401c010071490148681410300c07400c5042181414000c01010f5640c02e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 31322469 1250 31321219 31321229
    0x10050105030c011202041d160c080703031e050a0207020a05040c1b0203120307090f060906051210150201060612140105010c0f0602040909050c0306070503070e06130e0103020a0803090604 82
    0x44c02c0510b00d43c4014468048038001c01d259000e86400203840301c1c506811101c190758443d008103806080e0000303c0c7c815401e403118030f41c00c1f4010a240c032000d51f6080e00145064400482d0b160366082001c17021230392910405100c2c1600402c096540e030100d10400180d030b01c15410044c40b031480d000d003e11f01e2644c81030414106121407281f054500c0428000a03203030024201d00126103910000802400c1340d40814010121621880d151000980702c0c07205880c1d680150040c98002602482901d04c036483e0240101e402c4107000c400180c003252150448403c1c0b054030103829000d0307074480904102899001041d240740007080003080100c151200b0350001400018402e00381080340054110050000c000c84902c001c0d80d001070300b195030300d03030701c0302e0b54000703040403000644240c02550b8010999090202c7c0c8148522100e6881500e10303558003105450000b017101d550307600000706101182e41c504100008201410f8018140c14540d803442c07040051240050300708031010f030018400da107242e484030415503045d03603 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 31323719 1250 31322469 31322477
    0x40b0f0106020c040e1f020403150b0f0112090507090e0c19090504150e0a0b0609090d2a1401050709030c14010c02031b040c020d09030b071e050c10050105030c01 71
    0x200180d440c02d10b1320720300402c6d4178094041d5484002840030b0a5009000312881040c10b040d02d0011070200604844001c0516500804503170061807070f562040520b16187d03002203000084c11601c03030310380324a0a002e41d04401d5003140d8905000c0c42c5144108220080103104403001d049102039a40c20344480c180034412180982c1d1580701007420040e24140343c400c0030310340c040e0030003486461040d820b41c0c07500c9000041d1485403403080414103506100c44118495070100004181100c1d604500f1118140d000c0e00318604201e111054086405440b04408460b50240c0501d40b0019800f030419030840d140030300500180105042c0130400508a138800310300b120800c0d80d410032030b0400c01c0016600010322110003503050056040c40e503200e2901e01d10f8403110380c005440c104003500103c0c100380d9a88c80d01011940c00b1689252040000803150080c0690000d21490b20030103024001c501806030040c000c002c100400e00c04104020610800c00504d0380c035003010034060020b0b52414020940300d00c1070b5801d6034104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 31324969 1250 31323719 31323731
    0xb280507020f190201030f02030402010512040204060812040e0c03040f120212070b09070b04051309050a0501020408071d04031b03090512011d01090b13030e03010501030b040b0f0106020c04 83
    0x180d00030b100c040210001c200039281071504041d0002c00c45541c06508a0111b46410003146400346ca070300c242e92141d54107031191403409c002c51000900100c0010802c0303a1003500c0f41800315982d41d00b03121821105d00400c42c510786442c1045586140e2040040002c40382d0a024410040888c14244c2d01600c080c0d0000307451844100c0005049013041d5200307407580c0b4600b1000555100f08214400e079035100701175110030703249c0c2c00780c40d05903c0540c2c0c480c52254591001312100740760081c0340079502804009102d03c00702c03141140940d540f10700b641c00503804a041508044410003003948070021103108982000348041c0039142a40c0d000d080d10450815200741d20b4640b1101004160088552030041d00004203400d2000301082c04181c06400c0c0c00314120300100a1080c405600041401110304196100040403540c0d0b82c3c1e002200280c41c045034058007044450920011291000c1c860b850280d80145450034882ca068203103220581e0340508a203484540440c010071155074042200d1002640c212404101c07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 31326219 1250 31324969 31324981
    0x5091b09100e10081903050913060509040b06090f06010c06050915040606090b06040b0a0c170c0d031b0914060d0e0a0201031d0c061b06070c0b2805 65
    0x6200d00581048072005502418810f0082c00302c41d54030101c401200450780c042d203040701aa104403e540800402003001440000c41798901205503050024250b9070010710203554200044241500b942c0c207403841d496010520a107030401820b00341e4498542c5040b2126818107400003041e960312080042e107490356802c0402c4c0441d40510040c04241c0c0211449162401c0508116004041910502d12281c5c0391401e040510304010b0240d800b182d40902446080002b00c0fa015142c1010b0343c00c0490f011000c8060018032200307180042d00303001c14000c006140d2144003402c05011211020300c8814034100c0202d16265050380642384100360342c281055041c10145103400f0800c2406448001c5070694100003041e0a500400640c410855000360380038014502c0400f1503180081d0220b1000c00c050b000f0070701001d041d00b00f55000b845e01c1c401c0d201c0450840904420b60302d0800c6010759a04000440542c0300e102402803181e401501b00c4403181ca045030781c10201c06030041c003840d01c2000f20347c1c2e070340c0340c03400240 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 31327469 1250 31326219 31326241
    0x603070b0909060a091b020c190308031f030f020a050f1011030c030a0c02030610030309090b03150901050f01090c0504060c08070c030803090601060513050d02030109060204060c050105091b09 84
    0x104105c032003e106201c0381d5064441c0680400f240745005114403010340d1514504003444000c1100c68030003c0e10b50a0840d10343e20b88661000700314920300044500500e51031946038440e0001140107040710b00e2019003030b0bc100059250036502c02440b800401c034055000d5622010048078905240c2496420b400d02c0400041c1140203c190034007690001003004e0400f5600314480d00302080c800c40a90780141c0c1c0760b0303019030007200c02030001a00081503070005201e04802d9a0200d80f031640d00408994240004a82034506610101c03004081e594554042c0005002c2d80c401d0240504680e560902880e058800024034034002ca1188804014884040d181480031400440345650b400c0f400d500601900c0703040009241d88240d44000142c4607900000540b03078480c000342c8100c84c000f0120742075220b00e800100450400e2600c401e03a4955a00c1c06c11a00007581840203000411850315081c1c04005a41000c6003104c50080c80200345420603544103a40340120f1086806604040316458a183c0f60340d0503c0b2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 31328719 1250 31327469 31327489
    0x405130204020d0f0b060c0604140a05100b0102060601030b15070c0b0409060302120601030f080a021501080706030b06160209040f1401020d0e0d0905040518031602090603070b090906 80
    0x30790000c0c40014034100070407551300b201d040b03c1040141480b05886880071700c034540c45196058038440d0004408180000ca01e1a51003032103006000c215010740c8a980c444030f042122490f480504e280c2d480c500984c0c59601071041c00d501000074201044035003040e00c040741140824040908514800051640402103007000920103001c5d04440143c0701c1da15030705040010001404240d100e120580703183c4010312030008600f8142da074803100003904e08055a8036440b02e50045941c0c00c0549c054900d0011644078103c80081c001e041500c003c0111614000f0042c08035003c2c12286402400c003009001c0c0103c0b000502c030381e80c2d194180c45000e001e030390f076040914140119038401400e0150f102d908000b0120150044c2040c5104494108042d021607140c042d5039088402041c03020440020003042140751a6010540c0441418203090140040c2d8001c58116030007800e075055a080b80410308410b500340007001c161b001c80190020142c0b68200b50010045000d40d04205200d803143c00001400d540301c0300985 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 31329969 1250 31328719 31328723
    0xc070f12090305030d0b04051803040e070e0306040302061605040303050906070303090203030a0203031005060702030613020109091e150501050301031103010605130e060a0216140a1a0403030e03090f040513 90
    0x4e643c03502c0b404800c5101030017241d08280d00c51800d120120303c4440c01c0000c0705030b03034030280f500451806107032043c040001040201418203002505104001070745041c041188241d110358042c100e00d25008402c0c00010520244e0502081006e010a0000940042c121581031900719a1030b51030303220625046002d0443d45200039003500012a04000c0641c0000155002d81591502c14200725140c10610200307010314007010354141c3c80840468404d94042d0a4007034070034010314180d118a1744071103d007020ba8107065600703081c0c012500361804c403103811446215116141621001100b600d040c0000b0304034081804003502010351000c040d07126650952000f402408054405c143c01d40b06230750200010404046d444d45280035640018034400c00074400c44000c4002c09140450303940d80783d103e41d03949a101203440080c51040b100307040045500d0720050700340524000310740305192925140040030f489181c4070300c41c00e41d401800210425660800c865241d140c06541c000f07800c0d5110840b624404011b2840 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 31331219 1250 31329969 31329973
    0xa0203010c02030307080601050a08010603051302030f070303020c04090209010e0a24090b01031103012907060203070f0201060509070503040303020d1d01060509060d020d030c150506090c070f12090305 88
    0x40c141c4054022000c1e6102d0b1006455480013640c840300190f815100d860140c000103159100103200c1c182c0a54046500198511415207403005641e0210349080220300c58107031700b903101000070010154100507010340440291000d0010a40070760120341c861006002e0030070644428400107a2942c0c16500c60404109202c2002d00e8172a00340c403141c0e00d401414010328041d10f0400e2010142075019015003000d0320702c02041d4514582ca402c440700080c3c003495020400d01b80c2c00c055003c40d46080d002c06800d807103000b40b0b030040c5e807402c120a0250a10103904588015039041c0881001165500440cc661000d0a420091b42d00d43ea03a01c0c0440c000d201c0c000041e00c0107460030110304240345075182240c1c08a4501d10003004845c2c2c843c130400990040840b40756500000500040f801402c1c502c02c130ba14201c3c807a080c0005280c000313942e009111070700b1007001c050050707a4900b04103446c600494030a4005d860648a64038041c06502c80c15035802d4403800c0278100021820141c03081c1441010352400075504042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 31332469 1250 31331219 31331231
    0x80d0911090c1306080c070501020c031b06010807140109080a0b01090501060e0f040c0516030e04050a111204050c031002030103060b0609102105010b070201120c0507020f030a020301 80
    0x501102030a1088012600844441c0300103400301c001c0c903046070003003010b144104800b2841c1a0b0104c0c0c1e01c4800404164885a091160000140007400940344009400c4091a01d0b41118540150b01454841c4801143c1d480500100b0032243c02244c104141c03210b01d620b4440f00300780d0400580e903903a6541d10064a900c20708403440c082c840114007050599034103003418005c40e40d80e5641107816103a40b15010354040b10020b04000d0742e11302540301240c1c1e080203040c0076003411402d440c1551084000302c000e401203901c81040591034500341c402c00e80e1102150400300041c2d0160414001b032030182c10b001505035a07542c40801c0c00c1c00301c00c019010b50b900e0010101c1d00141d450403d080c0194000f807100b21030032410084260f03002d18000d02510f0919202038041c07500d004601601720340c8008581100178001c49880c00b00d40b011801801074a0207003c0041700319075605928400107284c40300702c5820600c158607040e03018031590703031101c1242d04c1d00b5011280d004d001d06080c80044d040100300500254907620b044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 31333719 1250 31332469 31332473
    0x603080a02010b030d0806030c0d230a05010c05040e0c0304060e0708030c01060812030705070620090306060d020618030f0307050703031403010e04080a120606050d06050612060d080d09 81
    0x50030034107860310280d054403100040400246c4d090b04050f10038507410b4008104122070380c2007600c080c0103001e0085003043c118151814000d0300f4034600e82c250710f2080e041910320005000090140d224100328a141041c9018a81038030094151405403852060040000129090085a41000c2c0c1400c0c03c0406480c80d550b9200d905d46e60346c1d44490070400465003891400600e10030042141801c00380d02c110000c0ca95a220030b0102d030140d01c0301c0c41c01c68401c0ea40c0d812684460360510b5150820f414669032481d40c80008908061074104028000362003184442c04003801a140d140c00d44101404580804045600020020b4280401c5149d000258400862034070f05004000a0060440340640c98185502c40718144412184c0710901400005040030404200002c850b0001003d42040c030740f07054120f0070b145c520380034151031142c4e1011001510201303281c5680c04451107080d004003c101c5170b032850f064400022100c040740c002c010a10400740c840391801407020745400c84e42039125040c01048448003c2c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 31334969 1250 31333719 31333721
    0x20a06120b030109020f01030506030f010e0c01080115020709111224010908030304080304060b09070f0305090c031011040b040b0c0c040908030f07020c041401150309080409020d0603080a0201 84
    0x381035000360300349141202030342018441e40c000a40c014101c20300c281c400390010750103400c02424094051203041c800c040c4040d001c1c0329821801e143d0790058101d410092000501c5200103030004a80000e0380c84ea001042c41e0002440c6040724000180410480114030012031140580d0349041c00484c0c1040400c880c010b00d1500603110014040880801c9070281001110340b0141c50096890642c0108045004224070b01d015580c0140311300e90205006418030007054541e42e0685000003c920103d161800c2640c06005a03a4440d00c03010040856205500010340ea4a2030120090030b0030741e031645071110801c100422280540404640075a565941d803010768542c0d0b00400c04504140148001d0310702c0340c5003501420301030940040d21a8150345901007401c0c200403000d84007005500c81c0c980031249039140e60050240d00c00d0003d940400640c0b4002031503802070242004101014949032400d0005100c0a0513541604e542540c0180c42e0a2001205070041c0b809400c081c1080f5000f080a0952640c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 31336219 1250 31334969 31334987
    0xc0d050705100c201921081e040c050a060903060e030405060301140109081b040612050706080702070f03080c2a04020a02030d0c0305010302180919050a020a06 70
    0x10460403240e0800c0b9100c100011540c0410110001400810200f0301c1c002032440181c4001d6100000c4e500130650501c0c62460342d040810040b40c1040d1503881c0b400300c40c100104d0040200016050410003031400c0c01c0618aa4030105c4a0b000302c4001900125045c014150382e80f0b8064080504001c440c55180c0d48080c210b00418403040301c01500300499070400200100c155070840f08050072840c00c5900704007801c9590050048a541003000c03401d000504d0400400c020f401040b40f580011070b4521020042c0801d131456074201d50035590020701031500041380003504c081114580d18040d0340f0b079210100102c1c1814203035402848000e60b034580201c148008480245a01c0d000f10044420068042064404000c018880c0c00307d0b9031454451100e0504084e0004d0230038200310710649180409010080c8216503071051840c0c0041c3e920001403085003044c0d0181211601e40e903441d5202c81c03506101c47c0707035601c1c8291900b0780240321104d150700802c6401c001d00c100056008003202002a1151001415451 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 31337469 1250 31336219 31336223
    0x2030f060906161d0f03010603060506030d050909041101091a030f07030504020d060203070302040902040308030901060506031519031202061501030902030604020d03090b0301030b010302010e04020c06070c02060c0d0507 96
    0x5900215010840703903141244043c0c15921142070b19100c040768021a0550340c06003c1c0c120b00b50b04544a00d40d64203205800155200b648005400c3c01c250040c9842e02c0054190700d024400104003202c2165200b604d01c0398082d0340110411801415080103c4181186500460500514581c883c0c7c401708e030040910700c216402c1d814000340365a805011010b44c0c3c0195806034000d40c24501038000301d06180c000f154071000c1343c20b01500c2d20307903a00e9140f4100e0f0b01030f500688401e4408028041300c071000b800782d5001854211500c40c2035003403040d090740e0703603500c4003892038864040100d184442d4903541160100031504030807040c0c225a02000d001c2c0d182e010854400e140143c0c0f0b6600ca44a540c001c1c8201c0031104e4010f4003c0c01959615401d2100303600c0b01e0a010713000d10101c40c600203682d1801070011406184200780500d4194503600c009440b1030901d5007080c0c42030b13005200360448610006149580400a403404585640c41800402ea9070310803031040c1040350041c2000d040076142c204004003805e0f4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 31338719 1250 31337469 31337473
    0x12060b190e040b060f0904020d080f040b04030b0c0f0301150c14030c010b01020d050d18061e050a11070201051806030a140c0a200708010207060c12090506060105130302030f0609 78
    0x15071284c0821880c030300107264240c0c0c480321101c041800741c21301000050507548646080c0346400b030014004a4039070003590101070b035000001400e1042003148807101c5e800851280e121402c004254905880a010500507484c000102501c0441d03064811141c504075a60448100c10500c1000700415850b940040c4c1075192035030030402480c446510029103060490440e07900e40d801c03c0c408128103c007800f010150300c00d01d5048200448041030080c85070980101d03120301c600b40c0c10004104c0c0c010517904000e1180d0145072a0117420380d00c1c0c60a28017100c0e0003c2d4240307407013560313001002c01c042c1006648000040d0400c001104204005000b41d01080401c4042c01c007007840d40e610036034810b030300e44102d220700c03000290a06244150000c8070003205240d0741480040d0381c119903c41c3c0c0b41c1d901320b80182400760340503600c414040303d615400c002e1801070301418080034044c120701622641e030751f410083d1405041040008422551348401e08400d806940e00401b5140d0029117100440d80d00c80d070070342d10300c680381c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 31339969 1250 31338719 31338721
    0x60504150312020c010206130606080706030603050f0d05090108040807060e010b0a05040b0303090d050f0a030e010e040b090106050906091c031b03020a02010e0406030501051801060504020412060b190e040b 90
    0xc035000150802c4213490590080c14030b656914100c119284911070100da070f00e0b4a50038007003601c1d00c0500019020300025500000c11a00e1410621b1804840c014030a419800000302043c81980c00b000303c81e400c1c0400c0c2032015060302c87d480c10002610a0b403030050306a9107000018080070300c06401c8107861170405c85082d0201e644503000c2208540f00101103d500d54410070400c03003142090075406000b64010000d44054040e89036409041c0f0020960490024403a580c02044568025011151065055604201da15040e0003c6400a80107014170b00a001000c6004800b65581d101192041400500880149407074251542000f143c1603030220042508918020030402185c2035401205816500401801101d40c006603000c5025054094102d0f44030b03a00400031a009005140c003400101d00f00c014615440c003e0381d0308494180c0c001620540c01041700300810140b80005010041c1c10110005070500c58400041c4114444000b9900c000d24a85001820070b0410f80c3d900c1c403450040c0604001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 31341219 1250 31339969 31340003
    0x705030c100c060c0c0b0a02070614070815031903020304092003040b090c0a1401090e071409130603030c0312200703020a1403090102120c1903030605041503 69
    0x160503900d0a01c0c001586604414022542d9500004404181c504101c12030301a1911014650842100e07910781140d0000380410070082d00b442180351408a41d0440310890801d03c0d0014850758001d010130325800c0380152044400d98041c0301400f11b01019804442d4540014a00651690000d2081545684c079086c141c2401c04990000f40d09103424000c5000d00c2c40d9a660b03a86840184060604400da02c18400000c03d152107c00d009000780075403040140c60740082d000010408595600708205052815061004154004000381490300740201e1b0300b620744541d840440c0308441c4004503054901d060a0001040c107030400d0ba907044c424040d035541e0303800d0b0a091885509940c0b40e200e80401c42031040212200c07100704000035021940c03181c03058030345508031501c8600107524400d88001d01381e0000511170341d0302d68040120302a0000030b005024100a513180c803840d00c56080c200124151540c109202040501c41e41c451030242400a008011070790380c01c8004412031300320740000c4508100d02c01e03541070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 31342469 1250 31341219 31341229
    0x6060301090804051905040510150f08070e0303090a090c02120403030806090601030e101b020105090c0906060c010c090302010e030105040c0303050d0f050405030a18030c0603051e0403020705030c 86
    0x39680e00541c04078645460301c02484844014031708103070300e035020359500414503580300e001d11801a50300188a8098078100781004510b104e041c00200d041c04044054403030000e40052565a0007103290820030380081d8204041390440c13040384d078200d911015808000c01c03002c0c11944003031600c09071035007107803090340303051600c02040d1049000c0a00400c0752000016100c2c6412030304c0650003079061401042455908400c0c601d401d9443c81000c0905c0e0716101951641c60081c0705d0300a41e41110320092046090403191030303465502c40004213010741c403490700045494442e001104c0300d106c0031500030004003420280040030300da44d0f400200c1c000360300c03007070204464074050080d24043c1d60480b06104480d441c5542c190ba039a800040140340c0581c590002841c0e1b000a840b4039803107140903c000e107540e005550030003444980003840119080e00200030500200f034010080342c05884550030000383da43c5071740d0303076070b03201e03035442a40350380003040010104000c0580c0401c1c44d004560307040d021600e1074810001000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 31343719 1250 31342469 31342481
    0x30c020d080a020a031e0c030c0e0604170109020306014104050714070b040b0105120a031110060303020307050f07060c0314070203061003170306090604020705010b13060806060301 79
    0x100000c07401800700e880c0e1426580100041081c0b81000a041c161203c04000d14407031400040940d90b03524940c088017240c140c000c07800c209003540342c035050040702000014214020f0703000d20500b400f58210300c00c005207425484140c92035002000c03580d4039070751000005014400c0b405010500e9441c103002d4580b0b509005118000030f000e08940206142808044c0402071400921000408c26003078044080c00032100020806d07207018003404942440c2500340103e81800c1030384001e000d082d01c0c035006460781300c021884d95610765152070f00c4031001c0c04119a00e8075110303e26a41c4a15103142900000030180c001008041151203802a40c84441150310b200e91200c1e0715119882c089403c2919901c0003030710490710068000d200300041402c04181341c01080c03600404a85048055016060500a11201c00f003107902d8810ba030301c005031a40c03401c01d000c07411030000038280b0340c05680c02044420400c2020b400c0b04072680c40141600300d49030860300ca090003800e5140f24020031400341d02c020800e40c0c28180142 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 31344969 1250 31343719 31343743
    0x80a140408040f090c17092b0e0307060905060f0d14150a05030d0e01140d0606020f0c0a0b0c0a06090302010c030b0906090c0f04080601090902010906081009020f0705120a030c02 78
    0x1206160701c0c083e804203400c00300401d520018024400b01c480c2000c04045070a90548c101341c08407000048580c0301400c00c0f000b1032003441c441d40c07041c2807c00c26103034480c8214007a101c00b601c046031104a00074075800140502007a0700642810400d941514180700c602c0e0a11520400320058a0708002e01c0038041000b1240c0142030701a044249015105809512050071289040c5000d00b0400d103291f6000320740d0b07041024042a401d454000401a280c0e0400c854048100813001a2030402000800911361090034450f0a840641c0400c0d5494580c4003030204100e2550444814840040c0501d00240280f0030310a1020100b45000140201814507503401031061101500c42442c035281c610b4220700a800c5481c43c040d1047c02080701242a4a0078460f03a0f00929007614080b80952481c03002520b04c00c0c50341c01240400010800f005040303904070304c4110031100380407001a03540e010800500942d206546000e045e03071141c3c55440a80d42c0b043d80007030242152680d0304200303801c42e0300b100700d845901030740d16 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 31346219 1250 31344969 31344977
    0xf03060905090606040506060f1206031c0e010c0201050f03040501050a150303020703022b0c0515091c0804080111030f010605070f0809031905010f0b01030c0c03080a140408040f090c 80
    0x35929082c507a01464115000a2445051003403050388274805c0d80c041030f0141c03080c4403c0002e120755420300300169685404c0c5202c100441d03005d1090020506d004840c041c0d4100982c5850b40400d41e4050340c11214a00b24444449541c3c0c58281025800780c00d082d00c06071035080c036005514109a00c0c0a21760307016a40d0586c06004031510359020091301300048040709080162120101c54040c02c905a10b04002d4400e801d0801c0d810300e05010400c0742c40c0e50340c801c16040c100030440c440c0595140c03c501e0101108200a124606001e401c281c55180100d410a040d00e610340300e21811f500b0350034409188280080d00b15560329070788038a41140c036405040801000d40340742324800000900500c010f4286000040d045640c00405820006050007108100f61000d0755503407070080012540340140511000d00b802c040c0080112182d000380b019401c904090100b154803808514011000e0b00006120821381103211040d0409051880495000c1d12a01082e003281541c0004c0750201c41c0a071450820321529 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 31347469 1250 31346219 31346221
    0xd0905150d14010e04060507050a080f070c08030a090c050402090a05010c050a0209010b070308060406030209191d0c090f1003061109030d02010c030e030405090703020f04080d0f030609050906 84
    0xa000009508002000d01d507035a280d00c803050501c8a2040414000c0c01070380c01118450411703041403411940f01525a4041060800000220701c0e04502da007a008907e4155141d202e03507881c91704880714141050001c0c40c800c800400d000f40c0c01e4094000d4005107001d1169520065594400c10007244242c440041d004965080208820f6000b20784501c82580a102907400821540c1d0000e030440e2403d811460300c0301004104882490703030041c903e51b4000c5041c0e070b08006290654000850420005003480c124003040e003000e802c0441c0a0704082050300d140e00f10320039140e0b01e900546849e41c3c0c04200c8503000d180d40c3c200044402c41a0070015009800c1c15100d500c0443c01e40c7c03240b46c0a4014081600c1030b10004000040054600f040455034244143e400002d540c3c1e5101402015101c42c9404020b141d8400e21050180d0303031742c5c5040660404841d040050ba1000c01e1503c1e08290301840d44031084034003501a04103e225017224919181142594040040617110201311045907019103501c2804d510a00c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 31348719 1250 31347469 31347499
    0x30c06040e150616030201020406030b06090d06051e0411011701060906050703052208010f0e030f0c011b0201150e1e04020f0a080325020915010903060203010b0c0d0905 74
    0x5084032050701d01903e241e1401e00000c215081c007001014080340181e40c005801c21034554140f0801c000754100720b41492514441e20001f52000a450201400182e500c80c0800d51500c00002c05003002c1e0a59004151a0f1401d418a492440142070003e400710f030041c94000458164084024103035003150b10784400c0f03175050450449a0780c100c52411003e0040421000b148081c022224a5071180014681c4690300d0401403500d0075524500600c60315241031106640e03078908040250703200c0601d5100800d03261003e9040d40707070240200360107503001d402001008201059040d084410004080151425140e42d50000404404400c03180442511078031000020441c0e0001c50a6808c103000900341c0c1000c42002001990161483d80f080103181d00001f00b910480e807202e004000b185d0032025221070002c030b040e00440d01021008111652042400b03180e2100e5a002c0d41c000e0000d10b402042c00c640701e60312646661026827041c042a1224842c006a00040e540310300450010394030054005007624802e4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 31349969 1250 31348719 31348741
    0x10507170a060e13150509030d11070b070c030225060302130f0b0403050c18010302060d020f0f0d14010501052a03070302060f0f01030506060f01050c06070e030c06040e 74
    0x41d0080500302e8807600005210950080c034540500280c54032101c02c000c0034034103118028041040e5040c101d041c1000c100c0301020200944074182c040c180b002c144400491499405841103050003803200003400d050080c4694040c1d21006210710a0b021070b400d10005101c00c00c40605c46490359001404052028440c0d280310b500030340740c10700c188551044031907202c9032440300d2100303150424020808007140800c1405410030032520050020784141000d2481210310404101c014080a030069800040110101c0c80c039a040303801001003444015150040b400741e01c505e41e44001d0100388600c1c200383c400c007512203403550032a04030b0300140c40304d500d802d25407010303a04550a00103400c100c0000d00e0081d201203506c240005c1c020944294080c1074246000e002910349100e01504100d250001800188002240000c0c842d821010450310700d9420340f001c20040703402c0c1c03250f84031181d1180241814400081e410000b241c0420f0021804d8441e00d0f1900310038449a801140b0400021540510204280001d5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 31351219 1250 31349969 31349971
    0x607060b0402090a0806060102120306030705040e100501060909060801050702100507110708010504061407050406030908091309060e0a08070b0603030708120f070e0303071b1701060e060301050717 86
    0x2800260500043c00300084402c100380d40072020321b0300001c080003240d60b4140b00100b02c5900b104480e80c210304024000c41d95070803050007084d004607a0780a203040915810049c2c010501e41c410400e02c01e80d0303160f00006194a00b188030310b400007810a5008501c43e03206000c1c01e0300c82c10300342d40100854600d00e107445003d0070000e484441401010300d2407062440091080c080540011000822036013010718103e0100c0d4010070128000e03040c0902803010b201c0d440742c12141150280d28000c00e2f0300d02e160811140034418030710899400652981640e080c5225900644e0b5158001c0200300807000c051242c25864601402e801803000c05c2c10000c240000d0309903110540c20204c0901228180b000d55906c1040c260300680d00c4d240c0040c00e810800040002520f1034030b034001064607201d00b542c5900030100c0c1c0d4038024950f004068007940580802200e0340000d9210007811036207440d04801d032040c0070180c02800385000b4200c1d00c140e40c800003526170505014140c0130721a03680d40c000e080b105c003040580030098 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 31352469 1250 31351219 31351241
    0x6040303020d140d0c05090f04090305030c0c120a0c021201021614010e0105130c060f090612110406050904050a0506030c010c030c05061005010f021203060d03030603050106030305090a090902060706 87
    0x40f0610900d00418168401c50002030303141d440307051703507114a801005561250313001d81601c00e074248600c00000a81c80750a51380c10401c0d00c0240c603202c0182c0d1a600d402c0401208082d007004201140c140c0741030f40d00002d0f409059000b03076690003407280b000c0c000600383d120b00c4050034101c00d4190b81800c001003000140c814030079561400016405d0100170b800d130a5071002d842c0e9140ca01c205215030300a001d00e9843c00b000a01031741c1449288504291006400764a0f04c0c032915081c40748100e94280800e8140d082a4042042100d0096036251600809000ca4001100305400340e4035000018000d400e1a1082a004250060060848900906c01150800c0403640b0841c03c001103400450009501000107600803109800020200c5007080c00040034092646c44682c04c540c88482052418000c003c1285d40009058568980c00909030505030b01038660b550000701151310342440001072540c03000142003c0c1408480340c80c8015661400581554010813010307501410030050400001d4203940008503c0c1c07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 31353719 1250 31352469 31352507
    0xf010e01030b04021305120d120c0c0f05160e04050709051e0f01060f030513020f0f060304120917070501030203180d020a0b0603010204030b130f150b030c06040303020d 74
    0x94031210104061760443c0d1305180d40364440303500a0060345441c100f550032031440070300102011180c21030010041c0e1a003102c2c080c040ca03520300e8a162500d1003500b92200041d00700c10f188041c00250f01e005680d400f050186031401e01d0904101241c401038165106010741e40000003448118249038400c0000e110242851003800c02c62039180000c00c00e5a03010724842d035074242845040b585090030240513401c3c6c1d03414180825242c9004c00090134900c68040e81c00c180c040e5541384010b5144404144455086030f042980704401004006c00c0001315259072001500707560781c40f0786003695446440290200305a4222130398102c02e009010551080e405160304c1091901f883d4204030744250864240381d8604003403401a0440c50604080c84038801020345c102500760001c600d010302e1074440d840d0011003e814030080307031001e1140c43c3c2032100f2801244200b0b0341004241c1034001000100c400100180202180240034034102608903103000e0094a0803617401d500036000e15010140200d03000c0d80a00c030034003113030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 31354969 1250 31353719 31353731
    0xa06080a0302010207034a12010506040c05070507060315030804080606090f1302060f07060203010f0f060207150e040f02040f0609050402030103050d0c03020316080304060f06050f010e0103 83
    0x104204022104815010740c0005030394052508005022030000f440c04800380b91b0300c10480d801076480c94991080d00c0c2005040301c04460f005a14240d01c094544483c40c0c1c131902407e18501d02c0241940a240641000c46081006411002040c1d801c0e0180104c0540543c000c600100700c00f901030313002001c4803940341d03500b20580c5403a581c80400d2504150481c0081d139001c0000c0000c40d0800003600c1d41c102c1190700c100c0e50149881c0c982d02ca41e00701c299200901403000800d003a4543c41c00e040c1551b512a5100006645079070f103c618072201c0d500d10740303d58038101403450381c002080c46c0080b54000640b03d00c07544810394901d64640540c0c1c0d180401038506d80080e5911180c45203120f41d4070240c0042e01c152940c6120b440d14101d002440c680342a000103110340d204000400004000040d20300c03541000c3c1c11f1460720300e038850800b40e085001394126420b401c2c0b0172049440c10481500000c52203036200303071030400440701040c01480403108180101a00102070b2004900598096200100d00100c14907000c229 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 31356219 1250 31354969 31354979
    0x40c03050304030b010905090601180b13050103080901140708030a0b0d0209010303030c11010b060414120102070c030b1e010506030903210402040606260c070b090610080d05120a06 79
    0x26503802a801030340c1e004e030f10704014894186180105d940100580c0020007441d410000e14000c0424068182d0000391740d110168101a21440b2000500842d446000c102d250f80da82001251548000810381c0022040781003024024a9902540d007103603005404241140c0d00c40c0d18810040014a800d0740d8050b01120144006a071440d01c000d000c0c40c820354020504101841001d015281002c0851580e070341041c10403103a41c0c032603200f0384080700d0107400200d101d00032410120b5002480c060061001c0d500005040003808000c0b500d0b43d085034440c840042483d82c0d8102000411008880c81980400303a0000400641c40d00c070b0051134014001a040d80e10f0103802441c0307811100442d502003005620100f0400041d880c252240000801a60a2540c18102c0b20b200c3c040904d038226080c045448541e50108d400904c0400035201c070700c2da00c0001d403440c2e07007400d103500c070340c0c821040301c0c80204212494008900f8030004140d2214803040e548030181020908220044840c0300100100300c89581c07480b00043c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 31357469 1250 31356219 31356223
    0x5041e0302090712060812030c0306060708040311150906030a0c0e03100b03120a09090c020a0f080d050c040f0e06060c010c050c01050f060120010e070f08060a0603020603070503040c0305 82
    0x20040c49140c60300700080c0380280004d005d4441541c00078086401c00680080b000848108aa50058030341103520b80e29603403000007500c1d60180c002e014214940100f404030030020040c6070288481707000c40307134000e81c150041070303001480c4190040c1c19044182400452408070032030304604009510390034506981e01318600400e2610300c0140001d21099200c005181c01e43c18180030030b0700c41030b60340d44d0303d28600319080f440502801994440c4c45185980c0c1c12068055038400e001e45415a6840310400d12585450305040e00c550708080c4090f02480e01d003001240000502c0c4007201c007101c080312141d030f991a1a0207010030408034000c09554000710100440001080d00f0b201c4e035403401450751610340c1c83e40720410300103007125030051002d00d10400d05400e1001d6a81c00038064041214990030101050260350000c0e03014200c0c0400d19820740c810310301c0202d00d10942485c00301c10380c0c422008441d0f1a80d41d00044405648483c88042e4005104001090340c42d84540015a40180600300030104c1c655030b1341c0c0f114 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 31358719 1250 31357469 31357471
    0x18010c0611040e150105031f08060403080a0b0f03061302061908041202010c0806060313140d021204150e03070e0108010203060405010602011e0e0c120a060e0304030305041e030209 79
    0x1c01a0603001800740704141140c1c0005800c061581c40c1c00d00029040c20000c2c0182c40003030405129a00308060050140925171000005844082c0c10387d00203040a15000e0036914098400d038007040e0070003c2d01c40c428188030001c21039078a0006c004000d140c89032800d1200b000340300c41c01a60402e1003003191002c0d40404082c80240030088d82d98003c0d0078038081c2003900c50741c0700501c0c000c0116410100a6403141e0750204400d50040070440b0400c0c6d59440350324003944408011400100724403003a55074140c408801154500710800140c095403843d54003441015041e10850083c078001401030490f00340214400d0b07110700209600501101c0d505078a0380c1d01c80301c1c08030099011129a0790004200107880c100b6000302801085540020700641492a0115002c04014150724080654550b00752804400401024814400103449038036070a0080300e00fa40c440d0380340c0b0002d845640c203260010007402070000855003140e801d035880350700705070070511880b562074143c0d07484c03c2610054140c04030150b50381401607 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 31359969 1250 31358719 31358741
    0xf0f02031e0306090f040b0408031302040c090e01060f0801150203070b09060103060b04020406020303190b040c0c0c0f0b0733020702030715021203060319030207030c0b04060518010c06 81
    0x400c0d02c2c0c2c41c010041003140240100010180700ca03040c280000101c3c2410102d0700540d210501c152a03549801070b0340d0554241800c080c0d486405d12aa111050307800070030b4001510168400c6c0340c5140c0c0c03035240603034058412844136800030f0302800041248808280402d4603440c40c40c41270f280386c11081c0d02d81ca9010041668222250307084000100100040c41c480c1c4001d1140540d01503081c02d182403406512408001e080e0740140100ea2442002070140b9413180c1182e0f0300c000d008000485c1070501c0140301000892003110403290211000c81c121b40003400220071500b540494070b04d401d40c55518940807000b0340601040f00c6102003070340d00e03013aa810f6039a07480b178101ea1500181c0710982401054940805640400315581211070000412580450030b62546115504201da0383e07240c1c02c020a191007030341c0080c4045031401205007020950302203840d5040342d0185070780082031074890b40d0981003441980b041102103801003010048085041c99032100040f0141041c004844240c2c07076450a0b10881aa1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 31361219 1250 31359969 31360027
    0x801060b041503180303180204020a0f0210061a0a18060f020c0406180908130e1617161718010c0201050118050919030201020306010809030304030f0f0203 68
    0xa0042081e1098010150001e40ca028003c0341c241000c1e4201d01044c418000d41003507210305100b074101c818042c0b42d1095a601900855845450b0035000300000000b140f0f5400500a40c202000d41b180d00d806407405550358400040c551400d000c400c6c1c1e4641e800110804284100703020200203003552101040c0041c03400791a1130808400c0381400900303141103034140034841c80c90401c00f40208040c0310841000350400c001c0015001c0740301d0401c40454060244509190f84140c040071503100003056070a809406c449090640c46248008169606034002c40612030445032140010b1034410514222880d81c0100d06000b00441203490102803030003011210340c1d1104651441c805e121000912a01404034202e2008024550400e9840a4046101c810350742c0303050348960105906a10030711a1010700003035a602da41c0c5c10f9500e0310300a8080e4004689084c0030132411000180c00c41f0010046a00c580c0d8180c0d6504c800c2e01d510b580694105109184c0740c0118442801580b5100300d400c1c41071480c0d4821029 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 31362469 1250 31361219 31361227
    0x1c030506031c201b220b0607150b09010f06020c0d020a05090403020d0207080114010b07080c0304060e150309030d0c0908151920031306050c0703080106050f0702190801060b 76
    0x1c5846030040750309846038020301170140102025100b03041004020069182c010482034102000540d0034043d0480c06001140c0a981d5402200280e5000c4c186107403050340c4204540c2e80e54071000141110700d200e990b0160304241c80d06825840e01d40a945020351004000d149116200d1022445000c003c44048001d6401084842c0c4082e40402410000b010550001e1009000142c0c101c00c0070311040c852107918800104d220410481102c00381d90a860b41c00049a440b80e0b0f0f96a001071100408039181400740880e18414152084c074a000c40344a13800600c0154508954900300c08000c00c524403001c03080100102001c0395800082c0545040b131141c14044211030700300507203c1181c82088901c104480c40c6065001507121010103c10407804e40390300c07900781c2c595480113041900d03042004802002c40d483d040400140d400b81c0c42c084c0c50307030501070341c5c51410036a25030070140d41d540708072003c0c8a0001d4041c400900103140030000740d9101c11034003604103040342c0e96041181c00c2d2000394020a1034000089 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 31363719 1250 31362469 31362493
    0x41502120a110901090e0402060f032809081204020f03010609090b0a05070804030804031205040804060e0405010b0912100f02040501020d0203040b0421050d021c030506031c20 77
    0x101840ea908960700510b986003107540ea00103440840944506501c420f00c1c2c200142c10741d030b04c0a00f03444242c1d4030030b28229038034540000401c022442201c640010410154000d071854072651050132059075000d07001d5413408484252481002c04003c0040742e10209031052103030300d03403000e0103543c00808030321002140c01c1030a440c1c6400f00364001851613408614000800c07200a074014442ea030095058200001903485604048400c080181141d6180c035040c502480100300f00d04006008031260340c0c0e1140014a200c0f030412041c0d40c400c0c801d041280200340041d0015182420511040b05601d42c1241c501c004240b0040307040d120b055007140c00703207980800c00b00304c10758040c8010a0f20440c0d500c0075510b041d0030090142050300441c0945217040301044000703022415000021001c26800074100c075200c40d0b180c03000a6991202045142e00403210b0780d0841c403114040c4c05424045c1e1001000740c0018000308000300306598541001c0300c00c0050b4040c101034500c04040004040d42c4041024001240c0301c0b03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 31364969 1250 31363719 31363721
    0x80301090609051009090201050d05070c14010506010804120504050d11030c030601120b06011419020f0c0d0803090313120201030501050f0d1106090414090105180a0803041502120a 79
    0x19520503442d42c1e0400d010405074030220500882a1030310840c00042030211030004842034040d0344801c4d01c0041c50003050103100d40e000202c80b01c2587c869800e103414500035112a40c03c2c2c84041d6074550100f0411800b06001039905d441941c1141940e140c4281000c0d5514000b441840c03c152054600c20714201100f0071a080c14010300f050180150002c051035458a0000b060a034074050b009009a101c0c1004552540c0c400c495903201c2003500c07105540ca4110f81040d02c07a04404844400c1e016109403402e0a85180002c83e101b064244020030b4021541030a4907400c01c0d035070005080c2c03005800208400d4070308003a01c05660014180010794143d2180d1648001341c126001070f04030701e2003100f80000c0035855a580c0d80c540009140e000d2800d10107608204082030880c0261615a0f90040c02c1c0090451240d05d4a415248100d080340001d02107030b10381034044074080c00520058401c91300901030a401089468000319000f6101d684040340c0d405010081d48101d81040c04080100d00b007042c01e2101428203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 31366219 1250 31364969 31364981
    0x15060914010c0803041407030f0803060a0906060c20040903231608090307030203030d0905120708041a040305100504060b0a0f05041a12070810020307120203130f08030109 75
    0x81c00c010007440c01a0f15040e0050000400c005d00f02c4a100304030203075584060190758010341c0d03c40c0049200305000d03c0c3c0606640c0003181c0311400b5000c0b100f40003c0c400014000e100803600700341c0b21071300a00398039240c000d682d111004d0300001802c00d08402060075210b921404207507500a03640d602100c0c2da4111103841038119140c0c208520031b400d0100d031510032460540040e000c0d034440c103401d80d01d2410380042410106250f00203945400b0100b4500c00001c025000309422501c44d0064902d2416a45540401c2c0e004032840900320400902c070610800b414507596014a00c0e40b6120141040d40c3e030b1b541c83e45882c401c1c08000c00c60613191010703c82046007a025a82c0090403c985010020742000d81304447c0369510312415108a44810b40148014902000d03168515006450f910540002c141c4103a80c0f0361a0344181d124602c207064814240c1c010500c08d0740c1c02400641d032100d09848280043c20065000a4007698404c00ca078018070000441d000081a41140f041003c903032650304d02009042100c607 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 31367469 1250 31366219 31366259
    0x1b05090307080a0f02010801141003020702011101090311070e040f02040203060d0503040602070314010c0f030b0415080304031202030f030105150c0105040309061e080a1808040801060305190209040209060103150609 94
    0x178901c4e102703000e030b88400000031003507000d2400588814080c00100e0723a03403403002e02c40c082e035510f01080e0b2424035601070842c403043c99001c81181c1310b40340c0d290240d8200c7c01c4201e90107403001360a030881600624042d002180c01c074a00a20310040076485444103415944603500c081d000d0381c40001c080003040a081c11a08508000720000c0001400c001d80260002d0070300b8840b18101580d407510344c0c42580d101d0b84011403040c5408001c010107520740c0c2181381d80307501501098030254400c1d00301e11a02803001003141c0010051010190544e440c0c00d060100c200e0b889d007400711041c2030a100d511800b440920403a4401ca000350341d851203103850303c0f43c042c2582400c1c030051081d007124000160009604111781d20380089902030300081a03d600140303a9250303000f00b100117100500004000806801c1500070304141c0380110152503142d0411051122071801040300203401084a000240240ca0440e150507441134040c100400d075901c051000b514404000c1d040000450072803003051140d5420025080d150300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 31368719 1250 31367469 31367489
    0x40b0f01080312040302010e0a05030d15121202010204030206030c1b030301080a030806210706020115050901060302090f03010e011505060c061603020405090f07121b05090307080a0f02010801 84
    0x350400ca10107489224145608040714485004101010300c00d40c09030244107003090549000100c00c0c90907d40b203a00105803040214288011507005500010184040394403d401b441d620070400e5994861025203072071034000395542800000301503240d441c000e610070034810840641d9010600007000344405414031812150b402800107002d42c080c00103a4801264141c1001442d03a40d80360300141070703d08415020f2401e603600c1411098400c90000c3d4803800d5400540092005d18101c0c85100e000f0f80d0140705580d840300c1502c0042248a004c3e600404180307201801001c4112000c41c017007802d6615205e003a000583d50b4400750309001c3e0580e040400030340b01c119105860704e0503002c045582e4103400703401c0702c0ca00100510b070700c01d1180c000c8d0704607001048007403c1c446146c03421151407441d904003102d6007004030b01601103510080680e4442e03280029640300e01089656000794044805400c8042e48981500c1020004601107104001c1034003403d00c150703070030701586080f84001880c0311b4040e40004410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 31369969 1250 31368719 31368721
    0x905130e03030c160f050f060f1009050c090d11030c0f06030105010809031201090501060906020a02091501090302032b180506160b0906060f10050f03040503070b0906040b0f 76
    0x62500030086035000043d8100700ca4603440a60289440c40c07101c071600030046005d0000c424200b01012600104071629441903c0c0150707101c1261385640316003102e044000b420542d00900802c040c0740d000c690172640240700c46003040c05080214040c0c0d0603210080c0c0d56140f000042131114501000070f03058001c03050f0b90910b040170070040460390901045c010181880340c40c50010b00d02c5502003080e114103e21040201a8035655000b0f00f03401020f080c000c004c006250a840401c00b9070001800c248501c2d0302070716400d05503a4180b0f1740f180480711300726103a040114008000000d41c1e0200081c89000c0c0d107100800850f1300c1c91090501d44507002c0300440084c010321815140f65411190204021940141c4806071390300d40c02c942c3c0136880a2442ca0040045007010148020741c500011801c0c464582911044151080d5404002c00e462089103528009002080651900304940f009950064071850440f424210a039580034801c504c221081d0510768003032000c00c401c1c0007c0f50283c5801c80a0b0500c02c10136 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 31371219 1250 31369969 31369991
    0x10302070f1106090d030503040302070608010303050d0b13020c010b0405062e0201020f0a0201150905100605131703030a0f021c09050c09010f0509181e03070204020406090513 77
    0x300e00e009520190507007070030585454403603d40108450244d84004c00650b401102c81c503001d071094106540540061048450100729203009001c141d06032909074940c941080100304440001d005500d03407440d0010380c0d2100c2440c0070701250026028484003107002280c0351034024144001c49600030030040c42603610ae0075015180c80190454640b91081d00785d44504611880401d80c0a07205494001c44039000000d030f01c0d042c482c0d0650283d1840c0c0d980450781e86a090b90380c0d6020055034001c0c1e81544c8215060f003000c015060040c00200117119100400000142d614400004080d81960b8659042d400c00010400d0100443c41810f00c41c0074100c0307045051062100700b0350100c80400f956500c07410303581c000180a0150401000300303040e00080c090350f40340d84c480c2942c02d4916858460305000c3e0400b000411038203000b040080d03800c10201801021b4040002143d044105095500b0314520301082241002607103d03800104060042900c980c1c025516290a10400805030b0300c040c014036103050b40c0501 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 31372469 1250 31371219 31371233
    0x60c030c0f0a0c0509070e0607080c0d080420120a0b010e1e04030509040b0405070f0f08060f010e0109180207021206040f170409020315012d0804061404050a060b01030207 75
    0x15100d081d21050178580d101c40003982e442e684115100d61040c0040390307500412041200030b0800c4517050f000d17251160b046410907920440203944c0240b0b41d03041c100407002c8d00c80d401184242111030040c885458003240303002241c107225090600b0b3350710011040047c01a280e82c50041074200000f048ac1443e1590031503c000545c1e40007400c01004c03c400000c40380d00a90300c0d50003000800c18018030810007800c201c000902003002251035040071901101e1003a40944c0100c0340b280c86144083c00c901031000030039004482d004000c000c0b0034140901544003255082d001c010b012007021038103200517914020b90040003e1091000501051580704e01308120000307030603803400c5041e42e60011034145024503d541082c2180155005902d5052010040144171311100314005a112801e880e41c180c2013810030783e4170031081008140010046400a451025240b003080680c1c0c0c003a0043d040040c0003040352100305403000040c1c40c26500d542c084040503040c00b0300c0b0b03c961801c00074242400c510740b0403140e40d903003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 31373719 1250 31372469 31372493
    0x6030c0306011503020d240503010c0903020d080d09080307020d0206100b12060301060909050304030615060203120a060e070e0102070902090307270612050f060403050313060605060c030c0f0a 84
    0x60404d900070039911b4480d462504601600c9680704540c075840301240312000102c0c00381e841407030302ca98205030310160100d025410080c280c9402510702c403030031a017a4643d03150690107202c060041a41c2c403c0c1036030200d0140405940101c81c030b079010b003908020b80c03d40289050300c007401c422000c2c00c0284081185070703c0c1d10100d5030301440760480c0f00016642c010000b8010728941d446031920a0070311918400b0000040000c00c1681e204070780c20024109002011407044049014290240c1d20411080f0700c4204850515540850424000300e0f890383c41e5000703040c03119810f581100c0030607035144a001d11581c0521071500980700e400011800e044400380060350301e10583c401d19082c032540d1140280c008081c0d01301c51100100911041c400660349001c00584582a034000382c03042d010f0303883c140c0385100c4007107005800313140c16039941070a60f10780c00355440f079081c90710200301c90b044d5440724006119142d80c400f03815011349032805952108540310710784c0d085c030003411011440ca411109503180011a801c0c640 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 31374969 1250 31373719 31373759
    0x10503010b0d0f020f09010f05010305090f030901120f0c030207122a0c0e070c021005090d0201030f090605070807030b0a05090705031009020c010605040b01020a0c170c0409060506030c030601 84
    0xf0100c03511035070020030041d44d030961070150801450b20021565501201c2d10604030340082c0e800700102d5444086440d2100c20302c1001810a82040114885c0d80d0310840300e040d40d80031601000200000310f28004c02c00c49181c9000303d40480d402080d0102403180c10039000714030044904000000032880e940c400800100081a042c102a803030510a01780451401c07240081e041140303c00d8011b0401d094040d014004203d0200d20030a040d64036048058424016164541c0e400b0307102048a061590065000c2c10010400542c541d0b03803003400c00041041c900916000e004242c41c0d0388418245403c00500391003507008018001c2150810422003a15020046640280103103451905d0340c4903820450045902d950146030b01ca40081880c0506040c1940681c0841d48111810401080c00a005a86841c0d600c1000b80400d4814442008030100c0308840b1489107002c20180d07150805200d0004040350301240f020744406681c4c1c4100700340c509003000340190468048008158030740c0742c01d2200422000c0070700c0d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 31376219 1250 31374969 31374983
    0xf0a05090a0b071209140c0607080a0507080d0203040b0403030e0c010e040506041515120e0606010309060e10050405010c09051e0a0509160305060915060309030d091a010503010b0d 79
    0x505007510540c0d0213412070040e0782c4284401e0485041c4452040c466080d91440d80c016030400b1304462501c0c1d41154a0140e0241c2d0660500079903000903640c9070040c103030650314541c080107901100074692005511442c030400c040e085c9070400d402c00030b003220848802001103900203502480c0c26030300710000c0801c6106c12603000c6669074540d00410301130b01c0003950444142003080d401244000e48581a0b40c00b000b510781d600806130009171561002d8410454050350607402203400300d28594440c1d0044182d103070156002107000307203200e0326903458000c840c4011360711155980c041c4820000c0a004045000c0c440e0321301002070a06000005400342002903130341d01198510624210ba90f161b40b035a510007020020039480107131400c5c800a4100441020220000030f2929000690074504400d15901030100320208010903004882881304942c001b40100c40284010711002c94207110f580030f880100d0307201c2c0d013034a552290101e554481110301a00031030b02c2641002c00c00c60542c0c5404060218040d00075507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 31377469 1250 31376219 31376221
    0x1a0f040e1f080c0d02120703080403030e0306070f05160b01060903060b04020a05030f100312030c081006090b0c01020c03070507050a0902030c07020d11040c02060106090602030c0a0b071101090b0f0a05090a0b 91
    0x200140800c00c064000b80c6147c000c00e0000024000c2510290003201d00036226001011003642c00c254030f94004952140118458501002083d44224040c1902e4142603451088400301602c0c0c550000409a01c201c0008291200c02d04c100681409503540c0d10200780c2d0103605207207465402914070702008007440224440140013030a58154122950020754001c1110303000036070381c0c070300c024041d1000003980000725410302c000c0f681c3c02c00010550300840c0c0d5140d030741440c19400d00e000c07250a40d001c1451050590340900500e096107000f440103200442c0b05500400e501403905042c020466059803211010a1040c010442c1c141e07800d000722840e107503046954040b0580a4901103202003000e445050b0030510700320a8200740e40e00040d401d410380c1c00b070b91100e0045958552049aa0b88155140c1e070f203064005803007035800100c105242c01d801c4401e600340320340c624030308007110350844060380c034182c179108503520a004050034908480ba030400f03401a0300f48224504002d01d2542c4d0130200e60700a1400d50054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 31378719 1250 31377469 31377473
    0x40914071d060d020616060b01080f100e07020312090f010606050c06010b0a2a02090105040b031203040303140a020403030807050c0a020f21010906050105191a0f040e1f080c0d 77
    0x40c215103400140406c0d40c40802d00c141000c0000f13201e40c00401c0d002c1461400400c41200c180000b4034880c00501e065015032900b440500c20f6050f001414640941c0300501000e84a00c01c0c2001407403056506500038201166803081c21400d407480f5a0020701030110401142c0700610005c90300358151900440701d240da4084220049560303901e080214490b00ca003c0c20000c011005e01c01e880b0f66424000c69800c0e40300c0c4d0301c9204100850f403242074126410307400309043e0756804d00020050350340140070341400503001a03805900c50684108a4402254681c00501070007050303040000c1c6500042c4514006007040d407503406040d0394446001010344102c2c50f149120607966905004158018900c10f1040f130182403035801e04d80602140103045424900705000481c460030724000750401064194588441d4034076001508850303040041c0344522405003003101007280710f50a802440200b00c400000441407034200545014240b50703c6141600e2000035200300001000013601a84a801c1101c01c1007020b2003134 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 31379969 1250 31378719 31378729
    0x3012307180b04080c1002010c02071a0403050601120318030206030a02220b070c050d020105030c0a030906090f060b1f050c0724080f0103080d050405010b040914071d060d02 76
    0x742d100d1201a8000078003c141a00301040c904203025050390864503d60310000181d007030728854116500140d01c0650104030f052040c0c0c20310441c1300390459006103800d4581e2601405c10034241c200c10025802d08140c2c1041652200314400038101d4100c60031901c0b0300b5640050200c1c40090021280e0540100d4150324a039624071209403814070340141c0c00001070341e50002c83c00940100c3c01c01d694203120703920005a18102250110030a950503034880349961758074207007006d65400031407580040555074040500010b4440c490340186074014a1040a110614900306050310503100c00c86010b90740080c0d414041030009050407541c20100e00b40240c0300d0800d90107151800c40076500c085140c003c201d1501c03210380403400b050f18680c00c0d00e80c1e40c0000e40e650100505156482840f0040c5005c800f046207035912003560303100c01e402c54070610001c10011100300c009001d03103920000c26180d07440810100f2a58a42c1088058010a000781c13510000020300c040310142c440005040c07a004e00c1601e200b0a0455481c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 31381219 1250 31379969 31380017
    0x509090405010e0706080105030d031103010306091e0b04060513110f150f04060e0d0305040317160b06010809010903080a0b18040308060a06090b0a0309020123030603012307 76
    0x140f8085618040e615072005050101c02e100b01d501901174842ca00c5c1209110740510028070f030791012410b00c4e6901c1c641d80c2000401000758155070040c038281c124800828410000000c40340107940410540c181400d1500403a8000b40c4140324407442251050005007481100380c80e1080111000c151090180e0040340c0744440002044402e07010000e1641c109040210140040e00d1107a69010702c600002c0c424410b040700111009004a84c1c1444100b000501e460f003111019040c40d65494100324451000a4440d03190000445003c0e00c84010041e01d035034031000d1260711241c088001d0000da030b0652005003a984001e05a000b4181d01d4889150390764581101e1240c00094803107640c5600e2500d4200188604c0051721018414a810b8600003402c620030301006041d2500502501e2a21040650503070040c100b450703081727052201203101c00384100e004800b404c0010407240c941691340c3c074080c800c0508650315081000341409400c03201c106c1001072003200d95484101070404100030600102a00043d01c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 31382469 1250 31381219 31381241
    0x3010e0f0a061706040c06030501050306010e0901020f0a021c020118060207050c06070b0103060501050d080a2102040605090301050c040b09011112030a090308060117071b0b040605010f15050909040501 88
    0x400d55882d00440f890010f04244500d0040344036402c140d44030517040302506d41c28828503a041d40001c3c011311408400c88845500040e102000504d094100c0041c000d0a070052a03200002d0380140810451803c114060f42c110415070384020050105601302c4003180401405018080a901103290710800c802023040210620000b0110f503168649494800c5d0480403d0200b00d550f282040b00000c1c0d00d003001c041035000140c1c0805c1450618145c08030481d1204540b8214404001032030034014183da840d031004101800450782c50680d40c1c4550400c2c9130a40303d026041034400117081000b044046494015205400d0003441e01842d442d90302000f440c0382c00e4102549281004000082c0302800d0469030004802501c20303220481a41d5510700191000c18040910541760341c100c200241e0032601c0351503d10790140f11513050070542a060344030003020000c02c60f011030704c40d5590300050050388690800c0750010a28409400a80a00140c000701280500c0c0d0055025040c20300105e410000c00390031541c1c85c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 31383719 1250 31382469 31382489
    0xc0f07020f060d1b0201020a020d111e030a110718050c070b15010306050102030a0801092705060907170a03030b0406030203010e010605040b03010204240309080c1f0203010e0f0a06 79
    0x7101146a0b48011300d1070a141d041c861110360151407042c2d0040c000c0e04e07c502895000b0b41488208804150f0b24440e40c140440d0b440d0242c074007040350007102c551082c2074408100002315102c110442000d4201c0c4010101440785e540a40c10400000401070769000c07184100c0c090220b40c0c0e4444540c81c01c0180a910001466403114038101b0010381152242c80c0300002c4240c0e400c1c0030a0340e98a0043e030700e0b40b003020014400910344000501c20b00040e03422803040c02035084000ca440c89260292207255a8018108071100d412401c00d111450b10100a810050710403113002000c50100d01c0d003155034840318032100800703050b1107040b00d02c00d0f580c4507440b0000440e00039009118800300e00503141d0081c0900e0013814030462904032107141d1800c0500c2610103039155584001510303500e031030152203668000c07003507001099210b400c0c980c00188400050a02040e0120091050352042400909903a418030f0404818500c140010490703110030414a603040440034402c8a0191104c58080c0041c248c190441110740c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 31384969 1250 31383719 31383727
    0x80c120c0319051005060d0b0903040b0c0f12030702030403061116080307020d0e1305130615031514150d05010e030909010e0601050304030f0203120c0405180c0f07020f06 75
    0x10b0340480e42c900c0050f200f82d00351800e0310030f0780300b0350400c032142600d081d5002061400e02c02d001500804516070000188003c030b03030505946e503004000719030200f441009640c00454413103203601300400c05240c81e030080032002c0741145408000203540740607510019092907100e449018041c0d05600442d040d0b4440d00224081c0f8004508040c04240d0043d140c1100510500903808000c6215a00d000d540301402032a6a0420f03059003180c038082c040140004007001c4e0700040540c0051081d01c298600759191550b41c2039124a9820b10b01d00401c840e1b0000d5158500300a250005000700410340c40d4040c0090091140e01c180f82004a4114050540d004126610700020001d5020000002c0c00d01e1031030403103074007c09a0301c03480807600301d100540b50140814403e0000c60002070040250721141c0c01140f04580c18220243c4200d140302005413504000300c1d1000800b44501e04201c00d808207140704c02200c9115605001525410610605038648615400440e840c0219a100c0c008415031400041410740c035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 31386219 1250 31384969 31384993
    0x11030708010e060d051b01020709050a090507060503040c2d0b040801060f42030606080603030304030206010e0c04260c010f0c020103020306040b030a030c1b080c120c03 74
    0x140030310a004101c005104440020400e00d000401c2c00300c4e459001010b44816110000340a0424010002003410750140380c1c000b141000329889030780c1c412001a070703011070301c844103013495802d10205820600c100501002000041541c0c1b0b040d00040340c1380f0408842001103c400c81c00891a400009844403026840000031242d000c60040c00c1a81d200400800000d90703654075034800e40c90903108584060300c0c40d00035050703210001134031990761504501c40140c2c480e00c500701105442d02030180e0100440d80d284405d110b20703548540c00d203a02850960046246040c90784000e5036400c01440b5011340e40c407850001511852201c0143d5000348254091801c854000607041d2044070002c80030310502c1d1150a041060540c81030001e4060071a06807502c01202100390011001fa610040150340c1141c1c40b00700d0b002e401c1d203003001300741c8504ac000d546000104001c0c0c40c2080240c4586142c81d013620103851410f000c403101c0442d400d4540501183e446010034400000306e402e180d498007040754580201d14070064 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 31387469 1250 31386219 31386227
    0x30818031e060c040807090c020106080d05030a05100b03131401060303030504140604030504140d020d060c0908061005120c030610030606060518040906140c04050a050406050303091003110307 84
    0x103900601806440c40356443c0b1240c1440c1c0c0c0110703c50f00300c01d54000c0d902041429240c3c3d1000300c922001d03200104070746484004051070691b0001128001944c0001007104924880c450703241c000c10150560783c0e08a103481c940ca8224040505190610541451030004200040042035000c009100091080e50355a00700907006000464094601c2105104203186003170303021541070b100786d40c1925a141010b0400b0031051001203400b0030350ba001078418114801681e980a0f4034001e40380f054802144031000540c00510901d09030384451915844a0103201030120040c0019084d0b8600761107038405007515070f6a540ca40541550f100d5050b004030014041100d00c1c1030300b0301c400d42c1d002e0740060282680d81c24080707403140304116130741d10312485501c1032150618241d003100d8a103c1c022080456400900c16030700c040041c05603116100c141d00014100200c1c108094480000c110454080003420729000c04a510b0f841a0f0f4012441000e0340f452024106020798010744414207584000c41d1240360503080a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 31388719 1250 31387469 31387513
    0xe0c040602070503060402031e0a021905010e030a020a050d03030204030602070b010510020f19080c010e010507110105010b0406030b06040b0703031505190501030203100e09070f0e01030c03081803 86
    0x400103000b84000802c0c50b041c00110280200d901034000c2407001074403064a40c007020f5020b030b0640079000300c0c0002400f40e692001c90b100090329504482d14141e1a00d00050302c00f0b40c540d54100d010785c10012401c03001d03a03507101100d000c42e2070681d01680350380441d00c5c040700240706503000240404d10108090052110b5101081c2c16600e0a8030303c60581c03516041c050f6030302c1c2100c5201400960002e615030051244840d401000b0340d205840316401d103012040d0b0182592003004140f01207a5454081105060340801111000c3c558540204080e5060103000c0c5018801c601586090545038031b486201525424201c800a00000c88116102c1030a840e000b4080d150341078084403840740760000411989015100c10303040000c0c40c2c10b81a8000c0c60800154041c0d08000d00580c06008031407800502048158600ea21071000301d00a4000e050416030321400940b401c3c0c000c0d18102c20074130014400038210848403001c3d031303800054580e11414040755604106251500e91780d0140038000c10591800f144078400307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 31389969 1250 31388719 31388729
    0x501030b130803040f080c0d020a0b16050d0506010203120a0609151206050402010908011104150806010503040602070611040e09100b0d081305030307120206060d020a0303050a090e0c04 81
    0x60815150701c0c000c0510300a01e0300e005885a44100080340002e640d40c003011000c180303d0b1000505269941e1403250421141000000c05a042203c046040007841ba0300c5a600c09500c10b01040c0d0a20b8290000340640036410b16200125034030000306842d41c0c020820350b010401c0b2140c12070224604000c00e03c1c040c15076845907061981c00c00003141200d40ca000c40a1049e03034404910000e2414203900c4840140c5400b40c01a0705000d564400420240000c0c0a4500030801c0000020717512071034100d4601203985c9038025001002542d42c14800c1c26030303016044a0b04150010f60258903940035047c80402011050350901c011200010001a10304010603407911608030340c415500340c0c040c5149540195404056034590000303402c041500000c00f0180600304002c800c203040c01905071070700007107440c591200708281c8028218916061040758100701315070f03100001340c6e080d00c0103010350360108091034a030b07002c002c05100000c81c0c050b61242c03082c66004c00510f81c3d8021110641040c0e402400c80354414051 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 31391219 1250 31389969 31389983
    0x60d050d020f1902010507030804020a030204020310031704050108040206030408040e01090f0f060503030a121b05031618030f0602160309060e0103060311120a14030405010e030607080a02090114070501050103 91
    0xc071010070860003c0c46900e094040c1c50303861400e011590100d0f02c0c0c0704001c2081b0f900000f0303240003101603200d62000d148128400e0032030791416415030034a040a2507507102100c0070000104028410359031300a030b01580159042d1103158403030f24740303241c5103032103000e9030300207206d0207007500c0001595410641000d008a00000300400c100818101180b00f038540b01d00642350946c1c0100072804410b0311a60002c110352042403400a01c80200700031140d002141e207400940000c0000c403e0115203030005038042c00514150610407942c111000c04005100b50f40d1201170901c0310f11201c140140035441c1c04490204034aa602c0f0341000d0100d140190810002c1e00801e000102c00a14000c182d500070311569061f203820480098241d0003100c02c00848000c5044070403005c0c05844066000140d146001c0c0b02180c02c0000a1078696082c031000402c03240d0000480380c0310b80d22070420705c840250440a02c40d000401c141d00541d0700c2d809070006880640d282c2569521218000403070005001040d8443d50689110302c407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 31392469 1250 31391219 31391233
    0x1080109020c120c0705060301180e0a03080103030f0507020414010303021c09051003060506040f090f110307030b0a0807080a17030702030a0e040b0402040902030601200d0305060d050d020f 83
    0x1520080340036203221a0b000d0f50280704542420700d000f002508034600030004640c103840d03c82d004030301590001e922141000001c8000000440f0030b90081c00044103495006082250140d02d000702240ca06200240a102840e81c8003c0d146e44980102ca400302d801502c01e200c1071042c40c1a40301034140901c81640180901c010071030601840caa80d03242800626a603040c1c1c424144000c00420030f0300c0380e100d1020b16036214400911510340c0c04c00f81004081c094521510746242654003401c3e070b140702c88044441341c54201c0044c94140c0003000e032034122456160000e11407250601140364103d107508644003521400f10700142803c800108003d140340f06a40d40c0d02e40c241c0c0e5002005280c041566803502603007090041d50345184c0701d416105840c5000500200d5108206800304080b40d0140d040a1203a5070008208101ca580000040b448a52404080340000413031806403901d5078070034442d8008250b02c3d980464140d9032440a11001075401c032050b1441c850048001942d2004015140801401884 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 31393719 1250 31392469 31392479
    0xa1403070507061512030809071d010312090506030c1b010204150e100804120302120403030b01030c02060613020d06080d02071d1b03070239060f04050909120711010801 74
    0x401d82000c41d0f42d400d0172803460500c9170303a041c0c4048100805918252187c10400950381900e103c40903210a06035440340c0155046091503201c4030202030f52001480400c0c082000982c407032600300c83d8881005900c2544071118041308880039501c2c4500810341d51300100380402d0641800b4900d86402d070b1241ca405800141d50018400310358070103c60b503008a0208000900840c121650b10041081d1720f186c010318202c0038544441c088101035805a00295980850304140d503050b1050085401060005101500e803140014640e45031a855288290390007289030500c2050540000740900510001d654901020501c025610041481031980c201c007440f10080002e400003007207501928044c0c0502903409030301540c903041a40007034402800c40c4a11404030b44041d400c2c40700100c0440e80009088103002a07510304a0a0350051015030b44103040c02c0024031520092441120101e800c00d0f20036404c1591404044c6041c00729008400a11000c0050442c0030010955100c00360039001b601e40b618640d0700d034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 31394969 1250 31393719 31393751
    0x30617070b07020603060604030f2f0f040e10060315060e130b1012030906090807050a03021002070e0a020a0207141c02130212160203120c0a140307050706 68
    0x54070407080c25840030403000c80942000802154460000ba141c2ea2406640c1d0b80c0301d10f003080140c1e034140d5600c00704019182c2403982c1d079100c3d0011440302c401480d109594000010f2101444408050f110300e548090141400b28280440002403172148010803000c4e540e070030a0805002002c3c400c43c0b049140980c01305000300c2540b007090048100c1118028a9141c650791a0500078000d000310b0188003031160b001440070710000a40080c20f22a98600f0380c0146041d5020b00340c0c0c481600304a01641003254180032580300d1418200489130102c1c2c1024242010f01026428010280c002202c5c0e464000c00700401504150001c1440d40290307400c58035050f9a91441c804440a4072584640c00b0041003221403441148401c01c025150004000c0d100c0c078422185032004030b031300485080100b41541c4080003841c4190a00209090003240091440c100708542020118000103112400150300415001c14282c032580c90114031400002c03038180d890600d440080e00719000140308451040c02c20064140c02000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 31396219 1250 31394969 31394983
    0x90518040c0b030c040b0301060c06060f080a06020d020409060602030703080903120112150e0f060c03010e010312020709060f05030c0d0b0105100513030b07080903070c090207050a060c030617 84
    0x1088045042d09000500406900140000c81d40d42130522000c0340c6081d942008500030220368071000004151441c0c26002d071089584182101101d001c0108921503003c56416a0154054001660362950149401c001e0055420141d02c035864080042080c98002006052080c0603072296140c0355121112181d480c45400c5218041c21510f20041142c0f611020090541c944181005000000c4842c6d103038040f55004101004503910219015505800c1400700e035800140781e00c0503e26641c10407541410710384c01807100901040803914458030309842401500d010340140c0100f40705841c0d07504400320080c2c040e402540e1107402101c680b841586440044491020792114070300c14540e28080c10450b070818004102d00c2804401c012840981d00c44bd005107010f1849213400f000785042608008058070320082c90101240c1c010440c8a012411407241b050413a0040e800c050307910f20882c03410301d003040b10506000b00710346d0038403400d048815095007010003a80c1c02d5004a01408118002040c0d69000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 31397469 1250 31396219 31396223
    0x406030f050a1a061003020a231801020303040f0b04020a03050303010807170313050f0102120c06040c0b0304050a0204050403050c06070905040e03040e0406050c070203030c030406080703061d0601110d09051804 92
    0x116017002510403a0181e0080c0076a25400e08181600c0b0441100300c0ba155003420117003100312480018808408407400700f8594004000384002c40c1149403030340d1954a10140008050095014130700058115510130880300c0107141d04c00280c0b512960346000c5150744410b03600492108182104441c0c80c170b004000152103184141103201203d1919150074004212680f51001c1d0460040c1d6285944800d007000003054582404801006503140c07a0074030aa00e47c07219004686100010403c3c0b0010410000e2040c50850301181c00240c1c40c0c89900e8240d40c1c9114101d6880e01500542e410410075036001a01442102c0041d202801040d0720064129164401c81c000c010401c0109000318000c28000d0f03100303c0d80903d407042070903d000302580001740345401c00d045103000c5500c006818840c5683c0304803800d4010046003828031410342003424441d1480c041c1010514807000410005440f60300c00d20740c008100100fa800c0d5400a506142c0c001d01040c9035024060281c6a091042d210001544c000c441c4225 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 31398719 1250 31397469 31397479
    0x40f0e03030712020d1503060f02040b120705190c02010206012411070b1210060306030b131106041e0e0f0c0304110301111b010506030c0402090406030f050a1a06 71
    0x5a18000c056803d410441e075001c00c00ca03070901901101003004e100d5003031806101100c07000c81034510310380002511500d02c070200a15006020030400c040c41d4905031140704081198805042e914044112118080d215600444191104032460902d4016680b941928000e07801e40340306030380310007103000d020310781c08800f44090900a422440c401d20504682244803504025100c046640d81507480081c0c000b0720a038000b001801c41801101c025a142c604001c0a0720b00702404960300c0c54951031402cac10000c00150012101da00c1420070009a0482025501401000141c4550b241c00c0c0e0700c94200d50240301c1c1c41c2a201148800310307a0075240c60ba80b9114a08913480d0201a42e01d04040d034582c0d400191044460035104400b00901d643e00b801403942d108811002c590304c9510790f0641c0700003403aa440652089900d40028010107071030124400e55031a0f400c0c4c4001daa250603040c0420010402c5503c05440e4040c040c514104012010880940e07450058201c200707646000c01215480039419901141c2c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 31399969 1250 31398719 31398721
    0x207050c03010b092a070302011515051602220b01120207050c0409020a0b04090b01081501410705010b0a060e10050d020a030c02190803041103070314010b040f0e0303 73
    0x1013171880c0f0407204886451408020314411100701407025801500d81240540d44903508400c84840081c9002c00070450101c051274203820001029040f48650072480c4600348400104500707645a442e15541780c80c50300b03800c0f01c40b1000704030311801c002c000d03070580c0c0d50029400001d00200d0a00382e000342c420050300440600b03603402c0424208402000c1c010b00c100e80044030300c400002c0c0d42c7c1018014000601c1c2c400d00200b1600400000144080e100030907822084160104c11038940c0d9202100d4441d01c0500780500707407001c80744101034a090307808142d0a9880d80c000c03911450b800c0202d43c00340076a20b07c14002030112045410400205c10001d0045100042c480810444585000390702a007242049080917860002c0b80c011100580c0d1003401c0c0300c80480c0d00d500894509a41c10440000802d811218514022401e03503510f800911000c0c5c00908804611204120a0782e02800303500d004503400714501c019008490003850280c103021400c02e200c0c92800303400b0720300400f440c003840640b510103d01031072131 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 31401219 1250 31399969 31399981
    0xc03030406090905060a0305060907090b01050309030a030e0c040207140c010e091603020d090b040b010501030203070509060c030f040602060f010902040e0126010c0c06060801150b0c0a020a090207050c03010b09 92
    0x91000410895001080300c0d0000301191050010038081d02c9408092f112407810802c072001a54070380041d00341041820410480300040200c241c0300300d801c0920f00400d1300100754559516010302800070b1a030041c40061960308100d0050b48500c80568060700380c60000e0401d00054448043c4408040e81100302c5034000350380c1c1251700c08100c444240508006040420003e40101203a025a4045030f4080c004810f01040c09204c0d100c5034014039003443c00f50724500c0c0c0410300800c0b0340038143d415800341c50007044100c03403a80c1c140191000d00031680402c544981e510320f002980c03100d081e10080030b00020342c000032030050580d00031907041c0d61000d98911026444d1440610a0005601d2004110015031039004200f203020700035100c48040c1780e0f80d2400709440a0401404075007040c1d02c601001c0e031400d4a00c560f411040c03c0c5480c1152040c1d84103d403140703a000304090412106000095100200b50004180c200d0154081c0c82498011002c848590300180285822101c40d022a1036201400b00300042c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 31402469 1250 31401219 31401221
    0x6031c05031f0f05010e030604020a05040b030a06020c030310080109030804021005070b0c03090f0610120219060c11010f02070b090f040e0d020d09060806100306080a12020c030304060909 82
    0x141000081c400181042100c209108a440e6241c1060718114803000040100d503174811703600e030391b00310f0700710041c08060405500050300c902c102d10490340150b840d941904203a80e820b20841c400c06030800c1065540724a11032000d9166403080702c000f00c8524060b5408510f9180502c130360300d20154103407150b4100351103940800441880408800c010400100554000502d040c00c001d805006203180b05501d80c10216201820a00c0c0200c41071034961000b004c05c400c036840241e1007021620940e00868040e071a038000b00301c90950303483c54005002c01c05031001a41560200c080c9c0e808a025091070234549821a00440b0081c120102c20001030380310180900c44030810100804480c01c1c020201216a080c0001103416140c280a20401ca0340202100c4110290103010100313002d9010700d0802801c5080110181c10280041d1819020344e00220003d08000e010b40c1c03100b0041c03c059811114100400d151006103001c030300a00c980113001c0c004841c2064200002601e06682e0b80e5100d084450b803c1c011a40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 31403719 1250 31402469 31402471
    0x7170106030510080318030d050903030706051e04050606030d03110d051801062603030106050403031404050d0b07020714030a06110d050403120605060f07140a051009030806031c0503 80
    0x38030b24420f040009020300d010001011402c0410680c0840410100c0030542098005254102840005c104445050782d020040f40c2110781c0c8050300140300c0e210f00c0b594441070a00100c1008002c0028018002031140c0010598490b1b2412011501d9540300b458086054503002c0036201c00c40c03882404a80080e60203504496440411059030301c9c4400fa41c80042070135610960700040010458800080141d030060a68840700c120000081d4070b19490701030001e06500c240d10018082209441d2a1840185040100e0307006050040800311040c0040c20011000d1400740c036500302500c1801c1c000030723030202d403036819681490300103000c0d0682c140140c0702c8601138041c62140e0b1600c22404c01100723550310728a20441d4000da004c5c0c1c1c0e41f812111030f002c04c01d404851039500300c1c0344202d2007803000c0b4900500502c112441c09910101c000e5643d5100e00d052460b10480a000130a030380550340c01e90b0319080c4c1907030051000c0d41c000e540f1081541ca551341450788800d95504010f03001001e4050894034140628025 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 31404969 1250 31403719 31403731
    0xc0603130203120a050901030b0d0c0e04080f0406091d0709050d14011103010602070603020c0a03120207050601090209041416030c0504090c0906120213180e0a0503030906071701060305 81
    0x70b184005030741c0310400c5050303001354829004103002080480d441e503407502c00ca0750819001d03200c0c0e888164090321840b000c503140c1e10641d07100c1900c081c0001c0411a0590a035003950400605c0701e511b441d1075690280c00000d440c01440b000a02501442036003010110b1143c1c010715246d120800414105814803080710b003600c9007981d072001c0c4c1d1005103010070000d100d07280d00f03903d1450340c003903c2c1d5040c00e40007401d20080d075100c00300b0580103202d04400c0c1000403948070130080d4541405198ac0031300b4181c043c061702074203801900e54040c0d50f0001440f550150001c00d40703d20200c40070001424540b0121030500000c0e20001c2e540e0341c5480c0d203042024000c1d4001420340f101703801c01d9410705995009080c1036070403000c2e00000217650907a04000698000014040701003401c0400d5040c494903010601a00240e44504101210030000e06202152581e010100c40e22161040d21380d80090340c01d00b980c1e40c2d8800c0d0f5080c0c0300751040750009081544154071252080380f80502c020b9040e440d0030300880140c6009402 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 31406219 1250 31404969 31404973
    0x70503060102120c0a030e0109080c06090f0409060501030605060a1d0c13030311100209030c10050f04030b0115020c03060f15060403051b011d120c04020c070f06020c0603130203 78
    0x40f40c061001c6601404001c440b20000b004052a24907000b031082112000d25418440c014070305200c0c04d5004602200c41400c25585207848110100004007009040c40d0940e4100d45410120818400180c000b58140d0340240003d05c60f44d16284103100342c08071a0b00c102404012190700d00580c00c4240c8860b00d800503000b1058604191984581c0340000040d079004038085901c1d49000c0103018401d1160b41a9424400c104500340a81b890100c0d4441030b50541c9036101c3c6080e400709818650185080e03a150f00316145509481e01d4036440e0140300b06401b030040b10f001c0c142000c074050009100081c0d23003c1142c07029002d05001d40380d1400712485910007070041c0d4100400c158810040d1786490000d040198011801031880140864162900362920f02d49a8100708282980d136103020402205141015815160307040d803505c6440100d400c007456601a40d03032150000524840380303000004d0180640e00c084603038800e05640e0b18001d0f0703990002c800e03450303401c01001c0c0002581140403035441c2c02d441e400582 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 31407469 1250 31406219 31406233
    0x406080102031006110c090c090117091e0d200a020607030c020f030f0304060c0c090c030914010203101403030909040303150f03020a090c020a0f0609020126070503060102 75
    0x8805003aa0401c4801c410102c0100404000d01944660114642c00898002d000da42c510500820750095000380240c010780310000e41003003207901c644030160380b52040d002c0414090400c21700c50364032908000c6000010842040390207640c900c0100303880042200c161101000446150340142042021a48d080b03014010300000002680310a4001d2100c0e074441c0c0e46801c2c00000c1407041000c0118205495402a4840c050320001004000210303010317a0071700d0500001020091801742084001c541082143c5420421540704060f0075420121426116400158602c00c2c824405803c0340011585413200b107030240c50402503805440001c603268400a02901d1910200c40d010403d8050141d4048001990761400303c07154001805041d1301401c03090021141035480e6800003107074904940180074009a5600200040701d00030003552144a5000d40e007603031901c542d403c01c00024580700340c1c2a0b02042c070180f001621420040c03c000848108506585040d80b50202d0444090b0401043d10781944900c1c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 31408719 1250 31407469 31407479
    0x5060d0f05100501090c09170c0307030b0a050108030c06010b0904060b03040b041104200307021c080108120903030706090201021f0204050f0f0108070315030204110d0509070f06030504020406 84
    0x15884100740210010300c0c0814800d40c454084400580c00076940e2850045528801c2d640041210200c4c5d00d00c1c08000386096040c0300c1d4038100b1841107040d90345032161450000800955040c1d1511034a00780600f00401d0381c0e00c06405840344500c1d1006030085d00b10300c00500581081e0341c0a0125250080e01c0041e0480d1100f80716816544151010360303604040804000030844c826050b080f414009a4052140c98088100000c1064110100e902644004400a81c0e958402c010150164200401241c1700c83d5440e44003070101d2130b0a008038440b60040c400d643d0502e00241045500c00b1f000075000b036250038090349518000340502c4504038118001c001034540b41091740103807003c01c4245542c0040c1c1d500d14207410000e000d44803007072545c0202007550086003281c1c2c000075580e51003403039800c000c1940703100780042c40b500b8141604000c1d400b41c6840081c1940e16165006000540b6408408011a0316004035907903030707000144035010303240600000c01d0010900c44e8100c10782151003c0e0011401d56218 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 31409969 1250 31408719 31408733
    0xc03020a170705012007030809280b01080109030e0103020a1205070905031501030804030209090a0605041208070c080d1128090f050f04020315040e0714041a010305060d 74
    0x8803100c511109000716071081400f83c28440c3c90340004200400c3d401c040b6103250740ca8224081c0c08030180a104140000070301015051102905813002074248031b0081e81e89000006003502505020340c5c501d03682078008542c1c1101403180404043d096150b0603003c114040046001e5845001c000d4108044911030161200840c000c450040a40341c0358009000d040209041c80c0041801c1d4110021010304010804550070504950542c1d8040d038403072682e5075600305514680b4280324001868540340004010030b100800a107240189901e0b511851607444142d002c45040180c00d00240c03038200c0800081c80070390b80c00e40c030a02000404507219420402d044040d410f80e140040b000c00c051129400f10140368580c041d500401500c1182040308030117003000c2c041a8410440c47c01c0a0043c0d40c000f000c510354141a00c1e09041d0808000d0040c0200e00c02e03c03030415107802c9181b140d58031081c0200b87c074003007500d0103014181005140c05610407181880c88011000b4200c0603044581100702d4810310000300d001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 31411219 1250 31409969 31409993
    0x120c01090c0e09100b06070f0302150c030115211a0a08070306050106050316080402040902060304061506050909041e050d030e06060402090f01030911040612050c0a030506070c03020a 80
    0x410744800c81640740c090002d500701a01513590351200d9190600d001c8044d6240c5044d9401d1541008480044100500d001d0345004411120441984850401c01001003000b100650603a070f20000100c1600b50183c800b070f10100309003901c0781000c2c0110300140700c1810381079002c0c20341042d010b204082c4a148503008104100f6144c2c0004001c1e400c441d4040c81448294020319006241c0391514601c2c51404810134802c2010b4801e02e8002c0052035030100d010340d603684e0040001c3c0c640041c0706655a003414503015004002440c03008180c034000e034400060301805101030f03c030707941805420001342e0380c1c4696801c07a030114049042d4a1302c5010601d50300214504101007928440151800250418107054444c40c01800a100a114074010010b41c1020303122160328007901c00003800e02152815444c0341c01d01130782c0c1e00042c54542180c07070441c00027241c41070212000300190040c4180c6039809000014044000b4080c00050016800341c03012603d0103104003104d0a20f580288140c4032110003980e030f090307401c2107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 31412469 1250 31411219 31411229
    0x616080d0c0215070e010c06090302010b06040603020903060a020a0c081309050403050c0c090105010507120e03010f020403030e0f150703050c0115031a01060e01050703120212040311030408120c01090c 88
    0x1220114031a405150f8440301c1c1e40000241c2040c40b40341c03143c080001c020940c1820001c040d1900c0d8541001098001d401100b841540100440e4856454001c001c009400041d00d15100744101c1d808a540342d601c501c204c502c0841c1960360310a000f134864450318a01e84c00034500b80c1d8404801704c3d000501c2d5036580f080c5400355119a5410750ba41c0b0644c0300c250300d48240f20f000203100c2c02d608001082540c0c1c00c2011520715030740c00071100e0303450481000f058a20030a000390154155007892980070042c041c40c0d0050003500e101c1d4445803a0011f0744001d01c1801c100170b500f010b4014851082900ca0300442c4000782012911a14280d45802102a5490b003592a00740c40c288690000f50340034010031040a01d00204041c950b076a1049941c58600d008202205000e0340034140704001401e40141841840411020f594014040d51f03229a40b5090b0300040700c0031030303040e8001041031207048141c80d804004c039812202480b00500f059440c0e46c07008656680310018401166594400c0c04000889008008004107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 31413719 1250 31412469 31412473
    0x7021e01031b02191104090f120f020a03080a0b09070807020f01050105060d0207170408030d06080a030804060510030203010e030406300203060a030f0309090f090506010b0f070b0c0301050f0a050616080d0c02 91
    0x3e14134503100d1000c270103424464007805906c03917200e46d145900084407481d07540c041c5011030340c580745c4840110040030b140caa110b0704800340504028820703030000d14042c01a90780303500302d80d84804d4007148142281d900780500baa00c90020880103008900a401500401e40a604401140c9020304c200a415600540c081c400540010529411600407031060200030060a00a03000c46480c540d07005000c1d4000500052040b07540f20b02007500c2c00d031015810809542d01800030002ca03000c0900c0144c0c0c9400c01d00c00c0f940010611091907414a07020003104088019010120f10140c0a1800400185d000104656049260380c0000000b10f000180b010f00010301a0700c23400f8547c0c1c1064820f800380c990324068640c005091a00d80d40005800140c0541103c10b10b0300707003c1e00c07060650050b0b44207214006026007c3d045100c18807401260480056040310811602d400400740c4070424044188818130030154016400d1016002c00240b0141c0740c9010f51040007860702c0c10359109808012201c0040c003450040e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 31414969 1250 31413719 31413743
    0x3090c030709150605070b130c0510051b0705010807110a120302090114040b07260406021c03060b1210080706020a060509060606030610020307021e01031b0219110409 73
    0x140841d1080359000d85414506175103410110741303520005000103020021042e1181c043c034420700003403404240c00b03450018810500f120500c1c2e07000b0515041038941c400594031a000c0c51084a5001543c8401c07100181c403400780c580d0320000300b901d030071441110894541c023580c122680015141003600035503079004d407001030703c41000da0001040d002c100c00c80780d510010104001d04c0854000b406450303905d40d00c03503007241040400c81803124900804100c0112294004a00071030a5a008103031403424032501400d11400100c03c20084055850310303c10000d804104000b01c0c42d078035500031001588102c1c81c003070740c0118558070310b00e40c1d1900d48181c1c006070042e00142111301c10400d1500580f9089500c41000342954107211002400d0380c48042c00035803080c403c0ce02da40000600a1080d102c00c40e40080206188100700e00d094105038881c401198006403034425510700100c1c00c4901010801c01e03e134001c00714400182d0449840880201041c3c40882d40d00c40b140089580741d020380b11001d0711500d903000070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 31416219 1250 31414969 31414991
    0x714031008160f14030a08040305010504051002032403030910080105100311091009030b0109090b0a0c230705030f1803070e07030f0b030105040506090d0c02011403090c030709 77
    0x4208200000049401000b1020810038004000366429a044903034000b0b1002481c6000920344000d050000b005813001140000c2480410350259204074098010744000000300d91b405002c9100c101d80503007818040000091010101002144031410040d0884c2e1620108100081e5000010100d050025a6080c01031004c0d003002c001140d0744080c0e500307003170105419982604403035000c0e03101c00078014096110b4406110f131143c50b03c10300460300405884030958490b040740010780382404040c2e031070b9214100030540201030780c449c0f070b40d0a00e0282d0300c41c80200540c080c03014070392101c03048007840c8007028400a00805d4060005140c0140805462540d42084c180411500c940c0340e01600d00c03a82080d00704003c10b41c0050410341e40302c0f400f4900001d40c5a00d000342c0c800200389802400d40c156180c04208030800c100028858010f00c3c0031802c03203100004180c0d0031102c4a40201f0024000740c02c5280030008054801e0185400c070785440c0c1965003080d81000440c1c038005040d84140c910640311480000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 31417469 1250 31416219 31416223
    0x6010509061810020a05150709050607030504030c050d050606010e0102010b030f010605131104090b0a0308070303051005060c030a032307050301180c0c020d0204090804090e010501050a0311090714031008 89
    0xd4800204d00140001c5079140c0c07100d50311110030000c1c0084800d000d10020f01c0b0079125401c1003010304070040150ba2681c4490500411680090008903120102c41e000800c482c90104004140c0c01d91100c024840c55640c1c0c0011a5016030804406d81550340f6140c60800d0341c0c1d002e10940c14408580e00c00082d100b40b0702005c01c103003c803070b0b4004200098070301f402c56610618204200da0030b8070603415012544500d01c7c00440e201c92a940c0c1b0103080500081103a030209689900114001c0c25450581c641032a150f004204142c41010030500c4643d02c00c002c24003146003e5080740111001040c00044003925100342d01400392022510032002803800401030010305a8461045480d5000900802500d0f80502001d00400c5080b10060f2042d050904d40c10304544d9150881d52042d030b44500025107030340c1c0d6034151501030228020401419402d01d8000304883c20241a0003007260b03003002c03c4180c11928036080c41803c001c003a08030810007008201d04d0607034006400056018042040c8402005490000124 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 31418719 1250 31417469 31417489
    0xa0201030b150306091e040b06090a06050604090f0e060a09050610030507060c02041b03051008010509060a0209150304030e0f041503080c1e01060306050105100504030803060105090618 81
    0x1902c00c080c0c8003103040c05103402c4070607a0352183c419540e6010750307268140051043d440d16001d03901e2103001c40c0c007004100311404900c5405280c0651740c030040f945418540e88180c81060088580182083c80208400d0645420041403174035554800608110040300e0142410812680d1602d129124000d0808200c0c0c1042881e43c011035219207070038904c0c11f41c0e842940380c100510801c002c129843c40346200b5591180d20466594a2465041080d500268005806003000b141c03c160000d0042c0e6000070000010f00500d840303464030b070010b402907070364180c1410025081030b42441c1e003100700070050300162861040194082c034020349038403a1703141c0003404000c0100407008025000324102a0004003410801c0940801d0b07941c01060316071107020403140030380341840d4484401c0034456034060070182c620040d402a41174901510307051020b40c0c1c0351070520482c5907480c0307002c0300080c504200400201f400c40c0090345e0091f00c145070035450070342c04100103030240c2c0000d4121316070900114030f171883c14640b0920030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 31419969 1250 31418719 31418741
    0x3090f061e09061b06040302060601031401150e060307020601030c090603020603040f03020c04091524060509010e0d06020c150105060706051807030f051002091012060f080a020103 79
    0x2440c00510040703048075401c0321009144041c001140c0a0341a54802d001e0311000d04400c21401a5915041c96282d039a4009a03019400350244c039011071402c0d4468050440481c55a9101c003105034a8403d4bc85803090f6161904d40402141c145540100d50314100110700586040e402007546504500f080c036405103a075800b4602e001d1030f04c5001c10040e22403200340d030743c4507401280804004c0000d00b0300303a04128154000940c0507190800110411003030802c1c154005c443d1000070840c1500c0a1018426100403161b540b4a0b82001c042c00c000d100c0c0f081000301201340040c540003002c0c1c0002c0c0c0103c0e0550a034030008461240d00860343e0b0041d040200040d500794210480b03982895403401010400350722440d94013030101505c9100003031f1510034002050310000054022101075682e00d080c80210340707400c1c840445050003004103450340c2d110280283d649100008100c4100d6000c03041c402d540c12544542d01d00103440c1c070f444000070540d0049410788018060b84010300649511880014112009214a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 31421219 1250 31419969 31419979
    0x9010f0f080a0c12060f02030a06030516140918030a09030302010c0c030e060d090503030f0f01080c0901150e0a030305130e011208070528030e030a03020a110f1203090f 74
    0x3000f00d00300d10780f000121101d821003900b13450b0207424480080d20710031128076220390000040c041030f400698494400c507802503065440303803c030290b000131003c9590301c2440146403071050015294600325804a030018124412960940e00c96413045013103420000c030b01000304a59860410078581c081c09050011a000d24003c00c40701d00a41c0d000d0402012401414050103002c80c003030500202d180c0c04420400d4104046a48924020700b400c10401030480741c08841081c1d150001440c4000015900c140d00001021809140c0c2054000300d0801225105402008012072441f202525640f0b058000382d80a660b40b1950b54201c68094404210180d000c1201c03400c00100410540c828008114000e6901184240e81d41655080292520321580011031004019070754174022564501c65200401d8480e4036a003500003403501c20181c4401480b000600541c10180012002a101d4107140c4402c81c001040446611a0b01003c924a6884801018101d90000802c1e180c686444006903258075800c0351 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 31422469 1250 31421219 31421233
    0x70c12020a051e010e0a050a03030b180402010c060b09190606090b0904020a0302040308041d060603070203070f0c0b0c0106080c0301020309030a080a0227010807030203070f1d09010f0f08 82
    0x1d02d4559502e01001d1822607012054440d0040701d000390055140c2d603100d0800c54580f084c3ca0b052854a5401040701140460300e00085008242001080301c07a412038403178407000c2ca503070715600103643e004c8100100f180c01e0b039621542c5505542d1000d0b88c0c00e000755007803031404070f110010b070313200c1c400b00d90301901f040341070022400003001104806811034010302c13404e0300e01503124590910b041d4040c0c0a00e400080c100c50000c500850060918002a0452100c040805955848640500915120646204d00181c100f005901c1c0415895592402500d21403501d03520010340d200c200c005245c10002e0384243c0b40e51503410412009804215075288520f0403002186103040c2501641d642e40f2030545d16400707028007100040d03801c50719681552f0700c82040b2403008104240030200c04110840e00405603000c80d03684008221542e11070700c282c030f01c00d9849450b07050441440050a841007048000781002481c520b100c010510385454407c94020300310410000344050424201c03580051a076001100b8a0340081 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 31423719 1250 31422469 31422473
    0x50705090a0303050706020403080318160303090501110a060f0902090603011103130602190e1008040209150312070c1d040203031206120106031101021b030709180605070c12020a 78
    0x40c221002c0301d81c1030402ca90345220902d03005001c0d00543e48003800f000c5021003004030140203120008190072381c6600b6112181e9138607441c00b0042e192800090005240c510090015501800a9038640d000f60300440b20503c5030b40e904c0c04250f40c001c00e45005602d8580c030002c003c608165140e81e0700120203c00038004640b0440341303640306000062000f900d0340d0880e42d0b200244665a41101c0d11001d110300303610211546050041c10458004c0d0085006001484040141e28804da0705140620b80c0208020786c1030300d41c2c03103404141d06940301c01e0036858010303c03000d006880031180040807000d00c6080304000a920b401d01030500c5003205802444400c414004210040e40d000c01206c120740705030458010581c030742c003000c0b0781100e124401012071986041300c04800e204068421451540d426821a030029030380a0708420f41d96802d0010325011350180505100d0300b51181c00089203440c40c0110070320701500986500d010b40d507090780c2d104003041100c80001d00744510f40550b907440c60018001043c1710360380350b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 31424969 1250 31423719 31423729
    0x90e06060a0521071e0305060a0501030f0e0a110907021b0d110621010b0403050c04090203031204080307020606041b0f090902070c0807050d05060406020a1b060207020405070509 78
    0x70031444100200081c11281c21041c1c50580d042c0080d03601644403040c030b083e000251061502228241c110b014902d044003a0b04e10030f020300e5108440c05804071003d1841c00b00103402812104114a9200e501e500d00e00c2e4400c5001c0108500582c0504103a424045e41041032180440c00030b8201c5013150441d048401d4400800f0300c2c86401c0c5403040e51801c13a03100c854108001c00703803d4010800e500c20400114414401e101c00d202c20800c0d44d0302c044500082c1da880d9101c40803407040d4400240607400c87c0258078400c1c541940084603141c00681030340d00d86070074400d1008101c0310482d07080344c49031400b10500c01c8041d030400a45a0226040e9010403125421700740c40070740319280c40d01c50070800520903542c90841e0721603c00c1c1e80050024007420f54486001e840d01424010450080100307500c12200001068a400e100c1c9201040d088000b90102c0e440c1e544802d4080c0d400300e0300d00c03414440340401c01e030001c001000404071a203006440041e10b8054610400c0295070020380300908000c0305001002e40c035514 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 31426219 1250 31424969 31424977
    0x3090c08030c0601030b0402040225020f0108060f041e0606050c0705030109030e0603040606030602161407050d080f04050604060305070320030a090f02030307032007080717030d060306060501090e0606 88
    0x6446c082d1039aa803480098013920906585000007500b80032000410540d101c00400014800c0f030351242d401c0041401150148412034000707070b2140503881c56000606240e0310120300411040100040d8901024540c4262540c661140001540000b006080c10206000032005090200c009004c40c082540700208920319246e07010b44910320010201d0108541ca500c2807006590050082d900c40c0308005c1502e54509550500342c0e0744d09a406000403040c80b001c03034600140e9100074002c0f11603880b991146d0403035400a0130700000c400c80810002c15140e685001500040900b0b036400310701440d01602c000c05540c000142c1505c118410055500d041d10301c041600e034001e0451400103502c5919041500014821050103505804001000c4041c580d11100d840400d40e00c0701c0c807220040178403585e40d40d035482607441280e2050308004414011a44a0000b045503030f01d14030200ea08100d0107255240c1224141c1e40111815035072000300304510f50b080300e005002807a03040a2000286085000300d203003441 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 31427469 1250 31426219 31426223
    0xf090d050a1d0406090b040c1e0c02180103050d09050409021f030908180a0501020a0c120c090c030b0a05060a02030d09020103090c1811031e07020106080d03090c08030c060103 77
    0x30322074007030000c10380320000340c2d00d100410600030117550307400c0b9000a04125035850b0007030742001004a2554011500c60b424400d5911a4442c80f12400c03038115013985070240300700e0b402000c5803408151582c08003000350196014601074900711550b1140505051100c0c0d002d0742c0294240a4500c0140c0e80340300d55600180b100c10786c62618a20102c801310300500c0c0b46000103151040201c6c264011007490303032804040070b078241c40c04140b580c1c480d001640e031090034601c01448a91020014440c024485034254102d40c440e80c1700e0407813140c48103001d40c00d5900c1402001c002a6980803110b00ba450401910402060182c0e070051800c5500342c3c0c000d44911c125004500d00c60745424591045911030361001c0c812541010703142c01e03040d4844a0030026100c04810360800d03039041c0011310103200d032a403045a01032004010038149041403143c146980c40030003440001995070f1050000f49450301032140100341c080a65000030050414600305882d0000b907000304445034414008410680400503038241965 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 31428719 1250 31427469 31427477
    0x30908190207270509010b1327050c0301110c070b0f09031f0b010801051008090c0301020301080c0102150121050c060a0f110a120e0103020405040903080f090d050a 72
    0x80c80085080c0c0c500182035228070240781080c400701d0001d0503c0e50103222003400d005010b01c15a150f5007030840c03e9400c42c0f07105541c014a41c090444c0c81c50015440201c140703005d0761950408003094031880c2e4208540360015602900141e001da00589802c4c440c0f200105146605030342004a0103051079512000c50140008014001800c68520302241c02998040c1100800300d07042c075040d41c41e0585a0030105201400c0103030074044031440c80d6000707a91040c10b0315809800c0030001005400c0403518200e0181c155141030080b10010305583d1001c0c0000c50103000360307100070301940200000091402c1820403010000550303900041c81644c0740b0034002c01c2d01070700e4088009403130000c41c18a1420b00d000001190f902c2800000c00070010f40c2c10610854208a40351501140380801e5000071f40c0f6448050001003007040d000640122050017540b05507202507040c5001070400b902c580c041411100400740a60104021008200300402800b1803250b0001d014005440c0740c1e8074612020b003c0f401a010070b00144 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 31429969 1250 31428719 31428757
    0x20303060d051507050c0d03020f0906030402010302070b01030b0115081009051b03100e0702010902030c09070c02030307050109170a0c0305090402070b0a090c0b0a02030301120f12030c080106030908 87
    0x3000c0304001031440e0b070070504050503d605120102034143d90111000c0320303050003618000d107003a50191003581c2c6003000b070f403500a15003a0701d64100106980000c1080381455400c1c0711150220f0101f01c0d89601951142c6c0100c1d00b82d504104002c02c429989481407002c10a48400b0002411903c0f414070080f110800b4010a450b2a000315207041088a01000b51400102008224064000c0000c202c100e5034024510022512001422802d803020386002035050b9008001c9602c80f410700401442d840801c2e40380c88e0b5102c5100b60300090035030f44403c40075100e981d116100c49080c06280c3c03114030b615240302d204080c036010143e00e0146c42107011030006018800c001c201c0312400d40700c90b01200c906030761090170200c8918004004c03100806c1c031003509880b58504540082072030210501243e0300d96600f50021800c0d03a1070104400ca141c610b1440840748600a19900b500280d40700300449161183c071380300410880445540240605070582c450310805042c440480b01144456044400301c6d0a8801e070f01e401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 31431219 1250 31429969 31429973
    0x90902010302040512010b01082d07021c0504080c0a0305151e0403020d0807030623060d0509031b0a120c06090c080f12030c031303110d120e0d020303060d 68
    0x9001e25131103580c10940d0703042000c0d40d00e08103600514680d9802d1702ca2001390313144c03012041c51156141e00f030010b03811050120043c540000103605a488249841240c421001080c06400315111800c071f010003150011500380420f170400d0040030101c2c0d0741070743d00200c410319584030250780741504040400000d4002c00454090046002144035041c2004850245403c180c43d0095550031410400800140b010001c101160b120f40510000c80311104d17680046e20118901c2c3d02035101400d49034943c80901000340f00c00040403400b589200b090028061500c8a2110102894943c8a1800d01a15800029041c400103e24409190926202e8641011000d1407847c160700242121103001c2c04444200341c001401c800000b40034044804004241c8181d0641c04005801d030340015280c10716540001d00c00100480703469203581071554024a4244000000c0c846c1c3c050070304900e80491400034014007110151400280641c00d111400c4500405200520140007500c0380000b8000c644544241c0c58000f007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 31432469 1250 31431219 31431221
    0x20703170405240108010f0e07170a050601090c090815040b06060c10050105030c06120103110112050703051005030a0c090b0402090a0b0c0601150801050904140a050f0c0402040b040909020103 84
    0x164800540000522204820303c50100680092107100d8540d07017008107042c02003065004071a04540c5242c0102001802c040f00c3c0380c480e0303980d038100d241d030380c40360b102e5a03008a00d04002940c000c1483d030200180c0c080e06800e000b0400441a00035002c00d6100070b0140c4022006011131907441500040300541c141c07500c8000030154800d200b0148168403410700f0b12000b0b03d03015030009040352000c404441d11038003d02c0c00e115050180a1240b1803c81c40301c40100b001c1755814500c5020007805244c0008200c603803009800844a0030f0f142c900004e0f0b940c204201e2a08240a015070151004500420030089150b54292024605010f0810680c1e1141041517642d102c540644e000f07924000e186030105603c4604020b669040400702854910400e07000048074544440000c810480c07680c0c900c44940e00703003c148040600c024108403003041409140c83e075680c0c2e00307001206030b0500c500c010b0000d8241c81034480b80307003450b01000684214810401005500100c0301114101c455003075010410011600041e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 31433719 1250 31432469 31432483
    0x806060405060a08010f09090f020603070c02090a0b01080f0411040c090f0308070c1703030106050309030412080702010908010b010e0d050c090c03011d060904030c051c020f010609020703170405 85
    0x641c2000300880c003044101c4d004643c40381a0350182c000031a40ba69140002000c2c0d40701e142029042031945070f4840d0150800500445e8001440e00304403541380b8a503808124028012200301c0e054030b560740600443e030369002010540114070085515054105922091085d10020b01020320681c0d5808803481d040b40101010401040c00e504440e02c829601d00b000c554680c002c083c11a11a202940c01095130484181070781106482203000f10f00b1070b07091500035600c540c0b001c1e20005851006001c00281c05450865940d0315a11440c1070b20703103da00c0340c40090b000c0503032508000e4569040412031074075641d01c0180340c80c01c1c480480700101d50303900707904002d404c048040c4402c5030410b0b03a050400c800d0b803d01703000a40c100c501020f164505140c400d051100d42000c11307206207502a00440104000c248200c029004007400341c0181c0d104441d45000340054055110304c0900036820082c82050038500030321070704000b0441020254a0050641c4c0c000f4007405006c252820401401004038040c450100000703 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 31434969 1250 31433719 31433729
    0x70c090b010e0316050112020f030402010c150207060c08180d0c0f0c080303041e020603060111011515020c010201090c03020402030907151805010f0c06020a020307150f050c040f0608060604 83
    0x501c101c2400504c4407031000c5001c0c06200d002c0348103400c10041c2c0804c1c510854040b2a0385c1225103003551207a90046070b16684010b012384100140901c0a101c50f5024801824040c2c85420b001409051705c20010f444200000e0411182503145141518882404101c1c0130b156140ca00c5d151001c2e00380f526000301802c0e03251002400d000038107540414413410010095020318001d41d0601001040c011414469003800c901c0290407920500100704194011307090b14a00080c043c00100e8190103411700484246616408035a0b102009248594040e40502549150890130b100030b011045850f107074100158980d220003800b50782d00200040c4a04800d01650010304819040c61550084118004042c9117414505401d8400b40c0807000907258003d21440d91803007003d8451b400324000320307210300c0000c1d00502801e5096000c20051940055016143e04030800880040007400310340c40c03000c0030200c4800400010010354204024023084c064103644c00c040b1b502074070b0040c1d513503600e000110f00d1a001e40e03402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 31436219 1250 31434969 31434973
    0x915040f0e0c04080318010909150512070b1611030a0302030705060c0306030a150e0316061406090f06010c0b01030609150c0e01030b04020421050105010b070c090b010e03 75
    0x86084040d51410004889448820141d01d440307900b901c480600c9544210180303036108114030040a0307515094a50b024805060100e01d8903a1000328900b5505203481d4802c07095403640c8103010901e0804104107030b00364600d0081c145a0f0070480c01e440305100300b200b03194003406c03103803007000800211102c2100c040304060240d80310700310103207400303583da4000d0b81c803c981c80c0c0101c3d00000c49200b070300e506a902c02e1170002c004180c4402e482c0c881e600b0f0143c8a4004020310341d100c40c41c1c8103955200300006e0066200717108200d803262505044c00c0c000c8442c06c02d95049051419010301000744c0ea1050307081c0e00081c4a44000c2200c1d241c141c0181d520480404d07000703180e01550f070300002c107200d460f600c90030615005001d0511030009000020048481d14a500f10102c3c6101d100d82c02154440c0c1c1c80780703680e031401a01c01413400e6143c88003009550103010a4a50310f19031101107004010080c0900d500400c00026502e0401c034680c1c0d80c8100544803401046500caa40700c0d581c540903841030036200000800541 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 31437469 1250 31436219 31436227
    0x708160e0c16030c05010f02130308090a0b04150318081b0c040c0e0f0306060303030c070c0801020c07050102070e0705030609040302030d050c19171609080f07140108090706050915 79
    0x603001d4000d0044103000e4a943d447c0c001c5440c2103210300d0080f2011040382502551400d402c55590000035002420000d070000c1c5d0b2050003180b0000b041c00180f000e806940802c580310502d1000c0182645d400190344806250301540c82e01c0006c5180023500d58130729010241003145050080c5c8140f81030010081e26a0081c10460203440094201c8a03035008108107881c22040050803206044e6102070554443d40c0685c003c0001400001048018125088c030880c06006801da0701c60045003a80c00401007441c3c1500700c01420400380d0380400c8440c00401c184a8107030450300d801c0f04080c020380030040200313024014040014042520034421900c03503e031814810480303410245410340040e00030491186400c105189410f41b01801180c40035480c4d241c11035052101c0c0d6805148040c4148580c1c00311013403212101e408900482c0c00d2181d5090503004a00070442d80c1d01c0c0199046607140000e041c0303814403040c8803d018038000041482025540789040c410350f80c3e102040856154180c240e860191004c001c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 31438719 1250 31437469 31437473
    0x50709020c1603030504170607080402040f150b030a051e0403050706021c0b0a080703050c04020a020a0b010b0304120c030e190b0403051b061201061b06020304030e030708160e0c16 79
    0x171016200781d03441404e81c141c48081361040c0e42d03520401170740e5110104281100003001442e01d40c00c00400c0034a0010042104803050320b207416000456005000784150120801c80c140c00207100d2640c6c0542a54040b03212840d003c01141222200580301508000d0000b403120203015181c0c046034845034080d51031031880480d1903038040081c0449681030740f0520040d80009554000012001d05994000000d48648112031003080029449140c8810560107040300307240200b0104002c031402000c5220342e1035941d02d46440c0807400741e181c582d001401d000720071f0303821004254405241c0c083c081c030035520420640c1055407100610381140d84801074541700058040204980414001a0450b0344041403121080f40c2d070400c00c2d00c1c011564036040d4018600010070006100d20500d0b0311224000c2ea100d0f101a4068940174240c0e441210240c020071a100700865039814200710800082121801501d4084510000b20100d0b801502ca0f610544282c140400c0b6103441c983d0445d00300d84183d54111840c090b142c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 31439969 1250 31438719 31438727
    0x6180c0901091505041202030f010509030310090504030e010f0e03010f020901020f010504020f100908060a0b0906030c10050d06180506180606090d03020f1b0a06020703050709020c160303 82
    0x82020140015001c110004003c5505645a41e00310541d460b000d05160814150b4000da034080c031310581e8103108011444050710402e2060320b00541420010b1580c0c3d185c00004200e1552070b0b5403042e04214070748410000483c2d8003612601007100d007403078512401d00d603010045810791080c0142caa0306501c0c1c010501112909070b802445c1c01c00d42a020341d812054160031003070890360200c2e4041e401c01010034504140d442d06403c03c1d1303400c05442c14011325032a00c4005140c0350502c00c40386c130429507651703240f211aa0b1030000000c903030040080f0024000d400f0b018020484001c8100c0c10070050090200b40c0510946450300507001070701001d42e001c001c000110b03041e4030141c901918580c3c0204925050035003003010078114644500d00141013249021101000e03c24080f040e07503410b03800c5000e503224900e03084031b0a0200c04a2002440b1940360f04035480c004101e44007815034088000e65100c0c1c5030400c0000d9020031a0021925110001a120043d101906040900829100c5010001c441001c001c250708 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 31441219 1250 31439969 31439977
    0xe0a05010c0504062007050d0302070807032907020c120a0b04050102031b0301030515040201030609090b090613031e05040b040305010f0c0528030e01020a0507061104050d080306180c 80
    0x6507036a85c160b9a80d42131903090034050300050760700c640180d01d0621450034502c1c01d090700e01c0c1c0b09104941245580e480c0f00c42c00e29030326400c00c071451907040101800103900004c4500540041c0b10a0087c1400d0803000a9901d59490b000240a0342d0101800804000144003c10300c0c26000314518005142624010f4000c0d0700c11100d1840c0c1c41c0d08400c030034407040e0010040e02d060741ea00c070009020340c0d10034601100f03058800400807410103407940700c0410020090b001d0414030f0b600c9899034084a09140c401c01d41408401440b031391032010030451280210341d01001100d0b1501246840414400d42d4040482d0030b03200b01d0700074510014000400200300003055001d5154040c500c03000f0070038000015405c64461056811881c4241440ca69603c24101e40341ca0101007600c1c0317814000b4000f542d48551509980100201e032010840108482d014070040d800780c2d5040050106410389064200f40008841c08140f0380094510f075404400504a0703140c1b00190364a030891448561070601c0d01a4482c006644 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 31442469 1250 31441219 31441229
    0x906070b061305060310020c03250203010b190e0a0e010507020723090412030b0a06020c15040803040e04030203091801050f01090602030d0b04061206090b090a0201080601030e0a05010c0504 83
    0x72140105031601043c410a801484010060800c16090100700400394004881003c000e01080001084171498440c2240c1140110009000604000e0040600b180c55541e0f8031409401c0c0b106094000b0784016070843d00380c82c01032078804015219100c0080c01090903100d804400d61800090244081d000148003081b19800200c0340d56030203050390301e0081d48003007000c400d070070101e00800315000854640b10311940f809207260001304025a40009002c07110107501000151300800780321780c0b00b401c1007008418110320098203145003920301240190340740714a100d929241d1101e00b021804152080c0100c4042ca48002c0120a62107441050b10045810a12803280704040055801c0d880c0e50050001b20308031841900518113111540c51002c015000401c131280d8403a07500d020100b8140001c6520344040c0b03024800005400196290640680c000034000644541c04140039200503a482442d607a400304013881c000c241d2541030340c0c2a5180900c01c01c0000c0013542040d1b030510406610a020740300310b138 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 31443719 1250 31442469 31442479
    0xe07080105091e040308130f060f14040f110105040924050111070e0601020a020d0515010b07080322060f0e1204050901030f170301060e010306060e03030d0b04020906070b06 76
    0x145602d00c450f2a90303181c5201c0e105074040410001004a800707660701550218205180100d074501c02d503602c1c08a0b10360b000c422201e01e0394809d44240404044d1080c84005800321914428508042d15900b100c0080c1c28001410540340060001d5207910403c20341c0c0c001d10300d003002804540560344900100120701d0b01e0740c0140c04400c60b00094158030039442c1002041c400005050310a007041e001340c0c10741c88020602030540c030801d1140001a1074655400780454047c0015050210a416040301c803a030042e0710800c0702c1d807418003c41c0c1c081413403442101c1d0444241d46204561900460b142c20384203647c400041e051034030304221100503503240e4101c41d1050703400c88141d8144000121049c2e005001c1c40c05000c3e0001498001840000d9138045021842402030113070020403e0125000780169000340c1215000503085844004030303507003500032074010707003e2818483d45982d000c00100e50b403402612240c20341070361210381100d40340d11658100d6820030000382c0500c0e40c4400382d003040c0000302c0c420381d5402c4c014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 31444969 1250 31443719 31443721
    0x30504081b0112050601030e030c03030609061002030d050a0603060212090706030218060309190c06080c072001030e1209011211041e0503010c090302040f0606020303070c05070e0708010509 83
    0x8450440600c05480c8140c440350551407280e0010300013030000400680c1895501d12401c1801c4e9020000740801c0c00018000355071f0303460000103001c1e2106000d01514007d1107044c0c036203c080c03500803059903841a540c04000030a076490b1007012000e44995031010301458800600c0c1c4545140301000c840c0b184d0710020446141d20350340e100c128100e120384443c0b00141d01818955540524008004540107154001181d04040780700b44c1031140f40854802c11203109510b120104125500070f06021760201c3e8030605241842e481d07807644200010b0200e80c0c1410000f0070383d800152a0f000398030000d040f91242c0308480d4803090300181c000841c2e014000c1d25020801400d83d12102c02c880d40103900c001d8043c4002c0500340b034031b000e82108100e2822050040f0b200150003011407a500c09106200c07940d003c90303540c618a14514014042180c0754041c40f0242d280c24000c0510410703400008603038200303d951400f10b5581100d070408505144541d04405910a01e040031302ca0095801a2502d050b40c0301181c0024017 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 31446219 1250 31444969 31444993
    0x321020105060102061611010f020f03040b0a0e0309010806060d0e010501081621020d06020706050a050c070f0210090f08060105010f090602250302030a05010509010e070b0d02071a0403050408 84
    0x2d40c07001200d011842c5440c0d1b0940706d0b109403281c88000c1c0300c902080004104010402101c40698200d85103c07207107854003004201c107014600140540003480d40b04100036074554003000685901c1103414060600c81c5e05004181e5075141d1404840c0324078003940b410452079440101c0300e406010280b1541f11544a44082c0030240e1190303404c264115034200d40c505c0e03c20b8034071001d000655400c444d400d90744218400e040f40045403180c0010314080c7d204503c001510701d0102585011504041d190000c840d42c2071100100080c03651034071418054044a4101031415610022074121030b9a803c030700c0318a104e0711030029010400242441c16220301340c030742c00c003007040b03104c01102c1051042c0300743c000607440301c4803c034600c45c0e120840603e00c3d01cbc8020078081103501d03500801d141c4103007101c00311100da42d694100040c2c3c001c00e2151200c03280760715002e000200e00d0103400d42c0ea58000d100710301407500e07800170f140030400c8005010b60044c4820290080414581801d001d1318907086485400d095014410508031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 31447469 1250 31446219 31446223
    0x20a0c051615050a0801170708030c10110712030b04180f020901050d080301090207050a02060a0c0b06030304230402040302191811070f03020a150f0b061e030a060321020105060102 79
    0x103d059442d921045d86030310b84010f0b564a0f42c802d01c0d0744603460040c81c41c0451800700500003001080150001800404541d00c02541210101d11808807414001c0c40304100088540b40310861041c1d00b86400f203842807101000400802850a4070312101643c0180d001c2007011480c8010705840c002c86007035410b40e03641c0c01403007405180c809005207405c80400c01030012118179400390401c2406403044405c806020742c0410200d6105010001c003080054501404100710000c0c9586e1220313090b0041d508191902103820820340b100311140341c100d1034200d00024692502e6042d203000756001001c0054034610744102220300700d1140212303184e09081c048105191210b2740640c02c07800c000103c0340c0b03142110f182c54808042c0d00c03601046085020b0141c8030f02c08a41000900801446d49000018140750405002130490340b6040b4400d0244900744004051110440d10b1010300090703080001d036a0390b60704801b40c00100415007004011f1070841c9103500c10500d040703400c4242c80b40550001c201c80c0d210100103903 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 31448719 1250 31447469 31447477
    0x91f0b0102030403170409090803010e0907060e0f010c0510020417010603020102061810050a0506040f1401060c05030f0a020102030a0e0118080c0106080709230403050706020a0c05161505 82
    0xd01690003044108009015051101e01302800d0204450030203031141e080205030344448000361030005c400b00040c44028008218070b85c0109015000701111780c94043c001e0f03c20031903211202d129000316007030b15003507074002c10807400301580c040243c0f10308110742c45410700290094068540c6071650540c24692004051003040c050701c0d016001409c1d01d07a255400100f000814003a1000b42d400340014502c0c5680290003103501400e44540c0200701d5203050030500003100c1e45420b00c1c10b1554100b059080c1075550000d0300c01c0c10f60790b10386019070000c01642000707032541c0b1500030300c440c81c3c0308001608504181c0c19400b95011f106031220500880703d00a109a081e541d844410048190712000042c0c006040302000340b103807a01c0400042003450b034591086040400d680c0c0302802064542445010b120140350032180091400540340c80213050640740281300380100800188203035800603a000b0820700a101c002c0810740c0c05000c941c803048543c1d0852550306010b20a07000840e030040c113400d594030f004005136 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 31449969 1250 31448719 31448741
    0x1050f010b0f03041a090f100c05030613020405030d050405040b0402030106020d0e030708070e0603010c0206011211010c0206030415060812160609050304060f27030201030e0c09091f 80
    0x15604004240348100101e62015108607496a103c07800341084160b0000e8003407140c0a00c0f0050071498850040c1c640c20440045600c8c18480c0c80c205204201503000b506480d0815010b03560f141c0290025000b0000910550300810780c5032081d0820303070020035440402001030700d00c20768051001001c4a000e20080e0700083c000c003005a0070880ea009640741c03003261a010552001800c8039150399980220fa4240081e5400c4002034100d000300304911070409001301c3d500308140c4d2009141c00c1d1b1500f5040344808200034802032148600c030310250380580c417601c0c1c8554101e800030f016a95a083c146071498100c00400c512043c1c143c181080050921008980e5001888021003072614090841990000b01c0b40102c6e4100c561a40e0384200a02103803082020300082c10f000d84468101f43c04c0284041d141182400c500010743d000204000b0500400ba070b8030500b1240d0a0038085400303c0300281039800e260500c4449500202c031401049090100020f10b030170368120031480c041d464100d0301c2241040d5803c03214a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 31451219 1250 31449969 31449989
    0x20c040b0a05040f060513200702100f03061a030610020106030b060103090c08011b170103050703020111011b02100b01020105010b0909130b0a0c0e0105160b0c0702031002070501050f01 81
    0x1c01c0103141080e4010081d4068011800102c003130700c1e40005088411f841d0303503201d1030750394032450100349910181c1c0c04010591042050350520b840c690014a210040c0d803101800c00482c01090400e0600a402150192810904022264a841c2038404084e00b040399400d1140700e0911600790000e00612608059941010360441c0c15038134071005501504100c4001c46000700510381c0011001020303c00c1e00b9091039920200847e140d01540024a000c100010390303808001494010000904000b459500300d07030782030074098264040c85151500400032072000d2050f0542c40705c1020043c950205451501d2000c9000801106407000012800c980e02409481001d41080209040301e16001b4603c0340c0c41140c0201c0f144403030780e82c3d035608401090241c4403c80300a89500106664a41000001e2120310080c0ba0544c140040340402850000903190060310304402e01c40441c0e020580c05048400309900502190b400c0f01e000c543c00c50007544808402e4482d54a0a0b0118911454500c4514100da240d460 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 31452469 1250 31451219 31451239
    0x103020a02060a051009110d140915040c030209041203050c0405090a0b030304030c140a0e060609010f03180b010305010615140a050409060b030906010e0c1b120c0d020c040b 76
    0x10140c801860042c0005401c0341510070006070f0420f06020f50442d00b2200501c1c180c40303140010910003540d842d5141c1c0901c038274641d010040032940c002081c04081000b4201291140c640d818032075044406500b002c1d4012041600708024899403040310300e10310b681c56904002c01d50742c80034000301502543c004c07103030700c00844404038142000e2a0460180b4100040039645041da40396a03808407945503600048011250307852902d0146040507420000b00380d5010150340741d1038204000349040c8180031031103050042c0c19001d101c02a1180d03000300010300e0300242c594036110007406e010403002d0307003448210b5942d03003409804154044040e20390303c14161300340c544140e03c0e000c84a10f181150040c407140b9082020a210004440c1000d0041a00a0400310107181d680d007004a8441e0400724160085610181c01c0030502c5080d0000030110340001244603034282d444400c40301d089041c51201c40e50900100d82c08030382c2500362400420300500601540e0200d03410402c4440c00e10047e207007042512a48015560 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 31453719 1250 31452469 31452481
    0xf190308060a0e250315030803090a080a030e010f0e061308090411070605060108042f0916020f1515040b0d050c03070504020301120305090d080406020610050103020a0206 75
    0x5500d00c1e00311400814000c00d15444003500b0148600c101c0343c4480521134001c02c0c0e20620714040602035181c4c0340f0f14080c0701c110786c24104000710403900d02c4020700780807000000844204013800b0743c41900381d02496140c1c0d07d02d69164010086c012000420365a9403a00c030301203041140c00d104110031191101c002d02169030b038803121072484c0a040002601c0c00b0f241008081c029548901ca40a406061030401903100e110b00d05080c000c68a00a01c5981484481c20a20011074140c0300c018081d008000e54002c08501480848400c5019510f4019000080e10061050180d0300d1504209880c2c3c3c503600300d41425007044051969020300700da2541c4a41c2c0180b0108425030360b8203001c4d4140c03610260000c21070740d080d0400702e5001840100207640c107400c440090f480b03601e0288083c0004050445007581035504061451a5031202c10038000c3c01c0c410700149000d059111032901240d07840d000720030a501c440e0b42c1d0001030b4032904216000c052420080d007000c40c5c00d40c020310945604e611140e000b402c1660315030b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 31454969 1250 31453719 31453727
    0xf05100e07020f07030b04030f05090d1502120a0608010c142508070b0a051503030d0f1d070e010902030f06010c031101020c0f0d02010b0607060b060702060d09050f1903 74
    0x58000c4085000c1e81c441500c41c40010804c407001180320f8804004540380030304008041003002031500301004000c20114000380c1e101c1d500c8100b1030350090002d1880840044c8040000c0c0b180345a00b060041c0b40c0c00800a181000d90711160032030364041c009011800d1814011104450120a00310f010003050042075400b4910a04041464034216030380701140c000c5807244140c5800c41042113801880000801012405502440b030300046600720b4080304004100003e51680070321180350584655a500c0711007031401580001d4512030094880468100ea8101525103c031600d01850002c802001c1c00003c111407644200c0317109448a140d074110903110000110b80084109006508001189404110302c500038401444000b40f484024060070000d081c0301070401d031150000d030056903d00038694186445860484119a500250019140111100154083c007864001941090307010171401106051580100c1c0c015008004507174814003035903006a134580c09812004403c0100402001c00030b802 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 31456219 1250 31454969 31454971
    0xe060109060302090a030f14010b030706170405150106090e060604050906040915050c0705011a010503042d0609021908030405060d021b0601030b010f080706120b04050108100f05100e 80
    0x402403511102d680c0c2c913202c0c07400c0c02009400c251248d03000000c12014150b0b007480b0b1030352440f000340c1c050041e8524190020f00300c425a00d660b40910100d08002904012007844a8843c001c0c0345000041d4950f1103a0005107400903a0003045040810b04012815900c0c08800795021910010b00302892540c2d900300b80f00140c0b40040c0211003004a90b00044440a070314002e05120301d00700d40c00580c641d541400c1460035181c4501e0195a00200540925000d0343c0c414116680150040c0c0291038003200032585e03001c0c9619644105108052000341740d820002190081c21006000304d40741408003100e038608604c2c08965100d5140207903c100810480c2d4104a2701810380603c1e4400300609007445d140b440807124141034110a4990082001842001101192140944821003000b038581e401c04004a47c3e9004502130b500921880e00b00109003440c240d00100030004020780103126550303550f01c4040d61128801115400c2d6400c0680302c0701d220b1814800c01e446403503143c81c4e400c038103441c0058400380810 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 31457469 1250 31456219 31456237
    0x171611040902130e120306090403050901140c010f06050f0a0306050a060f1e06050c0604110a051003060e010603090c05090615041508070807170619090f060e060109060302 75
    0x3481d042080d015075070f41a0190040a1201c40101c2d0140442c800141005e0220070090240d030070070320910003140c94500e5200c4c0d1161345418169a12000e010041c1e60603900f0340a90700e0804000140070313014040641000149401190051107000e803914204130f004191400c01039000342e5402002c0010407200e402c8182c10001082e070002c0e20781d8481140c800e1800194209030443c1c55407081e0201ca06c0e2180c0007070402002a485c2c81d90810041c81c0400d903d4120150010380f0075040ca500d155a15070b20912100010a002407101140050407e8080c004d802c003071044100c4001040000200c1600a00a0481c2103510a888c07403911402c1c0010000b1254003d04a25005422200752080c000004001800540320710800c2d6984401041001003603044000c142d1000c2184100c28094001e03005000d100102150250360f800f2550384a010544160200340c4040c086504180006612140c80e840700102c041c030000300307000254036041004141001a51060700052042d0001c0000038802d601602c001d070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 31458719 1250 31457469 31457471
    0xb01050d1505030102040b0c060c03040201170714030f070306080c0102150a060b13150302070213090f0b1807050a14090411040204030605011806030503040501050a031407080417161104 81
    0x1a02c610100e400c81e00180c001c80b01ca910005600700e00640104050313640103600e000300510703524180d4002401c11030085109121042d0340310200b640390307015103148408908400b07801600e0f842e1906c4e800c0e44051003641c0c0035010900d0100b0100f100500425480c10045040e001002141000045141980c6000b0001d0744020341e588030214201c2e07180b00040c498005c1d403120b4040c0c9141448000005002d01c50b00e0b06061620410000c80181c54145160840d85038170900003c00054030706060382c08084003100106180701142c104000303881c820301c08032078000743e0404448001c1e48a4080c0004494107002d41d003221100313046004007901c0d280100e00d40c0b0034800d98042e0000f410400120707040e600079070021554207480c5c4005110729801c06034000c20030f004070310050104c54039581700ca5840b441907000341030400030002564083c0358000d4001022120142c82c005031246807024000700680419181140c0f1804040d08011117814103c0035105a5030101c0c64102220038a5517441d548521042c10440d082 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 31459969 1250 31458719 31458761
    0x51209030f0706031410030201090b180d0503040609060305090601051c060c09060f0c0c05060f040302090f010e1303080118090506090a0203100612080708070503031311040b01050d 79
    0x2140305220181c010700c0b090310301240441140c80000c91740680281120219000c100c02000540c0c2c0c46003610302100e121228599a460700c441c0304c60321000411689a4026100e40ca075070303041010000080c0225106940e1b0103103500d4a60a01f142640c02c00d0701e0107101640000014491490505000c42000c0d10704082e00365040e038a6610402658031703068034a40420505031080105075003202da001c04001c498a010030400f00c16a66200e20420306000c2d1500954011428940c21505c42089401441d0010302030046841d00402186030b0740c0007400350324100040580441c840030301c5940741e01600b59050312a154240c0c2030140502d14405140840305855484601000c0401d10901401d405040702001800c2240d50383d006261070464030403080503105142203420407031002c903042d0040c50f4a500c4044107540d844241014607c5028215001d04980000814082c0604044601c078600b64429400c0d4a440741c0748034208002c4900f02e1090074041002000040075806240c5c0c480c000c0000341d10744074501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 31461219 1250 31459969 31459993
    0x3011404060e0c030f010501030501060b072001050c01020f030a0b010513030b060102010b0904140706080c0a05130e0f01060e060304150509070f0b0405040e0105010602210c030f042105120903 84
    0x1c1c20f07040e1170340c03a00769941d180010f02c18050203000356805485208100c0380b4124444d501c0b003040c0c0c00641c45810942e6440031031184540e1098080f00c40c503402000080d510780300d4552011540d42c0c0282e0340c8240251500a803011194003480a0360700400d002c09155500c2c03031454450034101c4500901c482d045540c0e41c04140103983c1e035050054029401415145005a00d0301152450416250082d0062221200811403510f500c1c4c0c0c12107621400f00d207003031074070b425605050540c902d81d0340e007109042e80410801c00080c0d14422411904031041a5900c440d8000384005128840c40141c0300074000d02000041d51405a156400c07858001d07040004941c0300d039946055009900103582c002114407600000c081140340b915005513608642070f03000800c8107514256000e0750f41d0b00c0780369000114113040068040703076025803c156480038948800340d81e1780b4210390744020701561080c0151071011440da0032071680311030406a940c400b0b65001000704407100146460440765044410f50380e40c584180030b5075201e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 31462469 1250 31461219 31461223
    0xc0d050a0501031a0405030301050d0c0803192604030c111807020c010806030a020d0312050903030a0608010903140c0a06230106020a05030f030c0f0705150603011404060e0c03 77
    0x200c40c4405420010345035045181c690050b0780708802c90f0740450fa0724010310000c80e001104030390448008607020702000d001e0740303000001402035034081005070202041007540c2103202e45182c0140f5440e903030b401c01f80c00040549004c3d08002d0620740c0c10b0b000c00c0240014000303406040056441402034120307046445001d40000d00e0b00c404507604120300c10520782800002501007021842c040000d090003004e916202011076510080004041e00c0b600c15a8460401e040c0505080d001000c4804d0061215191485110b65a54819950000c03107601d844d9000580b0a410b2042080e050b50658030805075800100c1070515603003224140b001d0f5402406640d400080700e500c11030000c00862810400055100d80301100840b0b0140d0111040d50012200500020400310403200c005004080c0d050f229100c50313046144d98000c14144501c2854006064000e0100024043e002c04500d004814655a602c20506081e41d23241c0307003000c4040c400c100c0840c0c00148184c011540c5d5511160444d0000210180000c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 31463719 1250 31462469 31462471
    0x90604080d020c042d021b030406090303090f0b09010c050c0402120604060b0705030f030705070c0602030714160512010b04020406170a02070b0601030209032514030601030201020a03080c0d05 84
    0x101c0960701101154081d41804c2c090858010180c100300c0c043c0c240300781884892a14601c54032070503198006140c4404100d00c0e00c190000a5880040300e8945464480c050800d0002c0d000c241c0104a54410001d0700740302d841440c01c25034843e9010b43d801e040d01d800040d07403110440c0c48110b455001c2d10071030a107a030301c40b4405080180703003009010500b814050103100031501c854000c05480a000c120b039402240001080364003115103100070958998078080211058016038030300804140360345200041e500c2e800400b510b405070003103840c41d01202d0007401a5a0b500c1c559207080041c2040940d00300700342c0c0b51654014501d01400400801d49c880c100300020100c0c0c3c815044000410400d0945106aa5959409a40c82030211208500d01800c0341c0b161a11100d008081070304050300082c0729003964506228400c20703100c44030407000c9030310030a1040703008c03000c0d040c001c2c0b003000700b03050000ca460340c900003c95038101d98040c0c0151000c140903490480b019000104041021030080192450072110740c4201 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 31464969 1250 31463719 31463743
    0x40b030f0609030a031d1c03060b030c0d0b041a0f01120203070513080609060402060306040213091e05011214031303031d060307080f1302090a0501060201060b0403080a0509060408 79
    0x2e5640c42080c3c48014040380c001b041034998a03485000c00c031031502000038800b6680219592428140390000400b01d0181c202a0400d58400e807000c028490000c601801520032202803203070030712940c03074408180421101d0003020076031800e503078800041050a0001c1440314000381803600b041c0b295500309030001a039006480c04400604001030607002042200c2e080310161803220042c102e5401c2012041c2c3e134504029102920910000002c1511a590b0382c1c1184c2841c0041170401040c1580c03100030fa4000d007007112001440b00c00b400c030141c0c0c402200740316180c144c4030313030100004010310300351240b614130802c0304c0600341903110811270140030070700d0800148000c601c00d90300c041504039522506034052101191107400350400784213022800750007000440e440030007503641d0308055640e0002e0741c1c2c0003040c4003000b9410240c0300d003c3c03001ca9102c1c0e801c02810381354141c00902002c2d55900300c585642c8607a20015185071001d02070904003902c03640081c900c01500800c003604154aa10100e41081042001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 31466219 1250 31464969 31464973
    0x30301080607110f03090603060d050118020a2c060f09010e06040c05030708070c0501060906090b04050709180b04110d0e15060a170a0f05030c0c0306060f040b030f0609 74
    0x700b06406a200c141000c9860340c0c035011308042074180003207580da80112000d25205100200003d11607844800a6000d41d0350010001c0c000a880070704041c0303c4c00f0203840103a01401c0805000b040100391320320040a803c1003800c800c0c14010300859030140c2c012014200552040c00600080400d580e101002c40c040c0c10b03090031121150401c5001c00c0f048881c18803041003801410300c204040260031030261580b1601508000700c080d82c0526041d40184259085980110b290600214440e005588106880801660104495125100305490a5200344580741e400075242901003000e00f544d80204e50403106c044c01c042000d440b210500b5400e0b4204441c0a13400940d504000f07003022408021050403081c140d1a0510700e4140000410a10803107030151a6682404100c2c40450a10800030301480f55002110f04d09281e9903407400c543c0340d51100a406645103c1c40000100380d00d00465400e020b908024030b0300340d100d204442441b000d07105105032140e25004001071801082030601c0000c2c030a80305440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 31467469 1250 31466219 31466221
    0x30c030308070f0201060f0b0a09090515040b0d02090601050c030c070306021c0603020604090911030a0305040e0f10030209060303070209070e010f050c07173306010314060112020c0303010806 84
    0xd0001e103c980c4040b2508110382c1400380401030100b00c048003006958001d449503569400e043c0303065486009583c8150340141c44c1c1410041c0c49142e000c600c3c1071a84d422141402004c0020040042c0120a080e01a503c105c070303080406c3c80303980254000c001107074004054078102100d40d0903442c10880240e10680e00b040c0c002900c0d151400440c20609009450f401c0204031031410b580220340507000d24051001550390b03510044c0180405d5000c400c40c0b1900040486003040c450340f034004c105e0b0f005031041000b0410302801041400d00040707040c038882c40300050604085403840e0200300b100b070f4010b000b8076014001044102c0258540c0c1142e142b1404950b03d80819004a00780010f2401442d0001402000310038001c00100c0940812040100c40c01c088036500e05144404202d0300303000f03c50807803640c0200c0c003200000d101c200440c4d1400000000324000102551032400540070340e07108401c40350340c41c014040007400c0b56000b0348100000c2600c00000600306140e81000034036643c400c2c1c10034042a03202c40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 31468719 1250 31467469 31467481
    0x60d0f080a0f0e100f031104080106030507030303060e0903160201030b1003060f0906060206040605100506190f140706090809060d0603140309090115021203010e070f1b020108060406030c030308 85
    0x1904016101c0700d05612416130300401c01c6000f01c00c1502050f0301d44400541000081003920040d140180080003c01c1d66842c142e03035a17007031740c2c4401c50100c2c0c10b10400044442281c0e000900c03907541c1e00045d42c500203e0f06007503400412421070803418180e4580e44a845030321a644001103100c00d5440004115042a04018100c0c0207580b0502c1458100102444103030350100d115900f082e40408082450f4503200c0e40c810100b030311900b005401250104042c1411404d110201c5502819038407031411911040b5011101c1d813040842c02450000200f0662000480503400350818500641d403940c1001d250b0030000c1c0c02035000325400c0401d280c540a060061150b110043c15110180c2130003540751070008800329544001c14030802c1e80784d01082d00c10805c460300a00c0400810300c01d600321140d80b581c5881f03101034008420750301400014506c152104856008000c00b8a0a400c088460030051a05a0044900c101c0041c4501c0c0c1054aa0310000002151100c403400618480c1c0c43e91003184c40c00c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 31469969 1250 31468719 31468727
    0xf0c0c01110f0a1502041208070b0a05041109090c030111040503010f020403170a02010906020a0f020d020a02030304140f060a11060f100e0403110d0216080114060d0f080a0f 76
    0x18640900300d0307000541802d03040d040002e1030308581e0794025900107050008480c3c0b00024003840d80040c103403c400c0b02e11401040311010040070390a10641944a594458603030700e0080b40d034100e0300141440005449510145081541654481ca01c0c600300c42c5581c018101203402d40760228500d00c0e400e071010605108a103030a00a00032881d0b0885811410a880d40c1c440112460719000c0c0501d580d1030000305101240d1017900f2001d00203800003030641d500d42502c0001031490403142030b00703030040c0503c440d2840340c40d102040d10480e044e0003c00a604180c10413131700c1030003070f5400c1d41310340e500c0b000c4881e285045403101d0707028100b0800b0300d4503660070002c4480e14160030250018001d98900080701e080100b043d007010501e100781d480050940d20640d807079240a41e10301000148002051040e00c02551a00fa80003078007090104c0010300c1c1000c5117590303003807031800d0f5400c45143c0c02c1c030740d07902000040c0b103820608441480d950140c4084642c00c4403070b8440c4050b0783c0c4034641003000980c0801058103003c2d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 31471219 1250 31469969 31469987
    0x6020d15240203120c0c070801060e04060c030203070c060c02010b0a0305030703020c0303031e060414040606030213090305270d110f0a0308070f111201020405030d0804170c030f0c0c01 81
    0x240043c502e40540d07100c03d070004200c01021031039501008507240c444e81d04100104000307028488000c000c240e8a40d000142c408000b290100c3d0b01da400c111038592010312a000792070007905651522511403260340d80301ea01504100c090441199611030640400e81d94210507000114002c9003d50b5540c04281002401c2488130203066000768020000d203c00c00401081c00b0307103068250100c003001a260b500000700030300100d020f0282c1c90f0a09a09210500c6151384c04042101d02c201c404000b40301101079041c3c241c4103d008054042401030015008094035981c240f00c0c0c03400781625480380c1244c060700255030562030100580740d14000c0300c40810981403490fa0b40407040707800c0301c45120700d918544d560405480781c07480081c83c800490b02c4440402103403060800308644001c0142001410f0129014000c0d0440d01c40c2c4e510a2103200c0c2210111800713445081e0081e44c2040030f01410b901040405502640440b80c4903140707200400c00130080b800c605018107091059440a85010740d8101d000400a40e2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 31472469 1250 31471219 31471289
    0x2191206050f0627040617010f0b0f040504020604030203060408130806060904060c0e030d03091109040c060c1a04030807020c0102060f06010e0d060f0606090e07050706020d15 77
    0x800303040c000182e600d40e4213a408180d4804800407030480031210002d420b02d110104540c21604041c000302d03c100c000c0b102c00e800c901100000704000e46604c0088825146424203541c0c2041d58080c9454042c01c10342c01a5900c00c1c00902114a015a29030100c1d150080407141900e404c1380101c0c103c034a841031158500700500a1400500850414000003001400302400080003260b440c2810490701c0c3c003449900701c1c13620004003542d04051034100040c1c043c00d0b030514112221403c448910f006442d255071907a00450b00403050200c0141000e0003511101000c503c1503c07440040b07020303022040c80a03a82544224072a9440b00348a051464004c1d141119807074285055400c5802004514403000f040d899018009292003180d40f0b004101284501c0b490542c0a484241007070109803502005030003e101301e1b4825503c03051255a10400c60f03030071480540720345000900401031900400e4850300030300b4003417401c1e503400540d0100d25110003981c00102e9002241000b82c0c0000b0804020a039a07640041113 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 31473719 1250 31472469 31472479
    0x8040e010e01170d02340305011a0312040b0a0c08130e090f0a06050c040306020705010515010c0305030a0203180a11011202040608010506070311190c0f030f0b0a0219120605 76
    0xf0040194403025426061b040c07901040040e0782e00703d000da0035100d403803907546000b0400b225101e00b0401d01034880c0021036941079100002d040e1041c200001e55030314545c2c100d1441800c1c40c0c24040e0b0048280e00c5030000204004544028a0100c1c88180041202e00e480d11601600782d4680942c00501041c024800e40c200c0c2c020030290b0389544404581805003aa00204c00190f41ea6894042a441d000c5da400c0603001c54404580e00c401c00c441540705500601c0b405150301440d080c4c0400459044001c11802800102c0502c040341e005001500519009401002086d00c44030388443c180d4a805000c200644880c4100303200c01616507042101000003030b025490039494a400e00d44060300c8801c0611415008040020f01300e000c7c103204e4146c460108003908255100d03454051819031208080d100c05442d80d095004d00000e803848810400b604496020310040c0d4014090b0f00c0313240107040d004242e0480c1d00e03020090303040c400c00071000104051794a9181c3c41000001a654401203440f1900035900070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 31474825 1106 31473719 31473733
    0x10806131d03130e0903070807060e01020702220c0306050f09060418050a03110303040c06030513021002150f060913060207050d08070314070503070c08040e010e0117 73
    0xa0320003a8044c0c1c02601d5200c0c04a40368850381d030004141d07076020440c01c0d0002d0b8503508031900c86002a1300041c10081d10750046049401c0210202e030084910030490700304401e0310300c1180c1070704149150812a060030000413410300003008034914070440d5410001603140d61181c00c0109940042842c104450b5600d00c0c045940f06401c1000310045109036503d451113207000025070b4401c079085058040c030b551a000050300200305c041d191701c0c40b1101e1440c0f00005600d81c40707490706503840603034014460441100b40344610100094203403140852401c042c000030f41d440d0940f081e0040009a0242441c84040c0380040083c03141d218001c00072701401d501400a550841c1800344070380c0b41a10305005c0d80d0000c00e618100340b03404030741150100b0014408180b68510419402104600c01c000483c60035440302034200380c15100341d01401030300554100501007050168254601c4a036104006c000b6 = true := by decide +kernel

theorem cover : BRFrame.Cov 31294969 31474825 := by
  have h0 := BRFrame.cov_init 31294969
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31294969 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 31294969 ≤ n) (h2 : n < 31474825) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
