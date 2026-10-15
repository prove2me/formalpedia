-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4437
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:36:31.079135+00:00
-- url     : https://prove2.me/submissions/118fb3ca-5f0c-4f38-9058-43d209bd5af3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 797841726 ≤ n < 798021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 797842976 1250 797841726 797841743
    0x51c0909151e03030801052d012609070b04030b01090b03010f09080703110c060f0903031e0a08010b03160f0e09010b210405150405010b06030c0a02190c05120307 71
    0x1842c1e1441115a1081202d11071303210382d80a640ca44041162801d41030105960030070781d0718492500d1140d004503031080802e042c1814a80d90480320603408100840d0300b0070b012502129404c6c00143c0c042080f0b010028030356400290b0030541196100301c181441072041e200b500351104410015a1717401e501000e00c180c00000100f00c10841e61902024a80006005501240107a10301005041c0c0105102a05110040502c1e00d080d5a400a0b0344150300158101c6405200501480318001059070404c58001301c002c1285482e8490307244028841c0340305130024402c1941c1070007030182511080203100005500c60510001e241c1c158401182d0000008500741e40c001004000091b0311488070005006541a805481400d100000403508641200782e170014043c0d44800c0e0180c0e41550400e540b10341103482400041201d10b0303c180094030711b4200f59036140d560302001a069400d10340400030070703640b2001c400c04a07048011a0320ba648140c070180c890b0600450b42480d401c140c032070060040b00c81880c0d101820 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 797844226 1250 797842976 797843009
    0x81b0d0204030308180d120218040f051603020403020a0312180f0906060305010509060d05030c0a030203090901093b070f090e070e0c0714060403030504051c090915 72
    0x44c05808250f400c2d03d04d03002c403144c2070718100101162451101d9001c0d2105050350928126440096100380c0655000c0c10045410541c00c1d513550040c00045031010102203264140300d82d44c3c0180c5054500c02200345481000108010b0700e580301404100c0c0d42200d004200c0184e014000e5800040786d01000341270b458030100110703050f43c0a00040040e41d4000303c00304502c1c3d0b01d81e04140d00321035080c024181e0007084000018031500d01201d584510364441c0007500d0800740d1682c869464000b500c001200541c0010405521034107180404500628203030209000c0040c400c25034488140c01d4007841054940802d0050701841030301340500700300d00309403011149030503601ca50402031000c0e50700803001d00c2418440b110f1044100011401d042d1400e00d12450b0594943e00c610500641c48101c04840e88400100b041c4441407080c006103118a00a49010480e40b07007901c5c0060401e03290050a0804503030800300007058030341c080c2001003030f03401ca05c50000d2030030070344a2140f52507440c55005200c41200d2020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 797845476 1250 797844226 797844233
    0xc0f0b040302060405060604090b2a0a08061e1c061b0203030a050a020301060206071803080d0b0907030e03071506081c080a020406050906090f1906110d081b0d020403 73
    0x350f01e8419406441952010703298101000181d079205103001e080318402c4030202e451460b1880b0109a01e8110041560a00b40d01e0042030410340c1210200d080032813005401c022650610030440741d00c40700703900c1041140342c43e910002202c01d68244860040d9021443c4036808000c00780e0712525041e941010030000e030b06640740700250f07030361300440d501c0c0304450401000c51210445070080ea4103a4905030041e01c07155907030f100c045032030b14907100c40462081030400300000429507000040494a00d10072000c21034055140c280f20405c0030141c190030800d0f1030b00e1000d03490600d02000341c1da074655005840004031454441c1c4071000c0c04d0b80e500320109a01130b904014211114aa65680c042d1196403202d49040d59040c924008902440c03043c00003050003001440d20620381036008016040c0c0040100052034481808030b800910305480c034001d4019040003d011060704208144507101d12040140038000c1004401801070402505000b503400705440c200744581c1c042d038252a1044600c442c11520baa03030320305 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 797846726 1250 797845476 797845483
    0x515060d061d04031b060f05161b03140f0d0c020a02010207150915200d020708010908072607051e0d09060f0c050111090f0108010807060c0f0b040302 66
    0x800d10703000c2e82c80c0320703065114415a90516071080790143c9921100d070000030301c4450024402c1e1800c03240035a0301d4191444880c028071039203001d80801c01c200390b005c00700104068440140d040d14075184c20003da01c400006980000062907005190000c0313901d601684c0a106c0c00740c001c0b440b00745101400e08484018880d4005583c0c0841d5000764200e440140da201101e04901ea0850320020000759004420303c0707100481290220f00c0c081c10728100e920a0113040c04900541c1f05642c1060182d001180700703032041a81048030381c021340303145e0700200302d910b00d40c0e03a440c0018490880d008014200302541d1110308600091916804903039140403035a212030f185040b030b8035481d81621030b908d2a00440c115030000c4c10700095042d4800031580b290880241040002d44035003001401103010000c40c001c6400c00a08280503184c080090300f207466442e40c41d42c200b00507042c003051407020b042103140001048001d200242840464203c1e0808460b26082030810540301c28030480d004d851099100180070405a002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 797847976 1250 797846726 797846729
    0x4050a0b01090b030415020a050d05130203070b0a0813051911090a091e17040b04170a05030403110f061c0e03090a0302041e0c0914060a080106030515060d06 69
    0x980c0c82c040b10035166004410079000684002d442d010740c050642024410310390081107100b00c00e01300503082c4904424100f0035030700e08995541407a2034180e090001c600b41000110b020745017410095041c18100c500042c2200002440e82c50040c0d4840c4485090010a0014941004040d15810400705603414031014074070982113034500961101c400105014401d11034451410303442158600510b081504e21908030309a05001c1d1b840740841404402d05020f01802440203100b90020582c5403441c0c20842e110441140719080420342245c170007040000d20201c2250203407235002190a081554101c0416035805a056103250030020000e03001c0d858072002c000c08940203c03114010321030040b1040d070442d240d0141c080d900e60483d9860206000524098101111003901d07240017a1004000c1030980050f604000841808904c414034184075014043c08180b210318402c0d21030910f00300303059500030018641440343d130b010142e0b40ca0115074003800e181501841907400401c1035440305000d800020042c00503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 797849226 1250 797847976 797847979
    0x10e070e091603091a13050601080a0302070312050c03040b070b0a060b04170307082d0403020d080903101d0115140d0312180c1706160c0204050a0b 65
    0x61030401045241c9040e1091060074402c100710031501220200794040d01640e54200c03100000a0411101c0304980e00105111301040c90441c0c41112950424604220068001190719009004014080303600050410100c030741c064502d000c410542d02085583c2d0041a001f102070340000035000030f4021148015180c164010311000b440b03038440d070082804840b654801c0306110701080c407040118048000d801c00106041d4010b8178501502c41e078a000c00f660109041141503000f000303002406601e40442075507201031089926181c13505540008070040c40d90940244000400036a048540e00c00780044145e981c040c040901020005064421102d4080d088000d0103610b8240300d0f01c207420b6155a40b5007203070307003160300c10002c1c0d00c3e51018040346610070b14082c0d0a002c4076419120301c00c81c50f0710507010811101200f44110600c603103090741500005600c00d140c1c0382c0521214164200010034610b030400c101d000481404014080c00303a070b4103020803d029501c24a06000c11003010403039005004207110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 797850476 1250 797849226 797849237
    0x402010f02100516090b0c100c020f060f100503061902090a03020306040317150a050d050111040801060e071d09061504030b011802040b04120f23102918010e07 70
    0x1c8071221b40e02c0c540509004e20207190f11020450042202c0c07644030541104c0544107a42201c1280c50700c041c6884010359270b8807038041d045030070420204500e07610080540000c0b000752205080149000800002074601c03190005c2d130014103003986a83e01d5100728015039020f07050f110030b0310b02420007514040920f02c1114004410000041584100086c00d0022810051031403c001d4202818420000c00c0710200b2100c9640c1c1e4004001400403090241000300704860010505038100400c0e09412000a072586090121003075808101e100c4103408800003070020794600c002279072901d000030a43c000c01c04540080d80c40000740441800b00c03000480307040c1c07503c0e02c0800320080f405005e020128422403042c0d4072000010300c81800092807502e03003008071500030030003c0da1440071621201c00201041e02252a00350788007403c014240d405019000078511400d90811204440c2200000d5000a81c541000031031142000c142c4681e460104071900442d02e840418402d42c1c44085d102e00096060b21483e001c0307007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 797851726 1250 797850476 797850479
    0x504060206040b091905100b0a062f0a140c01030209010e12070e150a0e3319051903050705010f050c01420603050a09060c050406031a090402010f0210051609 69
    0x20b0500b01a0101c550b240e4039002c01c00000100061444443c5c28240c0ba00d0b402403070800d80742c8104100c844406801006100c846c94dc014840c54900000090418141401800128000e03a003001d45048814400e84504920314003201c1180c0c2025407a070800b410b120000c201380003040443d91000d008150066500f002045d0300c509000400400803942ea1100c900a0214612000d0680320842e0145042c0d02e610400da0034690001810004d070b0030382001c1c410391102c0c0c2c20026850403002000081903c07002c4820703441e0441d212a9181c801c10b00540381800b182e000c0010115101c3c3d01140d15401c43e0030000c111110a00ba0003841d0082d0705040c0d002940c9210301c0c600360350400c00b81c80188560440c0c400a03c0039103410030030b402505009000010f5259a400994041040d5006148103100155070711662242824000b408a42ca0528444200c01c10041c1c500b1031621160300894006409080c088803a166081c012032a00181e1030703101013407508003010300060203403070140900c2241c0b8135201c1c3c00501d03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 797852976 1250 797851726 797851729
    0x130204081005091902030a0506010b0d11033106060f030203010b10020c0418140114150901090207061d0f010b27100801020a120c0504060206040b091905100b 69
    0x40b4000d403030a40c0303603400c0603070038028440354a001034841a20140548040c6015900d8030703402c00d10264068001c500c00000c10090744041c0f4820540304054102d840c07130560a01c013910082c40b94111031596408103124100c0e90004511031052405954841414000b80c0d40307800d560300903004103100482c025800c004440c4080d1509441034014403c00d0f40c01050320300e50b68010030000d80745031130181e002e07000443c2d2510f021070348a15014a400081f01c00208414091090307071900d68000401007200c603500141c8100d441da442040c5181159106940544c0b21031141c2400001401901c01c0210b07078000034040a403a6000218280d440c1c015913000800001d01d6000601010a0000c91401c0301c0300031840c00e07050300d6510010025005503141071400b51098072000040c1c01ca030b02446055000c03400d58071000d83c100303501d4000e000c0c54122600d4400d00b02860008044d41c1ca80c1e01600041038a0384500008900302d03010010115400141c2c50310b1111459182081500e030706c103244c0454230f800c1c00c1c580d0b0000c00d03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 797854226 1250 797852976 797852981
    0x20405060303030f0a090609120f020f0610030602030a060f03050f060a02090604030210021f24030c05010f02010b030a0f060b03060103020a172d06010e07050306120109021302040810 80
    0x10400c0413414142e50744c82540902c02071031a0502100c042d03980b041030001242443e0841c0824080907100c0240700d40840402a2030450603c0807032240764410000c0000c80e0500c58841000c5943c090b0002d616900e400c0182005020b40c0d030440c040b1807901c55000010702100240d600c00c40784c40d08060ba0b41c40e80f580d000684c141c1c40b0b03d04110b90040c0042108100500f491221524600e07040d00c155043da026180000100303c1c070050343e031750b1404d480f5038000405d03c03d0340543e507c442302d51000c5075504510715501c000c1c01c1000e034491181030102584c600c4504900071f403c91100442c0040507a01907008502d050b0400328002901070b203001e45840d01c08041d5040014205040e01d8000b42a00240c40c903005501c01c0c0d500c030508520f0014000d1071800a4902100d041c0548144503190303990030807040001c201403400c00140d020300c0070b0702c0b05101440300d00c0e034100301100c2e042031080e541d85c94aa120001818090010341d00025040311183c1b188814580700c5501030b20540380c0c2d81007500e01180017020008213 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 797855476 1250 797854226 797854231
    0x10050a090e0714160213020a030f05040507030609020607150c09080a170a0302090d080a030c0512040b070c1e0c09110f0d0905031912090b0711100903050702040506030303 75
    0x1040c803030302400306030100220103032000c0507441843c0c0c0408202c03a03010a001b803401d562250286600802d00c1d48116406024000701000c00d800208900c0c40c194640395a1050b19120180483da03565050b802551215421103d01a8103c50201d00038030f6240d000d0f030010030303d0f00041c10020b4004980851020004070f0b001d90074079001341b5251250b80f9a2403d440e070550085480405140d4204120410b58481100c1c1440031405001a9038075106c0242004c0d0641d003038100803d00304007040000700c1c11001c1000d11580c11540203d070011484d5034200c0c1c00d4a89010f1800701800074107041810f450180201d03510f04640502c500540f4029680c0e071044041a10b1210015030030700c140034005000442e090b10064040c0143c0080b01040ca01c0103600c2e0310741540d21081c41035110360100c085c400e2400760022080c905064801c4000c000094242e20754448203140500488108012440d01051800c000c1142c00110600c2c044100085400e03440c01410640c03059000700d00550810001481c2440c0c04401c1d0707403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 797856726 1250 797855476 797855491
    0x1080712020d0b0c0412060905010f02040e0c0f160b040311030a09050409060609020301030507290406030e0120070c09141602010e0303010b121005150904090210050a090e 75
    0x300001c0b0340d581c3d200c45030328000c181128650080c00001074031007080194807420744c0039840014111100f414001e0960b8007214000ca9214010442000818094040c4980c05040d074600b107520b0710000c3c400c84000d880742e50710700b02521080c050f106051050044503c4d0180f0703c41d03125103448008015400392030740120886000841c4401c0000c02c040e0030650401c84400d8819a070000d40c1644400d54441260420380090700c066000c94004d015003800c40304414002c491b481100300b0340c402a4081e50925108500a4804240e11424814182d544c250440c008403503c451810341e201e0124200b240e529040ba18040c4c5088400c3c203400181c1041c241b10750507142510b042d01d24456906c06586d420f4984091504104665881c51010007080f002d001450180c00320022595449058030002e4050072409000703444001c3c000c80b81000240ea81c0d90f1002d913181a4020b46a403140d84150000740181141003010b5080403040702642c40f00c1da80031006104880c0341e600c5000603592a200c03140c00841c011110381 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 797857976 1250 797856726 797856739
    0x51c0c11150a180602031005130902061c0207020a061e091505071a010e010303030606021501030624090e010e12070602030c0409020d0b151303022103030c030108071202 74
    0x4000b04030540107a0060001002104041d010a9444c40201d03441220042e65502481405004038038110182d10300344c1041c44005d00014100b0b800244051041c1101c0d80851392400308000b1395040140c040c3c0b030b1010340090914100907551000900380600c00411002000300d141d2807013070001e0041d04d0324410b80704000e510350f800c895410300903242944104001c1d200d40c041140ea61500e00d040c0800a8042c21900703a694017103500d50f280103000e54040d80c01200941d04141c0600340f04d41c2d000c0c1300d2941141d4002038040f0b022000c032100c10510143c501201c0e251500300801c0403034010030359002400940305850003000744840100119448a07081c0100a091319800c200c00340218010307070090f42c0c1101e401025249040c1e500c2540c001268044407052100b1601e42d040c68007145042c5035409007482c000140c042c5444801101c3c1d280718001401f0003485070202150600040b004018419401b0142401300e0360340e81007900139065242c00c02d100d000ba06205079030000c20600022081e4100d80342d805801c9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 797859226 1250 797857976 797857981
    0xb0604081504081207031e0e0c01201002090906030a15050601120911100201050c0405060d0209030105011e09020702060a030f0b1c15060f15051c0c1115 67
    0x107035554000c02400c00c0c1d446281c00c4c090348080541840d001d9015446a850020f1801c040120501c40d0250f408124903080b8540031103804010000324128203c0c1074240303000b0350a0300c02245104e502015000c0785208511420386002d900195030360040046400c216544500c641d180c208040c0e8031684a1001407034014540c04181c00302155401042c0c01038014108080e24526609001c4c2c12510415410354100700d001001110504121520707400250092000780007030302d00300030851001c1c400e81c42058014000043c07040f100e840b0380d41c1a06c03d0ba60740103000380205d5a4442d01a12650840030000051410301c240005030420f161086803a142e901074115800c00340c3c0c3d05401c1d0f00900d0844108414580c0714803070303121942e540c4801c41492034860382c00c00510042c075007480c000d070034004201c110350310b490140c0500c07080b00740d040c00380304403403960000e00c041006103031301180c5038001d04808111414004400e45413005403500903003018601c50380c5002079691a4824990340e001c9020a044000c85000c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 797860476 1250 797859226 797859253
    0xc0f030d08070c02090f1807050f0d020102070f271b200a0503210103020a030f1502030c090f03031e0906160501020c060f010f060807031b030905010b060408 69
    0x294460903d040c07a49000f105030b00429803004044a4000c1600140130810018100c883c030800c0785058024020400c4505180100d03c1110100440f18880c086144060b400c583c400c11600026103a071695004038550384850326441034401c18a04038000000d0880310080e920b843c812000030505071501062510840030080c5d8013048200001d2050002d07045c040c401c2410304211586009124030015991408040618a0340d412070469010503040004c0041001d070f0b07111607004083d65049080507003046420f10340354080002500384815007500120800c03017003aa603000540301107102030fa660729079044148101503c80c41101d1010f04035080b000c103034418184c0500c000d03002e50300014001d186401d808007c409850600c01c1d008a40d40d0307400080007c50904140641900010b04440a105650508580c00088102400307010100100c03480029025031207a0803100c413031002c41a000c21059010040100a8001c1d00000d50ba01d6080c6282010a41020b0040360704440d5041d000d091300841c040c0b07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 797861726 1250 797860476 797860487
    0xd0e0d0309090f090803130606090903021c09030b040804030506011a0304030e06091e130605011d15032505030c090d0f1712060301051005040c110d030c020c0f030d 72
    0xa0031031542d00e541e040d81c44c001030000c200070f501800b110842c840c403012691604205569243e001410698140082c03140040e0300021418134514030080c0c4240d40030840c480841d480502c5030b00260000c0d1044c4144070501c00d0b290014000d807800782d02561500c1e0307207921b440740c43c1c40b955130301400707442c60300304000380c00f20f44180e02840c500c0d50b005104501c0d20b0185000aa5140d280080d026441841d55541009501e00b01954244407052103405100e000d1408001030001841c0c0728140100c1c507a040030000d119a034207900c242c001060340c4bc00c0d1f070300ca0400051070345400c2c4001110303210501d03044a04150050007072040e130b8401d8400e06d903668544080d00d4103100c40340700e002008036101002400700134001107010000701412000d00b44e000e07894071402640c500309020044e004900903407400c1e0900807110b00b0300c07200c242652025280400c5041190034115800d01140d00100e000380920580208050b85c1600b00d03400080041e4202c8005900841c20001c83c15104940c2944c5940301c0840c8602d90340c05034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 797862976 1250 797861726 797861741
    0xa03030e0d05011d030405040f090305040308070f0c090c17010509060d1506151202090603060609010e03120901020d0513060f0c061419140f0a0207050a050d0e0d030909 74
    0x20000400c04d001056010105000111010b42980d00049401e00150a180c42403082c01c4118080621100b410394402a005206902001d42100e80004962050141e882130401c02c7c50391120070501416516426000107091302c45000000800c2d03a208100040000000c1c0c50580724000c1c80780321640c48080800c004109180402c94410445115810a00c0715502c900350040c03201905120000c02d00d150014540c40c03001c7c41c43c2411a1041c41580b400d40c5511040c2c96122070306884981d965445440141d6115440106203036040c0b064549880d8074000040282450003400c0c4c08075420f48181500c280c1c0d8600401c1040651340740c0104c001c101d16840356403418060a404d08080c0f082d030840f07444400540e003075400705800c541540c00c14090f40700190124800d1001940408000d00c003141e400c41403038070501070443e94020800b1400319002002e0342e4100e4080715406800c44100c00300724a04076481340612000007002c541d000c01d1030246414444000103896a056941074402c078200000d0354000c0032007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 797864226 1250 797862976 797862983
    0x10091b02100c0e03061005150301060206010902090117100f12030503130c08030a17060d1a07020c0a080705100c050a03030e1f02090906040e0a0b0c120412020c0a03030e0d 75
    0x1600c40c10586620140840340c005c403609030385914038905020a00c40f2403810814200150230b001c00c01040700b03507030105100e410b43d54a1032026948420850040750410b02d00c40d1072100f000b00c6801804200001d902200c0102e0f1900000704641c240e5410324030010388550100038010440400004504002c1c00080c41072491050303000409890300d680c445031858120b204080041050412060300081141550590140c0215091040c61900340d90f5a40d02694503032064418584800100700d601d4024091140d42c0c000c081c05030f094240d40d400c144c0741d40e03144c1403250340c3c02156a1071301260790b18400c0e0b50b000c0c0940c0e000340090582100c00d94040b0300510703000c4401d01660150021002c1ea41002e1035007040700f4131b031400025840d84040c1c400c0124542000e450317944074900e07020304800694004503503810040c3d040038106025603540482c010907880f446550002d2058010f04010411141c11501000715146034200d03003803481e81e80306100d8513141c43d02002d00410070600c602d05c05440c0103240e0300c2482d1322 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 797865476 1250 797864226 797864237
    0x5030a060b0304050d08010f0b040303030e100f060906080d210605060a0507020118080601060e0f0402070507030b07030506030a060b01030e1b030d14040e1b0310091b02100c 76
    0x292424070045540081e201196250080c03c05a10030b981e2084499002d000001c0010144501d0540030046078801d910000f814143c0303980555001030028042007901c40901d0700d0034010320326405102d01c000c24150103205d8403503140c020301081080002488880c40203040c1c540340c0c6481e500312040398103801403801d100e0006031100004541034949801400980c81103480300d070f0b1508554070000d004004c002c04400c009601c6000100f01d40303200000c01904580c40e5080c0f1701c1c64024200d000c200115207140300700390003c0c00014802c0411000060301300860307011b442241e42c035440300102201507401c01d9030780c660b02d40c2c420400382d400314440381d100c4940c58005040c0050080c4440d041541400d4030304a2101101c070303800000c400c15040500a02510a504d450700380820000304d07036031740d22900a034024141383c1c650b600000703a400c0f800e041080f4205260542074584a00d40802894003202e080d02038101801e0130070340c1c010448000007000c0900880307250050580c01c1c4869058034020300001030168100074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 797866726 1250 797865476 797865479
    0xf1c051303060c0306050915031b0307080328140910030605131d01090803040b090a021206070212210a0609020a020102040305010b010c0b18033a180305030a06 70
    0x7280340c03080c1d40f9110b5054a01040481c60802001501e54004010346c0160b003100f40a4100d541c2c02056000606100c85920b40a050a2001091030405240c000014030300c0000b07181440690000700000020f2900f000c1c60007540072101c41192160031000f100c502d00b20050088000c00c1c0390081d1040b100d004103181c00a80030383da8a0001e05240103031110414034503070340c0080c00c030301c0e01401c4010240106924000d11010381540c4d1100b10328480100064114464140822030550040c07001c000c603103400070128200e08204921080d20f5000c191400c0c4013610441c4001d180c035116241c01e490311800b14407448005039600060302c41100c50f00030401240e00396684c9002c00c00b210b5910107415040e600d64001030f2503c2c11417a0050840d64070183e0369060009a101c900000b60304000c0d01c603444a8103030203400112410030103051039030084410780315221400f040c0d12005c58214000c08100144040d61954540400d01c065074222a40c80b0f80d600b44100c10b070f01c2c42c103002c01d004000540d005020200001f8525 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 797867976 1250 797866726 797866733
    0x6030f1b03020d0b0a060e06031008010e030d1a0a0e0604090c0b0904060905040209060d06180b1519140607050d080106080a0c020705130f05040c080f1c051303 70
    0x140304454410010a6001c660407081c04070f1031054140f060070940304001c00508103400909002c0c440b09603984151f00c0000003c0c035039030700e41c0ca0318802040c2030760003803115202c540405030b240d40015120318141c80c580b4074511140303c02e14001085030f01e000307001210340724101202a000c807407004000540190f2114070f843c0015008000e0013004150803403030b10352119407a90030001590341d15444a200d0301c0c202000d2001507039038200c0513038000504848400c00a240d603d0000f020b0640e10340180ca415151244403810702c80000344180c49064459041c0c0c00365845e24040044d003100300a084295614400402d105100381015403201c0580c00610f640e041148503030b0703414600300350b4012a000042da1070b0300400507260442ea4040e0800311140042c485540f00540095460000b44a140e100da40b1641c01c28512001550000b42d01940c4141e06012524160400109000041c031510305a40f0950105824010b40440d00c80030701c094a07802682c800c0904802111283c00c420240056a022801e000002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 797869226 1250 797867976 797868011
    0xf030403021c0f020714060a030c0c0b010b0d180c03120903020411041a0a0e040b01031b08060906060915030402030102041710152601020405130f0e0f0706030f 70
    0x60b00c081e5a620000014501c4000741006059808030021600b000d20458141c2c0d42c000c1a541000d410707140004024500441c12140c514251744046c05524408002103429105c110086c49036100c04481031000084007501218600e050310310280c60040a40c00c00d00015003640d1071411241b00514240113030a0700d1350009411569007049802808500003810814941030208484100500050032410911100005000441c62240c3c1a01c40d666601008101c1e1b03000303900c41c0e151041c000c6885900048214405070134041c040d0340d5580f250103150001089440d011040b607500340301c041e0400400e0708a1400f208210f82024000306d03810354082c0004210200b041c100881040095002420441881600c0d6402c41e0b10511100440c8807801900348000b03290702e51042c490441ea203200c950b04010013014280280616000194041c4150404104464242c1c2000860882000c802c0040f098181e0885680d05040c0c1c010041340d800041041101500aa0082e03243c0740c00c050002c00d620094080700b460 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 797870476 1250 797869226 797869273
    0x20409020d090501060f06020706050c07120336050904050f0327040912050c0a021f031a090403270308072906040906020705060a0902150405060f03040302 68
    0x69007559070000b0301c140300c000d002d00c0c00185a582c003130208031410910020f4681c0a14000c135028400c00140340300c4c9500c02005050018604404811500c290516001b46011040d1540c201c0c0082d04020701c41c0040e900080750406041c080400782d11a0785400184a04804000c10981d03250180514071610f161050008010907119560700074805030700e4016031081c19400440030344c0101e1404001c580040c5411007060400c0507903041c01c9031203e60040d44149084003504009421600740046041545065400c9514a030b015171800e04c400304200c050301c03403401d00c94501d1962010103840401c000ca401621443d4210001800071030882c002c20810f0407044285030310031142d03084006061300a01c039816005103e480c02d04901c501e5821905104403400b14005440148203070f40e10001d0500300a03031581201c1201d5403110648010b4035040240f60020410f10000b03901075541c0c90700d03185165414104450035204020910703030509022141c1c8811039000200124154428000340300c4844980024046 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 797871726 1250 797870476 797870497
    0x60c08071b03020a08061003061d01060e0601030605220b121203011a0a1707020a17070c1d010320120a02010f0c0b0a0510170a0308241302040902 64
    0x300007510b140705008030a1070690055480e81c00000502501030515419a03044940086010800b80c42460020000990714103103440c0541c0303444030002d20300e42411602441040262030401c038042d42c1d074003884103084110507074410741c100399031240600801940c40304000f8070f4086e10102078850400301c10383c9002d0100c0102c001d103074404001003117101f004030180002912400e4059003014281c00010f4004d2050318400d4840903e12400200c1480c0708002428443c0c1d001031074540c03040c410000480a541c0146004d80e01c241c21104081900da000d00b0080840d024030f52404d00c0c450380b85448201c1240000200800c0d02c0d0001d11030503280707540c0c0c040603491044180002d45403c03042480054000140014000c00344a1030384802c0c400305200307045031580315506030400300d10790b9901d100084008500d6040024214803d264042610300f0018110300a54400c0d00e400c05140c4840c506501000380c22000d401c0002402201c140c43c606100c1c1000f1444280c1d9900903003400d45503a181410781e04a820800c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 797872976 1250 797871726 797871773
    0x1c09050d1b0f0308030613020d0c0804110301020403081b0a0b01080c1e030703171b06010f0b0301050f040902040e0615040f02090907050c0f0d11060a0e0304060c0807 73
    0x18640c62101e50741030030003071011944141e61030349555541c3d4040d00004090302d224941c0381c43c035800c848070142c04503080c0f070703060a0040000e142c0d00b12000e00401c805540c255502030348020600400d0505208690036a40c1203100301d4101110100c0200c200201c001c003100c264001c500c000300000c0c010190180c041c11000d8058a00d507002407040c80616240d00c0d05502511039411402d9599480105128050383e4204e8441303800001c0c0c4d050341203007610504000b0b07a40d190481c03481c074005540104186050350203e07031005082d259078140c0c26045005c01e00441d5485556041e0b6884185040e40c461845070344040c0c0085250b9416201c054188102120b40c03054180c0620050421403401e44540c01000c490820110b082480c1a0041207004a000300700805000d800103402c0349600080181c200c0b00e04a43c02200c00b031500055008011415080d00c3c86094422032010034480d01140c052072020511040040d4201850058120b4402c20140300590b00d0007010450440445c500c4000e5a4003c0c100070b501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 797874226 1250 797872976 797873003
    0x70b040b0a0b0103090b060607020a0e010605090114070203060c0d0e010f0c020c0a08030d05062b02040f0902030c060a091205010e0601120b0c0a090503031801020c010e031c09050d 79
    0x8440c182d50315110902d0401d8605080c840004025131803007908500306840c62038658150380b01050f007440d40364000c4170001c3c100200014105601400500074000300303070b980c2406203120000074140d40c003807501d0003036041e004a4000303111484040c003d0942041d5001c00420f5031400c03040124210b5814030700c412052611400c4405280e80c0400c42201501c809940136048075152560f81d13920390094400a0141507114000300e04d190380c1e0300c0c5600712846022003d0401042c0385440d8910642d01084089004508203001550b0003900381c030a62040540290143c54040c510000300080f41e441110050b0501c00700f01c1c004680046900802c1d4000c41c443d6000054030300b240107490349445016032000d0507072075500103454005800c078084207030811002400720380c45200c8040c05961000d4a50044c9030148408241007200c0080c000c01c0c048040820f8081d1000940340c40c004445910161410030f805520009142115849803450387e000141d00d4078114803003503101c9001403518000410207440007140d8864 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 797875476 1250 797874226 797874241
    0x606050301210336051215040303150603050a1b0c0b0c0c0d0801030203060109020306030319170f16020318091e01120b01081c03020306041508030c011826070b040b 72
    0x810101038030302243e00e000131b1680f04c07401c04e40c0c90302120300b004030b400d51040101e402c05000c4e400825869042c9100310341c1d40c6484980080c000c10f8120303014403550742051801e520049440e00e00d400313051156031369220000c400d512000c2c1014000381c48040480c208214210405a05202c000703900b88aa544105103940345004162400b003068200c52086407042040c0b01b0169000001c03218034080c4035070048280d000c078260685081c407060a05841c3d1008540030042107280307019072148030b51018282180300808542d4126038a00030040c0003a800c0300300421110817440c1100c0010350021034a81c0070101090300c091180303084a401c0c4d20420324041c20816860410032031141030303805013540d50010321040e841c2c81b051203101038000c60101c042c143e000021443c03580b20f617004002da41000140405541c0e65a2542d95a41d521012410040d07501e46214021406242003404c0301303030781c1c120b0720b0026210510241ca41100d4520080c0b000a1b1000700304030000070302c000385124452401402c200200d403402c100c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 797876726 1250 797875476 797875577
    0x121e02100f0b030a0219031a19050403080106050c0a06020c030c0d0c021302310603060602060105130230160f0917072706060503012103 60
    0x10707610070403802d101054007580c40c0099101c1000ba0103c4e00c01031540540054003803c91000e80028268280b24111a078113140b402508501412450762402c00c080719a00c5904d08450040c1e400500040c01d4000400100b0b00c200064401e44101c0000d850324000d90f50b07500d50403070b4849134450030180c1001ca182c4a00540c188004003005009040c101d460f8131055002480b90311801d40000384556000c0350300c03e44000700c510b0b55805030b800b0050003801f000f00b05058051031403a5124440009040070070109001d84041110360495201400b011781c4c0f90b04100c2c0c2a030203900000001d103a19111500260080c003041d003000c102500c80c10b0b080c00d103d41400251406410305505801e01440003042c00f08050301c1e4040340c3c160458410118000d11041c02120060a10915500c4070f4422500b0001110103589400403c8503114540d000800050360b0f607010031b641a0109224401c03804107091020784021320480781c901002c500c24604220012281d04451160981c4610740c9102c0000d0004087d0165640c0c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 797877976 1250 797876726 797876741
    0xf090504020c2415211902030d020c06070f11060307080a0501050a06120c0216030c0f060c081b0705040e01020d050114030d0c1106070311010f0c0c121e0210 69
    0x44110510702d14011451440d00c030f0505000d13600032203082e0381d07142524038521044090001601d0136904906940307118020303e042c162138213038807070300502868121080c000540051b107440040e140c0303030410780c01b620b0312440040380c2d8030156008034a001c0b40300c03000e55500f0011481022103840b01d038424200410300b003049070b5058020368040c0407841c405001081d08800c480c21855108032000c2411041c425080341000c0000400000e100340000002c0104004800182c040e2202d0702c2d10391001030b54803182120f0003165094045e000c84402c0019081030310100d40801d91402c90300d0203e0300b4041d91000420115030309082050f1850b50301041c1f442d0310605074020680104030030f080d100c80325078200001035103440c400c1d0401c0041c0040f44104e07800700155003014058516000300040d448518038180501207910f41074681a040d440e100000d02c1c0000144603040c0c0329070250741d690a031068a0b60310108502d2165500344248015072541800032075840321508812007460b809418030031180a00c02c000d40702c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 797879226 1250 797877976 797878033
    0x819060608030a32040306020913060b0c100b01090b0a110d110d0c0314090109050409030e091b041505090409050c190e060906061c092f010f090504020c 67
    0x402580d04200012134203407015240c01490040c0e491003110300284480060603d8070a955003400c0c1c00103a80c8840c4030142c4507100c2080160780941c0e06c2d03040c0000488424443d000e022565891081c48a41078500180072403004508102d242d0070540d1100b20b00e40399808400800040e2545880c001d09070044c083d074090100c0c0e504000c400383e410795a01800d201c0c21244803000e50007000c11451042e0307100c1d114190007040c019000308104040c601300105034442c0103100c1c600841800001ca500d055040141804825006059074182400c09521100045030000c0d0b10080103014042d800040e6158032601141a200b88010a103001c00c440c01c1c06041045040b0780e400c80340da45002000000c03010183c00c2c1c1d1109084800c550300740c5d12000001c42601a1450310015506a00003542c22002c0c1d680c0000c0106004083d1140f44100c2100e411000c43c60012035400c080301500da0003042540a0704441211480364203065924030307180d102140807a00484078a52042d880100c20003c002c442003200300d00d50b80d2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 797880476 1250 797879226 797879297
    0x90b0d11031504051e013303020402030415151a280206010303090b0c1e01181b050d0201050d0e07080a050606100302090a0b09220c030b0301060819060608030a 70
    0x340701c00340300c5040c02e0b60011503580c0d1440c000c2c103031f170070010f4070300710b8030103150300a000f103440e820f050a02d0040072103590704100c04c5074a0242102408441822800101d40a0307000c004803030300c08240552529044075580914080c134002c0c0f0841c00c8041110b180c0e10300022030380108a00c2d071542c1001003282500e64440c5c0701d8500c041007031800c22140425000c04821501d480c110200e0152164203006120003d11038582c6504119242c04009181c0c1c0245128036000d1004101c1d19210410054407440481000340418000c0181000902c4181c200b40075902c43d2000307690100e544e4028850800c100900f00f20780d282c1003042004001e18110500e0001c10405107001c60070620ba4002141040500d4000e1314601c03070000c100111681c1d6000350749140c01c0103442d141c621030381c410031040c001303031103a0180c4402081c1440841202d500303051203030b14101e0b0300300401011038203c1686850a11183c0c420b0a50308141c07208e00c08241d080d02000140f800401a5550051300e0554070071304031040c140b249149404c4039 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 797881726 1250 797880476 797880491
    0x11030d0c030e0127030c080c011104151403010504050907184d0405100503091902060a051c090c06081303080646090b0d11031504051e01 60
    0x104d082800c80640d81c107051200f90503c85d03040200304c900540300d03010125802d081100c10400080070180044440c4445802c098280f42d1205841c2402040c1c40450107150500040059103016001a5000b030601070503580c000d078440740d03903020700e8207400310841c20303240c841030402c991200f00320040c403801e62016800110a856400010400015421240c00306810b00c03640c0c0300c601d4007180031a001050000c2401d02100c28512002d84550011100001180101803a80140c1d000d218030a40025900504c044e1403d650404150340300d420141029100d541c4800c0140c1c10003c007841940b140c10700038408501e4030b510703148004081d1710008182c9400744910b09403120000380c1044c801c6400240c01c0f94110300003010804010541c0d54040710310656124414000d9442c1800d2172050881700198510030400300c0e1b2a0310941c0291200c1e00d40c840c1d00061506641d00c08601d942c481741600050080540700c0c04605000d8040d103079001560180c90b01d4021032161020620103090886003540a50300074440c51 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 797882976 1250 797881726 797881781
    0x150b04030f02120f0a0b010f05030c0f0427051005011512090807020306190b04020a02120706020913051e010323010f0c0306031208090d11030d0c030e01 67
    0x4201c82040207008503149284040807803420b0082200c0d1030007400071903480d089581041c1500f55000c0c442c1c4904c0c5000600042503d09009c24a42c141000140c441c0c10542200c4040c80001c1001c85d00c40208a040c045a84140071508406200468003410040100203034003601142141e0741a0702c80b00059816480c6240c0c000d40110145002070302d0250000352040c442d081c200424410040c0007076050103400c08200c543c0f41000c150115450001908100f61500c810504c8103d1007100c02890250340003401708502c500c1600c0040441520482d4050b00f4121008007140107540000c104108442d203134010801038100300c0321040d071500b01e078102038000d0b545507482d410503880741a2420003503070048900008003545c09400241254145980401040c010080000c0082c045400100c44c0b42c02c0d000e5401d1666841203c15600070088140034001c030b5660308800340c5402040650059290100b445150418607451107200221606614003088150309518041d0131104080001c10707000c48000500b0015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 797884226 1250 797882976 797882993
    0x4080319080613050702150c0d1b170a0605030d05030a0c08040f080a0c0c0f05180702030912010b0301020a08180106030b190209150405090a0e0d05071a0a150b0403 72
    0x8040c4050f0000350540f0b83c0785d000c80c20104140c0300d0200200160050108024215000780511001d000b810040d405c51120003524024840c40e544000400040440d17100e1411541d609401c603000020005800703580b0404a818611201800404240c02200300503044040b8050005003454234509129140f42540e00d201010460f07400c017030b082140c0481c208550a0254100f12003540e0800703a41485160b4821007180524080d001d080d004201e01e011007141c0003914034856025002c0c44c3c000d141000c03440c1040c0495035640f120148829900d80840c04105e4400784000c0c02c044909958000702c1d441c00103848411b0401c3c0c0341c02c0ca03540da0702d032040400200d01c9890510360408001010078100710400008100071303010b081c400ca6030060942900b2000108850000d100300c800944034010680c0d2400110022a0303078504115516030131681c2c01d0749609200700d00a00103a441401c001c05803486844000102e402c0c2102c812180d159514142c820041c05910003100402c0780e400759a14290660b0344801d02d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 797885476 1250 797884226 797884249
    0x3051c0e01020d0c050a0c080304060e0f090619090c021018030215060d0204180201020613030c17040312080a0b0a050303040e06060403080c0a1509020609150c03040803190806 77
    0xc0201080d108010400c060111b4a1826040f40b84098860303140d1a9403601d940c40742c8203000c04615086140401c6041c1103c820f000124002c103810300680d135040c2408504400142d034049034860043c000f240c8082c003446042c00803605540184815440340c10318000316500b00c1d002d102c4070f00049450300d00090380002d52110b614001c0c0903a014545600020415240d5401b030002c0d03000341050755018100601149001e2094000d0b405c4070040e440e0448031000314900001d001e80090200f0b651f40d008503d084d01d110003481400304a05151651300d4890200f102c01d810002000100308a05100d031101c3c040c011006902c0301102c0b480b204615100000b03039248a240310b9201d407005443c0009034199920b10640d002143c00c094269074442e020342c0116103492a6020840300d16000301241c0b01c0081c0144108102c595010b051640b078120240200f0a0000a9003184040c40d10200310f0031907000c0050010340700901c402d134021601c6011503014004211111003143d01000314840c00c002040e85ca0582414 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 797886726 1250 797885476 797885503
    0xf060c0318040f0608030717162004181103070b040509062b1b060503010b0705010e16182007080408010203040f02030f010e1e0c0a03051c0e0102 64
    0x704007004071408640034004050001d01d03154a0014000381c0701c5808030041c024140300d1900f0004001c0c3e40302104000b4028000401d500c1101030740182c000540f2044401100d000703c43c4511070b0a030303092000405890549203c0071800135440e502c2400c010040780b580401c0764085020b801d4250400400d0702c054080c0c1c1c440c02c1d01c1054050041080c507212524440312180305003958080d56103001400c21248806607004482101014500080701003645d1181003e45000e56101482d40c0d01c0c0064240d43c580200c00199002d5690744600300e0301080802890140c880034020303080800313180a80c000e0961184400700e80b01141007401e01611260041403002e04816004540e546403010341c20300c0c03041c60195800c490440c1d8400014002805070100d404180c0600c01c40c2190b00020380b10040350309842680c102d500c002d0b1f100c40e41c0c20841040e0025600080b18841c3e045a0405c030004000646c10a4241d0042d62160444209842848894032107210200501d00300325020f034080300300003940d070000c594000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 797887976 1250 797886726 797886757
    0x907030f11102d090b0a05030f1003020307180e0610080f010603020d0f0c1701020d2d0b180f060102010b10090608100e0411120c0d0f0311060a05060f060c03 69
    0x20442c98090302c1c00b60081c05c0880010f9496800d04400901561720aa440c080c40c07034800000102c0c100c810f03954080603640c4c0600a400441e291520441e90340c0c0703901e09401c80194a407004a1181e036001c21540d40301c0c0556403180d8010764601710720751b030402d011341d004403a040e41015014005078949a03007003c4541c1d801146c5500c42c2486003059182030300d01d0380120241881d014480450134405402a242da0b0300d480da400c002503c1c07858039051080b001c580d580300303041140001d85425462950b01140b08854050b0040340c0b590803080780700100340001c490b0241c210000340103004103960b0920601c2e001202c00d40b030302484002c1190000d4607503400c9210340d0f01000b072030400103002d0a04c4a22108000c1c232108210101c00e040c54507103240d038820650b00381809855500401e0440000c0040c1d16180b002c000303888045105900d868900c42400a40410360a110300c43e82d542480102c00c21580b48140e16100c000038445c10207104000e510b160f91840745202d62000d0281d0086500d001c4100c0341c20248440c0354 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 797889226 1250 797887976 797888057
    0x3c200405120102090a1d06121e210304060501080304060512040f14060916060f05090a0e040c090c0c0209060f0a1a0703030b1002150907030f1110 64
    0x4060280c4620b884103500314103980d40006688202c00680c6000e06e0110b0003281e025554002070100c0120101d00c1196035a00c039221903088000240a490480b0170700106442606080c0e422550f5080c103010b51600c2d440324000104000d0101c14441e1a024242c104095440c01b85400801400703030042c90700326071380480340c000400c0800c01076803c203003a032a41c03001e000400381d1106620030361076603030446d10500d50740030b400d5054000c403100202c01c106582c503035100c0790307414102034204a810f80c220701e0348160461503124000c03c5a070704070345c00b171442188280a2168090b08194280003960502c045401c2407128040d500c13030060b61b5500d04d05038414800da801c0300180714030b40000b0350810419804030103c1d0341c0c0e0104195000d254100141109402900c0602c400142d14080c0000c10703080302c0e40740c0e0041e007000b520a0001b400d00088540c205540d40b085801054903601c58520b0102700300821070b06c41c010b0600b0380213281400041003041c0d550a080104464600c2442241054440341541c40b580380b5a158 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 797890476 1250 797889226 797889259
    0x31e060f0f141513090603060c030c0207030209010b0a0908100203041403070b0403120219110d17010620030f07020f010e0d15021b0c0f060313063c200405 68
    0x11800c0288817508042c0110303940ca04000c0d000b010030b07040c0c0c134000a08041c889400d10f8000035030181220703805400307112540c1c80c1c0445000d0a421140104042104804002404240420612044042c0f00000503a00e0500385006803908072100c003401140d4005100b0080820481c61107250710a8050601d03480c81c40a0b04500c800a00c580004a01803130362031440e02d6911580141003c4030040441c0443e841d00c215030030142d5100205034507c0344002c20007801400201d202e203003100b180200c460400c8002e0415400c02508540110000445950000c00c049007946440d0580700e480c3e140c2070804007072070b1706090003294401110030070241a00b0725591802c041c010b070a5040b90081080c40003181001152942096228007000300003510650441a500b07840e46401da04490003000c1c128050a0029041e540700c40c00f9041c02207881c80015100300510100454251489940090900d05450100c404c00140d00448031140064016103442c01d9026181c3c2c6003040481d8292413007140e242000c03220313805 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 797891726 1250 797890476 797890507
    0xf1703180607200906030f0709020f07020d150c080f040f0201021c090815070f230403080703140301050d020d110612072d031e060f0f1415 61
    0x20304507800e10310003010212805484a1080000304ca0482c1c05445502c1019915032940e000c03130040d074002841c1007104052540c01021503860030050f09040514640014000702c1210400b9030b8074071803840d501e44942e5858807a843c070007a001c2c20041d9a60030640071860b08031200500c010b01001c00c001d04d00055a00030400000038070043c0d0420050900a200010080c1c40f042c840c1440f40d1140704c6801d0014161245410710403086680e4801100d01452400c6441c0b00a1040e0400f4002243d00c0e640e100000d5203003b0400396002d6450381c0c0d82d0b20040d00d001050004114038500303c0080520045c8600c4e0b440c038085011854045a4114003c02642405000c841100d10490307400040007545280e0915180076040c40341c504c989a8941d44c0805c0740d80c0c11500380780000361204415040002005041c003a50000000240000d2490f85400360b03d1513610850700c284e0804984102400010058005c0c16411803000d0203c210034003800917801c201051581043d04c11020340e07280003151201c2190000c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 797892976 1250 797891726 797891737
    0x1a07081609181e0204082508010f0504050f0706021e0f010c020f15010b0304080d02310f030f082212060f0b0a171005040c0f17031806 59
    0x402c004180c02c1403498100240f10001e201c52402c8907080018030394007030300c1c426a800c0f00c00d0000608020360350300b10340070b0b280002c606c01100f12900401010811000900c900d5111401c4070748006268106814045d26241e51540a102c45921210080c0500759000c10301143c0642082000d4440c08224411f203810920801e00c07143d090341c170303041307440d50783c40e50001e50f182e04441d000040c0c1d0f40000046081e140e60440134007995042100400100340040d000c00020814004541c00050811030f820700320740210010b0032036440c00c1103416005020030020181440004080b40c1010300301051075a541c60307440540e0104042c06e03041c00844c41c07084500642100503117071000ca00d100030390203859501e00303035021240d5582900d0503850400014501d6040348264bc01028000749083c00e43da14004028001d55a038440d4110701c2d00510449890154481c002d89024510681890701020b04061032414031071072551080041c10490360440d0813212010048511039000602c00820054694020a4075842003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 797894226 1250 797892976 797892989
    0xb0a051002010209090f0429040305070201050702040906050414031e130803030702011e06030203210f120a0b0f09070f090509040320010204080304091d0d0c1a07081609 74
    0x441000210881316200d87d04c40c82c41848810303200100088468000100400f0400500c001d001c00705000c42d0155001c1c241d054070500d4203600d80000c41c1d0104050303c0300090116896520340082c0810000c1c10303d010390408060720010743c1802201c0104007110400c402c4810444500000d074050108581034a8201921010301203c2d0380303040034100203008000040060a22000d415141140c012150240d002100e07002801482c005618400c11401d041007071545055a410810000316507403078500145c0840f0314015842c240074030f400c80c100010f40e805130344124070a4901b0a01c0203415600c6640c45a04101c1510341980d00e206c41e0101554038000c0c0b90402540400405d04003c201948441102c0340349426003164040c0403c040711260a0740900d02900e40160001c0c4400d03c400202503000d400480ca078448103c05052410420500780800341d4000350004000301010018407031443c00e60401d000c1000300040962604580c010088000580703e40d010984280c10f0b100c1c5180b01c0ca0f07050024184 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 797895476 1250 797894226 797894239
    0x904051c05030709080d200f10021201090624020f010504140c12060c0a121d060c03280b0a090e1002030907051005040e0a09030e040b0a051002010209 66
    0x5000c0c1018205070400c8070701200146200030046600000841c0c0034412922980724514005140100c0000740104401c49070014401c26511640c45e4908021650780701c05c00300c0d40140e0740e41d502c0000066194058200e20910350070030004000c0c40b016110060b070420b01d162051001c0700e000300d00880c00c00c80d5410000956609040901051090f120845a219455501221001000300c0309000841c17142411801e0f26400007400110350f00017940007840c10188034606a110b218505e00d414088421454119a19030364008030100c140341c040181942160000320003504501c1c00b240a800c002c10034070304e914042c914500358a45a030340ca80d040540c01c440c1c002c01c0410450340380c80c281c50090079040403541540c0300e0040c800c08420254400c0300e015003e4003001d810181d0828060142e5000000340380300c1004010400012504046001d050183e0147e40e804980c440003418001c0040c158580c4d80303032050345882c1e00300c1c0e0140d0300d0900e0541290400c1d24050209903e03a40309a0080c060349101940010303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 797896726 1250 797895476 797895523
    0x60f160c08030126012a0c0503070606030512041406090f040f091106090a050d0f0f030201020a14040e0403081515030108011112010b0304020a1a070510020c0c090405 73
    0x3448251307482031461030108841c000d04548041400c0e07621403141c6214410104a060001c0421418502c4551040781802c0d0075242140c0c2c0d540b8030f903910100e001c1d2380b16650303600280700f0400306104003201d88032a84200c50030303d070902110709050503082d4402d0744241c0c000540c4070440e4a801011388038119000b40200499001c0640d0f0034048c04854600304d1314083c61803070408880c0350600c00d40740c40d140302074840d40b4001d051400380003240d40070b03070002d03502040c48150f079000082c4202004542c251080c0e0000d0389501036100d024028980040b55101801014001400980d8855107200d6009401d0702c0c0644450301d8207407010039642089110550001208180f0b95100c9269400450484600900030000c448150221808038016070500c80031240c40640108035219800d4095500a80002c00030030b803403a50f03540c24841040c07412124080c010303400304041c4c0074843c00b8004002c8101ca298800d62070102c2c140d03801e5441d41e04140001c0e2241d0201404542406000c11500d240c0d100415544d41c9281c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 797897976 1250 797896726 797896739
    0x408121906031103070621020f040b0c0a0b0105010806010c03080711010204120312020903031614030a110c0405161103070515100f05060d0b012c01030e060f160c080301 74
    0x3505100300b0384c02071245000000b03003a8803c6488805905c0b054480c001100650000340300a540403a90240350210103000c046140c4c0c1301c07000104402c42c1e9030f078001c003810034441c68600000c0c60168000c034144507084040052a0f40c1080030030f005180d05152400465075882ba0079101003964051001c11981301180c00b250343d19000d001400f4180c001d85904650469405160082e48265a58903070035410900218100224104408200c00c1c81110218400722010208520f585c200c0341c58040021011124003410010510400341461801c2c0d40900183c034040301c0c01080c1568440000013001210340c6000d01c400400e0050b9502e05600405603000147c01007000402c5003001c0c4d0b101c1c8094181c0800c005980362140c0f544070200c0d80003616803400c1400c274160107802401314014050602c100400340003440c03905880d000d4546103044008030540032138a4001001c0ba03016402141d12a8417540901040b04c2c0c408402c1ea5000365015401c05d0000f8450504840c003a204810041c02e8034408000420403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 797899226 1250 797897976 797897993
    0x5040b1321030f0b0306060a032909010c20070510260601021e1518010e01140703150b0702030307050f01020405040c0903020f0d2103020d0b030105040812190603 71
    0x1a500030320f040c00548407440425454200540c2c580350f020947c11800c20015019090604844054600300d4500180100c1072040c202402c07160910303183d40d0307010b1340d102107500b064400000c0b0400e0700e1041001c0c043d43c889140c1e01d55070f90194034495007280c1c168004041c8207000e00c406c6215000d001c105000380071080090303000016250507001d80a020b031850414450940480c0708915000c00608031034040138589080e8400c00b425682d008084540c40701400b00c403d00581400500480c00003a83c000c0240071212744117405410801050309000040001c41c0b01881c20340142d8429000c4540d07210300e144002445c52140c260300034083e00482040000034201940900300300ea8003645c09101c04c400c828421520030b051400b00179441107a50f00c0c111861f0402d034540403030241c441c4640c1d002c4541c0c0000a50454050154200006500064500c48066090041e2034000701c042c2c00a0110741001c2c0d036821141e004100003140607900c032200040c500003401e40482d803500f054000c02c10403591a8105500c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 797900476 1250 797899226 797899241
    0x30f0605062805031b011d010c020619090524030a0f090b100501090b0d02031915060e0613050904030215130201031a06040504021305060d0b0901080105040b132103 72
    0x1017402900d10004200181000a0b80a03100580da010b106035185c040c12107201404140003810070130461500e50058a80c240184220422042900308884030b004000303010301642e4110901803130a9034808900e0191350320036480c00000b908405074a0340d50b42c110100c0140a4561654546030409200ca414445075010b41f602420410010b107009a131a40c0056400d48603d20070707400006403c1001c1384000d100e582c050340d00401c614105260040c00d41036502c0a03242c0c0c1c01c1c00c0700c0522444000400c000c80d041050070020b04001c0d103d8500b040b1084801c1e040240041c800c107401055401e000070109482400114500000c5c544101e80a00303100c00d190050090b0b190040f4040391070006070a005803043c090b80e50700f481d00185000c2c60207080c902880065004071360840070001040001251035035528000c1c04025080850024130030b9518000c000d0014010780c06805c0c40c0c0d01d440180000300307582680055000502210701d42c00c009252800c0f055041800e100d0b42014078000212041c3e00358550043c10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 797901726 1250 797900476 797900479
    0x7060c0203121b0601121a04030e041407090618210503030712051e0402010e180108030307200606040209060f0307030c08011d1b0405190503010f0501030f0605062805 73
    0x2562607886c2c1c00f20014952603188098030b109504031302d9031480341100c203065034018840d00d480072203480484c2c04070b0b0540e450801810711600340b0004010400e503118585d00001c000500d40855401c1c0001124000d86c901c2c0e020700e42c082480403d00c050340c400c402940b03c0909520508503540d030701d090600145140c0c1040400b04800d03040c20041181c49843d01403016807590112440030b503903156503006581c0c4490510003960000910f84280c110390b4a801d907224000c10001010b9a603a00c1c002d0b10080038030700681c1c0d103044200307807100b01040d92000001e5a00d42c041e03420344005035035181c0c060000f40140107680d103c00340c40100004001c090340e4540c10103000c10945441c3c040301340c2d0701d80302d0b1110022029003102c5514800701002428800c2c084140601d44500198803a01c0c2c140c903a80442caa0350046014000d00495100e41001a400c09204114035806210340400c641e50440e40e4044180b0b25900001e00003589a50224520341d84001c0503014000c108164003400540c0340081c40409100d0b0f1103804e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 797902976 1250 797901726 797901733
    0x1c0504060612150c021f0b0f06070c0b130b0315041d030a0503220b2e051207080d0c0209011508040b150d0602030115020d0207060c0203121b 62
    0x10b00c0d10300d110b0084054690080303d50000701c5000c2000001880004940403c41c45002058510241d0841a8400c403400c0c40c60003182c40c81c107200c244007168101c6040030b8000c0790308100d00700c0410b08022200c010b80f0100c10f411a41c41480c4034950307203800031075000302003040c07000021311800041c070108080a02d2000d070b4092210b01d90442048641001554060585810030403035200c2091007140203590082414001204140d0283d20007480404506000c9a031700000701e00340310744000050480d80904a000384046002c90985102c4102c450041c030075280039507410b0251500d035003400e011301c4000c0c0001d102150b10681750180e0060400b800800d0980c091130342c1074004200c242c0041762110006c02581c82d600901d0321160386884900704018020b0403c1c00014860328915903c1c0748400c5620b50144d0310160302c95050150061030500e40090940555200020390b01503030fa0045502c608494203414140408045400824104405060341028080000843d41002c0c03d41c80116200d1003288400c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 797904226 1250 797902976 797902979
    0x303130519270c17060d06060305030307093f061b09090b01031a090612060c0702040b01080603070314030409060b0a110304060e06030a0902060706060e10120b0c1c05040606 76
    0x75541e41850840d1034044c00200740c0021800c0c1440041c1458040c454040050800e03036948515017940c2042d1800400200000000c0007981c918101000d6aa81d8154003a0040c0400d1011182484001d0382e00326030b0341d41148000428405503a003c241011070b04a2101c40c45038688500030040303e803a01502040f585007005c0c0009a5202e8400e41d012007086164203010780e8201410011046e4000b0b000035440407860040200d000c1d018020355001c1c99000e4245034581c90684100020f0765102c00000707042020f1642040720380e035000100101103030740005800b950700d41803072a02070640c802c3e60040340b02c03e41000c100242e14984400104458a07982d81c1e43c0b4200e901614180382c0307078400d500c034810014151071114041450035100440d082071610701d0000c1c02006a13804650145c00c000001c1e911180d6961042129011001e66198412841c1d02010006814116444000e0454803000390442806030001409100d0180468900011003041000c06d041c85451900141404990480d540e5041080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 797905476 1250 797904226 797904251
    0x1050112180b010e011505032e060302090f090f0f0a02130b0408070e28180803041211030a0503090c0307030f0c12030905120c0a0f0311030313051927 66
    0x1b900010003016980701e902e180c60311170380b04451041d00480e50320700c47c0d1103001862050520100010003080e00c2e480268480c0b50800800104031840f683d014024407184080010422601d080e0a9001d40100c1c00f40c00540c44060b1118004d003e902c030106400c0c6030700400442d2408030007015008454080b41140c800c036840b980b8036042068140c1d2800f8030002e01e052a48405048619250b504c9100484001003e8080b50201c03c1e1500c591801034801d900000244004c0c0300d14014500c4903020581401c401840305000e130155a4441c5200990400c8008400702d20001800d010030b0703808182c01001c6481a50310703070a1208401d280c0c41800c90314068105c1001540307600340a41c90310400e400d6160035412501e0302c03041c48403040e807060481c2454040c0c0c00003520700d80e50f4410007901030640401100500c604500d84040c9520506000b0351184c0d00c184410803840300681290400d5410035142c0c585080351580c801d082c1110503402280c600110010006001c1103800c000000d2205984401c2c001d0981411 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 797906726 1250 797905476 797905499
    0x1403010b0d02010c2f01020d0807020d03110d0f29090705071110051c15031725020a0509040c031b120f02090106050c0601050112180b010e01 62
    0x24100e40c0c001c040c04881034059800f0344a00c00030140904200081d1100883c514280e10811807640000f40c0501072900d105540e0410080708120500e082c00301d042e040c0110040d60750f0b80d1110342002010340320b80d80540c1d0030300405c0030745843e80d0840406201450344219450090100ca00c0359480b41001c03400459540c0d902d01e400e070903080034007802c0d601440d1184d0390103e50503070081c0d4054812103281c0c102c12545482d20100c00751108680d603201a1254001802d150003011590b80e4510070300e0402807440d0100c80f145412004407a400400302c62001c542402458481c02200300a40c0309616161180341d0b100c00c0f00c2011360103240b013104c05a006548038401c00540002c1aa005030071500188000d00004d000924010a50425103901460140e503070744240e4000300c1410011a51094211050402c609064032000d024115604069042061002c800c40d921041440760714100040c00030b403050b0300c0d030040d0300c1821058003003100400c0b400c80500300841860340c01c0c0f1883d03154900b0b4900000d200030151 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 797907976 1250 797906726 797906741
    0xa02040509012315041503020d030e19081b0a15050405040b01030507080406090203011104090e10050613020a0302070614090601060e03071a0f040e1518010312120507020304140301 79
    0x40900c002d1403041c40240001480d0b0b00b2141001c004038020040090b07540c5190250080742b1075541c0401d4154041d0600c0342d428000b6801003840580c180047c0489400461070b03998400b1078610005403607400000050003a90164800c513511020441e44a41450f03201c0001c10544206031002e10942d50b40000440072108210707120400200c0e1300000c40c0c00a40d8a420070162203000030000b051140340c18041100c07076401940b0a10074283c3d41c0310b0a034101001845031004d1703080c01c85002c10151030044041290b044c0015907981200c0e070300180f0030368646e000740d05440000741c01010800000072a044c02e0b42004c1c17000e43d5041c0f05445080000989180715080e01010001d000d006405010310b0420070300e64045411001d010410030511a4a450070100ca010704000c0c041c0e0700c600307412803c0107110003664464034403010303006d9107112600b4040c04d0b0003646003c1c1101d901c02e45000100000100c2120750b000b1030000305070030a09103018800200d5001025000ba2044006102c0d85401a90101400c807008c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 797909226 1250 797907976 797907991
    0x3010b0304020d1104020d150e0105030a020d1b0b0a1211180f0d060504350c01150305100b0607050604080c03070f29090601170a020405090123 63
    0x400c0001d005080c845070362030f1228410b040b5010791014200c001410307600241000c58616607601428907400107500400d00003450304250002c00c65041201207a241d4030b991401030700484041e04984c0030443c4140b0300110221082c0c5041d0384550700c800215916500c0200d41800040d0742e0400710680a6840c40385c0d26050001000180c038240300600c210408e18681d151590340022040300300d00e42d0b0703100c0c10101480c103445010006170b43d01d400d00d05210b00b000b8841f01c0018000304101c2080844200c0080c0385180c1c1d40c0360110540302c4c030900c0c07a0395000d84070350001c1c50460720307200d6000002c003c0c002502030f03101c609c0900f062100070106000e110303090061450141c40340e0300000215000c151104001d11241404000352494605076807074542e4880c030602400c851141c050140c40c251003c400c0071344410000941e407100c0c25800e00d014010b0340d0301d4041c01407054040040401480f029001c12050758042d41c0604140b01d07501c0c1400c507040c001c00707032031075061b0400d071003400d0310105070342114205441a010b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 797910476 1250 797909226 797909249
    0x21c0f14031c0e01090803040c03060e07061b1e03030e0601080313150512040b190203070e1e040e03040905060d0b15060f07050604030e040e120c0109080a1e050301 72
    0x840302d28402a203072640e1249074030755031030412001041600c4000c43c8954001d0008020103495031404004607100340d42c038003103650000c078410b02803180d1000c3c4090040380da8181104a0549600701540426581040a0413000d4580703c98402c040d0150070040d4451280010743c1c440380ea032102c000303440380300300300c40d2103d03000600c8801d1001c14103540002801111a141142c101a0001d44410680800359002c2d03a80840312020004603405a4582c03640400300300c0303000d50840c103080c000036045001d020440c0f449003204100070000c0550144404a042c00010024041903000d00480b0b0384a5021b40156025241002d00060031800c150850f0164039500490344255561640c0b003481080001180a44d0f01c10000c104080c940340354100a001964054405006182090720f0f024007042c4c40701148602031740c24481c4000e01c00d076000c502d954110101c85080e03562460004842030040aa403070000b0400071011685518541e8403a0181c00c1d0ba00320710780c007148003811505040d91203000c01d01c6440c80c0740f80c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 797911726 1250 797910476 797910517
    0x5160906020c040f02040b0406050c06070504061b030c02060d0209030601050303030f18071a04050f010809030f0702010c05070609030b0f0c192102030a24090207021c0f1403 76
    0x4003a070100002c13655544005040680343c0407409050341c8254041c1c00000c50104041d566040c00b84a985d8011036141482c5141a10304a80035205004148580140c06601260f01085c54061425561801e86c01022660385161038004c0d40003e4000a00701800b81c840c0d40c00201c0d56090000441e4020b5510071003c940a946401000061565084000d400c074042c4110000704810710303030503042103140401c28050b01c590501d01401030801c00d00e640c9a04104148080c0044500701004071000f0703c1081c2d0515a55403058001a13072001c030b680000502c1403080020000746150302004c01c1c03050ba8441d210400040d2182c1c020504662001d0b25940602d02003000310468100425012810346802e5040c150041c0d40420086d41d1000220b42e90540c4a90f00001013000c00280f42c03080c1c405d051102410107c0201e040031070706d90301d4a040d0003540107031903000626109558a4420249200200403841c042c40c14007031030600c10089850800321801c44d4400031856541c0400300c146d034008442c2c0d092400311031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 797912976 1250 797911726 797911729
    0xa0204080c030c150703180603140a150608092e140709062a1406070906020606060703030b060a0c05010b0109080c0d0c09020c0703052e02030a060509040605160906020c 74
    0x254810017044052120741200e03021503811040c5180001c081d551000142c041050602a4520000400400800349800041541ca202100c1c0c01c40660762075203000c0c41c15030350760b81850317107400c8881d00140000621003903105410180d0000e0761440c1220b807803083c0060039801d070860310303800000da901e00c000c500c20040078400a44641034440da1518a448181e044803c09044500207001c2e01000b510207440c0d00d0354101c10321500701300c0036400508034034000c036881d480c0c8180251103034805499548034000004003030040c0f500c00d412010159a00500c00c0f03a0310351040c00d000e0a030b40fa481c4012601c5508241280f0007d600801e1948200d80706280139101d00ca86030010410180303900d02d81254003004c1541c000c10104158406080444e9510b4010300ca014114140780c0d04d011f249075020315002c0d0744a0907a0501c041c0310006c500c1d041c1c02910025072203440301021540500b00e03580199401a401104000622a080d0000c034050211000100b038009a4242d04032400402030181c007001da0b002c003c00f04c095 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 797914226 1250 797912976 797913019
    0x15110702011b03092102040507020606130203090c03030406051c1401050d0f0c090902011e0f1d03010c0302070605060931170c0d110d030c030e01050a0204080c030c 72
    0x300344640f42041d40945c445219010008100c81e46402c00c074294401d0310308508140c402c00d904964640001c182c0c3e46440d400140c00c0400b00b1030951000b540102c04106440010084480140c000505403a00d0f41c0e00e501c0000c20030341102c2c0741031514a414084070b450302d4020b0302c0380301720742d550810800203940e0a01060005040350800704031412003a5030704a10103c0c1c19088041c02810901c003010031005000d0000500c0c2c464200e10004180324283e641014098101800e40c4d58241c250400345d403440c2d06580c0004070354005e212480d40550a01c1d02c810061a8035a0082400c41d1251004102d02e031140400e100380407000b219091a074840d010503c904540740314500f00c16107112159038015044999031501c001100a081c07045001101144000c281c4030103000c02683c01c411403500040d80d1a900000c944c2c2c80408501074024507a0b01c0744e4401c0c1c01442500310040c1000400d0090019040a00080009500c14400c4e214240103400c401402c81c40e010801d860442d02c01400401003070b404114a0303a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 797915476 1250 797914226 797914277
    0x2a060106111b0f33090a0501050313020d020d0b0a060e0c09010f080606091908060903120c0915030907180209060301090f0608070806190e100e010b04091511070201 72
    0x4601d209100414105165078503561504c03030389600d196144d4111000f400303590005500240d06018081c0f0811211080e070903003001c00396404840202c241041800030454080e4000005058a0240820000711218907007029040307994103140d2041c650f440c0d5025544078020404064005012109800c0c1010320600d4070a8010000600c81c070718100700100041e0002c5d030303441c05920108124490401860000b400300340e521070400000380d0701c1c0c402d070a10030b0904404018142d515003000800e00031540c2d202e03d451441d46410f40c4421541da410a200d1203540c55429100301d45101d8448070494000100c1c60013540c1842c5001342031141141d090003540009041610103180b89903541c0d030000030f1410000c200c00801800c01401400c201d04100e25490f61500801e40500c04049c1005c4800d9080d0380001a549445041c00d140064101181081a0b003d8840552569400f40c10000d510062107500c2d417010300001c1814008010707560a030340f07581010380152440640410410220044c0b050301d00980c084e07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 797916726 1250 797915476 797915509
    0x2010c1518050d02160602031806250c172107060603062a020309040b040b030105011e0b03060619020708010e2b0c300e0f010305010b2a060106111b0f 66
    0x241819429540c4140701c146041c0302c5010b445220031500240480c08480001074040385a02100c6c010207052000e543e83b103280080b0300030500d0070200c0300782c68405100b9107010300d51102b81070011a5690900c1c00180907a100062255010702101c507078245109601c12103100740c1900507604010b20441000000d208003540160040e80300c1d08000f405a13004c0c860384d800b8001032905401294089214000b241c0456004940c0c01402007060011a0755140c0589084124107040103400c0850710320200cac2002c2040c1d01c01c110075803c0c422003945840d404241014580c041c149081044e09009500881403681a0600004904560800000300f10344d5090510b481240d89110052189800341704201d445c80c04101da80015000c400c50307409803615580707820b800386003441d041c040381d41071606074465481401c2c00d4070710091122003004004582500e01c84020b00440054079495a5540e801400a054400c006003050007800b0b07501c4500a1088000d1200070b501030091449002010288009a1801f4201c00c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 797917976 1250 797916726 797916739
    0x9031e090504020406030c020f01090809090a0f0c020705010e06090f010806031606050706180b220503040806090c1f0c0822080d0c02010c1518050d021606020318 71
    0x40707010380b52400100001c107482c0c3e900003008042032900074200210081503501c6c40c0d040c441003001060303102060710702580084640041e103031070b440312210007003d14404400d101da04260711198400d401240000440b6420380711111103203620010044644140d50410741c2c03207009043d0304110303540714250107540100b0280c100d441241181a0b000b144544a901980007e60700085500c108038581c02041040e480301c07288005112096603440c1d0040380003d100d00031605280301c0300724410344a081c44402d1141c1203070030340e50385075143c400c00e035201d1104640700d803c0c40c8a07103102c0d00c0d01410142c80c07008091808003540240a07054510841320342c03000c42403d80741c805041c00300200244082c03a0400c0f502c01d0b5111100900e61034002181e0814a000754100c0901c10380301022805070740c01031030303100b441c0c0c0d80050107150101d003909801c00200080fa1928802c100c00d06085020440d0018642440b84815002c55200f52035065600402168900802c0300617001800030748d014070380e4100302c410003c2c0000c124 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 797919226 1250 797917976 797917979
    0x150c15070311041202010e0d031b050309040e06061c0f2907050a020d03050c090f151b010e01020906220e0c18121e071d06030d0309031e09 61
    0x11040a40003a0071103442d190b02155404d04540c0c1025403503021203010385101003110306d280c5014242c8609040201f0011008044890030004140101e8044400c02403041042c811140c081a40d5800221211030061841c2803070079156480300704040d49000da10000851b012040355543e4001109041c825005019210a0072400b410600030002d11400982c0d840c41d413203142d0514000e2800411a1000c01070502d0318090087da541088201c8181460544810041640c02c0c0d0200305021801810303130035100404502c4168004594000d100b110760700400901900d11540029802c074824603445640c04981000200c0c0707030700c503d007034245201f001491102e50343c0c0e503440e40c0c00d0f150b820040350302d041004400100c41c072099102200d01c1c05424401e8600d008074903600c40d84c40d0f96407200c041c6030300001030014040d00507031001002010081e0600e98955194590302c1449051045000c2ea0301c4ca2290054a50701884a4401c0c800c880785941c040d92201da0740c000c1d1002100659204490010410100000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 797920476 1250 797919226 797919251
    0x503030a230d0e01050601090609050f0d0503030906071d1813020411031911031f080d260f0c0a020f010905030705070602030724060503010c0e150c150703 68
    0x54842d40d42081c1d00400c0780c10707100e0345050858400a100300d05002500105000e126800600c1d401a10002d13a20380c10f608501c2c1c80018100c0b03094201c0103106100000402c43d9166000c59400c0c001d0607542c440c105c2c0e01c1d82c60350f065544a5880d00009800008204603800c040c0080982d40380c006e00030f01410380e070214990b000b140c00d0340d0b03c2801d0f00b20705040c000180104480303403184044070f180b042c10080101500c07903400c010301844003030035081000b840c04484403c08803442080500030241c4600700c402c0140c04860103020001c8221a00c10303010142d044440307050303485030180743c4a40c1900b200015155981040810181c0000d404a0214441c0f00311444040000b441038990f01e40c003a40045481c0c0100d03181c080d00d08142130b0041000c6400502403980040c040368080c603100c1e09940380e030900303107032802e03c2d00c2c0018200d40e4003165041d03003401c2001c02216041107984034500700c1505c105450821400c1c0012540c891152410384641c0242401001d000940c1803e0b0341101c442e00d001300f842c402d50907 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 797921726 1250 797920476 797920547
    0x2060403080c011a0303090d0633050103200a030e0102090a0f080706020f062a040608040308010e01050d0219091d0106080d0e0906010e0405011712040503030a 70
    0x3280d002c9640c1d500d100e030740c0c0c20141c03810582d8038a0030120011031810007035001080c0d49458200c030040006407a41280000071140c0900c60070802070003000002c40800b460808040309150344039240c04645800621291003a400d1030001c0002c01440041d4603002c08140f084008142c00f1113941c100c1e541c01e1101142c581ea80f4904c0e04002d250581d020601c1c603080801d180d007001050341c40802994071940c00c1a00712440482c2d1554080700e4502c6103da500040507109600c00c0c290222100d2000c4006004248150801401c82c0164040e6035013140680c1c8648a21404038000c2c010940e10100721a4504e0040c903048090384211003c1f440b85420b0f0541e40d6405005568104001220311100743e0300556140009101d114000c1140e4002492120440c5c40041c02d10f20301c4a100600480110b00006c03ca640944050551043c000d4020001980d49040c155aa07110381403100030a03005641407030031610079440c01e1720103507840100034500c0c090602000762150600e5907414041c0410800c5a20300038003182 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 797922976 1250 797921726 797921737
    0xe06010c060509011e090201091e08190b06010822110306090109031412060d050a0212071401050c102a080601030501050d12030f0e0304080c03060f090d05070206040308 74
    0x1040041a032050040980800d117088003164011249405040304c0540ea01400242c1102c003051000f4141b6520a403081c07010280036040100184200c410125030003102d003006d21000c601409510f1440d840e42c600440d90f106041d0b0343c1200f0404119590708000c0503101d001e9803124465603ea0b907400e9803403404641000d8041707da0f202c690b5501c45c00c800038150459402c00403094201e00c25454040000c4051501007400b800e464001c1c01c0348003118041040401620000c0c6800402c0c5450440c030f031000c09983c405c0113000f0f40da806c002490aa482950041059840d50513001028010311001c6640e50002050601c0e80082d20405500c2d020f80c5480b0003814000600d411a03907643c0c514580000050162031060380003600500b41458118089814071030440a4001c2c03601c0c000c100107100303c082c80b01501c0c017450300d100c241c040000c0004400d00d0003c2c403603007182c00a406541710342da2a101c03105074a08045500b15000d82280740b201350450310030f40061550500c010203040c2401d849450341806500078 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 797924226 1250 797922976 797922991
    0xe0a0b040507031a07020d0507020f04050a05040c0602070812030a1803022515030c050f040b040e07080601080f0c0d0603060e1b1c0f0f030c06180c0e06010c0605 71
    0x5210901c24001410610311204400030002d55035403e00c220000c7d507a1144d010b0140c20084045000d04c21551450407000080100400c180842d061900e03030341000701415202104c50b40302e08100052500d00115141044481a002a00c2290040c0d884100250b200601080c01307030380d94220141c00ca001c85146001c03007a019600a006101c06000c440f041d181e0100f071041010300c81d1400c1004076001c0808280c1e944034031841d01048805000c4400c1d05c050043d00c00001d5215400307d000300b440410007014100300c0d6110000e0301070503100c019003501c4c018400d803041d600080e0604c00146020750388600b520340007490304d1306403403400c140300512108460860b081295541d40b52811a00e40c560200441c40d283c102d90030f502005282d4070030018049200301026240314607260360381201400f000360b03480724010360030010000000b9880e02d0000c001c220352000c01c0303e40501c2c00c80c800030a001c7c44012654550b0344218108046814122270118020340102082d04104400003000c000031094000c60f4001c1c01e4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 797925476 1250 797924226 797924233
    0x405030a09060207050901060507060b060301080f150f160e031606030e07081b13090302060402281208090a08071a0f040e10090204060801031109190e0a0b0405 70
    0x480490080c04000a0b910040c03c40d80150424003040d0f90fa00e00550440d84642000c2d5035640c69890030300007030283c050030240c0c41300c000300001803038500201e0041e803101c140c9415601107010b01030500c40014810f271024501c2e043c00f140021030480103201c5008008216003001000c000c80c400000303140c103607100203242201020310020030080d03805000c0c414400070020007910f00345080c540c95035511460081000380b4499200300381c090541321122013070162185090103001403003260402075921402960101d004000d003014001c40582214440c40c90000c0141084e91210310f410107035a0f2031501c094050390280020050600c49a40c0c5500500084c083d00000c2c0c580c0501d0210508142c0881010000d0501c0c410860300700760290b140c080300e0035100002d1002800751a030040459001c84240c01c18032030b65100040105a150700182c0c0f80741260701c07405691104e20011303006c0c06000c01c0207075803411840035012224070700001c203074001c2020002034000312840c0034001d84440844c0bc0003654265807582 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 797926726 1250 797925476 797925487
    0x90b040507030203090a060f06120b160f17071403090c040b010c0503030a180c14040c0c0807060914010f02032e06110a1203230c070605150405040503 66
    0x409018140d070107900c07801e046086113440455561228075100c00100801da6550030a02c40800076400100a031021500b49140310040d4944400548001da41103c14042900b06407002240304400c250707200841551205065020300e00b2400101401800c1c0d80144159029810000c40518000d180f041c14080001c1c01c3e4101400300b48003c8400000c881c904008502040f480810000400c0f02d400603442c220014155800c1041c45280c1e00c00040300815825503440d002079400c121402d0707031080f024100c4081000310031f0f188064804500c0100001c050408c144a0100400c203568412110305020b486586414100d80d1106070843d100118403260320380d030210500000f00d03a554900501c1c2a0044011002001d03c0d0034400fa640380708d4400c402c10040860a413046019090043c0800158048140c9050030842a0081c001e0170031301c4c400e00c50041490448500359452072040340d024202126803185000d030a40c44001c0645002040000700606074440641c0f1350301c2d51710903240304900640185032142e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 797927976 1250 797926726 797926729
    0x1b090915060605180d210203191e080603101104060e041107140a230d090f09151802040f090203010608150d0501050c0a021e0a12090f090b 61
    0x700d9598020341c0070054180311101c14082501028009483c0441c3c4500e900b0602e807800c040024a40d482e10303000381c2e507080b800009a60b000000b0784603082c3d443c1103417000101450b10880d2014100c5c82c40304002803d9074245140a4060681305411800c0030781500c4424180b580c1c0c20080c0c40428800c90a0b4a00c005801c01c04c242d8443e01c480304520089409024904807190031440c2e5014040c00580b022100c0300404c2c1059000300540800903070301a074a06003004e64581443d40000b400c1c2c801405500480090058403441b4078840c60607601012040c84800e414100307404000c00c00075002c124000c8503210b0206400c416000c5001d102c007103100015a442d4100540e00c1886581ca90010101c0d1740148014010b8030781110303040e5441805010a2110104035800140c1d2400d0400700241c80d6510344400e00403090b000d81c0007801402c0c5e0305d40072604005120240c0140401c3c86025644480c2c200c0400400040c01d0079511086042c0e5514101041c01e4480c40400d40d181000d038020001c070ba681d2100285503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 797929226 1250 797927976 797927981
    0x4081803030c12030601050d0f0c0305220b090a020d0b061f17280501090b060a0905100201022511010516151d011a030601060c1b090915 60
    0x2044080e800365080c1500d20014681d1000076114410480c00003100040d05a403182080d600801800e01d814000d16680764258001801e144070014002410580016040381c400c060041411414400750901b40c900c41c0c49000780d00c40c0140c951640e60161100c40c4015035681020000c0c42c600411120400b4104401040005c44651300e1103940201100304414038103800442c0c0c844820b4290f0441c580f91707999100c103000c0001000d949040741e0b80080103400c01d0100c41d0341c40340e4142c41c0c420780104601c22078801088120701800950500061840c8800d120a080840550741c04004a00026007001c15101076041000300b02001d440c444d00c03d61160000744a02c2041c90100c1c4079085c240b10745040c50850004140780801a0064050110115419803500306644100203420341440620200010075407514060115560070700c0f18004519442810f900d00070601c141295901d0312003190044641d40d43d595910b0308a10116981001c10100241910aa001c0e0040301031152003440042202260001e04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 797930476 1250 797929226 797929267
    0x105010e0f06030601060f031e0e010c0e220207050f0a030f0f08010e09070b03070f090f050612151c0b1506030a0b042012010602030a170403020f060408 67
    0x40c001000703003030102d142c03000b240c003038151406450840c3c000403421030164060032003640d1005038191000c038080301c4205030340d02000c48401780e08000d100902d88030300200d400110711204a580520240c0100640c840c076064114040fa2084401609040c41921194146880000000c0c12500002c00e040c00305540421403001d4002d4a06081c0e9940207445401442c12405000308a109075103003010a82140301040924020030000c7d91003076403072801e40d078000d100740940112440030510007500412036500410340da905955000d010702e401e21411140460790401c0182030b0b04052002c4203d0f43e000360300c0745011520541d141001d4030710150154905280201c0f40181051407880440206007501d070f80707010440b0b811041341385010519080050021703008205a003059a040c03690400e55100040e405400741c007078211a090303032072416070741e45800340d840788160a0400700044100c45007660800f8603940b8950410f00a02c11200020b00d50103030345140400982e03003590107040101d402041307105a03405c1e090303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 797931726 1250 797930476 797930491
    0x709020f03011203230d1811060318010609020a0e04090c0b0c1510060306060903030522090207060b240301090f1104030c030b0a2d1d0105010e 63
    0x5140600880d210500c500041c007881c90100352a181da0000c1c54454480030708030f81c01d058480142c1c3c0004200d420500d61000042c408111308000000c417000e442c0c00000b264841d0044041102c403001d41e002c001c801d610041000442011442c1c0c40410380b1004d215000280c044210016511845514003420078400c403031465100d1070030800c1240c0001c2441c56014200c1d5901c0d0100c0e0340f03c042d0201c5050520000d00d40035a1800d00410810810019001d1040c2c01c948054400b000043c0c0c44900c1180d41681600014003c07460812030300d036038a100e010303919100d18034008440d19265120111030302640d01c40d40c001d540d06a00d0b105420810b15101303900000d2412112418103040f1350b10a16188940814070490003080d030340e004981d078040350540000001515451907a551070381c403460324040310240c034002600c2c0c1082038400108001d4407481221490b03222180405524200703032000e03e003100800c00001c24443d4840010420000891440d103503a19038102c004140e9604010903000c601c54000c6c080d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 797932976 1250 797931726 797931731
    0xf0408100603080d0c021905012f1606020403021201090c140d03051809010e040614060105030613270620070f0303060b2a060105031f111602030709 65
    0x810008107a08204c41802481c118007040c19050080264244018101074600311007504944808105041d4403900607003031000d43c8602d80862110b5041188842c846140c0c824200422012007407031549006414801e10840016290540702d0340803a500f03064881512422b03a4642203074108018002d040900503080401000c01090080d90020720151a400e0f809014010b00045d0010f04000085056250b0600685220b0203941d50354540311000404036000e5400038940602c449100c084409101d0060f50141e484605540340d0170100f103000c1d0f07514280303000880c2e518880c0308140c0f0881468408410345500000306400d081c2d080280c03e5681c4156a03c44a187c0ca808403c2c0c0910108180e03501103420580030130480308030b880c00723400034000d6800060441001042e95001c1307030b91030031200910074501000307940351a00c9400300c2c0350f0b00d541c00c0c020305900d80c00648000d40c540d15000201c110244103030304041024400901c00000b503512030104050000600c400e500d09500741044403000900203a10f04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 797934226 1250 797932976 797932979
    0x10f02060105011206030b090f06070c0c060e010c35030103051213031e020f0102061509091912030b09040b130804030b1003020108091501090b010201060b0f04081006 73
    0x20344030081400740030305104140c01071030b002105a601003000b440d4443d12112050601c0307081582e64080130605102c403441820005440380d4882d0481500341540946060100b900740ba10603138a000c940c0c0f0f00b850411152544020209420a1314032460840c403030115041000c5845242d07016600344810722180c08002c00040000400c00245144020000c10308651118500483ca80c0580942e50000d4001e0a0b04080c1402400700c920f480d00361039100700c400410220f1103400598031400c080380c0203a265001080355107440c2c144041c8007a4002202030a40d520101c68921141894100c24400e5a0480e44900c0c015011500342c45804c2040c842150b01d10a01d28055403022521100200003070040c0020300c8525080041e248151405150311589060281c5041081c001c0042040d20060340007170030b4640030035070307888011038000710921881c0c4040b20182c0c2012582c07006003412440d240c0c1159a5044001003051001d4050b000000a01001664035460100e030107143c1000c0454800352186040300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 797935476 1250 797934226 797934257
    0x20108070216050904022806080f071205040303020c070e010806073b0d0803061807051803120c07031202010b0a090b01120f0603150b091b130b041401 66
    0x14200f1a001240c5111641d81da520210340d041d0704000004179002c840301c4040c0c807040000540c49059864995954070980c0d540d1381d2056030070000796800c002040070f00614015240c0d0035004944d002d070090801524040e5041245c0d880c000307150313111350501d00201005011b4010184a13031900038040b031400040400c031001c0d41410480b17030769020f00e003c0c00180c03148910034021ba1801c1b1211107402095400742158a08059550b039008582c1e15200e48242c0c081180008403010089009103d640d564a081c8246400142c000c812843c814960501c9591540041c00141c01d00802182981304080c00da1a4550315000c04660b21240c441c40070b59040c550026500d40350314880001b00e5100c0138010a80000d01c20050340e1440031401c468444600b8080c80c03440d040b00700c2d0009011207100d69242c840c581942107052089820101038594400111000302c3c141e42582d0420501c0405490741d0a40b074607148418001e820019540049103151000c20108004400c844008641d140301b802c00070311609419030b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 797936726 1250 797935476 797935513
    0x221011a0d122607050304230d14040e160f0c081e09040906020a020c1507061508060a1d06090727020d0b09010b1305040203040303020c0a0f0201080702 67
    0x44600040041415400032072054051038079480001c035031043e00c050b003030a207401001d81c1d1045805807020701c110504c10804044442c044602c031001c000103440503040c206011035804c108401184509581407001003081e0044640d030502071194150100c0480403600c1001c2d084054141a14091016415409002c40d0140c012128034049805c91200b0045084c006011903010340c3d01e1894010349810140e00c2049051380c0100b686042580840b100785503000104010083d04240200d01010b09002080000f0b81d55040801d1100c2d8581443e003d05449281d824034005048600c0c0d28420b4440050820014030b14680d035100c0c50980c0060401858141101c950359001841800c0894251800354400401c520001911680b80c40409655403c01d680c0e40e81d000e803441c80b0005110340100c0c0000103260310454121000000401803540c07101e840c1c503003004000d4000410a0b01410b030200982148013400340511092644540e1b540800301d54980001000b00400810713500540d0f015000d001006040003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 797937976 1250 797936726 797936753
    0xe061005191a0c0105070908100c020c06180907120f0c0507020d03111f0e0a020d0602030a021b01021b011e110403050d050c0d03090213090221011a0d 66
    0x1550b1403500001902ca92103103e6440c161005500e004103020407a5403080d0190200c503c060112100c00b5001000c4800315107c6a02a0001d40c0c4038628405043c100300c1e0181440c1c81d00c8440d1510401000f2001ca003101074201e85103400105210306c4c1482400301c1d4802c1c6131004044d1101000444500c100107802d130b1050140191162905440b5842054810701e4003050300c51540301503c05103d1903500f00c0380c00714011360760036042c141080d000c50f4691070001412184950000c00640011110f5100d060081d4000360145008c0d075001c115004a1510000030700c40081c08003c0010f90300d202004c804586034a1000000880d0303410a22151320a040c00c03000d50503501403c00b000903105406c0f0105800d144112362004100340070754114910320036001405844190000426140040702e041c40480494940c150001d501c06854443c000426485034003140c1d0307041c0301a201c180100e1100e090801c50001401828003181c0d100d002801103103180308900c0d01c01800565400210703e005558440d071074000c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 797939226 1250 797937976 797937989
    0x11d03030f1b07150e010c0c0503030d0b0103060e04020102060f0910020406051b0c0f1219050a1a13034b0e0a030305031e1e01050105120a0b04020d0e06100519 70
    0x441f8090000d00140180b01401000001c0840f50f8a000520700b00018216100000e800309113031580018903402407400040c0f041d50b059000e482d10303503940561610300c207201820f20b003160310442007001e005d40003610003040501615106c850322094541303a42c03907024141c1704402549812500d100c1c402c58503142520101c5950807039101d10f40e81e15194800f4906181c081c1c2c03111540c0d02c01d911607401d10030046aa68a480e0141110001d8590080000401c0e11415205225030b07500d04440c01c40464401c01c5aa03450071099644e4001a41400d40d5040c010268030441400130030170005070750060b00d00d00c00c1c210703080f803002d04000030400078040008940302030903c805414400004000b41c400f103e641001030035608250040406400c1c071002c0c091200b070f9001c0354803484d00961000490190301407829a040b08803a0402900e0380c3e600c0988100107800080c10b60360300240c00b4081015141c125002e0802004d01c414000c149902d0008442c1e000ca070b000d07034004d602540380441c003041d01d02900310302c100031b841c0b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 797940476 1250 797939226 797939237
    0xc0c08030c12090f03150a050f160c0c03140609070f0f03060506030c060715060608060d021210020d0b1302040501081605040b2a0309011d03030f1b07150e01 69
    0x400c0c00100d01290400c41e801c0b03500d4060400850710304c000b107004187c02107000c024100003954903986500c0d034080c001d90b002101c030313245507101d001d21a1184c903010803428800c0342c103001c00669030740e21400300c40d40c1e070960046160001d204210a402c1d0401c690002400080c1000881d540f410315141d010ba0301c00d0201914440c0c40c0c1c00050f07416107040002040a11000d00015924846400c1c980f500300b0241c03910070607103820a90002242842001e0f0580140c0b401414880602c82650801c9464450000980214011414500c10a60980c40980070182074402c0c003081200200e402c2007003440303032000c3c80740e042032040c4014840e81e40d000620039807160f04010002c0b0710340300003070080e82c0c1405940d01800c9807000000e0350244060080c03a100b8085880300c0c1001f405401d2a014050301c0303001d180c00140c00500d4068445ca03030368690404c40e034021701020341501e00e8401181c1c40d01c6017940c0044034004000041c1e0042c0c000b131000800044004000c0360052441d10030a01500a201c0d58406001d1410000b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 797941726 1250 797940476 797940487
    0x3040201121a04020c030f0301083d0c0e04050901091b0803040b0d060f150f030501030b0c0d0e100903080a0606020c040b0f0d051b0303130506070c0807060c0c08030c12 74
    0x10402c00847c1e0b0101074404c421626580e4481103541c0d5440780c480d40c00c1c2245800801ca01c842000040c100b01c0c1d12031a440c0c03154440b20007288800c010300040030b5050400031000d40002103511240b00f258041c0d0704000c008504003600342403415421400808a143c0008150310402c0300c0c160102c20b981c203a99020b24182c0d941d0840d101c81801815440d0807481c039000003000c0000e4060800d2017011554489900c43c855000180301c025402c43d0707400d110140503130004d14001105602d1103002404080014803000404054074448640f40207129000380c502640d807551108181500400c89682c0142546010700c196030a28400a4440c1e2500342194052a281c410402e1259542981410f240c2d901410b40080607000e1b080c182c0e594011a00c0481480026050482c00717414084111084e07546230108554483e8070384803d01c61030b0b5001002c1520806140a40070801e00d00c1032009d04000c6c076640e92042640480d0f42001710340460395510200c0d10341e0040210108400003c035944402d40c1c0400c0d005a20b40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 797942976 1250 797941726 797941747
    0x6040605060114030703090b010b070210051e0409060501020f1902040c30061e0e0c0f040815100608060108040309150c050c03030403080409050907051503040201121a0402 75
    0x5000f21081802404004010440d01d03590590000b004e060151001140c0303a645c03400c00c00c00d00d1080000c00394000c0b00560140c035030707140210010202040ea06003040065201210300c18000c0c1c1003030b0408042d583c2ca0304410400d541c1c1c10404d6025104165000c1c01e6050782d41c2641540c1c517901d555009019039141d01080c1c3c3c0d024080c54840350301c0384490a011403000500d24912040c440035407001e03104585050303000300780d9800c05030b01e402c543c011044120b0740341d030706259080181600061490004040410150124581c110054801041e2250040c4040e0f0030000490340c01300300c010700000059400c680704001b070543c1700c800e041d001402802e00700707503a8859041c1242c4601c078a4102d041200d418070b03240c01034550702503030890425003d0001d8861200714501016107910ac4c610000e414034000b40401d01620030740d544540d40010a08049031844e41c2d944020a64640310b20034045400d100110402041d56001200041915040c00d400c1000304501036048104010702d1140a000300c0e80499100e10340c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 797944226 1250 797942976 797942987
    0x111317010204031a1b09060f09130e07090605040b06030a020a110d170604050708061c0b040b070e1909020a021617160e0103410705010c05060406050601 67
    0xd5078205080666004c0000703181c099a09007901d049250320003891048100320300340800e0b1441e0607001000e15141401261003240c1640144541c00e52040500050407a0481e840c405c45a0b50017202015180700c07850700c01d50b40304603030040e0b212902640c2090b542c500d60340e51703900413aa0300200c1001c0040c2c480c5000b42c02114400c640c00719861080c0b1641124a81094100c440314044000c0901410090ba40e10001c0c042039403800e803130b19000701d51040041035492901e0180741c00104040080c0c3d41c445451601c0d0141244410742e825140000180c0904c902c246d4400420041d01206482e5083e00f09040441910048014441c8040007030307000c43e0100c9450310030b008600c45a40521416842d0503201c0415014164a000d141c0790244202c0710510302c410799800d000d03021605e034403200c8a0140c1c616217910a000312030a0a8061201c01200c10522540c4854a143c00f1517401c211040584004002c0f00c600e4a1440d07084907040c0010100010b000502c001030482d482030340b00001080c07a84640006036507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 797945476 1250 797944226 797944229
    0x11090a0c121e1a12031b01150501080c0f030109020310080c090a0209060405060d05060910080a1b15080106030609060803090f03010617060603010501050f01022d071404111317010204 80
    0x80c07000301182c4c040601e89001018195a05188113450544e2075164070050072100402c14401121010107010001e83d0b001d40541c0e039010f00a02400d500d80544e10402c240660b109801907903001c0d03404810300441506650413103002d446650700400a10000d4400205141c0000f0b01d00c1060176000120042c42c0c0c1c4961050700d004180180c00941c850079081d001e10050b14088911901492018000540d02e10107100b024089030760400160180b5089912100c40040305801403e801c103006180018100c803103102c900070100c0c0c042c0c2c1e41e40001d504010006094480c25441080758604154003400f00071000b008136103003d171045171512441c0304c0300008203001d406582d0095200e25448244e4090342c410201c5c0d49841004224000c2000340e80303a00402c002500ca1b9071040b401070313201076080702600c80b4401150b6820000c01c8244064034003911042413424000d5080000309602c04201e4005900f842e000301c58a20310202c00303290401d296070b24200340070070240c411181104802d100101080c0b000390304680 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 797946726 1250 797945476 797945479
    0x2301090807031a06010c020d171207030e0d031e0203041b0b040603180c06030509010902030106060c05070e070816050c030409060305060a0507021911090a0c121e1a 72
    0xc60301566428080803d8040010109402d046000054401d61144201c00714195005143d2803403007049441d000c42100c0407060300c48100104002002e0b0b18024025074920a1410395070126003901d0000e507403400d08807600c555605250501c80300d410680d02c1c0c0c025001c0ca44a02403001a11380e078030341c2812600740b11040d500c0c0c41082d49401c1c0220b44a0410b80040c010b44480e80c41c03c0c801d100f100340c4084100032080a0150017502020001c2c40350511030740116130070112103030010454400a800082c00c56a043c0d0210340400d4050b14202c082000603ca000010300009540d0012881c3c80a400362240c0b4004081144d80c070750500c414030341e481c01001540e103500d5464044986544e140c0014500805190009503010711030350700010724900807406101c1c41981d5a50241c101d2060b104029245529400000c0f9110550311b1012005501c0d5400e041d0b1148810100102c0c4405005030007400403150b6105c00324100d03007458003440024585000d2604d071458004c0b800254892607100030001e54141c8034085 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 797947976 1250 797946726 797946733
    0x301051513172505040203070c120203090102010c030b030a02270c091c020d110a030501020c1b030610120c0b070c06030c090e0f130206030408070501060f23010908 72
    0x40b50000c00b40c0078010442041c07004403202c01c5807a6603a41480a5401c00e03007815141016014402170505402a6404c140642444114100580d407211480c43c40c031405100180d10204101429613130902803035074410480d04042000c402445c01207070f1501c00c51f4001078002d4132065603051401a880c07000700b441c03000d0034000301800e040c0801c140400d0b03030200035050710881c240c071001102c5010f8004000000b80d0b000b082e21000c100e00d540c80e140d100d001c00000700c1d0301444034100040820828002445c001400d2000782c80d008202c000d080f00200c83c22081c2c075001380c1c025420000341400e9140e5140070380d084d0314002d100301c2c0028508402d80b50b4603908080040c107008244403080064011401d0140c44282d1070612100e00d03024811a5218081e228903810340f10554082401e905c41a800d0036006000141c0d081d141820940214100d54020785049030140700c0001d80200784802845240042c04004940012440c40e003905403407660b00d803d801040409200c500c0c0b040301e80c0504440340003800c000069 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 797949226 1250 797947976 797947979
    0x6031112190507060f0504080c132405090a0c050f0d061a0a20070302011b0c0f030b06010804080f030a0e0706020f010e0d1e090315020324060301051513 67
    0x8151951094030139140401e001007000401d0034007840c00d44003034038003000003407541101d00810000329403060158400700c260741e40100100c15039080c583c550000407030110b030b0888501c0c0601f40500c83e003005081c4500d06140c202955070440c0d000d41128a0802103406268032001242d800f000182030950120442300b00100451002c042c002c809400c0303850f01600c071030f061103030500b6042d6100c0e80d0314940b007112034200e050140700541c01180304010048085100c40780c008815a52000d40c421705030030014009402203000c00800000c0d02c88154890420318200000307003040d50303c541050050b030b07600315981007000c00060b810704803541c400011400414112400d1907500c10020392600807e0702004440d5080c020500c030340302d00001c0c11292038401955a0741d002e01c400c40c2c0e034103000300f038003a81d960421000f41e000001207642c4180c0b543c2d000000200069a80c104481e40007100183e40c215001030b2071074036104018035542d00040e641114000e94480c000c1d1042500d50301042d20600c4000d80f022541e0400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 797950476 1250 797949226 797949233
    0x1022a070b0706111c1d060c0706061e0f1202010f03050411030109080d0e0703020f06030403051608090901060c0201120f020c01050c070c0506072f0d150b040603111219 74
    0x82c483c00840c40c40404106140c5c6c0c400300070b1140d66031049004000da00c41d401203001c0007444c3c0000c050060145000242c1d9a403903035103042c40d031800c071354203c24004000c03d4240280400c0021110040c4561556003902e02559030010382055080301e20b00b02416a50b400080602158036005491030000500800550001c1d25068240d50401121287e43d64500321074103130b00303d00020f1120292600240300040c804160300c2000072aa20090049040000500c0850021103d4a085007402481000d9203500d9a10000c10f00440400591010702000b4012681e1030150340c00000209000074686404900c03100398800220180c0300d103050380c0c10306620b0f0804101c0202d0720403014103a50f5100e4881812039660392410010540101040600842980e480302281120313441e40701c0c0c4030000d4a400c10803901200400040c458120090b040d80c10100c20350000c0c1102e00c55214480080310300b290100025801c41d12110612040314211600440d001c02d2508840034040190300030040c880b0368143d020180515 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 797951726 1250 797950476 797950507
    0x50405010f0b0d020a0909020109030c0806093d06081f0c0203040501080a0f060e0a0218010201020316110c040e0708060105040c0c03031e0e01022a070b070611 70
    0x4a07250034585864404000c910f040a0310a2010780c000b41800756060806491000426806030100c1c14010b45030400400603003420064402020503101070801450b100c20102e0500342d181c518080e41d5594180104061300c94030f06070700d02110b034200000c5070704420540d0740070013403c036900800c01910030004040d044210030310100010400601c010f000c404420b040030307680d0780118042d0601050802e000290102582c4e4002039200044510114409964020007940301105848500009400061b4050080ca140c41e0600c0007210a2008610b1841c1403c02003003e120302d01c104008200701c800049200c1c110802000481020052007085024500c1d41e003141d0350303460352240c4400d50150000010700c0d890244180d00180e00151a000e0314104182c1c1c04074000c1103003c034003803c201d805964031b2a8042842c418460041112400140d0700c201880c0c80200c480c8000358003a4018040c1031940107501004110348045030440490251100d5091804001914010b802c407405044007084a21003010041d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 797952976 1250 797951726 797951741
    0x120e031b0c090906060904080910030f140f010b070c09050718121104050c07061b181d180313140603061e121c110312070e0103060905040501 62
    0x22161100026014052100c004481e40240d54001308001060b504000840d540d0041c450070b0894900401c00d00001d1088101c480e605000903030720041d041d580c0019102d0106c51354800c400c0601c0074641980d40c180400814040c2154409000c185202042540051a00a01403403d401e1001d8501280c000f00114500a500c11b031040441c840010000403d54040d001c0c1600810410707411409030041c400505000741092010220400100c40030a4031441000c8901e08000b002400e1443c0c03200f00100f600000e4400050703071a442c81002c102180303500d0b00b40004010084000b900c40c1d50b034003c0c41030f8010300345048210940000201c1943c0c118580071148181c0b024035017103032100e4000d04140031860004070b84a64100341400c20700046076581c0719128204000042c24a02801e0f000c40d0310505100c00c50501507400c0d41e1113480101403e4000041c007074640c0e0b6450041d820614854542c11014001410082c1400f219554000c0e060741b098000030060400c00b030040c42103003060b2400a000b042c04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 797954226 1250 797952976 797953027
    0xf06090106060525020f030a0f110f0d11120304060207060215060102150402040204120f06050606070203150402010e100503070801061b2306040b19090f03120e03 71
    0x2000d60201d442c0780918159910800c141100711503200200c0222241d103010f9010580e400703d0305051400c0039640801007181498890402030a604460786094910302550b50195403044611000024154441c000d0286480d83c001801002411282004c02c1001e0b0050b03c408455010004011031007640002d41c41c002c842041d422600010060f0f141280005016030ba41c1c2c1c0141c01283d8000450070003c21303925002800100018905542c41b405144000005501241d0071407803c00c400302488258031803903620110949541d4542415035000a889000301680100c001100e40f0114065910170016070f8400e24015100d00138000d4105000ba065400031145400000c0e0300c3e0001050f03641c80750380300c1c08040b082500807041d00e10595440004c0400c40f4180035845440120b00001000d108000e814016070081849140c00c0c04c100c5c0b0460901c01c0c10601e083d5469040040c034000154080da10450425054903180c000e5841c0c5511f10700190030400c00c4002c0f03610010502c00b00c56600030810080c010365 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 797955476 1250 797954226 797954231
    0x90603030513060f080612010f02181804110603040c08010c0908011a150c12070f020310090f0f080d0509011b02010509100c0c0506010b031b0c060403110f0f060901 72
    0x29100411200104d800040e00300040b40603001c00c541d8140318009030031074403020002080c0020741441c00000c0342c20038641d402c0050800003019400b8207081c02055114005000e40c0705140ca030544406021000440c00b150282000000040512034051040400342c14650700901c0a40305a50f80144018168041c41c17000313510300007540402405445110102910140500c0b031901c007065540003407a0080030345180310780190451b10141c82d100200a0807018498070409000c0d501381e0050500e071003441e0082e180c2d0546042042000f1500c012015890164001c90315100300106190804840c090000c170000400c1c107040500c0301480044d002000d1b0f440036a403aa1500225480c0100e0070303618295a034102940040040b14060411600b110004941d2420070410011180c0d44e07803803070510309900020004034013009002c0402d00c20007520b00342004c018455414100300d80c4046803034400180c0000c06010000c0c20740b0800ea0b07030074030041c1ca45001110036503c00d1159046501e440340811642a0401d51 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 797956726 1250 797955476 797955479
    0x5031b011b03050d0b100e061602030f03040e090d050409020307171305010507020109020f0d020d12020d021204050f010e04180807050f0106120b280b13020a0507030513090603030513 80
    0x201b800003803490107490740d54007c0e00f41e484401e1040623409004000d50072244d450246026803030400014501c295480b00a554962402c141c2c6103051030050319100c12501f10803010079005500805850035500358540050b40c1c0e49039080f0646103465030000c1d00c0b1000d02c2d44005c0009a80c000d88003880560300450007800740350b4590800300d080740c09500009500100c541450000d81c2800c40103d44d811b440a001c005a8001d03944983c503140300b5401a00d401648400c00300c1c0803656040c401030840c2d140711002a411309050a0001ea003113a030500712141005801540184c1c2a81c07903402c0b00d40760000740c4181c407030001e103e41020324690b4042442174a16101b8500310340d0540005218200803180c07514100003030b11150f50341d543c00c0e00c400689500b1249028950f10f000d0021510210102c668103400300290aa001c0c1062002004105041400403441846824030709908502101c000f990305180185e90ba040905503901070b8452038004036501031400b40007208250b0040000e01111850078141c10005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 797957976 1250 797956726 797956729
    0xa120612030909290a0b070503301503071502030406081b070b09030903100b090a05040308011701060b22170703080d0f14060103060f05031b011b03050d0b 68
    0x40e25074002c02c401c2051000d207103444d0310860701480f85070118001c01d0710b5421551908071040c1c642080c0f4003501c8507080011998001540b508424090941c03802070000002d40d244585440300d1401068030141d94007612070125256024041b01002e0040c0c42e0100000c0e20b80301100070341e20341043c061000841d015002254400c80030440314200380c1c420100c0b20380b800c081640d581302c0050300a007400d0321620007442030561666090160140c1d4000a8000240786110701d001c02045c2c1502038040c0c030a40d850034003404042540091030381c0c1550381e0041000f800d1a0b10850b107034010281a03000007000140031403032440c5480c1d460010001c1501c000290f400c40e644808030000c181c48040710b8a00c15070301603001040003c1840000d802420307501c40001413804a001a032400399503400f420300c140400700c102000b54540c0c040c82500050450280c00c9074540b0b04050102e5903400a66180a80c2010101c666110983c0b10765041100b5200c4644131320321011107850b025005400c801c1c1403420301d5041c24201c0d03055 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 797959226 1250 797957976 797957981
    0x201050a06050607120513030b0c0901120c0807110c130e0f0d0504030f03050409050405010c0212070506130804080d050a090b0a120e010b12160512120a120612030909 73
    0xa0b80d812540041e0540301e01c5c40d041d90b555000d5082c20000e02a8044d001002ca415007090740e12131b081150000303590300081c00004000b080507a0381000d0f02031901100781e10440c0c0c04100c0c00c0d84038040c0d0030682c03005500003580c14580080051141c3e0f00040c81910420a5030351500403c519580c42422640f0a00005952946403198103012400056040c4410030104070148400e900c581d0290601600c2c082d124000c0c00e06882c4102e40c181e0f0242e44414901810681c100820355620f40b402c0c24007420004035a42d42ca031034000242144070f4140030400110248002901160020580c082c121a25119032180280642e0404811540404c0c049400041c0600d090002c1352000180c3e0394445800360341c01c0e90210300900c402000301103259696014855541c40c2c41d0111200800a60700401c4071100004618160100540203140503c40030300750403c40050009010529a07000b01c0504c0e201d40440c0710480c0c1050a02c0381c18403045082520002c3c1161521400045807402643c0d5031400320348680c490820f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 797960476 1250 797959226 797959237
    0x5120a020406121203200c010e1002090f0d080c011b090803040b091c1b031b0f030b04063207030b0618040e010627060b03040b060316060201050a060506 67
    0x13605010309a800228480c0d88450100545500381d0060795054645060182c0c101c1140d00e941a1741d00c10110424480800103203014007007c0ea0198609403102010a20811580561302e0041c1e101e1454102007019180c2500c2c2c0c0c0c1c041d07881c02001000200000081d51242800340c090205824031008948000084202c40507900c4d0350811a292000040c00d2202d00119212000d10038006c411000d40000c4500d81c1c0d52001041600c3d451030014218101490161158801a0354042c01d1500130030a07001e401c003c11044a8216a89084a98450030058080c00c490408ea44030303584400305150040955800c040c0740256400540f0201d69100c840c00d40c100c890580d00503903c010240054060380b1407a0b40c440320380c1c0001400100c1d0b110400e603809429111a500511080340050f002c10032084c080d41040c914106191106000185c54001c042c000c506c4041e10150010380344000003561514100800303545403a4030100030a61644d11107000340200815189052040d042c15000100c1d03250030410b584 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 797961726 1250 797960476 797960483
    0x30020712090b0906070f11130f0b0a030f24020a091404140f0a150f0524070b0a022503080711030d020307140406030b03010b042a0905120a02040612 65
    0x5d00d41a846d4648070040001c9800c22900210000301d092a540c58500460840103101000818032a140580303180644010701190341c012a00311104001040030780040524603500040026492403100d03030790320f14440144801c450741d940005040c80400e5032100d40300c0300b150040c034000041d1003045c10810080d5607a02c0106141000c01c1c4002c508144c4292840b01d41000121100190319042410740f41d110904603806111545101a0300300b025003014500c660742c5643d0136441030010740c80032001031040d006100c00070700f9171000c003030016a411206034121010003104154181c070741e0208013512002d1400c1c1c2c0381704800040408021a4002c0c1c018000300464842130f0000e50308081e6040c00c04402900001d10078010040303410310400d21100c000700100b0203400d1aa9000c10300c01020f2052500b0740710710b000000c1c00b4034540000e841c0104086045500c0c1d04050b5046010030070b61074907048584224035044954810310300350039102541c10024070080102d1080e1024807003560b9402e240710000f001c988025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 797962976 1250 797961726 797961739
    0x2010f11030307111906090203070e010807140a09021c141018090b010b0307090807063203150f0301020c03030f131a04030305130330020712090b09 65
    0xc0c0341da83c02410032481380c1921104031100d950390826580d104529209094804542d980550415424140041c101800f950154441954074100800b99199441d101d0a42c07071010350032240b0120b40d02d400c5c0880042403e8072055448010540e1800b400d005459000c0812a00d016010b0754104201c1030a180b003810044031b2481307401d240412410494600c0c1a9907100f15a907001c82200180108030818042d00601d42c1040d200d04e09240043c01d0b0b510b440e0801a07082d17001030380400000742c0c001000c0340c1507100203030911a0036011070000d025280903151a011800000301c01c208041500d0261400d00381022500500080f54250074103080388035140040b50180c008000040740d2644011a007600081c0192903401c2820312519005000c002075070312200c0700d56002c1f05100526a1502804d50806048128000e0140e9541da0280c003040701e001403d211204c0c0950392b1003006645c0310400807a101700c480259550b0340a03180c841001c0880c070305820003041025101041c002a50400c0c0e40a0f00d80c080d082 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 797964226 1250 797962976 797962981
    0x3070f0504020904060b0304030203071a010521030c1b131512020a090207050a031214010e190e0d020d0f050d0506060f1b010b0f0a0306110403051902010f110303 71
    0x2840040d43c01401d140da001a110351700000c0784080000150312450003035000d0340d2188024540441130000280240c03e5200b081401841140d0318800a094403000441c140883c100815054500314000c5508400e414003400510140d4900f0784031440c40c20900c101c031036000c040d5140b9400012a11801014284040d4211090208104a00540d000a40010045240241d03a82d246000343d9000e503108860070303000152070310100343e001804490701c0007802c44140144091450303000541c0c04144145040001c83c50b011031a001043c5880c0d91544032201000d02514185d004100d50303c5c3c4000c0f42841c014071a04040245480c82550640c4090314581d940078502880c8601c88009000701802050340928100710f81450152080c0080219117401061003103552404000c41342108c2004400e41d000e400c89017801042079030f13600110410b90307071300403070004550807244405d503514010b40e0402006d074490130041c800c05940711721036108040d200360307200050050202e42c1158241c0004100080e04c0d80184007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 797965476 1250 797964226 797964229
    0x806010807180b030c12010902131a0d142508010509061b0906031509091207080d06050a0b070c05104d0c0405090a03081f06110c03070f05 61
    0x22801062200800b152070042a000000d21a078110020210040c0c0d59550340508604000c40d010b040e040c0040d04c10024008001d520503d00074405071018407802c0f10300c001e40100b00c10b031001037400d282103004641d5504468081658000c840030011135400070b4480380020040c105001d0144240003a00180c21300b51034280b076920424004520782402a202805102d5290b120341c40618450340d229207403040c0c3d01444800f40002c000018064030599003000c004102c0346a20b14040b10321440d4003800240d95824403071b900c080240025080594001a0711900040d4800c2c1440a40f02440c0240008806290b50b03030f0030003800b08040e0702c2c8000407500360307910000c0c400030000c2035100041c07203400c2c82411140100410460081d10481450500c4d4070280c0d1030b0010304e01082003400880007078900304481d081140010b680c3e43c0c81040000c04109028000a50f006060349200b003d4203459500b0313004071601d0b1107020f060303c0e01c1c2c090042164481c40c0100b410524001520388212800004a048514100740 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 797966726 1250 797965476 797965481
    0x2011a01020c120f030d09150908090f06192c03070312050c07031212020f03060603180609010b040e03031e06010e0604081c18270213080601080718 65
    0xd44080c0c034081d032445400800d2003440141b00c03500c00c034000003a55004525089061070002c084440c60b50307103040c5000e00020307401c1c01112a110800c0303400d0101c0c01140d10002d01c181c440e414038004402a40d240c2140d1303080e000403c4040340c103080059000c00c0e00c40d08100386041904002c200c0da05602044080000c03d18114002c080c013041ca2900e91700d014010024145412116401103800b021a04442c848156000408118245164009501d41034103020170700e03502c1c080900240d1007084000040349601900d80c01c4c44070342d901c80d00b007a910f15145c01e1069500810407910102c3c041c038101850100504400301c200da01c01d100c9442d0032060342c0001e9a401035046d000500c41c0e410b21141d1002070542c0d81e5803102030802403039084010a070b00d20207801003010400686484178207000420040e5001e01107061b4081c0300790b401d080c180c082d105600c442c00c1861009141c6000540314030029200c510382d015452101c080d00c0140c400c649032a43d80e8035987d45c0d10520391003108031484456815a061280d6038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 797967976 1250 797966726 797966749
    0x905061f0807030f1b1103040501020a060e0114100e0105010509030a060e2d10020306060d1517010c091707030b130c0b030910023f01080304030302011a01020c 70
    0x1840c0c00900d101d06504e04100b1250148946490704100c0340302d41422662203039104a80144a101031810540f0b42000030359240d000550082150380c4072141d00c14404800d50210b04401d0401c10b9411150400014403843d0300b0450003240040c000020000ca03465010310101c403201c0c80c2c041d004124115098648400805512444110901442e0181c01c025030042c402c00043c0e4001003450166490844d03040fa25003880303800481c401c940140200302d040c2c0c1e201015035040c1605181701041c5800c2203410301080581d186c0045a05005005a03003125102c151702500f4030301020344607001c0326900d401040001003010400c59041d50321070740e03040c00002c60401030543c008204600403201c4030340c29600d16840c2030603500107042c10000441080b40c290b0301000803c50220340003508600d41f814076250308d01c2d07045c01624448038604004040e88041103a0300b0180400e080010840c45035561240c0c00691654050701c070075001982041a02071200c444800600715103c016001003d194180906010310025103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 797969226 1250 797967976 797967991
    0x1050301030b012303030a050c01180f030c05010609060f030b090a0222090212160e090703230d030e070905010803040306180b0109060314150a0203130c08070905061f08 74
    0x501001004c1500c1c100040c051400403503c2c0d1b19190705080c2c602c02d085a400c500c400801d11440d410040105214203140c020003030301450701c144076008a090140c050000c60388140d80303035881e0aa000582c0074090910400b41c0384a00c1600e005078a4104142c0d54a25019402941c0103910390101d05003a80c0c8180400320b000000c18021a02d04100e03000500c1500000c08900560341001d0310800140b00320610b0000500000c4901c0381031424a03460103039948445000c02058090320410340b030036021040540d000b101d03001100f114400c82a00c20002e000e0700d040e03600d003891071003000400b052000270380c000c3d141070b02d10540083d030400e4699217030180903015102000803c28030342c1c03030701001207030220100394041c10b00300b80d020490078a14078001611242c8620100c29542103a140102c03295032443d5070301d800285124015031030340c480703412002010b04001f03401000250242c2c0000341e0b00d040812420215209040200034507035030b9400b0700071901d1204428030f500624000c0304c1320342e00e070003003590340d810031035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 797970476 1250 797969226 797969279
    0x30f030e121c050109050f0709080a0b0a11070f03020c040c05180109030f0b16030b06030a05040c08030c010e0601060315031e0b1519050d020f060c03121501050301030b01 75
    0x982c010003800f22682038120040c1d5584400802441301ca60003034007500500039280032001d603481c19a40a454203000c000c01010f2411507401310b1030040d0700c3e402c0000f540b034518441d90307540c2455103420000c48a03c400e0171005401340c80080c0c00c0c2032034248544030040400f521802c1c41c1c810117024400c6500300801c160ba041c000780b15004404208200c1903036282c140720760801d0007603040c05000c86603160320000141c010142004140c40f4603482d003005503604800e00c003030046410f447e5480c0c500952419500650b0161001003502103e4600c1500001c1c121100f04080e01c10590701d840c000c80503114000f9100d0382ea02c00c2d022007000041e084035407202c1580500c07000d410307404003969661048075109031035502c980e210844114503c0d02d070658a2403013030074011079821031913490000800d072030982e06400a48510030074040a0100c1c0c0360380d400c590041101d201940d50f2050025200d12744a50140c03a60655031000c0856100c1c25401a01140d050703e030001d28001c5541e19064060030075090012880001a2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 797971726 1250 797970476 797970517
    0xf0303110f1c030b04092a03050316021203030c0f0f0c030d060806060f09010b07060f020a0f02070b1201170c030f030a030b09130813170307030f030e12 67
    0x6020b02020b01401da28218840454400c001c005080d9001602298400c6107400b5103400020596100104107202e4114191180d203030260840340003d0580d40050294000000e051130a20804815001003610840d502e0083d034030400d0311141e990004a44a50441c007080001240c2c0c40400303006401100d03480c0c0e2000380713401c14034544603046801195100702c0343c60b02c4460a0040e1082404203d50020b81078030b045c0c1200088000142d01e98606104040d480400050307980188031154001c84203003180300b00c056550700e0b1400401025200d1001104005014071803010070180c09507000c40b4250415202d805100da402d128101036030710803000a200b8180b00e0308201c503201d51400d0103a04c001580c16805951140e0071701e4405815501a41240d5202d850020704200381e8529901c0c0a461207900a29981d442c0d03101c0d000380d24920f01240d00039000c4c03141420701000501030000028026284079aa0b00031095003c4501038050301c0c1005601134098118000c04021101c0000180802c0d890204610a410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 797972976 1250 797971726 797971753
    0x913050d050316020c010e01030c09030b09030d0b030a0b1b040302091e01090c0504261507030b01030b1c2405090d1812050c040c030f0b0108010f030311 67
    0x410a903200011807808810003c2c29651200d50034410f001c0303400904540704401e00003d0008035102c19090500d81d4070300c3c0c05c00d21a8440d010b403a01459008203202c44604101d000070380c1d20b4001050b4800d54a00b041071000c032078180804c07140f01c419402a03400540d522041c5940c2410642d0f24210180c5200c20301001000d40c0e100b0384c0d00d41c003544107648101178500380070101e600300c41d8050304140e51040c00d00d919800300c158072a040743d08462181d01c040008003841d001c12929074488a951020a01c946100c00d4469000018410300170700241d141041303041c42250066050342c0e49501c0746540940e140c02c00406a030702044084110a204130341c0e0200d00002281001c01c1080c2074030034a05202c4d500c008000b40c00701c0400600c3c103c0d1200e414081c0042c29a0fa041120003c600c0c0112081c1010f000703000410800300700070303406c0017400091050190120800d0000c008180a070074140e6068200110114554040c0c010181030381c0b407030b41101010a04588013954590003509040000384654400030703030203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 797974226 1250 797972976 797972983
    0x30111070b0c16020904083721060315050112080307080a1104090606081f060c0807020d0602250b0601030c1206030c06090b030106050a0f0c0b04060219030b030606091305 75
    0x141e403082e00c2180e162800900d00d050348001c480c036400030f400c8401d0982318200802c40c0070206550010325090002100654000307500a1000c3c078841c814034181030011040008c901040d82140203062003c03c007d80e600c03004049524031144c40a0720402c0d040006c039003103a01c1985026032080740e201012549054002141500c0e41c016030041e900c545d551001800301513840040745412203031031480c0341800c1c0220007400341880c1c0c4d42e11456050056a0000f001080340800079640000d800505020511010b07050080180d8444400031881c9001000e504014645618000d954070b900f25007012001c0c1da4450040d0700030818210100c06000da540c0039072122a031140100c8001c1d61150f400c33030010741e01e8000013816a00c15904000100d0303074184018007040da440003e59800f51014a007200b0300d00322070b03101511040b00c0713450f01510f244507020810080c0402c580003000c8400b4201c10400100f00341407012022a004c00000c40d600d90042c6002c102c081c80c04d07491642d00b28044d0018021654102d590781c070315 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 797975476 1250 797974226 797974231
    0x15020313020108090322050f2d01020a1b060f1b03050901030e0109060b01080903031b07080d02030f100b070c050d06021b0609060f07080a1d010e0705030111070b0c160209 75
    0x3001c1072180018080c905000420400803c8c083e030b416a644900c119111076028101990100222007a00129205a10070460400d2007600b20403041550078051942c2982e540050141b440030810320810040b80030b03c1120800c0c5038006a44940c911100540d504036403581c008034038141055106c4407071104528080c4034803a900c0d407203240300040c03440f034400014142e01c1000380080c2d010742040c410400c42c1c41d803c2c2034403800d244140038a16503076040c07850810064041e986001440138408000c10044584204e103050080024504905880755140c0c1030b550b0360302c40d001000b482c68420403010003503030500d0f0340759201c454814a805420100325442d8610b0800084a01c1c1d103c540c04507040c004216010b1050030340206030307840c0091061501842c050012100601780c000010f9482c00414103c445068101100798107210003800701100340780c006560307100c950203a14441d500e0031215108203541c8204840308640d00803141c800742c0c3e540c0000c032180f51b004513592603d00b00203038000100596a40020033b2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 797976726 1250 797975476 797975527
    0xb04240c0c120809060c0f0f0a020f07081f020d0207060504200409030c0807050705121509030901020d120e0601090504140c1f030e0a050a150203130201080903 70
    0x10203a081d41c20007044078030940100d6000d014900b800e03c60503003404644140e00c032100035081035580c8102c0c2e083c40040c1c4684031110070f5083c408640001c1c181c0d40850306050000e00c5004960006403114404e6841d070010050036481c100050f943d0302d1000420b03402606c425400c441d40181000441d8a4840c1a0707802210308450340b14088440705101040318019201191040e00c042041da10280d401500802c0d1800d409060880301041d06402c01c030041103540c024000103402d41003118000071000760b0701c0c0c641028030722818404c8400070706003503400401da03590640b05a00400c09c031820150151000341e00113070f1240d0a036455158070b0364a04400c10203180200248440040e03549064146600d065007146d122410907082034108144a0340c0c1e50700c407030b080e00400304480300503107001c1c4005070028940c4541d2510503025414010040c00b10200e070199850340140d1900102e2007582c031880c012440304850507640c00d03044c03040e0341025520508100d58804241c0341100d25000d98101402241180c982901 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 797977976 1250 797976726 797976737
    0x902030f120c0609010c0914061306090501271a0714070f0501030207023001060e0f060a03080a0c06021204060b0307060c0c0306020703090b191701030b04240c 70
    0x400c2c88040100c654070400b100005c02c029005590001c00c41c0e505841000b88020031500000070341e40e0382d04111000920490b2610070070559510001d00303515500d11807a40411116602e51640607410820140b61750540032540404904248400400802080007e219031800340810f0000420100030186240d000c84028450540f51040d4042c6d4096250070081c1018014840100180c94018110304400603400c50080035481001d0000c088485a524503100c0350300301817001890044024886006072401804040540d481c00d0601c90f0044451000520956003003250071f01d030350301c900013066103180300703800141c6031980001c035002e803640054509071000b5941e05003c1465280c2003015000419190522101e00c40481d100c103a0100710030701c409040d10341c000540f14100740c8540c0921000c2c1030f1030083d0644822141c1c1180da01e80000e000e0940100d1201320f100254680111040740c103c0342c5c0300c2c5106030075079500c0d505c9200f885140c1e0217400c02d1050780003000f80303100b00d50b010303110450700c041e5240c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 797979226 1250 797977976 797977987
    0x10302090a1b08010e01170c012a1b0503010b0d0807050a12020d02390f1008010e0a110703051e030a0c1b050703020d1a0a0507110d080a0902030f12 65
    0xb00062003c0c10787c0115180307801c1248405051001040102e00080c0c2400c0c0846140d908840700711394180304030a00301c002c2c050316030400c0c200402c020600f4510f0b206042d40000d00b50311007007854200c54000080d65840f2082c00310100004100d1001001002e22480588182d1860341d40d98040366040e540c882e00240c0c12840342c0c501250790401c556590268009000e106036009030100c1c0241c030064000640b1400c0840454407040e485001c071020082c5c0f0b01804041d2058014070b0000c1c1458420701070b00800407410808502842e005005c0d454581800303c050514207420b90b036003918141e210b000300a44100007a00125a002409405903100d005444d20203e002d0440d0319004003c0010803d000c540004220000800700e43c0c0020110b080c1e0b6415620380b4031000140c10401d1101405c548012088503142040040c0564160003a0340904625160780310311003041c0030000d4441c800d10800c440025802c5000802030340064100b107480500180c03d8508001a0a80311818003502010f4001b564400207607 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 797980476 1250 797979226 797979239
    0x1306021c0219021605060c1515030d08060a050d11220617030d0e150103050313050603060f10090b2709010308040306020a2709110403050303010302090a1b0801 70
    0x1c0e018542030161001c1d100744000d88402c43c0c0c0380600317070281d50b000b16008240d0262081042050070007001d80701c04050792a2404035155001c1c1c1030407a000c94041e0007440d10400d40705000f010391030702a44008040d10741c0d80e030805040c42814806440c0585118802c5201024651103045040000c09180662552280f6060258a0a0f1a060303403107010404184c61060fa0072002c00b1081d10347c4085102c00208107010005c17402c528100c207401d100c0741e140c0000e00000081100010082c01c8408140c1c40142202d50345008100250000301d980580200d08030749a03900d1450074040c000c0c170b0079030715062040c2a0703525440d669040360851002d8086965241000903007003280c41c8894000000b0443e0441c01c0c0c3c1d811903aa6086074051032100a20b03184c1c01180d0111210702664a450881030071060351003a03004900302840c41c2103940d11a000c03229240c20047c00e5060641070865042d20740000c001c1d403a6905e0341c7c2c2803011601000f4850810281e480103558880d18201d0a04040d0322111340c1c078001307154140b29 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 797981726 1250 797980476 797980507
    0xf091e09060b090c090d1112190204050115020a060b010203160b1b040812070501110307080708150607021522080d02010c0c140a150f0b060a081306021c02 68
    0x40140720604004c5c02551140c1c0e449001c0707074076040e9114500b448100d15101c0411294601c3c0e01030702c0078600415014842e03902e11003000da00791a0084509000d541d13a642140c0c900d241c0e40303003408001070b005407c907440881c4203034201003000740040c81181d14010740302d890f600120303004107012640c14908105004134000355503841c44070026004c21a03403805240551140d600c1b201000d100e039031000086042e1050107002c0d0b01c40307440a00c0700c01c070341903a914044000a03c0e1030300c100c4d0b04030042001880440c07000d000420072641541c00c00392555140148c0e9408110441c1d0300450152128001002800040316220340008140c0517074961019001b801c0c00501c9041c44d400f88140421a0301d17161804405962101481c120f1603044079100444410ba8054a07040507850040030b04034058819541405160a40c031880030600340d00c0e82080a05212420400c09108082c401c2c4006031141d804108048011008010751034841c00d401440c015041c09a240381c03140f102e001c0d0000940c040741d030383da0941010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 797982976 1250 797981726 797981731
    0x8040b04090f051e092805150606090d05010e070b0403050d050a0804152408071212030b0607051c1d03150c090301050a050610090f091e09060b09 64
    0x318803c3c825032400b00060f015041a40c071030440b07074030145000300d01100c82c144110050f00844c0620326441048210700343c4002500301c407007240c0740e20480920007241c90f1428a4039014010084c80c0703c0c41c1c52158402c00059075440802500c1c81d540c0c80c0c49a41180700100002d1004194083c000e641b0346103503040090514030802d04d01e6003485001c10503041e01592118403580e000380d00080c04509042d1030086140107101514024440c01c0300703452203100707007000d583d141003c4492000480c0c5803030740c8804c1c80c0745507215000002009945402c0000d016180a030300410406e1902922150401c00247c460780e241000320306903e02141c26080320004455800210b0342c0c19040d05804501411200c1c00210399a2002d040030050302041c9940071501401c5040c00300d41ca0404010000c2c00182000c50606004100c1a103c0034850701031f210340d40c2c58075130103004200100c4800301100111a85040b0a060181090002c8010709100c4d1602c038540c160751034860050028024200043e8101d000070601803c920302 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 797984226 1250 797982976 797983001
    0x9111807020a06020d0b040c17090c150901140409020d1b050d151d220206030703111201080312010506180f061b3f090102070308040b0409 61
    0x4150030801000d07000120101d500b5809000140c1d01c06503c034040b00100b1b2070215150340a800d2405408500398070000d80614060a00320381c1c0525194011980d80c0e490b04520110b8000d01096405c608280d02c81c0301900b115041070500d40007441a1075a8640158015008884c6480e8046800043e00c03c2c18485e8403424081d03404002d00080e185030000e02213008040a00c142e8940b04c0c10002c9484583e01d0181c001070924402800e503a60088000e8401ca031021205081d8000390380d0411a038864204001c00612034010717001030314544030007000324081d2100c03412000744403004010390140c1002402005000f1303d8400b0184d51580d0b9027002e21400c40b1010fa102601c0341c001840b8841c1c07650049035405810f02d2003103030785c00300744240240030590313500034081000411a580c0548039145d420201e5038078000c04261148070b1007110884001c61341500380c0f03d1100c03036000030700008030103512691000700803103001401200d4400740c0d2030350741400640c41a04041030102010408002038191030007042d0100c6030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 797985476 1250 797984226 797984269
    0x100509031318180308010e33090901020f07080307020120070201030e0a080d0c0207050a080a0203060703091a0603010f05040606060f030926070b010f0e0a05061e01050c010911 77
    0x5461300c00070711050041c01000700c02900132000c204c01003c00d002c240e140c0c081c001c801d0881c1c00720b4042902d504000d400042d5000b03950b070100042114406200b15a2010443d440c41c1e030400160303450b00d140c0c5400040401d4299969198074040f101030341d001c040400c2c1002d841042e92040107100044c10740d010f14014034090b911000703403400020018400d80d2a448500000050100200f0714101d2614049170305c16500108006800701e01c3c0c00010034040c00050080c0c0440b6074503210040200c1c110741d03210f50080c11001501c0c03000e401c1041304090840c0c015000800204014000e007000c64220341d0f00341d40450b500d5698540400800c0d8000c2c4120000940c5401c081102d03404d103803102c0c01c0c1002030f141c000400080400d42c665040b181041030b00c05043d007082d04c2454960319042d0029038010203001d00c40d003044404000446811413402100e1054a01400c1c009c40303014842885c08214000414403414008107104100d1144400d219500503d40107040301c144030903040044c4907400c1d0b80c3c03d4026801c0701 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 797986726 1250 797985476 797985521
    0x40e0a0617120a030b0a0f030501061205030405010305040c05120d12020f030f1b0408030418060810090309050d0605061203030709030305030408040e0a020315090108100509031318 79
    0x107001c0b41049000c5070042c207a5903101c09030b0341c045008040300b0b2580c40e03001d07035401d102080c0c1400480b510782c103907441800200a400e440d814100f404410120000342694020007060045503c29000650003610a481c0f20300819256030005101090b03042ca4000d6941c0240490580c1a5110701d042010840d41c0c0e07011444c1040c11005803130140310017012090021220380108001d840e005060748015840c464030070340c8440d125400c60b40c4990051081155160380b800380410081c002c0d105030000c907107290004001f45007510340c20501805040b8000d50a21107901d50008154840556000607588280340000300340c9400010001c0c20b0304002c1e540102c0d82e0051007042461600240c015044ea50941000c039101d40c1d8502e84202c441c41950401280880b8090500c42c0c6808240c0146000b07885901100382140c0e03049080c00910340e005d204050440e4402c6d103101507041d45035400950003c40c6501600d15008544101048160495101144c1340500c3ca800c02c005c85610f10030269401e4004a0108004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 797987976 1250 797986726 797986769
    0xf030f0e0a03020d02030a0803101e2d05060a020706120b030d0804052814010507090b16050a03021e06010e0604022514161212050f040e0a06 62
    0x40880c00000c0c00744c64a21001c00c00d5607403c01c80400d03010b904c003900e15500e00d080001504038541c0783c0310b904602201e15418481001c5280c050a098400c400910f441041d01640c3c42d004c0800102d03440d02c0004104c0380040795a8555078000e006a654680044c0602c0c0d1900d0b6000b80030040e94800020700c240b40c40c900968a5802040034440342d0013a2400c0c41c00350325141401070900030459481c5440341e01d4890241c18688030000202603003405005e1525a805d10b9043c942e003031b258115203107800100d07142c5041c0460001d17240a8500d0460200c184480e50b0b1940d610307075192049281055015900040c400d0301108080020b400c1d8405034030000e030810707500d440e102c4204810090f09180c480c580100c0e2440100e4020401258180b03183c14140f40c00d140c01f8103241e81c0c948869140100103005422981d0b200341060560384c02210000d0040c80820b03410307034540e6a20f41c900000c03c002004810444010140d070707442d0241014100e0208000500d08000f5825011602c06600c102c54000d542c10581070030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 797989226 1250 797987976 797987989
    0x613181b06050322242003040f0210110f07300602300403030c170f07051b0705041820030c1c050c0102120a03110d06030f030f0e 57
    0x800c1341c200c41310004c0c8810b40ca400d01c91a064956120111894003d4030b42d100b146541090080b4403a8441c001c034507000081c00030305180310031600a0700441c9900e41720030050403c2000e1449108251a24110001c0840c11150400280008101c26581300d4981889880d1841030b02d0b140ca1451300075903402c01100c1d4500c16041c080c41100203032030164045141034413013145d520307450180142c0c40b43d8040503c0c1c1c2c1c24486410135100351416400203207000341d480591800341d8608404103059070300c071045c10340c0c80c5a002039205500500f50020403100740040f0480001008038141448a036602500d42c990404061204456140b9a40e00c24601d2802e03400b000718682820035011810120303509181c041583c0c0101c1d01d0f0044246089030030003400c1c10b507200f20043c3c2880c01e400b5179201c0c400340c510014010004a035a0450302d0311010100070304000001181d4020351103001d400b484043d0041c241303500c0c1400b11007220300342d608c1030342c0ca034a024032074004065104003183c52000803402e1111405403004046070b80c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 797990476 1250 797989226 797989261
    0x70b160c061b1104060b0d02071a1302040b0409020303130821040e0a06051203090f03010515120703170a180f061803020a0306090b0a0b06030613181b060503 69
    0xc3c2d90503884511807140c555400c1000503000c038550082c0e07a440c2c0a60180c000354031800054030050700b220310f206560310784582094000d440000d040383ca4500141c081000429400c94501d03070042d541c42c074420068074188064506060f0801001c3c0e0010b00e00802e0390f0a0040d4800407a0b07000c0c542d0164180d1a00754881034a050303803120502e50019a482d00300a1009011030380249a10030b14101c1145d40020340000100350442065a0541501002d85c0a0600740d078019541c5c2c1c044520b0b90001d003141c5040009450401030311003021252001c0e41c0e5101c5000c04901085201c5c0f80001c00241c5c0c640745a00208c80e4640400d59110300d2005a180039076100d0600c0340c0303015102c20031100412008038181d030404410050741d001070600d9281607036854064000c028052080750300b80c0c06a0001540000288101c4000c00b0020340180d156580704030402017000c516034807110740c0d9996100c202d215140d1000c04400c080d03201c0c0c6901c3c120400e000045690140003036201e4410442d0070402c2200d004808214060f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 797991726 1250 797990476 797990483
    0xf030a0e0a061a03070617010506032502060406180b010b030a020403051e0706020a0b06060304021813030306080d0507060507090b16030912081605070b160c061b 71
    0x40300c848914989060040303411025000a040220314140c91030503080c51100464220100c0b1400e956456056850a100070010604501e02900400080c2448001154080046441461918005428118192050240000180d200d40100b00422042e80709103030a40b9181034800704400c10a9132755070585081402012207145022000c10748241c3c19406440c0595805002d5070320100d000c00c45c0b84c0040758003030f014007503a20483c1c500045140c00410800001030f00a08584030320b42d616814440309a10280c0100c1e080107100c424458500f00702207842d401406078030b000c400b1945060a005040c2c2e002a0404034640d00001c2c041929250490116a0300c0740d031200002c21aa1790307500701515500c829a0015818900000c0c03a032140c08881000ca9204030300c80d0300da001d2001d03110801c01c2d1945010010043c04a54100300000f01100f4400003100000d01c5102166210340e114444480580c001e01c20100c8551440da160380b08009040b00b03c0000703415249496040812088800941401c40d0503018 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 797992976 1250 797991726 797991731
    0x60506041b1d03150603160303120c0e0d030302070b061f0e030313060504090524041d100b03010506100804140703051e010e07060225090e03030403140f030a 69
    0x8609081c0b012202000c00740010190f6460701c0002e04203200f000012141c0c80d120f406540710313840c1c5440281c505503088e80d8040ea0341100c0c4202d1800d0580003804006841c03020b001c80144c1d5840140c0c0c8015544807050300c00c1c0d8000d82c0300d038541d00d005811a03072b021300264071944070b5007503a540c4000a1b94400d40114958501080724400080110b8114400e19028a0b03214801c108041120740d0020003c008a03001030070700f0800c03980d5007860000381c000350b001c00c2c24040c000a01c0c21045443c160b088000d285040c4601a0342804842e85c41e9890712009a800c264180d864500900440c9002c3c17281a900480a131000d050302074140000400d981d070018401030414020025110f8106030400040700510f6010040320a0001030a0b0203583c80c400061010015600344040d0121600000c50803504032403842c0c0090001038a454111002002030015040170001074040002d0000520f01071040b170a51160017640d0b170b90030030742001054005541c030079800302c02c0b0420015129112400841390b2180e40740000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 797994226 1250 797992976 797992997
    0xb03030901120b09040b04030f020109030e120f010f0b1c0b01031415070228050717010b030102070609060e070b0301210206030403090f3804030503040909060506041b 73
    0x10b1030300901002603d036030424014410001040300e0b501400b0b000d0f5004c0e40f510080301c074004030200e090780c0c0f8003200100040c083e909040000e0801d50704401310020441e090f522030404c1b0441c1d1a08489003006a00001c0391900c5080e1400c0c00c000000640051303440702006407698180e154400d00d00011303c40144445910620100381007400d104c64441e000c0120170507442ca05010400a42d00e200e60403504103405041c02411021000001d810140c0642c0b281c043e141c41803a0038001249401c4104907000c0c43d5486e0103200c0402d40e400e10041100c0c91003614002621103450030074008541c5184491105548800c0702845012410780542e03044035510044003100e40e0680e9581c2024100c2c03180005c0d00700350088284410543c1101071403080c6d507003d154588150799030381c4110a1307201c844016140c3e503110314032004c1d24420101c61010049800207803c20300e442d989a0307960f46544d02c50380c0880165560707640d8000810840707001300b9420940448040c000c0c4030044c0c0c1181550703001c024000e0f0030701041142 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 797995476 1250 797994226 797994257
    0xa08011208070807080304020a0b07030c02040b1c0b09060f010501080a203106050d0216020a08030d060f03030f120f02030a0c08010b12060d08090303031005130b03030901 75
    0x11501c000d41d020102c20744419852174803802d2a00144c0d8128481c004d5100301107581a00c0806a6010382c0c0c041da120151440240c0038803000b40078101e501070300290b8003d02d004010724a0b540014902d8401c108200140c07402b020800d080c04000f501d000140b40d4200c004100581e0300c150704d1508810189400502c141c00114940c905525050807a2404600810040c00104540d80022a400c0b01c16540065192000c829035441d80d9685c0109401300d02c00f402a5009000c003580038210740340800c87c500842e90305580009500003c40da0001d0013560000800600194103030045400800d07244003d801158203550f4058070841c46400b1120412480070300751071452103140c000c00781d9021360f040b04660740c5c204240103101500900440b8400314926900000300b4103d14403c07180040600035000d1050749030442040801302d1148010380c4c50820a00c0310360a190760920045000700700d002c40c80f546a40c43d01c400c6c04603040c4030018180e060361600c50810701c240c401000300d500041d000d1074221203c1e001600c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 797996726 1250 797995476 797995493
    0x1f0203040e0a050a0b0d0c0b091c0609140d050706020c1903030c020d08040f020d291005090f07050a0203160602071112070311210705010e060a080112 66
    0x28081030004084005011850005610050150140c0d13501030012605c40424048044120701000709020401c81c07040041c50f441101401100700000c261600e8500305241c08400b540b0344070310a5034040e070b94228901c200445951418445039081015141c41c07402114040d065004405018000b2600000c24841070300e01885210f9816a00000d40e01c4120070606000b0021300720f0b040820050b1040300f810010380c038001c445052245512150710105140c2c20340c00d00c2204a0320ba801260131813405030f00c0c08540011517822020f0048440d422031014a041010143c0545040d80a94043d4081e5414092003455588056034041d0b11030400e43d40c0d6210024042b80385100d18000720796450301888041007005440d400030aa07c40c0a0255800d1864100042082040030322000894a501c10481040044d951410b02400c500c0000d0119160300f00c0c1011140d200f01006540100d260040a814829980c09c94074000407944180e0350780707040004280c0d0282c048401070250480125a034021f0004010020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 797997976 1250 797996726 797996729
    0x61d0a0503010504121d061e21101202100806190f030605060103050624070b190509011a04090c0312021e0a0c1412010606050909090105061f020304 65
    0x29000f0001c03881c15041c1000c2c08140441e181c40022030075511288a000c800c0303180040c0d5400108018502071100780c50344c403940c00480a441881f0418080d000a00008000c0c0c04001d04500c01350700d4452501c1d4026101c8100a40c001c190071840d409448030160701d900d890095500e825060483c41501c4510005040c5010a60400d5032050780c4007000c14000d10002500f0102c3c2d00c00c40302030246442c2c0b00015000d4a80460b4400c0c0c210701e50440b036041506804416184002290f070038075161120a886000441404507040703400114032188449482803036100c0d0070323840010751000300202905000c10101443d54000e106d0b2241d03440e40d89d0030b0300f405030800f00800110b910000c0310741328886005000e900c2d8151f008001c1c0209058034000035a5060105880031050f6020310f0181a540c01d160404081c032085107590390700f01161400300081c00409100c0d03440a81126116581c8404d1090108242100000c02400f05c0381d06100501030152500c080820860b01c040307041607403107030501404038a107011b81d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 797999226 1250 797997976 797997979
    0xe0c070f06060b12060301090f03051c18031112191e0309030207080601050907110102270a051804020603041401020301060f17041703060111030705010c0810061d0a05 73
    0x50800002e40c2c00703841c100600009581e503116542c59031701c0f4010182251074440003d0040154000c001d00000d21070402000f50f8a208103030314201410811110049950140c000300211243c0000c0d0420b16401c00c1d4641094080c010060045150b5201c000040303000390182c03104c0074505a0b039403980042c095007460b2410003603001c03c1d4a00c82480c0c6001406004400e82c190054041d00002007104200803030b4042c16210f001d0104160354881d0b4604480c202c02000200720b4a545c240521500c4200151061040c03203112011080804041010450240e01c103510503445134055080301c0044071036108040750321680403200e2075101e41e07450401c04c0241c0c00b844190100d6501c0000082503030b58001030340c0981e80b10a41d03a074022540c450300280c0002c4109482c0035244a2403020100400232005000b50760200f01807411040700520000b07020b14540001d0011682d40c0d4442c0610641c25900082035540b01c01c181140c5188146084405004001e0a000b030040341c1e204000d00c0205034881e82c1c20100140070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 798000476 1250 797999226 797999231
    0x2704050607080c190f03110d021b060106020312060f03060709080607030915052d040c1205031204141203060f0303090d060207210203030f06040b0a051c082d040e0c070f06 75
    0x40d1004a48000c3d408001a03081c5080c03039541d2022b02c140002900f506899554004502d40110078a03141d15200c0001c101e07651000708507071100c04980b024014603018026070f07160b82e1902c9050900302802d1120083c0b0381b0003014030b806030810108140f85200c440b51134a8440008480c2c03100352038a00030b4044252003c00c07078000c4202d03070030300c1e0b0740e05802d414401e5000d4094040000c0d1070715047d84a407142910080c00302e600a100c0103980c95a1b860095400c544240e509000003032141100301d003410742e12106050502c00c0801084107a061112040ca0810411005103141c80344c5180043c0c0d8004103204041c1c015940410090100710141804441c10005400303421101040004002d5907540202e901c015078041280c045000c03814107015962001200901e41440c0c58204400d00c04414031100e00d031b05185244003192404a00500000c003400da00c1e080c40e85415441000b1103503511461078aa07203201140401040100400c04401c0b01d40014038040e04950303590150809048081c03410201802c400d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 798001726 1250 798000476 798000487
    0x60f070c090e030c0f07030206041806170304050102010e0d051c0b1c061503210c0818150f16052103070e03060c092704050607080c190f0311 62
    0x702e001000d804c03090049400c854030b1440c441440c980791040da10000390813071018401405490003a410300c0030418000310000a032207554440010708001e060414402039040020148010f590a024102048002d01d00405525201c20710040c454414000b0f0b0741100d00c171511000800e2002034120550300c0c400140100d0304645018541605c0a01d801802c40b0801d00e0036803814410b80c00c1210600440340c21240e0100070010403921000e94a000c000103a0407c0300e4501a1800200e0303070701c003400f424050346100001d088070281c2444108007803c400f1903c102d80510110900c005802d04a52001800c5038082561002d00e00d0300341e02e000380300044646a140040c042d01185140c43c4c0241d4811180d603515590341400c5035040c16200c41d000d480c160501e84042100341d442c1e0820580e440c2040548102c2c0034148401c40000805114042e00e0456080c0c0080c414000c0d426444401e55400495000170f40d1301e84108031101403004840300c0d15500501070b0b5510026200c1d8003e500280b440c07010002c1c120750f41c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 798002976 1250 798001726 798001751
    0x10e1305061207030b130512040e190e0a0b0603191104050609040f171605010e0606040b03030301151407030905210c090601110102040b04031b050a06050705070f0303050310060e060f070c09 83
    0x2b03070411501e41400c440c608004090302d41c11802060f000010705c0d4003030f200005881c0c070b81c00300c9040d0003820680c151140d43c450303000c0010080d0260041c640034000081d140c0364203074100015100081d20719441104401e0034000030400c00c841c0c0105469012280c11440c80e88840034401a014080c00c02d5642074a04081805101040d040752540e072480c4030903a1121f9807500c04103c211039052a0300b9400d540184014050050b41c06517014624142d0308000c45003040f0028020395581c4110421400104001e10810003820201c003a4840d009030070325081c201800c40b85840d655200e590080070300c00c2100c000810b515900031004d480390001820025941d403621071b540d00b5907070307449444119503000d95204011104015401c1c0360003030f988001c00e001d6440d854068200e409801034034098410f40500c0000040b00c603010365a510003144261105602ea00c0c02003444460488103a10500c20f10010000d44030290f41c6030303400c848171140340f200500d80758103050a000c143d0702101d8102010040ca0314410500c40c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 798004226 1250 798002976 798002999
    0x1801091211030f030f0a1b06020f0a030b090609070e010e1e0312120609070e04050708010e060d050c0d0303140403080f01060207081b010e1305061207030b13051204 72
    0x101d12064045403070b1a580605016a248107103002014103a6091117003c0066104044c800e40c00300301045200c98401070b42d00e0320403c980c402c4d10040d0070100300040003015640c040c051100d0b006401c840c0c80c4060b10386007020500c005802090942042618020440107a020b4a084c162404c0d0280c041e1b9407181c1e800524120490507141294468440d034500c114001105004480c0f41c06812030f0144c01e603464050078410b0a0300041c0c40d00d024003c2c6145991465251840b0b50f0b80b0500b00c9a0392850700b54907160716401c100030060311903401070411087d03800102c0c00020781086500030513281e210000303274107040440041601000418080c203134074085c4410705500c0703401c0c180101c1c400c9900c950305903a07451090b60b84400c0c0c1e2050b00300c507401800000d40c0e910be20f10402d0750010418100036140d00302c0394000800c0030b10048500080941e03030714148281c40c1402c40209101c01076401c003c1c2a031508544424451400c0105411802c06101d540300f003c01009103c00c0c8141d9420080d8141c6076074503501344508 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 798005476 1250 798004226 798004253
    0x50a0b0109020c280308060112050c0d0606050c0703021c050f0a02100c050705010507150213080c0a080a060216140a0303150e061e10020f0f060c18010912 68
    0x14400c013030032641940340306056010991300014503100f89a480360750684403040001e043c281881109480e460b04144c16010703540c450030366040364035614502210008229051600700404114060145010360754001908105030380e01114425800c0400d0710211001030203020008103140600301c213003034000000080c001e24084c800c45803060014010101164518280c080141240e07001001c100007950040d4020603019000d207568500c507103250018070041c3d0b07100d00c0c541480e0503030846040040ca00140084510b50b18100c0d030707e0031528501507201d5502c5440c2c00010703060f16400100010764801c00c2009a1106600941b1400c0801a104205442d00d086900607000300e8105801c0603103004c4071140c035000356120411645040d1f20380034180036120340d00c12180c501122003120a10b04682d903810326200d031031750268000c00154403203050701400c000300d400000c282a804441401600307107840c0d00351a0004480b82403000d40d00341c1c64004a44990860f408071509080034000c0f00c1c103202e4804980d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 798006726 1250 798005476 798005497
    0x813050a060e0c0d1a150d03110c0a0e060a0e150f0f09010b071e03080c070501060f181505030d050a03021e18010e093c0f07050304020a060c050a0b010902 68
    0x60469941c3d43c01546c0c403514005620307500082c901c0d03000c000070740214460118092000221303651800d0358000706600c4c0401e60040a01003c4e10740410441e894440c40b0803005d0801819035030420b060080301a2520024089024410940085550070940310b85440c041401360050039294a035a4441c0750f24465482480c1c103403030510320041a10221410100507105040d41944e40b40c0a03996524000c6142ea003142104540702e5494250008140900c903a140d40a0400c181001c4c5000e041c4802c008116a0ba8600c5400c400020718401c0242c0ea40110b610040101030f81025990344880d65001c400a00c2848221219104600700300c0124204840c0900102e00c40c009007407501e000424015106c07180c0601500d94008005000104501745000301a21240b0b00c10086000c07001c04030300720008900038040e5140c58811481e0401c40c81138004c12510fa0841e1590400d80c2ca503040a8010130044074040c00703583c003440b80f020100410001c0821140c03045540240a045941d42c407000310380301a600418510 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 798007976 1250 798006726 798006773
    0x307120305160207081902040b180612011505060a09030b1302010f030203090703150e030c0610060809060a020f0c0109032304060c1103031c0c0813050a060e0c0d 71
    0x41c440b26000140b20025601d00500801c81001c001000490b4a186030004076080b5803501d8410f0411b0b1140d02044650070860032514140345850010301a07820313038084007403e140e07050041c1f019080c00060b00301010303260300791000e41d0307a6004200c2c03d440002280e4802041c0c0f0b2011010085070746506000d20203158401d80c0d80d00c2d036041c90b008040342a80002d071140f00319034104e040104000380c161000d09400c841200390114076241c5040800d415600f00891804d082d4008008000103c00e00c101854003070592414285401e040c00c1d11010f907100c0b00144510842640002c141c14451210300c240e80348040350800910403007020303143c01064440440740540e400e890b800c7c006c3c854248a401030b182512465030b19562510b19580b5640362944030000540d170140020005001614824a0011034482d61000042160b440c050802445010001e1009620605440480c0000b600c00700f03031454050380040022840e0400c2404550601c2c41c3e11054590040d070b103a03e540d0070007281440c43d500740400c00070320f03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 798009226 1250 798007976 798008011
    0x30601030f0c0b0f0913060f0902040e090f0d1b02041109030601080606031002090a031a160203040b1204062408100501030201020d05030a0212040c050f0d05061302030307120305 78
    0x152030300c0c01650510740e10b1340030038828038080d41844214103102c00094100810b0b002d985942c2d0b104500c10682103001c1850700000d091000b007008403800e0307421001150041000582030302c040c5448a074290b11180c00c01c6a02d4460349041c11118200c40b034070315001441040404c02d41024044517038000002c50b13020340213000002408210200e40c1ca40f2800c3d002c1c01420071044100c00c454001d5210981155000403d48404404602105800000d00440710b901001500300f22082d05841e040f00d808010841d881008141300112144040d940401c1c61240e641c0e01c50f440360b2500d4005029040640f04208041250070841c040b1748010103404c40f80c50700e05441100c0c0d1314200c4102910424000640540e110741d10000e9440c2c40385d4002c40d801324910000501303103450b1102d10200027000361010340d040c0a10400c240070a150003009099600c90845682156694903070350541c8408005020b0b220ba1a012030748101075440600c00c07540702e264807000722520040090340140003003100303480d2600c05d80401d602 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 798010476 1250 798009226 798009239
    0x806090d0801060e010c060501060302090315040314090d0212011d070b0910021509010c03050903070c17010b060f130803040308071b090c09060e0a0e060f04020702030601030f0c 78
    0x30145104145680d51140c5682003010550f0040310380c401583c100002020040042410751003914041c044030b83c3d0150f510200d0782d042504d480d02c0600030780902c010387c000784000240c2100381400c118082002c01519005894001001c081c10307020040d41101621800c403c5404d810740c0442c000c0901046202c01203103d100c00c00b0350b100a103010320052104108101403240c42c004401701c400500c548103c4100110710184401c0f4000c099500100c2c3e07a458413403d4000c16054015070764030109070002503003401c4184d1141d0700b8040440c4205030312501300d10307156007110000303401c44c95490902904035692504c0510751000c1550007070340000015003000308082142790bc08001c580440b83c200c118142400003e40f203c010000701c1906190340b00c12105800600c0c9080c50143c010420855114412030780d103000d2014146a00c504842c8d8814142c01005000342256400400e82000d03059904d68449900900031500a00c90703844003950601c2103900000030001565008621a07101751484551203a4465 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 798011726 1250 798010476 798010483
    0x6050103150e13050a050f0d0915020307120306091107021306030807140c120d0801050418060207080f031f060c080a03240f05150a020309060703050d0213080609 71
    0x1e03028040d03801d1000310f0103d08010070004100f50046080d24060080f81c2c1d14203142006100360381843c0c0c3c1007003100380388054000780044020030030983d02e1003020846c200000d44920502c4001801c1181c94004040001d10035840180602012901000140c0700c800c10740c5041d03046050200c0c459030705107d170000441070501480c400c495011460390f081c1502661403240141154014108038803c840d401c14503591000d802021080306000600f030449600d503001010300405130001d0340128203000c82c0c10909540011450750141c5c01100c010780344c04040c54095003601c00d040e90002c4a09000c014080b650342e03047c2e00100d103c45600070300c0300e500b56141025110490340c584090080c0d4402c0c42426a428001c4d007241c5981c1007854201d07087c4102c0407001c01c0c0c03202081d0f00300c0760904010702c03424015800c080480342d16200184111501342040100d00035503038031814280c41c1c029640420103100301400341d42601c4030b250740c006d4150348809884124100110003845803142c148a03550124851507000b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 798012976 1250 798011726 798011729
    0xc070f0b070510090b0117011e0203040b13020102120c070f09021201150912050a02040c020309030d0203071539030f0b09010524030f0f06010203040806130303020702130605010315 79
    0x5a0385d0f040c1c0d030f803074807500311300004100801d01225502d80c445542d082100840040b0701d00043c403001a140d04003424258001c2c1c0d8000c0c811145100c00d100202e0160f0303000520809902080d410495a84001c400710508061030f580c08210360700c0c42c074000426220403540240242c198003440d0180c8980e0b07603481840040030a9814100800c0469070140210206d6040c07010b0058050412200142030aa001c50215010302082c10b0040e04007096400881c0703420b014034000d51082c1d10045007002e02540715031078560b088034480100c0c15a56441c0d01d42140b600441c04089048150344c0c43c400b2000c101881e0550510800094006481c0901d000624441e6200310031510b40c0103031074075400d80e007000c0038400341441c1c01081c07079200c0c02c88842d02d101c1c1644d2000298803402c048142d005803814950104401248082e0120303040d90001d01003808500400504603a10409001d1201c0c420101ea04045d0001e21940002a4000113103140d0340c1011402c40e00250202e820a98041040149681c4e01e044001440d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 798014226 1250 798012976 798012983
    0x60702160519080a0606030b131a09160b070b0c043212010603050706030e1921030e1b101202130e0f10060e060c070f0b07051009 57
    0x4150041c0054200303918480c0009000680c00c10000351180142c3d40b8207031007500d00700c03151a12103a05204220100708d2042c4c200c00fa050713944503003c0103031b6a060060090042e4620007414080300194410034100f2030f90b0b0041100100781c14040783c590009031f0141d1300003102a106001d00c00040350214250380e00300c2c2d0444a00c0b86901740821010b58585a582400400342c001da6003031440c1a02e07181c0e82d00003d048019403100300000782c051652500b2400c5c0603159003c18245403901c2a034200c80180420700d021085c0161010741542c43c0e03079213005802c200403407407088440c3c40e6600300012030a415a02110305450040103c1c0c508002c01c0003c0300010800c3e001031a00400503c1803014030302c2c040c8805142c004500200076040c001d4079100c131840727803041d503201c030051110708400d01170901220700740305820201644034a003c55050810113421000520b1225026100001da04a4a203000380710030740241c1540d5640304500d55440004a020340c01c0414242c07100c3c01102d840d04a100000c2c4502c01c841d40c0d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 798015476 1250 798014226 798014263
    0x70f03061410031d01111803010c0516031101020a030228092603070609020a0b0918040318060e01120501210c0f060305010905180a0206030601050918010305060702 72
    0x1e0a00f1406088400c0b41c8510000110404000d00301c42800b03038180c59001c02c03a04640301c4508807442640254001da2980c0680d240260103400036a212080340d18040007074400c03005072851850100d0740e002c0c0d024010315080d41701007001583c3e00c0e4960010000031030f508108901c040d640b200800c074407482100c161000319042ca4020020105003682069100645012090700040d5040c06a41164080394040320340c5a40d41001d0302c1145080440400904000b00c045400d100e0000085a501c91140c40c542d102c0001410000301058465050400701c00b0b000d079490940c00e95a41c1c00a45070b0a280e422a40c0440c9130120b40c07040e4030382d1600c201812110380c0d8200c1d20003410b09c80243c0d03210b0001700d001541c4c04c4d014040007050b002c1034400305034000c120369500001c40750303d04600003044603409440040070240455441e0032a15000440100550701212102c0d502d40f00e48005031039621404008640186004d40780111240b40d500600781224044c0c02901c01c265140101282c48020004600d500b650 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 798016726 1250 798015476 798015499
    0x6211a0616060c1d181909140d081b070b040f0602120108011a060403020f010c02330702010c0b073011040f0e130804081b04050105030312090c0603070f030614 70
    0x4a1b01243d442c20300c00002c1b80010300390100d41791400b05c184400307500342507540300341c94094000c0c0d8441501b41d4000c0f03230b4400548204a42c80c4038004148a500000340c071041008002ca424401d80542c031301000c82d4071071800c41d50358140301c0c1d18114541c024420f61145518184800500307c1d000c02c50101031000c002e0105103824155401c100d00ca980c07440da0181005202500c4100584480001c40070007274202481c8c48c8540c08010700196060200200c600f0300c1c6074207001410061b60080c000145c81684400d0709505c035a1189001c80d10081c0c4111450291032280b01a075419110b03070b01c1e851441c100c1c040f000f80885013009203820458880c610a000b038007200d95004002402c5006200ca030481d83c880400b181a441a441300800c98110b900b203480c0541240306a500984c40951030f00c1041c400c00c2d1414059985400d0000362240120100c81a091603803c0015126000500900441940c014869503c03424408001450510340c200030102003864194003040501140200c4014610b0090466040d907 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 798017976 1250 798016726 798016741
    0x11805060304050c031e070501050f2b02180906060306150c1006030303061d0705091e03121b030f030a020705030c0706211a0616060c1d18 61
    0x6500040080d200303409a44d20810783e41c1d500340003898034949002200072129840b030424a003400b040703510140c1880420000c91820240309803e486090b251510103542e0310031342c1502011407d4503c01c00c0200548005030154200311003e241c52008501035901d814542d50307880c1403042e1b03880156080c0e58414428050345030116007500c028590035840c00142e40c800d107280354140090307a84030741044000c00d48400050140c3c10810050080c03103080c0304030480d11030034066406411845141c0d0680d000350384c6209191030103503000100043c3e04c00050211259510900c0e201c0f11260401d0343c00c501039030a0720070451071070324001040d00c1328801c007100d21500e15260b400400c00254072885c000ca0341800280600c550a100502602d4001c00d10340c2c540d800d80c14100e48400040700028621005517510b03083c440d5400300021070203882e1140098030f40c180d031540d5401c100303542c03100c4000d802000c540c00c11141082003580b2110522a040150a8041e0320804050402044e00700c480074025131488140001202c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 798019226 1250 798017976 798017989
    0x602010606092402031303052b0f030e12040b030708072c01090305011803020f070e040219210515060d0611310e0615031021050c011805 60
    0x4440f541c012680303000b8502e999501c0344803081d0300c00d490340e070084001b000b1210100c1000c012104510701c2c81d00c00304840d810010f40915403075120075041650351300d0301c06040e0768200030340205030942c3d10b1101d865070740d1800d961000380d004031082000299079030041000f5034000c140200840d8500381c00011321300e0301c072641040081214005241000841e400002c0821002e105480c6603115a140340007210310242000791400d96102c501900c0b40d40011000c00c40000e6204040c0d03002a4119005060400144240c2540403050f03000f200f0009016010020122807078003c480010b44074030150794030b020108825021040c01200e03c203030010301185403c0006050341e80071006401c030280d480d43c02c00c0c0e81031030308112118050a005c1c00320800c8402141c0c5444101c24071000070711141182114a107008000300302d12100c461091408014044080f55610003d0403440f0054035501235100454010004400485000900b043d950350261065010302540301d101c11081025003111940321140c50181800310303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 798020476 1250 798019226 798019289
    0x70b0d021c0222080a0305160c301205090a0f060306090b0a0f06080c04050d030825020d0f02070801050c070515060906040f090f0c060201060609 64
    0x951a60030445040420100c11861224540341140182c99150003255a14454908090000f01504070701e4100b15441000414810996040c83c046850700180034030034505074030040004180c00d0200b04d0100702020441141c03040d42c001490f0800440403110f01059480e5075403500a4819580d01c01c81c1d00300e040c0a00018000c515001d0502060160b4561305800300b80041e1b0000320004c0e40300c0104001c801054002c1c401c4035801220380a55003498000d2281d0203180c5485100c0070f0107210000901c41e480b0500940d4020000900001380b001c0c2c05250060003004120741696607403074000c1d07a000002440b003101d140851134a400801000300030708010388051501412030740441c4540400401e101c6428054280139150b90310450b91540b0582c0341850a0200401c185a1020b40706001c000301a9200b01100380c0109043c0c070005000241c0e80400c03005042c2c00100908000d01c00320b0140100034030fa00d01030341120381c42c4d40200031031a00c0b444115100215441140d41c0a48210441142400700950010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 798021582 1106 798020476 798020497
    0xc0d0606060207140a0608100902040914070201090c0612020d1107060b061845010906050d0828020a0312111209031b01090203011508070b 61
    0x740d038601140f051a003004001c5c0301140c0100d01d51100c0728049c240049080d50707120b0300c0c0c0040001405901c4c1a150303001e049600000c048502c10b00c00c100040c1c1d070204401e52110302c1c2c94003c4a02e28105a202c0007002d608114005440e00c51b44541c2c40030300180440203407100c44904000b022503119032411806180e0812007158440e040440100c0780039001c880c1d036040e110744910f041d5461454040c000e01210032030480f9910701d074806510b200c6007401c46100e8042e2a070301e400110301507460a10032160007001d422000030004101d0340140c000e0182000481600c44051440c03c0b40e105070401a02003d40c012140d404145640045411400100c5503030501550140c10926401c4e4410485a00b00c2c05203860041341045000380104c5080708008800340031600841c810290003441840d204074865031800707134020030724403400d07080404841d21400503082440c03500b0b0625001e5070005d180607 = true := by decide +kernel

theorem cover : BRFrame.Cov 797841726 798021582 := by
  have h0 := BRFrame.cov_init 797841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 797841726 ≤ n) (h2 : n < 798021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
