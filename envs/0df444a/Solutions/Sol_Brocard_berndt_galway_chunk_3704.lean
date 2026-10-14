-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3704
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:26:22.775006+00:00
-- url     : https://prove2.me/submissions/4f072341-873f-48cf-926c-f86821c87752

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 666007194 ≤ n < 666187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 666008444 1250 666007194 666007201
    0xa06020f061f03030507020d02061b060a060303080114030c060301060f0314070827060c0405180f0c07080d02040f08060702010b0d0b070315030c0603060e01080309060a05040e090102070c0501020303 87
    0xb40c4000070200d030782c1420019965a00c501c0801d426001c00b09010354443c4010950406000e00000034804a00d06041900d40383d50b2034030b22100c01c446c0280000340c001f544110060000c0034404d00018068600141100c00065034440001c0450380309810880002c0c3c49046080b00d29501801212251540044c07a244681303070011000744a0080102441440f912103c0398100a01101440214088022081e1101490324640100d0b10b580a403041500646034654070020400140d10114010480000203c1c0e5039101d4807008000c0f5008444180c48004007000b4614080c143d601c001c100905034000c200c1d070710620382143c00d424000700810325419a414405d003115503035112410403101e50b5218007002c04603140d1000450040825001406560110343c01c040107100302c2000c8101200d003585d40600031142c41e6060000c0440080c46541182d510078001c00c0145c0c07030010081d001044c0f6038540b850400340d9440150482220503500079155035030020b0520203102c04518400050300c0203000031880c505 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 666009694 1250 666008444 666008491
    0x10615030b240f1608030601080a0c09060e01032403020301110f04060c0f060c1101050a062916060f050604090b0f09010e01241d0c03090a020a06020f06 67
    0x240886000e00e240d40b4000b03010f00c2c6120660090750001180c12214030420350240c94003c04917801610700c0d40c0401e8420002904500c034034040c1d4440a0f003140d689507081450103500b130b0345407004000414189a120383e4036600c0d010303040748010b644508c00000b14400700d2071801130501310f40e185950110030041c104840310082c894007084804030740951034071002d041e40900308604000403180d001425142001e840003141a8410b001c00c0404076548020003007600c0e04244201107034a24803848041c510185ca000d034900c480c03a0380c5000210702c61301c81da603d8007544c2c04000285c00d11501c01212a29036510802e400c0d0a036610171503a11a0b805d403020489880e0a8036070700c3c95004018a17400404001c40c000a15415003034005d2454821340800038070210b10b4825000c803420030301d56030203982610000c100085510200503c50400d910408014020f43c5425405c91451741c401403400000d0310035240d1030786c0141c440a40c0040101580d030f01500309205e101c407015090070b6002d454000903000708040d4940ca107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 666010944 1250 666009694 666009739
    0x120509130b0f0a0608010605130f0b03071d1e0d050a0b100906180c020f0303070908120a050a050307030908070c031a070e040e0106031505010f0806040c030201140903010615030b 78
    0x11000780c109907440b2009d8a45103140380440b80c0240da800c0b210710b100090741d040e81c000a1401406140c951300c55402070703079911124040400c1d480c2ea603c4061014418107000c07001c1a030030a00080500024408c0c440b40d2545490710768032a00459011948400300204080e514001c48003030085c01c4001c1c0320f4140f42680c10000000ca0079200004d06035510520a203041c02040309940e018502e4056035140e241250010340000701d180f06a21240c0501489081c940c84d140e0129880d189140c2c0320a410301041000844142c2c100038944018103954444090110b00414064040070b841001c0c500045411403501048210044540e0700035600000184040d0f01e0700f041410b80c412a0554000400103071401025001d8071785540003a1801d0480e8285105a11244c5c00241c1a90500140c590816a480c030700315903600c90460300030f00b02074503400d401c1c4010340c0300e00130600c22070350030801d542d00342030185000a00719400b95003d840c041c41c010300301144040d014080c1c800c81801c100c0390001e494440d4803003038049 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 666012194 1250 666010944 666010949
    0x507030b0a020715020d0b010e030d111e01050703061e0314100f380d030504031b050103060803040308040e09070f030b01080105060406030f120509130b0f0a060801 72
    0x40c12840400900241001e90644a0b00d503000031500d0307010410b11001100030f500410100c030850b810180c0010895008a030500d102c400c0c090020403210341c00500482d28088240c0300d0281d94010300d046d040942d070030403c44a0301100c0d841c0c00082c107414580c41c0641140c0103580482c01c0000a440d0080e110102c038640082183e4006000c10001036101010710300f170509986000b40158a09034007a0102c1c0304e598410200700903105c81014402c45c100c40203400507092120a8540e10460031000103090800921115405110b820300e2424039490765201308400610461502006484810070000ca60380f50040c503000300540b4005d540340a0454583c41110722590089031020300041d03000c0f0354104401c110b520010141c01d4a00214070741ca918002072840700a11a0004960070440271480a280611555084907480a0700700d0805e00e260752181c41e14480300c01e9200c1848014015080c1940b1885a0b5810503c001a80040c4c0884440c0030800604082c03000f8038020141c00c4400d014035904042d00034103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 666013444 1250 666012194 666012203
    0x7020c010f03180302060414160326180a0b27031905030301180c2c090c0c10050708040f151d1c0f05130801110a02061003050703 57
    0x822103508201600689050009511034001c84100d0fa0103060f07000c103030b440c004ca126201010269031010105540d840581c2c120940c00c07003100e80c0810018480c2c008000c115003030044080942000c28803800295044117103401e08500c070281c2c50103540e140010f482c401410320031041c0da0404030403500d198006800400205490144810401080e80c0e0401c00d400707981000e1148045074006c3e03840c180d91690000c2c810700103525030080c0300e080450349034017a80044113415074800340740c05019100829080d21403060380341c0038011070800403416101c500c0383c14030500c64440c01e190b130303041c111041501d015182058401407610307180600903174680c04094250416000450752413260010b0511514000ca070302146000740c2e180c0034040e4145003403220303441441c0e5060401d60701041e407020705083c200d28070720f1800e00000302e9092500c0820b90040001c1c041c40b650552480d043c968580a682c0d08580c890303800390302302900205d45405030300da04000d10ba0784180f004400c5076a0340e14640c0d4a03aa5014207000080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 666014694 1250 666013444 666013457
    0x182103020c0d080d090609080309010902130b0907050d0b03010507031b050403020d1b09090f02010e180414100e0304091104121709030a0c03030e030d09090905070506030a0b090a0507020c01 83
    0x174144a040d80000310010f40002c001d41c2e0742d060480c1c190340200340d941c00c00c0340246c0d203190407600c04901c14440c0704001000600314002596401504840d26427060919160380c0c0e913100d01c40440713071700c1c00d101e2280f00c0c079002c0e10002200003002c41c00d0350303a41c103116015608000b0204004e00041c0c590403100700040d13610544c0e81500c41410802074016941070b800009195180500e09418400300b0002c103841c0e14002c0e2220411215a00c02384918075028200a08441c2041c01c0840d0015050200c0c016041181c00140c800c00d10403003c01c00706944e2940c0c4d001c101c9900c0402e051091110b80e00c6800c6ca40701c002c2c62007038901860030040403030b8502c0b0800c001e414a10304541d985004200d1000b1a003045034010705890450105181040c400382d030710b00042e80056102e49100100e030038005603c0c6140021519072990b91850001ca040161003c2c1a0440c0c060040ca040000c0c5034450a001e14010300150801150000d4203600340482c1d40710041594003914108014031032a41c0c0c003c00c5103c0307000028a040e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 666015944 1250 666014694 666014711
    0x5040e010c2106080d2723030115080f01050703050103021003090203031b060a06170304051c12110105130c05090a090b090a060e0102070b0601182103020c0d080d 71
    0x8005000e294040780c085d0040341084403d0b50b52114000c0b011040586c040c2a00c500313004a40c1081c88658028140b1510046c0d42d403504d141111700c100002108010300104505211500944d05141164080c51482d8400100103101800c02c1c0901644603c407031074104125032440d0009440700d21030303440c4401170550b501080015500c090040314004e61a502e8a0403500300c6e91075450307603250780480d01c540560380740c00c0020400102e0303065960380b80030503c80210f0600d4203081c2000b110b400e40d8520710039010f64154102000980d0020120385405160320b541d0100054850b0142c07c0d076038010b20b640c0c0849207041d0308400281c044810101a0b64042e100c0c020726584440911004011100001e0320700303102c5104000104400288005882d480780c881071156020910300d0314282e00415000400410040001030510f501c10071800742c2c160894100506c145540c1c60034400c52500410040005510210040c814142c0400c4841c60a11040ea0f6405460340d1070740b01d42070755008401c036095445403114440b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 666017194 1250 666015944 666016007
    0x105190302040b0a0c0303050703050408040b090a080105130309060203212a030a20030105040b03030f0d1b0c0c0501050f0702150a18030c06030902061b0705040e010c 73
    0x56030042c100254143d5561040c40320080c1c858482000101c00080c01e18001600283c8240a41401990b026500f00c2c1010b040111011707a5811090140b40c00c46d00401c00040c0d10b82c42401140e0007140ca200111074660302c5c0b802c0c000c00300100c0390006000d40d030041046281c0c0104c1c7d5400340d4000716998011841c0398550001c000010f1038009040311800500e542415200024400110700502c0d1080003000f40e140e03402c0d0321803082d00032741105885001050004000c0c0d0b02b019000780c1103166000781980c0c0740410007955504140c0007600815074440c1da5240b684203d420708a40c010b82112141800744c10b010155641c1045410f060042c10304001001c0303081107070030444000341c0f094164000c0074146000300c1e040d90130343e06800056440001a451800c40580c2907208109074042e660030000d41c0c80d00508005003036000d843e80074000c036040382e8200075055081150421034a980c0e42c4d58005440003034a064104003d6500d004825500c0e03074540710740c0001150304103036441801c8112203c040b2000200312074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 666018444 1250 666017194 666017197
    0xb24240307030b03060405101514040b0411071113090206030604090305041a030f0105040c020a030305062b02011d10110a0c0f170d081503070513091a060105190302 72
    0x7800c94040c400c14052100300304008c69078800640900000b042050b00c2ea000003d010451845491580089484641611700301904666026800904041522584034a0303030340365540700400c1524002c9010358010880d2a12500004d0351010410050041580e035030000340080c0300140143e445030303940c0d14420003018000c005883c01030844018441c00142c00b007a104240b80d10403110340100303246480002c50285800e110701d004a85095000703054058071541e0940040c0b5000e0851030307203c00d64404a1100c6c0c401c2102440403040c1c000342c0f01404c0350a038400900400072140950148020b1401d00e03162a4aa00009040840c0032303103011400c8064039407016051100540c0d014151134415031022503c80700305900f51044075100c400700840401145842d030b45a0308201e501100050070a80426a140d92448040c64a030740d004042e03591555a5000180f400c0c07101000c0001038584844808060051a01103520b1b840c558040080c0e00d4503000c0002800c038400c0d2101301c44480d02c42040c1c1d4800724403039030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 666019694 1250 666018444 666018461
    0x10171213030507080a03050f0c0109081303030f03050c0a0e04020d020c060f0a02030405070b0f0c0d0801061b050304050d03090305010606021c0e0108160c0b2424030703 74
    0x100015540c680880e45036092205034001036506109005001401584c0014180c1c10309405682d8103061003800c1e50039600f694043c0680f00380355900c603101c142c089100140180b0003a0020320f4425030103451498090112640a0713542804c0c1441e00042100c004140300c100c039290b514500c3c02da031901102c840018003d00030b0600442100e44042801980d004001903124042d50080c0320b84641c43e61084c2c4140c0c2640b00031103000b030403608108410407007141c000700a08061816400041d00340880301240502d825061141c40c3c0002c0da800004118081d00402001da0400074a0000a101c0c2600e8803007654900c154030400d40038001c5c40c2e0402c030030f040c8200f483c0740182d07034450f00034405a95945802980c5010f4040d581e500c13950381440f1861007a006a0a403001d0781e0b0706844da4075959451f010004a01c0510405c402c082c4424000d81000042c88043c40f90311416841c14a0310030911440c0c07985009112444109026210884205880324042802000091802c60302d060b500c1d234410380d044024040c0f03003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 666020944 1250 666019694 666019723
    0x6021606080c070c090f05250e011101090317091207020d03031e090201020c010903050a0f0503130603021b03120103150908071a0f1009110405091810051017 69
    0x10180400c5000c51500034002098080780240a00d4494001c507100b83c04840d4040032010284121103001d85000f0500103c0682713050502448112a071810310703095030301d4600c08800040051a0710181200f2030300500350080d450303034000c001ca44d0818687c8002403140c514041c3c4640d0b040f00700b01007090310035000350500507001304452826200740c0d203124001d03200c01c05040b40980610040c15907594450855401125000b038003c0c04655590344a0203091010504242c41900041100d00d00845041c02c15038014159546c0050b96903088a0703c292039007807210340360070341074104121a8407041d40c0200d41906403500020110500e2101c50542c80040c02200e0000b0000c102c00305040c82440000c0d141130103100a50700b000130803651030354440410300d041210f1000c1c0c00d0801c0881444100503640c40342400324003980806140940707400006204c040222070b900c9031084000c504403030340001404001580540900b0500040c01d001015854522a03800341e0114015540e884401c0182d04200d6200141c054 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 666022194 1250 666020944 666020963
    0x8100f0608150115050306180414160f0902031e0712060e0f09070308040603020705070305010e1609140601030b06091003050a1116020f0114190906021606080c07 71
    0x1180e068400c2d0203030074410344d08141c00b43d00c40b0012040c0108210f034031440009020440c1c4002c0800d1280c2d01e9035001c6c00c240e88458900001c0d15508e00c041041011001e03000e1441004146004464881144203420150320035006000303100031098000400e01f0407028001c8040c105e550f030640304882000c0d0b01d02405207070b00d080080011306054240c9002d401140c5c614090003060395040103141c0e41d00520300c001010305808000402415200e0790140010751310510580e24415a03030348a6a00f90340001039007081c02d0b0403686e5a0383d203400c41194410000c0c01070321400e20000c2a060460400c040000f402d1030b042c0b503101c803c032074003540c1c8500454250350001000201000c400300d030b0080042c641190002403c0b440c200c1b0a91050320300d00c003554840c07210f074180d15240c5a107503400e202c0004406984141844104806040780028250140410652035502c1021441d01241c3c0242540d080d680b06a05540200e9400c03845101007200b04400d807407082c180b038070442e02c69442030022845144409081440c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 666023444 1250 666022194 666022213
    0x6040b040812010f050f0d03020d05130504060f05030d0c0c050f0d0818030c011103090d060e03030f090105011d04060903090503070803090a0801151502010b130b031608100f0608 78
    0x44070740030064517426203280142541e00428400030904201c806400341c1d103e0100002c0c0c0512403801054150b00d101d861249450381c480c085000d4a00c036401003015060090400d0001d802c0c1042441c40ba011103240000003003845031600100150365004082c00748604800010058030350200c2100400e600030b8059981e1011842d456408010644c4128441d0061404803442c5d1341c441d130310000c0c664000c40301a5140542031400c0001006005404903a0503464208030782c0806014000745200301743c2a4466045460400756290031103005070040c22a00c81080402e0080003007020040c2d5101d94031030700004011050382000c6e0b4014503180e2141f41d1502c41c041020507040c8020000c0e0000e89000d0b075610062940340d0307802c2800c0c0e80328071928000c5c003104a1010045820340700300c0b400e00311109000024503140c588001ca1480850020a404c00c0f6803107900010450404001c00d032040308447c58600741c0541490f039825114050004082901d0740c4a00d41005815011750000004204a0007126842c0700f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 666024694 1250 666023444 666023459
    0x60f03021306110c06030c0a05071e0b1b0f09041a04150602060c030919110307030b160e21150405060103032a0f1b082d06040b04081201 60
    0x3e41260140d40035501081090f03013008000d0b44e01809044003030508283d0008800c9616400c94142624114145495070a0780002c0242c41c080c940d0091100b9600c5150030b890706000c110007007005130711103001001f258103a0801001a02c049140c11500840c02c1c802a85c944039010800a010951180c6070040141c24100d07010418000c40c0e80b942c09642d071039503c0c1d00703030781800b8001140d1540e41c0c0c0c1c0188000c4a40e000120b9000c1801512038294196103d03411800b01e860030700185c1046411403403034403c2c481120342a9105211140c481d10b8240751f020318074000300320070fa10003003415000c0071241140c1524505080c8201c02d0510380c08155490310345850300704981d44600c00e110a07030100c0c003041c19501c00000112000300d030003080f10980d05101e1189a44095009161400550b03080c0c0c501c1035500020400507038072074010007907007006005408a0541c555820550040c44800156043d0045255540f010420036841a00700b48001c8050b595424490f805214000380c402507103008400204807072 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 666025944 1250 666024694 666024707
    0xf06200c0c030304030515060a0f06080406060503010e100509030c0f0610050a030f0201141c09020109080d0801050d0f02060d0903231e16080d0b01090f060f03021306 73
    0x80d0909003121030300d100000515440f0b10860002070030b150807050740c1030f0a451003a421950403150182c06003021341e54503004d814905103039070044000558080107001c24403000c0d010700400741c60100c00030840c0c040b040f08060369440c409081300f11030faa01c4100103101c4140074003d5030054001c03481961122944441080c1e150303041102c000401e0074004002080f6400c0000440d400d8a5104c00d02d403201c1e414540040d02c85a171101c8200880c46400c2200240003400dc42e0a8010360f900f5000c040388000381d91001405034581500300e0f0126a110190003a0429442148581102c2c01501c56082615407428141d40f0030481510180d0058800506000150500c0c0c0c0511405802076491303000c0301c100c0f03641140d00000c0744107a040c03403800d007400f5070f14011181c0c0c000700c981d20310320f82545840e00e80c401c0a0400c4840c28408103a418030302c086070304844200d0364001e102c03040d1000d18141070b40504201219940364000e001d07801c1003201008041d54140c1c02641240d0000314001e074000011a582c80000317041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 666027194 1250 666025944 666025957
    0xc0406030812130c030b0c040f03050a1406070c15020702090106080a05160f2d05040f1703070807030909090b190e1018140d090605090d0f0620 63
    0x141c0b181c1000034120742642101e80004540c8280014042c500d1a20b9085c0a540e02401c130580c1c280041200084c0c1c500c460b6881002140b050025180e40000e070304000e0342a6140c1d0524500c0d5810140401a600368001400d44481d68801d103d40103c0c0400c143e80c000a004450000350816010400403078880d802081e60703031040d07a00b0f84061019030b4440000d41c48884c0b0810344030300810300d450301c2071034014058804000c0070a061410320039100700079116910000e18000500010a6001030213102c0c1e40e1600c51010003034000e07504440308451454001642d288102070340a0202d2034081000002c05219000f02c2009085642003800389501c035040080d9480c0c005e65410801401150011060307250174040c190700b00e10b14802400c100220981e41a0103482d2002000c0080c840b03404040340041c0038159110740700a02e09006052006110001400da4005034018209100f820f0000d42d100b40e4a4145250480c1d5000100ca900c0701a1403418101400c1e1010184181804a05072401c000c105640580030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 666028444 1250 666027194 666027217
    0x20309071a250218070519020606090103060c210f0534020f061f08060112110609040e0f01150e1b0906030f01030302071d180c04060308 60
    0x80010000034015410711031041104940d010480c1d20b019041d00ea00e29103100540090000412a5459015100040c60440d46840462000720300008001400800c1303540b440070600050070b25050003c00941410030510000342441d8581c1c0140100c00d1203562001070070040350024203408648118a42c01030120314044024442c0391000049003c200c0300000e10120010420010072724000c415480903881003c10101d040d40306e600d00b1910340314401c102492003800420303c80404c0ea201c03422040c541000c2d9074003800700b95001c040140100000a140700c2051980001e5040780c80c11044007091a42c040d6120465000307160075103004d030100c0c003c05c0c06440380c10311400030804c0b032501c1c00d50701560707030b2050240e1184050b00c400043c2e4407400c841d803006174103503031114150b09000d0446c000500b980c1c01241c000380310b003031804010820160104424000f50100e241c2c00c089903020101c8801034a83e000b001d9130203d010103009400030403030900004907000303000b5109000981c4c483c104800d41d03a012107140304 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 666029694 1250 666028444 666028469
    0xb131a0312090316061e091d0603060c0406050f0d0b15071110050d02031003020a0f060305150f0108070908011a210c1504260d02070f050d06020d02030907 68
    0xa004121307504c000d058408645035103424540034800030074a80c400c00d800d082400b655140c00b141d142450304d1803112846440c0854019882c05e5428103007412005050750701c840205110500c003181d00b14003071712000804a0b00007510b829540c4000c8002d00480a01da5410141c0905183d11802002c00103100445c000e003030342003155000f01c061001003c00e0f03180c8200001d1090000002414080c0c000710b07000594807049010140d140e4001421160141d4403031116034201207010801e0ba50140110340e807011141004180810220000c10078195003c0e4400b41082007500002d41d1581c081c68207080586034290007080780c03c0181c00343c00000e40c00b011800b84907070310201034911003541090b4018480d1207000068040c9558072001e00940d03140400010010742018000445c1d039480e000048420580c400900e10f403208007840c0018108980361040b45c085421401007401340c0c10441280d1003c90380203032004d2840000500f0300e40020b01801d43c00c0a1940d00010903c4902000015903006035100c80c0880d2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 666030944 1250 666029694 666029713
    0x91008060316030308060d080c0f0d0f0807120905030c121e0313330203010302041d1e030c010219080619090b0d05010c18090b131a03120903 62
    0x2d10550056210007030000300507a001440034180b641c0101d135124840e00105090840c04002c45040019228292a0360390201100c84034040d480700f102c80c0060b0701c03410195850b08060300018403840c540c01403041459211070b83d901c00c1090400841e9510241c13101501c80c5510302d078400103035540c0038904080e1400801d4018044003005001100d016a00889540c000390885598040158200074550400a940c0b080c0405181c0508924441259801c200061380d07507055104200071259a20381500d034840b891840d40e00507035800903081c0c0a4001d00d00d141c0e00d00d00c40c42d004c06072651143c244544919400818101d0031102e2000e440c0d00030310115201c4d0300741740c3c0d5a01c040c420030440c0d096860f4080c0d41070000030041044203520005100700081c026440b000c40a4990f00e00f90780341c0b010f4400009920780880c407854250440d001018103100751081c04070612590011380c40d80c40c0d2845140348950358801001040c60382c2070006c400f07054050241e5003001a40c0c0d0000c90190042d810b800c0c0a4010ac5401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 666032194 1250 666030944 666030973
    0x3030a111911100218040e010e0a0609030f0504083705010603050706080906010905092b0e10020325020901030c0315052203021e010f1103070c03140910080603 70
    0x988222118000d031044001c5e0b10030b0108405081e40d0200d0031029540c98640d03241943c002e000c0303200000d01582d4041294051454000c180c86202e0707904004025081c0020310032060302060210180e55080040c43d81503000550500a88010700e8600f43c8807885d55440d00200203041d008a001c403401402071f02e21050b0386034010754200b00c0c1120301059582200c2c00520074142c4a620458002c0600f0b41140d0b040242041c0034141520340140038440341c81c600e880b40d03102683c0a031100a807404140c500b0000611100c101a40d40e000d520380c000c41d101c00c8039a001d504014445035108180750006c1802c0069652410030132402030040c00191003440320f90705510b400d0134040c05a00c2c01083c00402139201314500440640c0d80a914080803411402100e45010032811070504007181840080000521420646504130458060856000c0e8260f400d104110880d85c02c85a46c16449406040005010070758022100c0b503031050f011510382c056146d02009010b20703800307814580300e02d50940032140740d85076001c00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 666033444 1250 666032194 666032197
    0x801091a040209060d11040906052409190e03040b070201080f01180b27060f0d0819020f12120903120604020a0c060504080a09061103030a1119111002 66
    0x740a0340200e01c06010032004e0070031409811901b0302514a250001444200040564800c4002514000e8035041404501d01c440b50112407140b8000040c010034028080101d40b00d044001e058409524850041611480d40c82e0419403180410100366991031743c85482416054004440503070000c1c40c4107000808040c0d101c03070700c0c6050fa004201200f8549141c0704180b0050b0401c0710909400c20f41000d100310301d1010241940c400005408071605203403812105004811481a0500340728440106050010541990840e69220100d80941a50021902c0c003a031518542a5249209108001c00c1450075084840903052555500c004c2c4070040c1c0b0b03011102c6640e0b020301040004100c0300000440d44e07500e030943c01400100d10030700308000020120b459610450704215410740380800002a1815080e60014200024119500300303004040502d4600075600d0100070080e115491703482c04800d840c0a040400d03034150300b4004136901100c84400d20000c1101c500700d8200c03c424070400503070b40801000c500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 666034694 1250 666033444 666033451
    0xa020f0f0a2405090c040f15050d03020703050d030b030c0109180902121605040b0d1703040609150b010f021c05162a090603030503012705010801091a 66
    0x200100401030702a180d020000081080200840755006100040c4030100e000d850301c540c901c003010f003220103964401d100c2501e00044070012058640174076000959910104441030f540141d403c0042a009447c0c2a03181c00c0700c50f0400fa20078860641c06014850341078004003515501a815103a51034040001926009a580100800844c620890701c0c4840160390181010600050000004501c2c140f0000c0c181360f08003190a5065108210500c51810700380120844408152a0f24965488503201d540c02582c041d00d12085550001010505005254005002d51900081002090201041810014803a9800c124003086034484e00e842100c0c0003044450b00c00c1c85c41618107000302404401160f0340e60181450420000717800c225000807a0542c01034a00c85140444036007800d2404040e0b0700c805003500d5002092250400740e09000007640601500d0440320340180107001c1910305140000c2d814809100d0a00c9207140400000b40c0d88415000b440307515000f1003581c00e0019003c4522480078500300c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 666035944 1250 666034694 666034723
    0x306040201080c0d0b0a120b0f040210120e030a0c0213060806340302040f080102040b0f030402011e08011d25020a0609030c0605060d1104020903070b0d020a020f 71
    0x1a000a0000f0700900081181034101c0c0b0002030304c1d01070403000824905040d00420340c980250b8549034108809018400d07003114400b01100002d192542c001100b0f0804030b42480c00b042044a802ca20402160b00403503123046a81e010350383c03540141103004086448100b0141d00c00c41c01c85c12400340d400558441d001c00d807244180038012941c0c8060903250b910450103046240ca44060700405803c4500b01242003810100b5507015944a29010501c1120340c140d8100744079603441048204450b0385060102c0fa1070903101550b070707a280c1d6131350b0005031603049291044a4050541ca042c8140301d90b404107500c0e05a03003101147d19104c00688400d050b00040c21600400c04001c881c0e50080035602040810342d000000d40304070b0782e07005015501c4a0903507518400440102d56100b40c40800c0040c1170203850780c402030580389100480c070207444520144040043d2a8011580054222035540301441040301429640284039600d40d90f41e80f000c8005d41c04a4645070040c09549110900e808011a2410124046 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 666037194 1250 666035944 666035957
    0x9050906041208070903170903010609060f15170601050d02072a061d04091a1918060506120a03020f0c180a11090d050d0f052d07060504080310050306040201 69
    0x45a42e201c1c000038500f1f024554401081c4020a8190b50074000d40c0064003903040c002c640c6601d4820180c10300401c5811410100b802d042c0100e55882e0300a901180d000840c40800c0705944541006032450b1081c403104000b440c0c000500070301401803101c1040d40c62141c1c60010b60a0303130460144c3c009a282c0901070040090803158541c4041010020715100204001303000041d84621541d8001d900800d00d01e40c9400d8120030010080d5204202d2081602510811418410240d102d1112200d91101250060103541d4946c042955515110f8803000a9120b103000c50f815000e03070f03041c0079569011210300c110007031084c0a01030300c0c542041030b070302c1250700c1200c80452940c0e1a050b8900d80a00703410444d5110344007040c802211580c2c4c641418032040c80c001c601078030380400554030062442500c074415006001e0100008020b1400c21583c124200b580c0d540424010b15201c03d0b620a284600380c0c000d840d1500b0b00090005110400004500480120540e603008642e12010b00d5100c0d00120781c00782c0400d50 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 666038444 1250 666037194 666037199
    0xa0f1805060c01141608070801061b1401021c1a0d15180b01240f050c0f071d0907030f0602180a03080301080705030115051504090509060412080709 65
    0x1d1920281202001c00d000100c0c400c0fa0a2900e08130a140803203e5801c40031803040303829241074210300300e80c2d040700b100e142c450180e40c10b110000e03242c0401e45ea03c840690052001c03000c2030001c522000703040302c2c0d480b100941d51007555040b480c0e040040c2d1000b012000f49025071900949046008648001002904a0502c100162604001c50154142d003051550711098001c0700c81c3e803000c00e0b21000500c1240071400650506900003920388104456903255004880020000c1d5000540025484160302c2d0150b40c40710403c2103681494100d010913500380c030174980046950070a0100c08041088080c40081d09079455611081d078510607803201030a001780301513560012803403903001442c0b0951600524440320748080701060348107005070320650340c005010005106040c02440070500601e002c0f0028400442008060a1740ea015881124820500060100d4134900c2100c2076034010501035000f00040d1030102c0e0f000381c581000300d508a0742c0036143c040e1001141e02038035240d8010015507440581450 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 666039694 1250 666038444 666038449
    0x206100906050d0b040c080114040605150321041d1807032d050a030309050f1f0e01060510030b0411120f040204060b0d0f0506063c040b0a0f1805 64
    0x2003c5c0040d40d51115000010515070741c00d0080c40c507082095192954145400d082c10310840782c014060110301050510650031035540000c5101d1000b480380400d008440107582c17404050312482d44840170b000020001004070240902c0d001c0c1c850760140100104003542c40300c40d03d88031121408028003201405000702d04281d0321209500e40000800d408408400c030a4452a00d0914a0780c412800283c4910100c0c04100c0180040000c0404400003002180701c0d03003000c251481c07600c1010301102c0365920500740c5640d60941000004100160141c0810741134088001c0140c41030604460069041280200c0399151500486482d03034541142a1a07030b444044400b24513410180060b60b000e600e56801103403102c0d20800500650348034800c00203e0021042c0328038207a43c0000c3c6281d1060000340103001c40041038100d2a1401c0c81184903000c0c6a41103001c21113001441c1d0a00c95000000108022030100c0c41c81d401815000b0854a80e248030070b072040011181d146008045072002c45440e00204000d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 666040944 1250 666039694 666039713
    0x1203090605090103290a051e0409020f040513050d0503130f0507090c11060c030105090402190e0c0c0f0708211b0c0109080d050909070c0b04030206100906050d 70
    0x5460500d000f140c04940c0c41c0d038100c0d5112170034a02d95081c3d2a101c1e03101550b4503001c005903004103c1030b84c96482c0307001b412030311030310440d842003031035020315280c4ca5820215551400026003401009008001d2410718008016000250f030034220b4003482801c065400f228001c1041c1e0b0312400000d403040c0c0c0119010350742e015072010301c4030046a803440350b1040442d05244501031480140b100d40e503442c61095402ca1841d2034184094424605850204014012a00c0b4645240e50268040c1c0b15030391030a0700c1c4041b5205441241e8881448080d800041c4210340740100020060521190103c5021600440102d9200c03c11442445400e601c0700003828101c801c2030013204005202e0030080d0b41418094200420b0707895a03160250126001520200265a00035020b240a0300402c03004288075681c415000d8101c1c4142020584281c400000240d0f9140c860311014a507503500100c002058103041c540a9074850701035501c069110144403001c144046a80b081b0f4048481c01090b18060b00d0440e160794420 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 666042194 1250 666040944 666040957
    0x50117040b18010e1c182312010603050d030501170604170c0118030305010e040305042105010c020703140a051209031908030f15032a040c181203090605 67
    0x10b0f54903040b683c03115000510030003910b2803000e0144c0354000308001c0000c2c03100340911012440d0800c0b48405020b040a001001064043d032011001382000f010300002d88820700d0707150605810b41c2030040c0482081008505822103c849403020301859803100d101c032848255000384a505540b000000070040740f22101d207180c030004107a0b5980d203060300c0241c9490943e04001c94854003000915440e000305036161095600612840403048030300d0900c1c0d680102984194840d400c0f60090300750b038480d094080880c4441d1a0755002000300a03103140d0b8180070b519006140f0050f0384026070440c5d14000351502240c440d500d9a40311010344140a415850403d458100305030030f941600c910506180d203400510604003c03140502c03846612480c2c185450104400000c161804914034070040103800e0f2070000c0c2007900b400710190b04264002090301001030000c00b0b41c0300d41e80d00c541800d594080c1a50000c50101150540c1c0c1c4889a0007600c0b99401d050000114000400262252404000c0584610f001c0c0c045d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 666043444 1250 666042194 666042241
    0x1501030f0b0a0602030403020a090c08240612040c05040501060f18051809061f03030806131112060303031326042d0b1603031d0106050117040b 63
    0x80c05000034010424895450f000400980d100150500643c9000e0701000000c122100f4140300d800d40e4194010140314000d00700040d05d800810420000c02c00705240c0b00b00a0380702604c02915202c41442ca094080c00c2a1400d40e0340d240c0010003c0341a0429005881c10f072503d071340300c0d40d0309113204610031605030074000d610000c40c010072000401c441e510314001502112103032a42081a050004a45050006c003a01d000c1386401c3c20066221042542e2081d441100c3c5c06040410f00303582c4000204030180d10346a0942d00440ca0701e0b605c10310b03415007500034184001030202ca20300b041d070f580740030705644c0d1009980b101c0440c4650100e950018222425112154102e880c6038882107030020903060f120b40080c2c115a0810002003103480001c60714140c085c0c00701c04482172070080180f03400c003030014911987d65810b9419460300403102c2494005e80115004810000c0e481007107600c0424607d0081840703005d00c900140c926006103521015404c0c030540180e411444c0028103855800d174104055082011014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 666044694 1250 666043444 666043451
    0xd1e0f0902060901141201140306090a170a12061511010b060f0f0f0c0c15070f120c020303070c060315150c0f0203030304120e0d1104051e0702010204090f051501030f 73
    0x190700d2000402a1f00911882d552040c0b030507040010103003414402401545d155200c0506080420f0b06071107500004070f80e140f03030729541d6444641c085030041c400040400c2041d0402c0c0e07001500d548446007800a0181c01c1d543e602c0094584101d460076602c0d0321200d6680000c0910070100f26001e030100414403204400721440c541580c01850f60b0540c6c0040038028403e4025080004050030156030764032403503040200003850080300341e944036072a61502202a00c60342080403149165401441d114031065002002c481d25200d00c0c0c9019100104a402a200020b04002c244413803c040307000c4041c00d03210144090307003180c0e4800004489180e1490000d9a001206600e00d1700561014030003075006074001e040f01c80400708280070290000d0700d103002a07070103541c80c409864081410092a00301a030011180441d0a444641e4a80503005010518030f103845000c0080c0305003942c05500403c126409a0001c1c0804030110340124219074049600f0100101030740c42c0f1019641c401e50000d4421810a80e002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 666045944 1250 666044694 666044707
    0x3060b030a151512050a0b04031812051e031912020c010b04060b031306110c0303010e010608160c021c08400b0a050d1e0f090206090114 60
    0xc20080c00c44240b107450030350f034511001e01290f9002070010302405101007072980050250361460358404d40c8a17400380801581e04082810503201c2c904a02243c05510300c9858699251300094031480c4141070112040c1c45480c201070b0307641c0400a000011241c06001035400e2040401e145c0840101c240c20300002c1080040301280c861903148060050010400000226440c0040601044a009411140401c50144104038120f141c41e0116840c0b0799200c040481d40404000c00d103161402000343d802010b000200008c5081c5005060560403a005580c440c80d854070341c10800c0300d02c03a080121200015101081c10300250401d41c0b102c1e0383d00000d102601240364080d40300e01089400200c5000324102d0078041c881c492401803a001d43c0c200140706202c4280403c06a441030381018584100a42d1000103d404001c017801202a5202039200d0001880104690507150740a410950595420103290074521012400c0d1071042403802c40d40608140e150005d15801540c41c2140100380c0d850003901000403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 666047194 1250 666045944 666045953
    0xc0904240b0603011202040b0118090f02090301140402010f0824211b120a03110f061f1d0601081b070c050a05090f0a02250507082503060b030a 63
    0x35030080445e05810302c001006441044207072011030f0019810049000c08500541c1c503441c24400c100d0f13070141350019030380341d0058035140a0700a05103681e60551030090341400303503808520103522840c402d82e07521200c5241d2207000e4420035419108401c1c01021501040030003160010010f081070030080941144c44010100c04459032117108548000760041708483c0075100e00c452400c000c0e070100b10750f0807810207a056400d940da040301c8080a801c01c6404041c04031503010178803910504074010f0007503901a19160140c818101020b00c1d0214140c240700c0e900003440c01501c004004c0e982102d2245100f507807640801140c2900018041000c0b100c980c445d00d812244103100207000700d500c03c0c400740c04103031700d03000800070312106503408240a1007110007000004008010040c2d801300080c400142c0700c40b005440b0043d1030750884001210820402c0c00f030410f206002a800c4203c81c40d10048480a2a00740c0322850382c0008014504c412104100040c80000e5042c0c210000040d409030444011074299280c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 666048444 1250 666047194 666047197
    0x50112030f0c210309120e01050d050a090206030901020a02070501210b0102030d090c0e1803040605131a0903061503070b0306062107110a0b0403050313080f0c0c0904240b06 76
    0x402101084d505d4002c4020402c102ca20006004140d060640d100641c01d00040d2051241c00440140c15548000050302d104141c2d001d101300c02d401030138281d12881d24100d418003d500c00300e1440c025101c1d41e080020650700c5000f881201d11045030f490038100c0d6501e045400035044c0b254020341035020901c60030a038181140324041c4010701584e100c100b42c51070561180f800c3c100103802e400c8126a5000c100a0702c490020454080701c003186007980d0b54a0780054540800007440c0c2203119040c103008203000b10710201c0005442c5203030046040e204c0d03d03152500c020101000c9070f1307002d0f50103400035a02040b5911700d24015660088025106514080c500d169185003861303075240d040c9210a030030080c00388a070b034041a03107000c00210340c0082c100c07030310f0035282d214681000400003001c0080010000d02801c070104002d0345410303802180c540d201c040700c900514040c1c00012141c1a103114607201c1e45210f00c0c2c88082c09024a402189242c0303d0349840c1c0100103107030301440c0c0b0300210a868000b1617400c0e495000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 666049694 1250 666048444 666048503
    0xa17070507030501020a0509190506040e0c0f12090105061813020609030d030912050c07090b0103020c0105041203110412022106010324020a0e011b020312090301050112030f0c 77
    0x54031183e0b140545030402040c0106a11050204d09d1101d0b400d02464a91404a9058070f00801142c2c4203503440c0d403181220f500c03070424690444034010980601d0000003e030201e0041c1c021030024000c6a6600c0305001f00100103004d40c1c0c14031004980401d503d821007600c4803041d68005030405203041410320110380780c400b9080c06800001d5480003248180001c40c0d0032541010306500e880c1d40341c82314034244031360b071520540a003205245e500c03104400d00368003c1d41290019404d0100074052480e01d420920007060880034404007103402d14035007500702442c01c0d007290192400c4414400c14845c3c01d4007030000480710000346014800111106105e00d0500700800ca000354030035890222110540f40000b41041404050401007d006110080074580c10050340380c1101028178181c030b110014200d0480c005200440d000c1d4140c0112140c6000b210500c0c0c004081601e4203030001d02c5144d0ba604140c03203201c490004040d0000310518040c10100d0300c42c0c1c0b10005101c0c00390075140c034110080c40b11408202c3d03014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 666050944 1250 666049694 666049697
    0x2040617060609100306050c04080a061a010c0c09090f050a050a11010e0f0906010306170705040b01090b07060b180c070525050411041a04170a17070507030501020a 72
    0x5900040584108460365100b03400340c52071100340c206030100a14000c100e0100034611a219000141d030450584103030360007004140211224806942042030003800b018110008000e00e8080444140d4058442c2103001c036400207401283c2171414001000408080700d040305c0790500c020000c00401ca00f0002c2c0d01415004201500021a851400305800c403d901480d5051043c210092085551080c0c40301c000c03803d0a841c191111381c0d9441c0100c000b002a5040040d03e80c41c100b0388a0030034440000d01d1010342300302796010446440204010344241c10b1303d00c110600c02c00100b00364000142580c00001100c0c0b000b40c590160089090040c04038802d04407005150042c01080d000f003407000800400c80070419002c0142560040b0103001c0903051901d000d0f4078025074480300f81c48400e17070000c0e003264001c060038001e03d51588a03a40c0380075281c0d0702610030301e07124042d255001039041d00041a40e442d4141d210f0071600540c030702040000100d400c1068242d455020b000c3c070010100308280004c00340c0e003245 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 666052194 1250 666050944 666050969
    0x162703050f24010f06110a061a0f0909031b070b0d09021309080318160605040312030b091816030b060a060309121b0f08190c051506010c020406 63
    0x9200c000039035030703044078280c5100942c101c0100594002100507009440d428a40030170f02100c80c80d08140380a03840304008081901d8140016900c502c16040c040c0c038003c048800d884c203900e0f0f100411502c2030081c0c90980070341d04100015640760369408844400e100e295001c0d200c0c00c50f0b0320000c036000c070703002a6208140e030b40c3c4442a900c01c43c40d102001c04862101c50508100968a0381c440201500008100c0600d80040d43c14003054100108580d481c0c00e140304c4083c40d007598079440002c1c00340d002444112210050000e020031580d0203401201014030002d44104c05550302c03016513015103107030309454280e03e000f0a030112000740e4120035050042c6000d6502c1c1c0c99141449814400f503824968480d80406103031040700300000380644840c14240b01c0034a4221844400c1504403000000030710300013031810001044501c100141200a40a510345455910711140c0e800c240548000341c60070401803194000b031030034260348442e8250080c0c00000614106000c600c071580414100d030701c0c50b00500040c080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 666053444 1250 666052194 666052213
    0x90907090513170d0525051b1e062a070305120f01030c0801020708030a020309010b0604180c03060b1911010609020c0f030702180a0f02030c030609162703050f 70
    0x7013900426822010b694016003e245c20880c9000130ba0940075004410000b00144052503083c2820b1505031152601c0c051b10006542035400b552651100300c2c0030409030243e5000100400340a40c0c4586107040c01401c00d107000051482141c505a10032001182404800c2c05175510081d5140d101504c951103400d80343d100c0c0e505505200c00541150341c0b0800060f0700405c41c3c00c2c0054550b10a4a800250000000d41c40e0349a07460b1840c003510050107107540003a4041b400141c2d101c2c001d11110803540b4400410480b83d4070100b801c50903200c1c075020f100c0e07030014100591035602c00340860482184e10180340a6050708034050005096641c50b9012400380c030b03008515000344000a10942c401110010021480c03c41c041d408569512681d141d00301a645440000a000103803507003219050400c4148210b41d680f8cc04c3c030040304140c00031380b042400742d80c451740040da4200d074030301310304615141b16110029454240701c00118450407848203420302e8400e00d0780010014804104001026000c400540405407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 666054694 1250 666053444 666053467
    0x1006090e0f0d140c070e070804031101270204060e10051e010807050c01060e0408030a0f050108190c080312071403040321022a0c09090709051317 64
    0x90300300048198100030030440d4590f80150b02402c0034418403400540f00c0b44420038030f60901c1d4030342e801030306141c5165081224083e07100b01c20034440c0b44681c5480d4903105a0060442c203e03409a140000804030702002136200000d00c1c5140c0e00c10910091004c11429221004280d00c0700d02540c03200c8502c42d96007410700051420303001c1c94641c01d448064892880310320a000030b000c4c82c0301811083c10707c82c2c00101e50500c80310a40048019021740210b448203030500d481c005032a0f910440e1b00340c03142c1d890103104400c15a980d001d181e04882420008081d0384003a0019003d0445000c0342c00c48515008000024400b203003807001d031803503000c0c3c00180d5240f4509020081c14203c041c50b58940c40034410020040083d4101207920104080039440c02506428085001d000f80310f0714095a0060140e072203201d03508110341d020410720700010000c0d5600c0043c0c0500344852540305448100c801d81040d48240590802e80d4030441c0d100b282e01314100306201140e1198003820f46040c140384030400c030004e0301a690f00b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 666055944 1250 666054694 666054703
    0x40f120e0111061302091b13090b0423060f040e010f050f040312090804180603020a050307140906040603080c0f0c10020a030807090b0a021c0e030d0503091006090e 72
    0xb0688a018140d2840c0603203200704880d1449100038820312200c00450401d400303503040c0034403802401d5034a07035030f440385441c200c03040400c6842004082c508100c070150141c00e0502400580c12181c80c0381e0107242c07102103800024400011314658000000b202d00030090341e00c0740074006417000395200007c1c0c40e00300c103c902000d8840043c500c808a5040c4800e110000781c0c0700480c0454846071b00d000055144d120300d4603501e94821780e48886130340090940d002e845200796034401e0b03044a05c00c0f55031541c21699a03041c5038841e013003481420f6a000104200191074180303010300c6a4040c40c0100300007055038036541c543d030a5802003203200005902010320f41c4c0450800304660a09184102d62080030001030410080d42c46c219504000c0400074050701180c1160b0183c11854050481e00e021252280080390000750b442054017045402615880c14101005003d00b12118602a014001d460300e000380e07a90580c0c10b5403001e030a09606105600c484512a0240c0c400c1c0c8028102e03820002c2201d040039030005141 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 666057194 1250 666055944 666055967
    0x607470f0109090201170a0209091927020d02131112010807180b041401151409061b100504080702090f092d010501061e0c03020703020108040f120e01 66
    0x21a03e0140c1c41000743c0e03041a8450f01c03181122402c034009a95410400300130703004881c4403582148111040c000c4803265400c41824100c034068080150750a80b0300d412a422011200d54581d00003690015009410201c0e110751442f400a01400e07044150061060f0446420310700d5030320b003a0004503591280d109103c4a1134018804200108040d034100380820b0076020003441107010007581e854a908041c0c071107400410326085115408012580e540c1c00c0c40480021000c52100002c2501c00b5500045410400341c407032400014000e82e003001a48103004a030030210038040c802c28890b946811002c030071a405400d2140e4401c03031182d1780326840c501c184901c0382d01c007505089001d41c04a04102c00c44000050950440e5040290728080340f0214040d0700120b00a040000c46550805001165035a082007802c11030400010b00311400210351101100d03a04c0700120b008005801aa5041001d50303c00c00e03901b0341090040d000d580d2046095a1071050100910341a000410111850b000341d56030000c010000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 666058444 1250 666057194 666057209
    0x506090303100f15120b03060a0f150f06110f010c020a06110a1409010302070212010e0d020307032c10180b09090c03090a020306010305070f050607470f01 68
    0x10b10b07a0405000600b41c84010130f6040400c8001140001010265041295100c60250964046003400c031010006840b000e60300d24030309414001c0032108062000a40e00440303a407101c522617014200300048410300040c60400c1f5051007500740c1021a03000a201d00000c100b0702c1e8000b440480414038104003500e681c100072001941d01404203d80003500a250341080403032400d50580d0f11968003005078000d008421020b03420040301100007045400541c0328502c003205542c1191845046060200c2c2d8900c60804020002031000d8071343c4c2805030044c22441002c034201c0c00c0880c400410b820125107200c0c3d004419a00245d4401c1e581245d181c0d4054540010300034841200c1d152004e01c80200e20f0300b030700180c03445149050000004902000900820507880d40c02400d4545959407820301a07035030540d5028000300130000050001d0b00d46020402c8807600c2d40d0191076510102511070f00c0441064401c0b9001c0103281009040708182e000902001941628501c41003442d8141850520701c5210140c00406 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 666059694 1250 666058444 666058469
    0x501050106110c0111120f1b0a031b0606030231021303110621040501050f100e060d022d15120a0e010c0305180c0906100c050609030310 60
    0x201c0000b00441c10314903640003805d00880788940035010b20300c0d1801c6030780e00025544001c202c805240100b03034018402e0407043d10803800350010900f1002c0d140d41d190407004010804d56080800c40f0303110b114403803414a0140741c00045041e5a500481d4003d1032000100e40759241c0c0c045500c9144601c550700450903c003c0b441181006c46030390b003a418040c4140005440f070320311028401295541c0e1802c40744001c2103d4125001081e4034401140c40d89410780d0708948075401d02000800340440c252460f03101c0d060344040103038070610f00020382c8542000941055080030b6904122000360320394280c4000c5d043d05410801d903090b440390451800c9082d6148030140318010504003100007228600603101d460b03076016003c184130303190031401c10004e00c080001c0d21543d50a0444000b40241c00d90300952140904c90700203081524441e29054071011002359031984060a9404500c04c2d00701015180320322009401d0038000140951074003842c10b401185d031074030f05900010400007081c3c400c0b10000018014121146e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 666060944 1250 666059694 666059717
    0x10e0a051305030306060d110f04080706170a0c1704080a1d0904140f0106060302071a3102030712030f022a04110703080123010c1209150206040501050106 68
    0x2c980b02d100c0600401c3c46000041560402c1a840d940040c111032034010005d03075603682851580c01c06400c648900980d03400341160000b0320a000c0c442071201041c1c954803020040d6202c140e440300070508000c0e004104100f00980780800186c621049010381c1c011044507840d0a580c2800811141c2050101d1000000c155101c060585541d4102c1e41c025520040c1116000d00e50b66450707140c0582442085111740c02c00c0e0340002c580750554000c120140c0100442840714044a0320300c902e494081e50214004404000304841d20286408140c1103244141c81d992501d6a194000918041c4260094a1404c1030000c3c0c0c20105a04103070021021881400034028000c0c0484501340e2006410480030071381c11220168114030f6886a010700705c0112002c140b0b035107901d524280148600401d00941a224000321032190082100000304011b840c0140d40b40d1548072001c1d46c92440303810000808105000c004103007c80c4c0c91010088800e0440b01c6075006165a281c9400d201c0e00b911b0341a403054040c0080f02030710 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 666062194 1250 666060944 666060953
    0x8100903080f0402030f070608010f09050402130f0209130f06080c03151317030907050301020c0a06020f040902040312020c04091211071703130e0c0a1d040203010e0a0513 75
    0x1c503039005a120450507469521400482e007400c45000c0300e001c0a018941000c107034182c000d200716040e00c45d4140707441c039866196075044040312070985011798009040310f00d10862442680050300c04000031180076042000a40103c0c42090704000d04840b402d403144561201781c3d1030f600c85c80000b0f184071740041c01c13440030f1232000c640ca4801d8052421304001c00b060000d40c0080110001841140d0b001000c03021400b9645607420749a00161801c1da524090480c00051500d014020b6420703040305400038185e1000103990704402544000c3e220030000509104c0001c5103032852010704020342c0122907190b98020315900082c100720fa582c0e10a48110f1401c40c1e0039000c141c040e0405541c440b8141050702c1c0c28044040080c2c40d00c0700070f41c0714542140c050355451030441004000b8001e007440714409000c00c207071103500202a4500c02c44079055541c405000d030003002440b0341142003203402020103040c0f9804000c000b00c1c0987e4400d820041e104220300e0140080e07100207201e115400070103c0b44c84241d0b00307560b0341d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 666063444 1250 666062194 666062207
    0x70302010c12170a1b0c03020717010f02070503030603060a0908040b0319060303270b030604020702061303033903031a0a030c0503010c0f021c090902120108100903 72
    0x4024203101c06907505006a01c0c003403c10001091803e10100c100c5260200d0003002500050b001030b0a040390040c104030a25009501c12090340b6416005030a066003002441c4024018100f042640382d03494060305101515248005c0c0304907030048000d1940c07440c2a905240c90024040c015589a03450f1104400200b08404180e03070075205410400d5a8a4451b0040490764184040d09201380501e000400800c0581026001700c980000e800494810360100c2e0f200303580c1c0c130110f101d052400141040041c14519103607000308a920320003080682410740d014900e500c8043c1e84d400840101d61502c1c4821521035100d10241c1c3d942522503450543c0100b040c1c05102e40d81100f850040c10b1540fa1045c090070409484002141c84001908203031002d0b649041940f030186491260a01952034071240248540c8030702001d402242c1580c004003c4403000541d5000b824541c0c2c1411010031031a140045801c1e81c85000800c1e81805030782800d800d550602860904291252003000101071a02d94040002908400e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 666064694 1250 666063444 666063467
    0x807031a06131815020a05221d0f150d02130f020a020c041802031e010f0c0e0f031c050310270501092717031003050c0307030201 57
    0x14005034807500c500000c40d00020300c00e0598215a4140400c0c00b03411000d500742d40d10054000c10708807110402100541c0201d114004800001030002c00c000320302c075001010740d0000d01c0c01d004500130206a50f400c0c17150385100030a071404522510001407158011150300d070310341c02010122180c0c540c604920001541e0042000c07000340907455034215505005400d5000104003003000c43d080d5924401d0840003034079551100c1c03841d8450381c0303003039849188602c0d40307a04c044040751701a004100a19601d040c8003107450324958130140546d210807403035072400d61074024144030b0130407a1644202c926a440800c10200103615160303009902500d096811034420178020542006203040040c1c0d40c0d207451024420a461580203144810000410b14100d00c0504000d100740b40d050300c0c002c02c626600d0300400c0c42511804001c482101c21211030300d03001e40c02000c18070840d840c425640310b243c40c00b40c00c060b0103083d04100d8079909425810782080003406402d120044080c042203001d000b0311402c50380064200061032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 666065944 1250 666064694 666064733
    0x302070501050a05120a110a0201060f0e0f0705070501291f0206150604030209070801051201060b07030f021006060206060a08011e200f0d06080105070e0603070207050a03050f07080703 81
    0x108081060401c06e41c0c000d60030026a1041182d0b509411440640a0409807041c000104400c0000003016118a0151801a103040c030b52103950740c413501c904440581040c107040d1460355807068508041d14400c0240e4a19010f13819008221815010400c160349211806110700598804401170720181d0225000d030b40035520010751041c4c8114500800c03400d0089800080d000f0b544c080600044039080b001c000e0481c0d40842d05010403803110180d00c0c0c01c0c0c66440c802c440c8462020f01401c00024010b03100200041c0c420310440d404d000c1201c0c440c806403422984020007503088201400400d0410200354000741c0703081c000038000c00e0000d40b00000d80d40030a100c6da481d015038482003403404c021142e241c2100403141442158803800c80c01d00c0e01515a0000c3c20306e01d192845e003000080c8008060103114840d0b400c3d519020b40044800c4144240790348000c1550f03046000741040800c03d6618010508080c500810080c42d440f01061400d03032030440b00e9000741c0019407002c1000c1000401c0d901c84051240340c0b4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 666067194 1250 666065944 666065977
    0x17041208070504030b10080705150418020c0307030305070f0e030613050a14250e1503071706150102120d0c02210706050a1509020903120307020a0302070501050a05 72
    0x18071504035414012a0401030800800c54188010700c40d62100c91403c0c0c501c2e1034103883ca43d43d51007040140c040c841e001000119003040c88100800b41104c018040b402d1074a80f4090302d01981035205508691006404031701003941c0e54203100e00c080c0d00041018032452141400d0003003001c11000280e407030710020031111070031040c2a40d44003085814000c082e1038607440004c400d07100010410143e120240b070f540005224843c010b5540e4461520403180c802c40e20052181103868503800f045035203000f11190f48580501c16100700191060001410503121441c82029142074104100e030b00d1040d18030902d0690466010200032850303240810120391015600000c009051184010181e0518102203a50b40241c0d4004954082c40c854107001404a50321441c0c042104d55104030a18044550582c0200d05507007401c182401404081d038020a0080b40041c21142c084000e016042503690080300c00a0050308600501410560100302c808060602400d14500348a00c14074010001d0061071036002a94a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 666068444 1250 666067194 666067201
    0xb0d090609020d0c0608070903030f0c11030f0c0118062a0203192108060d05070302030a0c03140f0303060103021b060c0406020c0109050d0605101d0717041208 70
    0x390360018008039400341003d94464034608102c01139484501c1101c0100b04040c000071880c0d481460f484040d40d5154545041c405d10b911802c0b210564060710407100340c2034580340d4028a80d4100200c5c014172103c0300040407000c050000050207641e8803080f1507284400103406004c42a04207080b900300101350091102c0001c481c45d24000701c0c0c81120006901401480f1000f41450040140c0240c25405950303901c80300d203500480210340c1c421640306000080c040d00007007240c600e0560044045c01d1b00030400c99040301c1c0c62b500024204074020b001140c148402e50010030411410340c8006001d8940f5034060204d003441501020380368400184440d04140d80000c80c40c00140000c200b4508100f48602190800e00d04413804002c10360082c0030b80f10143c030071416880750642c4200000026607030043d0a07032120050a40e903040c05000040c14080d082d003052000494041183d43c55078a484810301d550301198109484094901400c4410040c1400b0b1750008000216904140f41c03811261586030905483e80e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 666069694 1250 666068444 666068453
    0x30f0703121413031208060105070c0e0907173319020c0f06270309090709120c091104030305221211040e1f1a0d05030a0e0603010b0d09 60
    0x81903c0c942c03580c0f0701003d400803080c03000040140741380c54035540702c004407529070000554003401006401841c6414542e01030204104455001d40c10031892303800c803864161900510400e41c5503040c50342d00c0d07030740c016028000c074001c160524410823000001e035400e00d501e101c001c01b90542d00003005412150301800c802001c0caa010b42c11aa43c40550b60113a40d91a0500350f080340e04e40d00195401034514421008070088003100d06500403003422510b0056103000340c2442441100b00c0001c00c1e10082c840284130009a500004a8841845104030b1548081c075051010000480c0c440c9401040c04510034801800040e4020003111083c2d10020001da51900035808603a007000c105800c041041d510310880c03a410080320540860200c0d504840900032090041d03406036480c07111088440002281107224020700c2065800303c41c04011021179400d1401d03d00000c10000b556102046074282c2c03001601c1044654003801d4188141c20485aa80c550351400090060074000c00c844540c4050384e4013400380401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 666070944 1250 666069694 666069697
    0x105012f0307151a03030f1219060b211018110406030e072c0a180804080c0d030e1005040f1d0106030c0c0b090c0406030b0105030f07031214 62
    0x40d40c0c4001c00768034180c00d00001201410030018100962007003400c04c1c005514001c4103580c000780d40c0188881c201455001d9401010801818203910601d9075a0244076141150107510058180014800d5850400d01c0c228aa2a007070300e03090300915880001448000140d41740c0b0300e8101c9180c154804184141c0701d08680c010085c824852510080c00680001d490b0f8142d0001e0b03a5245031b0300d06640e94540c2d01d58005e1682c031400d400601c40e0000d0080b0383c2075007014404620b03800c0340c4100e40020b142c0802c4a031994066240e200190352908001c14200000b00081040c00d03441c07032080e5442100c10010f5903000c2d00c51203030002c0d054414188110082200b9114000b0f440062080c0707400c690030583c2c6c44d0090041e1016020003084005045800401c803c1d020380542060310b0f1540e500d0041c2c2d00350796100e84a000501070a0300003140134a0703107521040d0347da41c041ea002840c090031144115501d400d04240c50070050305032000460b0050032081011404030301e803040f050441404c21700100807440100044a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 666072194 1250 666070944 666070957
    0x50604020916090e190f0c090806040b06090c0d020a0c110d0f020915060316090e0c09040b060403080309010f0605010c05100b1f020a050d090b070222020403050c03060105012f03 78
    0x5c280b030303c205a204007103950420380700722561b500d17020903054440355450307111041160046d002065450205589050102100354850164004c103400d09840d000818141c0e4040f42111001511242480c414855500454004402c0458102030385410540d2483d0700c01081c450040c0c410952040001c10803040b841d8079000391040100011f5403894003041850190b09218201c0c800110314080212391050412420307401841201034942c00d02d00c0b0801004040d03c0841502e54001505000000004420301c0c09940550390030000840e00c02c94840054003155010343c0460f0401618002d0b0313501154000c1414103854800e198041000358082c408140410000107010482510520341f6a0703500b540401c00018192148080e500c5a00300005e0440e1a4801409540720786403003048001d0041c81c0207050030581f151141e24030b003220440d4406800480c0c10940c000d48450300404100b80c41c0b0701c0d05003c101d014100c2401c05154082000703140390018012181c0740e194840b400048525541c00030810342c0d50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 666073444 1250 666072194 666072241
    0x170415090f17040803041202032404050c032a0d0803010e010303020706020a12050715020408101d03042d062a0201050a0c0201031107050604020916090e 67
    0x100011441c100e840c00c020194161a881d0091480004a008900c110f40480c1c001c6030046003041d003070031181c068020401c10100c0e4503100c1c002c000b032010301c0c9484403205001310000c082d107803030314040c140541850081803642e8420380015943c1c000301190f0107003008800114a440c0d4407000c003d000414106441854040c2034480c2c040000540b1300304001134a81a20710030760a442d44a9503401003660b4451280c4c500811407400c0e40b0109441501c0340e0b01030407a160142c010702004104600c540c40407603115400100c50740e00114183c0001507481d00528010560301802d03600400500d90003103491340154000c1d0790100b9881c0011b0710305030501c2705018540001c050104049166039100190101010169040c2603100e40c0b640c8551066011481c03401150701a119686400142c410460b42c0c0c82c1b00803401c90525981c0c42500358481c200901404400d8880c07002051136042c0360041281001000b0550a10418130744001030340c0356070000740f400c200d52082c0d000c500e2544070032074400c10b240c0d040d002c9400b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 666074694 1250 666073444 666073451
    0x7020a030236090712110a03060c030e150a05070c1b030605010e0603070603110d0e060a050f1b0d0e1005070905060a0e061305031f11040303170415 65
    0x3010300524071028041803440655120040266115518002c00c554410b03a40c1c0111204003d444190500b00842a2041d6183c90130148610001005003515400945034156201040051203404d07100ea00781f102044001003800384009a00e01c0340c0940c0c01030198036090340b0790000c525a00e006401ea02502a402020408521501c84528010030103c0c032040d1052030800b80000307100c00d65031140754010840a0041c01910341010401e401078601074141c4100d0440801c400c1028003094441c07207081d02850809062541032080042c800d4481c0a00301036010141401031000041c1410b00240740d080120711001e4503620800c1c0142d00610684100002c18001c84421080c540002d80c40640708400700e880b440b10954845007480001e0103482c50040102d8038209120b00c940c42c242028240c0b400c0e510344031504051f00d9001107410240203044056130814018428424400d69009007052416100b14289c2007a185880041130030440c050744841031411200072500303011042520320341000c000d01c4240f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 666075944 1250 666074694 666074719
    0xd0b10210212012d032d0b060409111003090c0902035109150612091905150c0a0f0f170c0d110a0c0212030705150105040b09010503060c07020a0302 65
    0xd2290702c000701d14041e41a100b209408000104150041d01401c1e082100c000840c8c2e02c000910004181544d0b0070b0f1441a207003070b0b0025060369403000520b1480341d41c0e070303011800d1000c0340b43c10301c074464983d04218022401401000f144031001c0014090310b1583d5500a4003108420080c81c0b062800110381a800100c6032101480b080324230084101e4801d070603103404c0407a07a14010400700e4a00380030b60003903011004109044060080100403608410018180c8107042d20454034107403888460030044a0541103604004644842c50004951200703541020900c0d01c0c1c0c905200034982c4079085440b0081c84074a0203029aa2481001c11108200c00305c25005084e042041c100811904060b5020708840e0901d442d856400b07150106450810841b41c581c103070b040c1c00300e80c20040b644031070341075005161000307018400120f0020014030090b2a00c0700000d00b51541440c0a000c1590716800805000d5070340306004100544000842a511442c464240e507103c0680e840013031098905980041d6000d0024040c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 666077194 1250 666075944 666075953
    0xd15020d090210080f01050621130210020706360902031f050a0e180604230105070e120f0604082101060210020d0b10210212012d03 58
    0x7020740103000316004031081c0b00c0003604a602000c200d640c000c0e00c0800c000108080e00382440a40640c050203c141d140740c03c00700101c0b8014800417108a540c0c1400c02e42c182095080000d444540d42078180f01802440d8103200018100420410700302060701c0c0c141c0025005188510f88524420715101c900c15900ca87d00c0005102070f400568103d01c080411601c03d1240c40c84c1400c0d0441100c0c406884420b00e6071800300b072800803c400420401d0800c8600110190405003445214400c51141c100012001c04c400e050b45a904249680303032000c3d81c985400c0c8a01c09400803030125007a04200c0c3c40340201e600041d5480d04025031200318a045201d90380078042000564400b034070800c08142244040c41c000d0b0207800031140f00a11685000d0307041a80c407598603003540e40013040c000d010114041009180b900c0401c440d03554500740039000822081951080c0103c400c81c0201413680b1003820b504100500100a02004042c402d207801c1e6030202c000301203800c01075400a110501c80e050102d00155803400c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 666078444 1250 666077194 666077201
    0x10c080316020714030c0d23030408010c0311071115070c0503010b0102160e04020a1a0a0206070f0f0c05070905071d01080403081816060c022403060d15020d 69
    0x7815405402010340120302c0400240c03e040c0074035801002449030b42d15035800c3c003584501c10300c0d007900d2414054400c00c0080c903419556a0740c801d000c0d0002c6a0b03883c03400d0780c160700316901c50f40f038402018100000500100034be8004c1d9820a80c004650f003c802d0440030001d8140a0701644d9400311800128241050041060320f80302140c4098000b401034595250049842c1c00310140c1c51004031041040c2404182d1076124078070b80c0188060641296a6155000c403071800b01240b122102e410b1002480440341a4180f00094103ca51030804040c9031148444c040e2280142100e148108103655a5003010720008100040080401500c10030440c01c054000401101d03401c000084540000c000284480d486032500c00e116a8141d550403140f512604008414009501e00002040c8100c0003030100d0710f20f0042d682030040070b480e00c0d002134200e9644148078041c09001600c01c03059240d21800c2c0354254111080f00d500840c00c807142d9030044418641003414083c5c08544044051020841550b094501e52 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 666079694 1250 666078444 666078481
    0x1e05130209090f0f070503101a03070e0f090a090807080309010e210906030c090405010b1b0102040302060a0503060a0909110411031005011b0206160c0f06050315010c0803 75
    0x100c0c2600c50b41d4904400340f00908003912050080c400d0900005c201601c244c4c041c0d9005507900b0040b42d01c2942d02e0501c0750048407a990941020540003003803004958004401c1c480007041900d182102420700000101500001480ea0403410780b6005200c003003011000803103402c1640611299102d00300300400c0b60080c00c190914880750704c00c80c0c0d40c0d000902d00c122603810020440b80d056500d020600014400c440d000601030311601101400860701030380d82d90107114080c1044015817500d401008204400c5511400c07000318550b4410001030001d40c44100c201c8180070030500f0210790343d8440c207011900c83d584c198003042d03540349084503120401803110381203a41800100c0342172000004242d48030010b44000d8425128200c0d20003420401d80d40220a03a01c04882140ca009459801a40206006038480480307500350301c00008a100c10020340c420750b03c001c1d16500184054940c1400005005488050103c0c000c0e0780e9610005102603106e04040e50720070358408001a243d003003402c8950404c5615a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 666080944 1250 666079694 666079699
    0x608060a060b1914040305010e0d08060d0510050c09090f070e0414070806030715050423060f092e08060906010f03050c130605071208040c1e05130209 66
    0x3260000b00644410300380c40d01c00908000b03910402d24045070a4074103944100102c0f24111042c000080415001e104203003840c00c118000d8440344c04800c60050040030001d00c1c0300d02c80c040074a0400042240050011400180c62a0000fa19100c02c0d4200e101d600421240c1c5074001c03801410050049404402d00b0700a40c0e07035403201c1c9103001840c000c0009a40310741e41181c1c0241d0441b00020300640c4145045a040038020302a514020340390221160308a12101d4400b0108000250400210012010900c0100606070000600d2444500007a155229114016040d0708000c81c0070040c50391007611001102c41d20b0340c2c5c8200118044d101401c151999050703a080440e00550004010b0300b03180e00d0013449164140c0d0b9011824650300d2007900213200107400c10f029a28107014643c0d02410804021001c0c0c251500d6540d145c88403441e1406544141d80b0604040181803030a00c000034a009031414141c0b60091416100c19220079000e5222001b00d0741b0035944414614245e070710204240e402005c0c0f00605 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 666082194 1250 666080944 666080951
    0x1202162a0909080702010f2a021206010b030609040503040b0403030906081e16020c030d0e0307080309060a0c0510090804051306030f03030e070b03070807031a0a14010507060608060a 80
    0x15501c07444200d0b14a071034003402000c2c04101400c010f40c807c3c90003005044550600025109101000040031800550ba40800b030500741c1107107003946000d000600626041c44004c052560601c03510f483c040c0406008240540042808201008014402d0314081c14018070180e8440e9540d0600038a201c0325489008046418000454a1041c2c0f0302d0345105046200000c041c3c86894090004c10b00140c60519841180509641803d40f56402d00801d405810356560b40c8106450100070541415115801501d042d03004221035807094035030205603580b049031030a0030b152901480c2040ea0400c110325a05007609490311628000f08090704026105031a400d03200c154650b4501030780441210010f010181400c0094506880000d1180e04540b0440640350140c44085556400201725070700240d40c03020100c3c50582c204801103034144135007080c00c0c0e021691040042001d401003044412240600741c00081d28404612030350340642c0131100340e40c4d03000004000482e82c03a0342030341d2294800d80305901c00904 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 666083444 1250 666082194 666082199
    0x10c02060f0f180f0d0b07030f0501030501060504051e060d03030f0c1808030403150f0902060703030506190b0d05070509060c030408011817090418150c0206071202162a 74
    0x340107264004400020f40300300000c0c401506d44010030302c8010950b00400d91503c2c400d00781c0d18090b0296034003c510602c008112141068200130544030014024942204e2a000036a860413078141c185400c00805d41d001001c8507001d0a080300030b4040032010528070381c1030030305401030540e00c0304003510080092175003035000340c0d21034421325101e101e02e03c0040c01102c4400c2d0081d41038516030348003068111184400140000e03043d400318040e90090f0350b051300402d0382c7d00c007001044d0800a020500605005407806206800c2031444e4446001d82c0c18000512552500050074642c02101140d800020090030039840300c04900c00d10307540754054000e0226075401c000d051542c9400c0c00f11482d0710140d0002c1d0800054019000b01072240e088440780660060b2156503103079200c803800d501c4070340680c094250460b206c4820b03000103054980120303110701154004010031018551009410078078240d10400540d0380c143c0304118413410704c4401c501030000c010711800fa480d03500c454589544400d6605d02d003007500d0355 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 666084694 1250 666083444 666083449
    0x20c1e15010806060f03210f0d0e160e06060d09050f072c010e1b040f030f1209030519170c062712030705130b04080f0f0309010c02060f0f18 62
    0x30880c40f042a0b80740c3c10b206072884484130400f07031a03440048c01c406810901d00540351003e40d909030703421401681008035030f21017070210304001d48050050302ca0012162309148001c186d561003031b5621424040e07a90056101048410f211030426070304800210b030522501e611540411b4005a001c0303004030f11382402028080800034101c14100c1c0c004910140c0303581d036180307658581d20454400d00c01241c0c80802001c14442503c0344904043d50082070703509103c000c0c500d454031000020507427070010b000d040d5a04000080c000100d0907070344401030108641111301c1c0d180070a214041e8417504100744a01080d01c2a506000154091140c14100c1114000000900400e400e003c00300b44159150b401ca5400c0c1c0720752150003c000c6402c41c074a840c0144c03910000000b45624140070750044820744400040800c0200410045001c07203440d50030281c48412124544655a03118950196051010200c032203800c0d543e501065491510324800941e40d5412200490303080c0d03a12244528140c05071035105c070348060 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 666085944 1250 666084694 666084703
    0xb0301140103081c02040618060c0507030201030b2b020a0609080d0c1401051311040b06040312020f03181e01170a020412080403050d03020c1e15010806060f03 70
    0x8031056500014241d0071600e41c1031580d404001e105085480d4182c3c1c880c5030000d944010001440c0903518013510403a41710000e03500880c250300010070004200c0031000851000f040305003c41e40e09090000310001e002c03000c24079a10f910a0100204042c059803613884c40d040c0c1e13504140040c8203c82174070741d030b0b501c480d41512622a180a07440c6a0b034800c000e1030714514002d00c03801040d540180e0b0040b0a0360380d079880c820309580d02100e00d503c500d489036803085c0810440c030348018640e2031300f11814880c0b40300c5100401c0e1035000d54400601110708a80140018500a2082e55049100d60040d00d0f9900f80004810742207103d01241d403400398070710000c44106821200d44e0f100c1c01c0c0360142c1da02c1c04000c01c402107100d034641c80136201d1041141c1c00c000004200320f0104806450900c5002141d45070341c03a42c24140d0802c01000e15007410306004000c00c4c419400c000c15080f0f1a1401c0c0303013580201d4801c401040303103000c02c49010124161078a00021610310000150284503110403280000304010100034107456 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 666087194 1250 666085944 666085961
    0x81305041401151b03021f05160e041517160605070f240c0905090106090506030406060302060f030a24230414010f06050a0819021e0405040b0301 64
    0x1401e00c10010b000d000c0e201c0344950503212881c500b1001890f54240000d032040c6103000700300d0250303100d08030030302c0300c0074015041620b03d20510304100001c3c5060000045103003400c070403d108020f101020000a690f50350710a22414040e800720700364483d1617420300030520030b5102402d040c034418980c2d0303164000780010f11001039601303035900c007800c0148a07600c0315000c018203102182d021021060303210b44003500f070541100e1034550aa020481061140300500400001d4012500032004d00005102141c1c02c0084001212800e4071a66a0b039520b906040c401400d16070002507002c1c10000b182241070041101070b5004014924042010715a00c3d41c682d1032150390910494100808603500304001c0d9103c0c250107402c60a88103041400309648000102110106100c1c40020034401c8014080302e0600d034610000380016003006868040342a01c09050307441d00800e41d0740e40350501c1500d414801e00301c0d015141484104081355590380c45103080322003150010b0040e01e000d60309d4a620340f0010314050060442 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 666088444 1250 666087194 666087221
    0x15141803040f0e06040b0d050606010e0306061026090318041812110f03040f05010903030203040b130314010b01080604061d0405030909070f0206060a030b06040c0210020708130504 79
    0x78400d1074030f00c010503e14002030046601c5651490311112640360b1042181a4501c210003a2001c1d1034600c0015042031410400349000b503104104000c07103900c44029141c17914105041c4903a5103a00790180d2058141001820030201101e141840342d4200d0004c042c1c8104001c201070407818903200c5050208071500040310000c2e1980705008500459030100065107020018034001c14501e1181c072580346005a80400e0094940c00090100244d403800903450015100919105500b00c1c69030302c000b540c900036402b461820040001e0407807030400c40c00031080001c0d03511085096010003802961070003040780e0203001b03002c14011301c00036030795107000d00c5030406a40341031189010b4a0445644078001000040c021034540c03208104210841da0740580c4240f2807800d40d0f840041851540307000905000c400b41c030890040d00c20000502c0000e0410341c040e41e0180082d00d0010b4a07288002c001c924064003032000003005880002e91200f440420070050100c00a01a9034911003a50790062200310f0320458410071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 666089694 1250 666088444 666088469
    0x70e180a0204090c091104030212070608070f020c100c0303060f06020a0311030909040b0106030605090408030103031d06030703240518040305040b0301090b0f010c031b1514180304 79
    0x800610b0302c0d41c003075030344207006a200c41c0f1072503103e51482085030460401c1484040c80480c0400452a02c40910203c2003100c1000c1c0514518144024215100140c4818248007070321074a124403034400c100715030290304000c3c0a01180614400c02802c18a0450026030009007041070100342c0404055218044038100c0c0e0082c405c10b41c01c2d46040714480f1151041410794001081200a10b548080455000300d009071032401481d45800b401404540d41740d4807860152100c0001c00c00440c40010550741141e0305814041c0959641c0c603821404403003010242e960148000c0203100354075503d64041080785030f40c01a90001781074902d401d40200c0802e4401c4961240c00c0440400401d00e8031504650820b10908000d41003075110501c428480e0800d8000c040e4150b80e43c0301e101c9181c41c007410101500002824aa4840bc0894500078212900780e0001d4031682d404034042c408101640341140304054040c18100084002a1252010b41205075031030885d640148852046001001c4102c50803101c1c3c020044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 666090944 1250 666089694 666089713
    0x11030105070e220608060717090d1d03011404081905040302030d050f04080d0203191b080c0c060d0902240d0b0d0501020a020a1b030203101d0708070e18 67
    0x2c2c0030750688100c2c078103400360f1981c01c000b4101d0030400404e03000700c4140d283c23407002d050540c9409031004d4000f0141c1503240e00001403108800e4000e404e401800007001c480c110310441c240c01190161441480c2000304022402c108014406080090320113000044254880042c182d00212954080d0f0f00000c0d605030007940810b104030b8018001010300b0b920780100799041c50f580d010030a003084a20701100700945c10004000720b01d2104000e100a80c1b0b0700c641028140c0314000c0f19095014a500ca07070040000c14001010030003420b04000035507081d40001c0125070345611221203070000d041c8140080340a5510280c600b08010300242c24041110200c068560602c04a03084a030040d00c14040041c4e00b2109540d49000450020300081c2211405038004191a15a501d0107054006444001214540d41e1034030520040e0f501050300400c0f0000020042400c202c17180d40403480200b00074035041641705400000840000200e8980101d400340e842c0d5060700d540c0d41090008080540c20780400341d42151090 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 666092194 1250 666090944 666090979
    0x20c04020706110a03020409140411040e010b060c07030b01060e01020d140906030411190b040603091104020a020a0b060a0e062709010204030203210717090d11030105070e 75
    0x509081030107044049031a0060100c0b101c0140c1c131822007140025000601404000098003601364801c5441039100028986074442e203000c03110000c0542c1c8115214100e20704188025080b10004500041505581d07285002101c0c0e628150351004513030300400e00d8000550b040c003030209161103036810303000340903003500200086400243c40500b03c3c040714001d02c0721024640340d1034060740c411fa115040705814510418104102000301071aa000c012801182c18090b994008094030201d400700c1c100818404003a2601055144d0000390742908a8404680565201d5000030000440ca00601840045071103140034414486030500680c2182c40644000c6802800c0c1000100c05100d8001600508003003e008130341e0a0403015681e01d00669000301d414020761170300744428000080b2101d0100f007244e0758400d034801c0c43e002e240001751400b071000200e6103c5048ee44119660724130001d0129210040380e00e0101d00425200c0d8040e400388d80703020b0000d207070350b800b800d03e00c0380c0154000c11400d070706402d5400c0f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 666093444 1250 666092194 666092197
    0x201111e07080403061112100501120b120109110907110606060702010e03100c120203040c060e030a060e030a0801120507090b03010603050609030918070c06020f070b0406050f0115020c0402 83
    0x1002c581c031900401c4000041403580c030030141d0300309040200a59070b1031504111060303a031028040040c0c20121190401041e80c21890b0888845240c60300400c42e440740100141a01101401e03501f915401c144202d410841c0080b1003143d0690111020318054454002c00c40d07c40d404034190600f10351000002c6900f40c03501c00050a000b40c814584544641c142c2008030b41041071981c1039030b1055840700324007000d058000b4800c80d41c214186800f1421458151250341440b003d41c807a100c1800000d10007052203480500c00704820640102c001e20618480261640e84c80e803041544a00043c5030400128000000d08802200305401030001d10046090120100040c02082c28081c0e06650301c220000c0003540a0101f944180925070145485005c1c0400b82724000160040240041c4514800c00907002e0704150160000381d00071000507121203500c0c039141c0319485904400360448007280c08110800c401a00204c5c403410148000c00b5140c3d0b61078444442c0b0003907018500300507801400614404e41480d90 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 666094694 1250 666093444 666093457
    0x20d050c101104350c030705090c040f15091502060609060103180501050901050703140414010204030b09100f0b061b010f060b030f06031b091503010f0204060201111e 73
    0x980394a415900c4c00300a07030000000c450204040d601c200750740a411070300350141c041c190041001d081590f650800285c1c980d078090090501c24010100480c07904050310040d44c01510343d81d070612200f5134a48948d1150f0083c858000400640e0814022800e401c20072a02d00075168281c00501054a40b07508101038020010038107410180d482000240b2815482c3d005070300341f4084c074000600340c24100c9030300b070a441c001095501414180042d50103003070308218540d54001d0f0855514081000a400c0ca0f60292007240d00c0a0407800050044c000300841c0403138084c60302410302e00c00300a41e5a1041c948001d58009402d2130742c0c08941480000b6200d13054181403480c0c0300d83c3c2000000c1c650203114413035048176156005148885004010000d03014442c18203503410200450050034030000f070300007422074894202d060038060811500404c4520328000c441e0000e224000300203001c50400c150960740250024072417100158205000800188450812208811100c9402215085418014409075444072 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 666095944 1250 666094694 666094721
    0x106020304150e04240e010b180105030405030c100e0f0f120c0c030d020705090f0108060406020702060d0504050d03061a0313140a0f0b0906090a110d140d020d050c10 73
    0x50415003502001900d0a103200a046038005ca505070406415405000c1c0c143c1150320303220300c01c00c06090700014200d40d0015000003440e1044d035075551840d203a41035001c1c151080c640d074410010403c9041005800c94034060b50710408071000c180100716403941d50b20442081012680040441d100640c0381d81b0010840300422100701d0301d5980d01c0e140441d1a00f008072495500507041100248114a0001031054110390f502184803425414007185585030303c009070000301940c0d0300040313210454882905840b81c0b01007a171010000ba140c203040081c0c55800c2c081d0b220780042c2c40c3c030001150501d4800500c44551807080d260a0a654030704002c2004032240d0403042e50415202d003080120503500300701000d400381c840c48a16501705400e20b0000d031404e00160401056400883c2001708202c400180c5080c05500b014507114190301040220385e08141410b005000c03003155064a403184840011250241c108603801c43c1e1902030501000c0795540640384c030100c2d81d50005480e00c18008141e400075085d06100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 666097194 1250 666095944 666095951
    0x403060b1c031223150f01050a0f0807090819030f092102010201060e0903040302010f030b0913020a08010e0a0b060307150f120218101409090a0f051801050106020304150e04 76
    0x200138003000c100780100c91070344030604402c0c0d2414213810030b6864038243c040e003801c1c082d003004001d00700500b8005801805900300010903000450241c410a203131801031000030f090b00c8040110100149205244540c1a404a8404030b12004894401c0f0480300c00c4410421081c00403690000c02250002c440d405c0981c1150340f0f40c031020844200b0501810700035a0010003d5503913524520000d880c0c14408440d180505113850303108800c6807140e426559002c2c0d078500003001c440e00c0510000d403044200390040348076903107401401c00110b40300140c04a0894010000c4404070303941d2008141c0d4460050003940940c014040715900d8980c042c03081701d00403688904000310324905204100040303130880890201041c2c60714031a80c18505103d02c14900c0028941b400c000d1011203100d25200a1180202e4240603100c3c2e807000480034a425803080840d03807941c00c018000e0b1704210040e8072115040390340e88200c55107040c00001d005400041154115804c000002060171000b00c0182c2d8142552049290400d46 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 666098444 1250 666097194 666097241
    0xd020301140103031101140a0906090602030903090f1918060914070815091906081605090f0106080412030b130606020708161403120403060b1c0312 65
    0x142030060700c0d02065601d040420940c59030030020710380c0f18095040a06039140219a1806111182e961a8010940100490780c03000d60302c2c2c4030005161404000d02054030100c144403a044010004080c16a01210102d404100b1101041180821940400d591030915601009807080b035449034841040001400100035660b012a0415240d190700d880c184030300868100072100307810004403600320500b45800e03403041101101142c000c020140000e60150740280610031780e440d45800040c0030384070080541c3c0d800c1e001500d518120b08264090307079214540100018088080c2010080c2c1203c0d01d0f0307a140011601d42e526008038003900300a06c4c90400d038503002d060425854001503200540301740c1000207462883e060b4001d0900245412240090304103a03003403100d48881d4802207007500c00844d0090111000c00000901d8000c10103520b40c1c0d2104042000402d120041d48103519100003034580c000c03c581100f440040d040d904643c02008124106140f14054001e0740c01800441c13080405943d2425 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 666099694 1250 666098444 666098449
    0x4200901081f090b120118080f041d07020c03061e0c0403080a0c0302010f0c050f0a09080604030302090f060304150c1b0c08010b1c080307050912010c09050a120308060d02 75
    0x82e141c0020014588950300b03140c0038245211004d6404180ca0020084e14440a85c0481d90420302080909400004180b0f03080c1054050f089800034483c040305400010400031800a8407102280c0c80700150041d00080102400c01198984c030a2849400c000350a445094000c482200c001d030100c02003400900c40400010000002448544070544980d0000201c500d002420348007540900c004040c241440c03090b036143c1240658030014603151038580c450304050070486a40400d42d001000c0c6109034828001456090b60082550b5841506d04044d0111b2801c240100c2d403000303a50051095070300c00c01080c0030700015840405000014130389140c901440898201c07031005126030580f12800e60b41c8042103050003d00c558010800c00352100f150a240e6004a514040d10452000d48040c00c00000107420700d10440445600201c020824039400c4990146c075402407421150704004594070b483c011501c3d10f4411402e07006c03904502c0e250200d4071030702d42e404c6441070307806003039141c00c181d11240710001039 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 666100944 1250 666099694 666099751
    0xf0a140103050c130204060903020d062c1209130903030b031b030712030f0507030e0604090c0f0c020609040e0a02063402030c01112a0420090108 64
    0x2140100000d003c0c110403601000040c21501071060b4286204100c1001010703000364401046940480700d90400500c9801c01c1c1000c0c1044c1100124040c14a084848510126140740c20819100800702d61000555140180d10780c0300f81c12840d41d00c050801e045902e0030304a6002880300e5480781c600420705040c2c0b81c01080c076240ba820001c4956440b1801c0a2103141410401400145a1012410310b4040c0946014042003c040f0b0040100280040c00005140c020b0310752040c1307a1009000a6600c42d030b10740c0c00c4802401c1800010300000d25149500002d540318280e0b4442c21900284030501c0c090f5a0030070000104030782491215a4014074100ca00560364400c042d01314201d2a0502d983e1214022810b100b0940c1101d41446252050641410160718000340d14201c118081c01d1821116405003200d81c0b03001c02d4807068494014003501450000c9164100303103d142081964203101c40c500c200c04007140e855014112044d480d4090240b03401e0703503114000654100201c0c00c1c441c42000124401c8120a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 666102194 1250 666100944 666100949
    0x181c120203040510170105091f06020606040e0a0b1f090213091512020f0d05010504060c020610080a0605060a030c08061506040b03040210110703052d060f0a1401 71
    0x56000460b040000d81400b100a12018880f4a000303800c0c1d001030843c0d00130f080418000e541c01b40c02c080340002c12000c9901004200c01c031440742c80d9203034159941c1c0025a2040103d40c120300403810301e2058034266000241001d20700e41c3c0002c0c1401650b07652203608001c0c0e007030003807280700d40710101b000020104c40324401040e03500800150808103504003c10a003c0c1d6000c0600d50320a120349500800000300028040344016a0446110006580d4440000c541541005019089518141c2800100416588003410222050302929a60b54600c070170707903055007058420343c951600b0400b4580c002603215403080d54040320042506034000c0d1652651549529a6000010503a2004050244a00a40f0507803050300f5000c9440c1c030303d440d061002ca10031318000030748024000c0c1d032004000c40c10b1324024003441d40401d510300107c40035141e6078105031742e9501440e94100442540c52000d121000d140a00c10038400c26000003c00f130b19181c0c03800742e845480d03009040d110b009640385910319904900c6031880b0300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 666103444 1250 666102194 666102197
    0x1803080901231807080303130305091302120903160311010908160b0108060709061107030b270102131211150a020105130b01090b041d030717181c12 65
    0x5031801d4081000702a02420080303407644d00c1080100440c9070000122070380802000d5000c12105894a800d0f40c190150922059205013446c881c1040c10195030b000c4d08040300020285442e07070300d50f564482d03168030406007400c444148180e211008039000e41001080007903141d000007101c0d0b00584501003070f40c1159120f00c0f483e40710b031f200c04014080c3c0004d600303014121100140400b42014203001e4400001031044c2d0080c0304075070700c1110302d50b03a0038441c0e80000d5401c0340e048a020b01e0b04088014210800f800840c01490501c1e00e42001502c05200343d540203010040304090f01d0703041c0401190f0071001201c00f1070345413500f08a21325140d1180d114841c40c5080380d031001502d800321180b020342592401040682c41e003010310400790201e10304040c43c6045416101000400d9107141e07000c0760140c4074441c0701841c0d0741003e40c0e00941c4000000021310b01c00d03003da0941d800200050155080e1481812824001488400080c2e841d9241042c4014915041c0000d80101c521441c0d4459940300f20305882e500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 666104694 1250 666103444 666103511
    0x10819083009010e0303010611100e030c1005010b0313020a150305010302010f0e01090603020f0c0a20010c0f1514090a0c090204030b180106031401020403151803080901 74
    0x41d40340d01e02015140d0044015002403040b20081c03034800c1d50364001440307500100810718104864121043c010f003a0b40210718542800710b00700c4031407603a54030380c0304800070022407250070707443e000030710151040f941130b544003020311441d50300c1d04040d4512000038204166881a0025400101021441907814507101035450100d0103600d1400058802070340e0340704031400d0040008002600daa03001c1214008d0b40c1c664100181c44152121107180ca6004840841d07800b0f100382c2b24030304184004501c0184956541802505c01c0d0a8004011118010780c8040204141d054000217400201d00080001c1240c0d40090001590716010201a03400740382900c040800d41c2040c007072203051055989504024100140c0c0562a10345075503501001844014210003801c500000384092361007082d00810021500112203da0221090014078001e6110340300071502c020f40e00181e0300b0504560300405043c2e02c0d00806e0100301c401e0586050b41c031000c00410348061556a5002e40c46031020401e00c03070081c00c41c0580c208 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 666105944 1250 666104694 666104767
    0x20609030f2e11030a090323030a1b1205091009060c020d080601091406070c0608010e0603070b07032304060e012c0d0326061801081908 60
    0x850110310181e82d09030b003507070500381250000440c1d0011039401c050490310025410700d81c0c0c07c04640e891200d806075040c41581821800c03043c01008040d60103041070400421408052070140700c1d14800007000100802c4d4422202141e0341540d42c016a4816251401e0751490720b400d815607021102d4010040380c0140e03840b44a072040d150704100345804603005082c00c004504100001911080b0300340f241e800280001004540c00b601c03044151441140c1c420003c0d00c03002d8072400e005e1324811090144a41c01d42c90040000c046203400a0140111200800a10710b02029074404840c658582c0c0740b0600d016118800111400d12400d00030401400b0581c1c9101c0c0c01e100d018001808400c01000d02d11802d07455203c103003451050745030348450300700d4222108130310002603142c150740e01c0440d5050b42c4500c580d0301c80016034181d1040c907100e124040c00c82c0e06011108441544001c1c1400030f000ea804035600040c02c0401c80072a0143c2c1240342d1b4082c0d040300b41002007480082d000c000e1030341c110301d90210449545 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 666107194 1250 666105944 666106003
    0x51f2c0606030706081305010b060f040e090a080403080306120f010e100e070e0619120c0803130b03091204030609030e0a0b0a050a030b09100e070e0d020609030f 71
    0x60300d810000441c00340c0300141c5071042c02401031038050400006015502485401c20109500681c840400904040e44030050103030b00905940161140c40c84040c0108005204030502040d52400c0e00d40c040c0b20701e0f081c64155100c041c05504003c0032903400c50710800900c89010030400c10815400b00d0080045240f410802400b4180b060300b18070030781c01070f091901034a82650042400e90075110112034088890b61490001084607070140d040100c05175005c6000700b0105100700c200e018150080d4030200c0d40b280d64004241e030301d200f00c404500e003603030601c403060180d0f8140c80c000759040f41c1c1c1401103070301c0151900b1401c00c3c540e102d03502c1200e1403075582030560209a003000720005480011100e46403003a1401003800134a1250001c440100f01c0e000071307880892402039209078560039016015415138030f030104252500550302d0003080031403130040000a241903c43c61003d02c60b2030015103500009080c0b0740c240992600f03c2103203158580542209807180840c00c1002d0804010f0b1185003401c271043e400f14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 666108444 1250 666107194 666107203
    0xb0c0a0306270f090809040203040f021e0a0b0c0c210f011a0604060c0b0a0f0608030d0b0301050106090506031e091c020a0f0807110915120703051f2c 66
    0xc508443c5402e00880740003081072041941e0010742c095902580d00e60321071408190000c3c00150082d80013810000c0f20b00321240000c22030203210700644a03100803d44600c1003401c98020740340e41c040075a21000d504481e505207030f11048101c035504000459580b43c006a00d42c104600b181962180d60340d00c0410613640c095850282c0f109034410740340780b4a06802c241c402040c01c03154403006003c01c100f040c08500031482ca644004070100315403804110302ca40754251181c5a170f000d0514000a20b041c00c0000c0c1980c641845000d04030703500c1d500c40318150381c40d1405006407500024201144c151a00e981b06c0c000c44220f024642c420707900c4402418900300180c0c0d4044283d80750306102011588100b000030300180450303400d00c040d181c200c02c0c060b448101500d029490007c03402011908660102d040c40100511601c0d540030f610002c950448400b401444681d654181501c40a01503a01480040c40480e8020710340808034910082e010900000322400c58840050600c103444024248030800386040d1810300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 666109694 1250 666108444 666108461
    0x608120d0b0d020306010605180604060302040503064005010f0506131109221a012c0d0206070f1101140a090521120301210b0c0a030627 60
    0x1100310400e42e000c0c0c0c0120340e0320340c0140665014402c00013000c80003001960910b10003200300500b1f403542c5a032142d00042c0a5081442058003034440c44e00030844144003c200c14401c44034090250f00102d489480906800d0043c0580c54002c280c04001d10020031000e004804182c17031001d0f40803900e400c2031802c1c000307010321302d030366041425140c00310034508002283c00322010120100e80a5081540c80700c00110081424070f0a4603001e807a20400740d0301000700001b003d00c0c0343c200340c851400d1100c1802c50030220405d44440b403011041c0b6035141000034940850b0101580e03001906180c280301c40307640c42141004240c601540c0d5903001541c1d030526076a00480c14800003048264240c20003400c41070103444c100329802518401c0d0030050f400c01d94039180b06034035141090100e045070f01e981c0701039103400c220354030070f000d803120301181265182a40c04041105a009603032214070301000743d072404201100c83d0001d040000406440310707000241d01142410006000b0050000c182c03030090b00405000403100c006 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 666110944 1250 666109694 666109699
    0x1050907112a0909060a1a06030406180203060403030e0118350d090203010b061309021e0706050f01060e1834030606030515060a030608120d0b 63
    0x3a845a0907a00020a0100b07001c025641c0c51940d03a064151003501503410106015003124080e030402c111400005002c0340601800082001822200581d1544c01840d0761081500300382d0070000704000484543c8040103070020450019414506c9a0009040c02415078080d400a0b0300d481d80500d03e90000c3c030904070007142d411440701ca034103925070f0781d058403000c0758103001d017031800b1025208580911b03041c40745e035052654031026a4030b02040304500b0003030040c00c0d0107a010350700c0d0000d502e0071401c00c1821242c020340710401c4201158640700c1440702a5100b501001c8040344c11903020103c1c5003502c400b90000901c14080480c091030b04202c07006910105074407200420403c03041d151140c1c1ca41c06903000d40e0705103009486d10701d030b03a44941c0d403407042c500b03402030074035500c006640c80d541c01e0202d58410007850b5a0b50b130180503407656844201c040c1c0d101a18030030041511080c0f11490351a1180080110b0f460034140032440d503503580c040a0030030301c03055004404c4d00c00000704054400c4d0030303114007420680c04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 666112194 1250 666110944 666110957
    0x12010810090b01060809120a021f020a08160212071217010308040605250f020a0b09031b011809060f060201110d23091b1c0305030c1c0501050907 64
    0x29180c190b0035210610401d803d2008100100e25080790074031800007202c0443c9810b03a03607a00740c00c0c4025030b145542e00c03120442c003d0b90460091131030100e000720703404c0d1030440e0f94945080c1c0ba101c500300280780a943e0074800b580f2803110701d03048144150029041c4075002d9064034045d02401c100143c542c1060944032a0310103403900060001901e481c05450540380c96143c401d4a075000c41d050864521a040104140c81c0d00c05c190f01c0e410402021008104c1c10b109455054145940704c00038901401413200043d4141c10101c039030091003140c0707800d20400c00d90514040d1030320082c40035003071b4079914217402c01d0304204d8562200344605444000080c00500803031000308000c5040c3c2911034041d020340b60207007241c142c4030b840b14081c003400c8104008601c004405899103506041400740e0795260700c2000c02c000214600c01c20741c110719011521003120070703803022100300301e011596040780e0315030008101e40303d05031040c0410300560481025800090807140701c00241941032004002c003421006001c0c4081158 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 666113444 1250 666112194 666112211
    0xf0b09010210020f091801030516083d0608010e03070b04060504020a0b0a0c05070609030305090d141605120d05040e060f040903051305151c1112010810 67
    0x740000c40d160700303154100005849241e0b030204880c840c403542c541150300c500000800e181c0007a625140c40d040700e104808a80806425904103072001c0f0140c403480d03181781c1012240241403103071021035501d80062100314030000c072481c3c02c85c410403030340385d00b58091015556001440981004d02c1581a8040380360700550804c00e140c3e61b0302c48400700c01403009085949035000b03d000c6460781d20103407025014040c0759a40b214041d520040c011050703108207540d2803180701000070b00d01e03009040407801e1fa41c065403400c1c6403c0c011014003140000005040719a84000502c2032904113051120208420158101c810824074080030040b0a00180813034a040750012450f114440e0b821908031000c54100303d6015030181c4c1c4641c00900365040e050042900682031011174010543c1c00b0000381410443c1c4d0301d60014a545440620001c0d020f2034070140340301d101c10003120302d6280100d041c5260b015000c1d1404a20140100d902640d00d030080301d44280c1d07a003012001404234440a000602c0d08000f070030000c000c0300d103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 666114694 1250 666113444 666113447
    0xc050f070321020c0c04020f0f04120b0f010e0109020a18060c1a01080307030f020a1b080d030e0d03020706152c1e0a09020a030507080c0d050a0615030c0e010f0b0901 73
    0x40c0980c1d00341b803080782d000a0004038041c4040541c0c800da5007410780c10343c13550fa5920310750410700c5502c0c0d004c40303803042d440001804220645424034107a41c80c1440c403284681c24150380310300a40c03080400e80240030008903040d4002440609410140c0f0785a81c5130842c075492442d224540506585010b402c521400c00140f01015000043d505807070b40502c2c040d00002c0c1900d80a074101500e455010b401104004981000d16100085540440301284101d408003000880c00700c044924420004450381c0007200d0a00042d882030f00035004050040100040b407190340c1310300030740b030782059440740050548410052481c5031034103120500d81c04080b86a80841c0c60004429143c08425100d513000f840740542c045642c441031544807490141c0c2c090101030103170b9180d003000c9642d0050761007214100c0c80350680d411140d052001300c040005a1100080c1114411551094003800440c4804075a006c089440000071480b290540b00003058200d50600003941014175040c43e18443d5042846094420082010540d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 666115944 1250 666114694 666114703
    0x1e030c013e0304080610060c020d03080a021b0a0203010b181f080609070f06020a0f021c1208060108010605030c1c020d090506161107090c050f070321020c 68
    0x6100180700c6124105410101c2222010103407aa859900c00814007150301c3d6800603182d400383c0d04d9480c0d0782c1c50250313441908403828a00b0100080d0000903241801c00041e02a010942c0c212003000d1003d401d01c80300340c824a01340f083c25107000003207a010100702c90943c1400e21504d416554141c89220700d07103501902101c10528054655104051480c10221100d2850f10492010b01b11940030f842090529220096940105002d94100350403840000985d0720300004046d940103034024a000c81c0f4811a07000c019000c8098603a55840002505036140051506050140b0810060312080c106e030810200040220310b05070010b80c1803203420420300500000e1902501c410404002c0d001c03401d29141580c08000e4003848001c0c440d42030038200c403076080007800f045c42d9100700707a0240400c1000c03044880496440310410089c07070041d0802103046c001240180c0048054641c542022483c0170041c882036195644903900640003d680040b070f460107030120620104034014071039000d40c10400443d50b0310703456 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 666117194 1250 666115944 666115997
    0x1032109120501020d050403050a030516020a02061305280e0103110d1406010815060d0c060f0306050a0b0306040b0301140105010e01020708120c10020a08010e04020d021e030c01 78
    0x4040c40200c07000030800e00b5011202225a402c2c014003680c1414580500f064111000f542d000c60f081a0008881000e984016800340c0c516500800d00d000c0d080d001c3c0400341d88402148a5030004124020900c0c0d2038440ca001c800a0000911207170b2070075100341040c403101c601d8104c01900c103840030041003c6100c95102005844c402c13681c0035030304d00b400d00d4040f0b8100b500c2c0d90107a0036030181900004207d100801c504e021400e641d4500d00590790f8030030070401009008040145114020041888844d00c40d0803075060501c003501f4001f40c041d494030b00241c80c0710600d511980d000300c40001002050f040a00640042a0050380284003455010364400210401406014100800c01e003003c6240c0e072007013154400800801c019180840c540f407025205541c01800390a1072381c03081500700c030007c0d007251003160424815603880651a13400e04045a01480000d40203980c041103c20203500540d0341d0080c40360001005456103c10754001d0400c0c10305051b01d5841c0075040c050b21003c0b074200364004101e400b07007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 666118444 1250 666117194 666117209
    0x90911040f12080f1b01050f070e01080906040609140118110f090c090301090b0906090c03030c100b061c1e0b0a142b1505091b030705060c010501032109 67
    0x803160810700c1501720340a501d142042c020760810040c41808001404418050901c590f61050580320300801034a280000b913503001d50359805200000e012940b19800410024492400c480c49440e00e204024207641110087c10000d420580050080064603059032110002c140c99410b0b84010640005069890003004c1c00c90f4034100040d8085941e07020340c03101142c2903204450603454140600364a0f610801190120390500c11440c0060281c6400401e98400c149110010310741c0d110182c00e0f0b00003800150002d41e070009000c0c04141c0c0350980304500b00c800c0460b00700300020004a485011035801e01c0010b507140d4410314000741880f040e00c451003094161002d400140340541d030508003203124031001c181900291400f41f60f000000c0c5296411001010f40920002e0010070040782c1076100b00d072402e480d22101c5521001510218190300c600c8000c8500c03004082d03030300c2690341d20080340a55005d00094442655280014010421a101c0c0007240f280d031610f5588054240c0e0740b02030000c0c545405a80c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 666119694 1250 666118444 666118447
    0x703060e0a090809100c1709060703030f06030b01060f090510120b06040e010b0418050709151202030a0b0a080106080d0810330e01140703090911040f12080f 69
    0x30601c03002d0700c125104d00c1406407080c14160800d8000400711100034001702c494008100c1000d80c0c21544030186d82440030001d184928200780c6a8040e0010250944081c00d043c0d180c00001002c2801904064024251901e88201c40160702d07000410744402500070500c074848014801c0303c0b0684c40107000c2011301d406080044c40050482c001313801c0d0b010343cad0300c00c0d07a00881c400004901882e86402400c1210b030340f004150300c0b400c44a11008240c581c115050000564030322010000c0800315240700f01c0b528200e052002c0160f114600020599004a0b900c0c5030542c2c40325202034690a0034520f0b074000704103640080180e41e003002c504a46902d800404981080060b40200c1d20b45103110860500500c44220301c00b1800c0b182c0d910329445404560030a0700407412400440d0340d218029070340708000220503914043c0806620308103040c15003000f10260700f04104804081481720003842346515a0707a0744500d1319292443c10249880302e0340c06e600300d1020406204080e0340000c040c0d401351402050228200c0c0e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 666120944 1250 666119694 666119711
    0xb03100e030307030213080f1507020c060d0902120a0803100b040f0e0910060810050106081005040e030903030403060501170a0b0a0f0b03160603060b210c070b1501080703060e0a 78
    0x3250701b544141c0041259024107502c03c0c0c0c0352080081d000c12031210b0400d50f848240d80c0c200d002d03a144d07110f04602c07540001c1d0420102d03c95100607400700d080a4401814030744000905003600b441c0c2107950100716107000c80042408a0b203100d1070303400d400504841180d68641418010030720030310510381c070950680310b05010100b0780c000c509000070500000124000c0042d55961000603555108004050b00b0007444c19001180c0240300e807500300d06ca4008040701d03044032441c0806100c024203911107030071000c0c0402d2040c0940c40d601071009000079030003900040342a5052544603031014449059009866021809201c005644448410750064401d01e0006e440703c22251400701804aa952060303040c01040d140c0101540001070141c10346003a0b60301040a01e4070703008501d0180c410301c401a0800c6402080300703c40110004440b651101c2c0d41020907007883c10698480c62030034416140d00140c1180040c520340c6550344890103907800b07402c0b481c003806071500e0440076403d0a40050501c010458803180c0d11b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 666122194 1250 666120944 666120967
    0x130e15100b1309060603020906090108040309090617070501020309031506031e030d050105120a081c060e040302010e0102070201090e06030a0b070c151a010c050c040501090b03100e0303070302 84
    0x4900601da00000c0d1640c44a51120000030004a40204041d5030b240c03d00120304c4c0c42c82407007940c840c44009040c9504e0702c00100d0056076050ba00400480411245900c003242c4903c050080300010411802c20224000505003032500b4170103d5007110341150b00520041c0d0003070b900001c0c0010120440c481403942e0340c0300d200200b4100304241203da0428200c00a012000c00b40c0040103014203183d0340c908002d00d1362910308000400c6400c0407408200c0d400f19a00a000c28904001010740816003403540c0ca1200304200c205050f02c40d25441401c450b45648200030074160203011b50400c42c101c03c4000c40c503040b21540060400c003401c0c010f50070100501d10001d200f0303032070400514030415000040b4040c1031801e120005c0c0704416680f012140842c12040410f00600301c0d01480c0030b50041c802200201082c0c100046aa001c2070440560b202e1051140111080d111481242e0107080c00a6001c50740d070030315800340352034a81e0302c9500603002842c00c0c0c0702e000810400303c2035a400100d2807034050307598280100f2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 666123444 1250 666122194 666122221
    0x20f0702120c040c05031e190e162409030506041203020c0a0b0126070905130c090f18030816030204050307080607200601032d060506130e15 62
    0xb42c40d03001450b0800c480c02030390b0868003a500c94550000c0d07911052814814103007590000f071700c0c10090408400c208007421a0b1070380203100451200300031a080300c0400b01c4840c04000840d4060b82c0310350301c88101754a84688500c1d01c0d524128060030030001c10ba20359030741c040e5138900091010346801e00c808840c0b25554031a4044a0440400c8011681c6140b00b030f0070316854951080c0f00710101c0c0d420451840c0300c01c00e0788030380a0301c4e038410b088060009580342080342406004014036203940d13000781c0400c040010701e1b00a441c0c2d01604c1d91322070010f0158440004081100c81030b4888004116880b180040080d5100000300d0340b0000c203410709a5070b4404034805801074052074202c250b0500440302d011961b4200000c103144a207807156180c03055410b407646d8007070380851064507c2010f0b030081d01c014404901c081001c281c03040c10302440c54281075481c207015803050080c0c640454405e41c80c1e0080c080d441c54001110f4840d16080c603420085100c0303080c10b0300d40e00e43c140c028010f030100e4101c000070920b640120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 666124694 1250 666123444 666123463
    0x4060506032503231806070e01080c12160302040803040b030919021e03071a18120a020f12190b010e010506070f060e10090b0a020f070212 61
    0x4010546a0400018a006402c1c0d031080c5888880040600a80c41c2d511a000c0c1082041352807121a000b881010090b0802000041c4940380b40d126400807490788041c01c0002d58400d07526a03a650201c1c2807041c0006104050203042d440050b001403100742900141c05000d00d07003000c00d031011030003903003220f607400d40107806a90301144d014000801c0000d14443c25100451080000c2025120340b1445010501c2c02c0044940e00a5081890b29203031510a80055008c09480140102111802c950724029009404500c007940350000310301242006031943c9003a000c4e014000d003181ea0f040c542070b001070343c1c581c1c072086030001034400c440c1d011460b080750f140c0d441a154040440016583c030502c400045050703845810a0071920240100000a9519640100203042e40e4008040924020040c6c480010340c82e00c41c1026200c041e40d440c10001e035600200603410b401e80420001003500d21403810b003d0f07110100146071100c61401041030b05d942c0303000d10040343d00300c5604a072641c00701200500321528000c20b0750f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 666125944 1250 666124694 666124699
    0x1c141812120f09011b0e0103050f010b0301030b07120c031a0306010303020d051b06010b1b0c150a02160f0f080606150721231920100903032f0306040605 67
    0x130310729491151b40c410044e0841d01001e0301e0901007a294007080741c41c40700c400d115034000c0030803e00060000408940d041c3d50000c10604d031100e40d00c404400c40c00b0884100c0c0100c03c0100c0d0b61003c0e0b03060030805e0f54000f0f08801100310040d0045600d1902c02a44800d101d40e651b9003088130001d2000f201d403008015140000c03407403d04844a541c0c4400c08440c055200c001c2803039106440c18080403420100080343c214200b405460711200c0c0c40040c2910ac000d4000c1d00401c3d043d40208404031500201600c0c0240007096556803039480c1e140340c210540d8040038140c0084420f40c10410400c4040c0d11010f0049010340d10105205d66540800d040070101648403103490b81c4070400a00c2600c4100d80c1c0007070704199960800e03500c14054060241010707000d02c03c013542ca858042c020070300708041034054541d400c0843c002d01d0800300011144001c4078244480c041000c0c08030740d60b628040080c10b6143c0708821a95120003020111600034681c5030b0310203c55546080800400003002420316107036608200000c0002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 666127194 1250 666125944 666125981
    0x109031a0a1d030703050703260a0b0105130b0c071707150c03210f0906020c0d021204121104050c090f0603010b1c141812120f0901 58
    0x502100354002081a203a40488600344400e001e440c002c039152807061002c1540086142442c955400d0b02c031030300202c8040d01805141030710104407003000c8072513082e08684400d0751f0a6a1500302c0300d2800302c418010800307040100911456030110711320703a42d185c1510500040107445000d100350940c500100d9820000000315055130014412a00261400540364000c0740428244100d0008651508500ca00034000880c1c1007103c07100700880c548801c1250f0480719000c02d04d100462002c6003a50314543d41111a10341c0012801c0782a0000d0081c0b03a101d08181c07018068916100c88980b80a008500420019625000d8190108401c00c1c04d039042070140a44184054581100000b041d90442040140a100036403041d08142c540b200441e416640f405c11150f0400d0f0302c00c50480d6620182c1c1000c80c11113903890100d13403200c00340d601800d88a45048401c0480180700032100c42d0800c2d4411a02c01042c070014043d6803400440d01e91015072000018081c50420342c0c41c2d50116015020340952101c00703066 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 666128444 1250 666127194 666127223
    0x50109030c03090504051506030402150301080703021e0a17030702030a29060102210906030a02040302120703081611220606020c03070303231306082202010e010903 72
    0x41204240d424540283c41c0c400d0103d90314014882a14011180e05c00156400c0140e03450380e02c0c020003c1d5808c6400030f80403105e408040815038003d5442a042070314298003040303042046141141d041841c01c0458080300081966502c0410b5030890503005640021942c41c400c44003290b810000e4994441e00201110031820840c00e0080c13420002c910740c0c2e60045c3e40c0c0303c44581d610407038405490240300182d0003050308804c441d4041c42071401d401e03007026140404005c91201c65440304050350190040580059503540f851040000a0b28480c0d043c0c07405402003841040810507000a541d06110951400700059015280c0810003140d407050f4541e10485102c40808400714400412000c000309070000c106039a02c03428160307a84d11589040c0b0707078181e1083c1001c0c03000900c6410002c115401820590080507507405490304250000d40390649006030080080004ca07174042403c54010220036901101c0354120700d0b86071720f004948032001e414170031010360184950f4403811f007020056820001c004c03a00301 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 666129694 1250 666128444 666128447
    0x30b18070303030b090f060306041203090b010b03070f140d0b18070e01030e010908030118020c0a080702010318031b0c0909060501091d1c300f110d1805010903 70
    0x3030a4642401043da000000700b41b49181c8007254001d04000f0000d00003980c0c0c0707940d8003c0c1c103848a40c01d141096143e40b990710019020340c0c0349501078403289161686910b400c1e80005d0034142c084002c4010484034101001c00140d15104441d1540ca031408041281081c51001c500070440c2d81140034180076080c010000c0c003d500481d0000141c000b40e03000e210030103000c4d10040c01e940b5a40b00261050100b000100805021001b0351015003d0909001d81044150f85c40c0c1401e100b0400c0301541c0312400003172004210b42c2d040c8100c5900c504180305c80a030300060340c0c9000f405078600d5940c82d80c0c0182d00c02c404000384400d00c8004802020006418480145240760000c0940400e21425000c282061107000340c00d00c0c2181c1500324800110000d2800360251298100182d03600b400601c240240305215074104074101c1d00c4c0042c002640e01d030995050303498224240848204282e034644682c03401210349c0482c134120084900b00d080300d03140803d4500c040380c03502520710300d100d00042c2698a44600c0c0b10406 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 666130944 1250 666129694 666129701
    0x803071d04020405010e060d090f0c0e100e04061e060b0c0c0f0907050d1107140c03010c1d21070303080f0c0412030210061e1e030b1807030303 63
    0x680900040d0445030009020030390040380541e5002c51081e00c0400014100300b4054000402c00d001d0110f40030105072610f008010b00aa000e8403404000c100900c500c00c102803180e0f03049108400410303a501d00d0421040c817070342d4002c0c0c0700500751519038054805640c3c41c6040c0c00e10325000503000700311b0550b0380d00300344040d80d0110001400030300400001e9056031401244401310007102400a0f01d040d43e40076011100c3e60b2181c40032444540e0349a9a40a540d844440940002c81c400c001e10090060b07820141e83c501030954030b600b0b101740e04021502502c0c0d0b03400780c1c2c5802042200080c01c000e0b021014000303031150300c140000074650031402ca0340c1c4001160000c0c462045a00030348468034036840b040c01c80100c94038201c0d0422400101004204034080e189441307a2112800380c1705490031085207017400780680d1a15403144210b20100d1044181095a030b000903401031541d45409100c400c286000c20b5010303901c61201a0100f40c05a0014101c458100840c1101c0a042003e68080715182e10b07000c0c0c002c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 666132194 1250 666130944 666130967
    0x30210030e072301030501080a03030509100e0a020906040504020f13270b0c03010b04030b25020a050106120b2403100615140d0c0e0607050a1101090608180a080307 72
    0xc4a43d481ca012602d5000780b0486041e11a00c9004d040c6000c141d031016809000d000d445d21000c0d03c60407038104055140d512800340881c1000d400b429800d2800e00410100c0ea00150142c3e02c00d62800050200507601c500409500007010b0361410220710300000100005d1041000c01c461174008840751100080c90b450220303001c2407041e400d41d00c1d03d40b00c1c0740d5450341c240024061803e40810400c03050020544410185521a5403101c3c3c0104100144844203801c0c0750340c00928000d070b80080c11240400000303000d080086c2c104d00c041c600c50950f040d200c131404010080c04c41e0800050314080c4007905040c0003454059000040c049502043c04444003400406951041e200c08140c081c0303100044901c900028904050801611810a05000103001c020320100700301600340174001c5410301480c0c8941e00a8000c4500540241000d0707032441c10b001100c00c200304c114034100858070005200b0940c0001c401d0f5081100d030000d003020f100c2071549042c13034902c244d50050050ba0010042044140d40a80b52100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 666133444 1250 666132194 666132239
    0xa05161d0a110c0703081e030c07082b140c09100e040b030307080304030f14070b0628090614091303090302061b0d021506010e040b150909070f09030210030e07 70
    0x21148400d1502923000981d04c80d41144000c003c1a00411003140103001064000b0180c100c150100b802c0701c4110000c0384a1003181c1071780b00d0000712240c0881e00c00302e40e4071800e21030a40e07243c0f500b4030340040c2c420b80741c0901c0b540c00e2140886540700903480d2a4070000d411040901201d030348080701d0034800400d03003041760220006800000002c0010b48283c0078440320b20242c2013900c1c100309690755200482e0740d0007800340f50040c10201a03260f071a02d01c01024850035243d06a040b40b800e0a242c170032400d80b6450741080c2807401c1d0340d50400c1041c0d20780031701c0564414250a6a004000d01510f000c40d4161066031019601200200d24400e000520558046681e440c07402103510401074a035003662a01c5480c84034400c100168000100d0b154001c5440e40c4000c413005100090100311200005c294002c40c561628007840c010803a04a10308102c10000d400141c182055603590201c082e00030080b09144c00000d0080903801c120741001e50007900f148886428081c103440019803158042401d40c0f00c101040074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 666134694 1250 666133444 666133477
    0x3090d230a030903080c03120c041d040c0302040507050c01090308070f0f021513150501091103090a260712140f1b0f0a05161d0a110c070308 62
    0x61150400180e0792180951640783c00c1d14461035500c82d40715a4200300c0e1a54410b000400c843d00c03440828200042c819800d07c0c3d400c0c4c1d03c43e0708049294105076059007a902820100383c09100204041d0ac04e12012241d044038041100e9407203c0c070440d03241c0224061a0510341c00d15440701c0c1055040a5114402c2801c0d80d1030141410b00410110307544e10043c0700d040e01581080c0410a0248003482085138043c01800072035844041e180d58403519510001e10003012190b8520060004598034000c003004040c904100b1030841c02d001c0040741c2c462005c0c1000400c825141c07095200041205000c9800507445920f82c0b0b41c80b00003038203210014000c090201c00019180c1c11a1114410f02c03d010b43c4c1030842000342c01070400560a51218038a80443d004000c9449100c240c0c6401c80b5080141003a558414000b03081611003040b4100c145c0401c0d0341000702000c95146445821a8001c00e00c2c5610618030a800305100d00c9406101001e4420340b07040314154010720390040700f40210b003001812016035000040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 666135944 1250 666134694 666134753
    0x61a010302071e0311030a05070b01060503060a090c020a0206030c07110415030b1b040b1201080d0f03090609020a0f061101091e060e01060e06100201060f1703090d 72
    0x4504078800e80318010040b010a0440d60310f07041110365a405041d00ca802c11001c544168130505240d9041080c042d00080c0c0d00084050070040c41203003550040c821070034202d085003070010004a040d41e00e8000c03414102c1d07a40c1c02c10541c0c10300c02c1022000c1d00742c0203480e09a407820569010031007580048000d842c013859024070881141800d100700500080ca0725601a8642d0440c0d580140c40031016003000c00140f2000007041d00090018014801818503000690b0791380004098025038500c140d0101c1c1c4a82c004010f400456a086030002507188005d00d00080d41404030b10b00301c401881e0628002e900300d2002e020100380303000c4000c5100c0541e1841d880781c20a418500c10031600340e074001e6a0040c4002c40c1030130766010b004c00140d909800d04c0e1182c0404912216800c6c800e5003190020384c461100c0340b04c2c0d2800d1003100e04203014420b002c0780c120300c02442581c0c24204404800440e520405048200c0c0f1195000a0304080c0143d410480005018040500207410100d80700690740344410615802034041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 666137194 1250 666135944 666135947
    0x3020a11070e1504110307030603120f05190c060603060209041a31180b01090e1c050d06030f141f091e0506041704060c02061e0304061a01 61
    0x30004a030780003100207500d540c071581a21880000360180c030340c00a441701d03928411004070002a5104101aa50010f0618070390708040102e0741c80021071409103e6415404811a6489411502d0010141c1215501110404811100101a10006068a450130130040b0800031150002e020f00306040380c042c0006100c2d009030b02598a03003140003a0740200801382d030b061000d0070702e10640e203080000018070302c41c0001715245106403502c900381c100400c1d82684141e020454040440c5024000992007003080900c0c10030026074032000f10804c088128071064903000040d1180085803501e0042c10f0051100e5907403440c200b815980c01d070f0011101074003414040d036100b540000b10141100c0c011090540c003114100001d1008040300c00b0195890b0b014004800d15421614014a0701a441007005049034613160801031480f0700d00514072140071030108402c00c1406d601031100940241c04613641d43d9541c4881805045e40b640d40305c5060706c1000e001c000c100502142d94081c030f111f404c11130040b0040c00a03c000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 666138444 1250 666137194 666137203
    0x200109060203090d030203220302011d030d0c140f0f120f03010909020d140c0306070f0234060207181b0e040f023105010804032a0303020a11 62
    0x55031005034003d100301c40441c0b03803c240c040c4c072180c024015030741782c0054100001d40903950800c1000307008015100400841d40d11107a4a8002c0c0e400c60390401d0315050640020351a0700381d00c10501c04001031a41450b00b40000030001c0b4038401080000c0b104030b110100104c07034440c8421401500d103401084007880c5500c1140c821600d03001d4405102c03501c0d50b82010100c030003c2025a0040c1e8001740110106d20000d088021000c5041c1c0d071035030040030044000000c1501c2c0c0712004054104000c0007400c8014041d400146252401c0d12003580c000e43d0315a4003c4504480006400ba054000700c21080050072070380211f000030580b00805401d0040f1101c0013282c0e42916180140024246840f000e402000d92103000b074545132243c02003003c81e9061240308010240d070400800036901d0b0b0403c40f20703881d07a081090502c031803129102040740d0355603140c00006000180010b002500b44400340e81301c3d120400702117a0303c9030f058208100492070b000103400c0040083d00244202c5000c02e0380c0103441c0c00022000603 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 666139694 1250 666138444 666138449
    0x24130e011409070f0504050303040b180f060d0209010509040f09050f0a1104090816050105151203030f1305070b13080303060307031401141e06011103030402100c020904200109 77
    0x522140003500c0d0024201e94902e41408103004001703091101007115a820f0000344001c0460300b120b50b40350100307004250400b0b9103c0241912440c000c01c8885060f80310749040e90440b8034654070058407a00080c0042c1c503984580348030140c0c05480d00d00f00d11000c2070079038403030380101d4010001c0303a035810f07485540d05076509116200507080310410700d015049450aa040300c0c05c49807140c030482e8103182ca03000403480041c071800c404407035036511802080792100c00700d03c9031411100c089950404490200c0b0340140c42e88400f40400c100055408005540020881c0034031100380d40c088100c1d1171048c0e444944208c503812404aa1089141325040014690340c0041640e014900082c00780000b2459962442d418828004000825540300c0819000751040c84045d544180c50003c0842450b260341c015070040000020a1076043c442011825001410004140ca0344554140d684440300605050159110501a80c00a520211107002c200c20840080110001d42c9038401c2040710b2002c0070001510200c0300e60 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 666140944 1250 666139694 666139699
    0xe04050609071707090c050c0a05010b121203041101091e03110d0203060708101511010f110403080d0f0207050d090806010b0f0d0605030105010305071701051524130e0114 75
    0x800d02803143c00e5655200755440c80e2142021440c0860000c0c00c0c1d418195241c07810b0310203941d00d214cd6501801c0000521001c8101a000352110300001d40580f000d0740400360000d040c80c00e00c003076625016402400c2c00406070606800a036215070b8134261120604889000499204a0761110100c441c10021801d0300f11741d6000700607103180d40e10000c080707400400c02000203612440700030000840e00400301c0d80c51003210080e5181d02c0000040c905440c25155902ca03001109031415070030740c040603078501c140d03800c2d00d501c010440d990703400d200e900c0300c09480c00c002c0d507070842ca20004500080050003e20b00340320b00102c0e22141c0c1041d83e10741240b0b840714000d216103005910200213142c1d803019002e00505881d0100c00340052483d80715008282160801d80003100c890344801000c1c068404403c41c2d004040c07005030000c3c4a00d14186801c0107019030403910050050550066041c0c02401401c0401d0380400604c9a450f2180d104c00402c41c00c0c4071192055031402040000040380c0803101084050821002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 666142194 1250 666140944 666140953
    0x331090b0d06020a020a1b050a050a060905191508060f180109112a060a020a0903060b010309050d09090c1b03080402030f0d050d1a0a1a040e040506090717 68
    0x101c1e161503003c1c2d130000e8101d10841c050a0b1400e03000803c0e400d0109480c5035200f130441c424078100030501a4034107660700480c1c80350f41101010404158080c4c2c00d1802d0710303002d4030303001c05148500808501810954100324809411440100c0308158885001445440c0c115071407003c4801840600844c041c44038082d6040c0b0b0000401032128540b0f90b0420900d00c41c0d1a4441860f00030740c0d0f40404142e24555100c001208200c542414017500d0400c4102d4000b030b00d0a00452400c0f84440c400f5003c0709003880010146904c0f240050140d030301070707845141c010341c02c103064a40566607607100030002182030042d0300402e03290000d902c003528454948030031882c0740034004088540c86901d040d501124000c0040340d041c420035451080c5050700348010310400080d03844e0952200500c150b1a0240c40c9009100c04510b001c0e0910108199140329083e0100c0b00c0c44074102440d401500c0301d1346482d11079508108000302d00b4100303000422000003081d0b44114440c8043d2a502078850f0782a403820014a03c0c0300c01660320 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 666143444 1250 666142194 666142219
    0x3210f03020c070e13050f06070e0102190201210f0f0e01110304110619020a110d05030702012109030e09130f08030c090d05030d06140117090331090b 66
    0x3e04141054101000550017540d4042d595241ca141c59a41d00f54801c083e04541c0a000c08030741c0181012281701030900140100701610107024800e0703204a030000e410090000e50003c421248140100c0010700403440502c1503980c0c44101c10082c044c0c0c000c501c9650703468201c42540c0c861041c452088503450190081780303580c5882e00d0314001d641450707441e940d11880800041503600d6203030708130264106850f005030030710f24a2401d107030010011030764030280a0b412271036a02c070000d4400310031280342a9090034400b900c3d0080c100d82004007200302d010700701000d1801259209054100c405c0a0190400f03e030070403107540e41d444000f50701a8180300d00415010104012500041e280405542d104640c400918108a03201c40010900070380d800041d00e06400000700a244120203000780d0002c0d2000341440e0b01007074404400201401d001c1e05048000c400da0402040075000c00b8030440b9841c07088003c0c210314130f0101c0c80d8107540d030050303a00d0b80c4c22954000000000340c01c500350181c102a084c006150030070400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 666144694 1250 666143444 666143459
    0x906020709021c060e041e11010503070915020f070f05150f070f03110d030b010f0302090a03050607090806090d05070f02011709010b040e0f1c0903210f03020c07 71
    0x1042900310804a0054200040d20b0b20f070248a144010140c250f000210360905007491034142c5404913080a4102010f0815800318035081281c1031400820b281c00d69599848100444403038480d5045446104100c240b150512540050307014a8003d41c00300b69941540c0d24a880e8101030860310481b500980e40f2408400030201e5600034091001c220818985000103651b12100c200908034001c5021964209540d40601c10800c0122a080c0050908020300c0c042c1c040081e0003004038058403810190000b900c0c03c3c2503102d1030712a0004660010840d000f5081c03c29020b021000d06003d5440e4511030b00c07002542d590000500142c0d485041e841d00c619068003501e8100111099034030590500141d403a9030011038041c0c8035034034468402180000394a5029004220a0300d1445005001942c080020300d07084000c00b292800300c0b00c082125030764805059641c140c514155651001e444640302032905095010f030722031120308260040d600d400b440c0d011032a00780c00724001c0302c1030040b203540015405e00690 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 666145944 1250 666144694 666144697
    0x50c0a030c030204051020030406090306110a02060109050604150306050f0907030f031409060d0c0f0521040201111b03010b09070c031d0409030203090405010905091002031e010e0610090602070902 86
    0x80e1100a4200c0d4031f051120452561b48217511000019061103020402d200e12845426440000f00a50310300d03118003680020b40e41d030f1040c0100d004555440e008601180d031103910507503498410703105000c036081d0b0740e05201c802803004450140b8403541140015258078404036460054a5000f551002d4100c05030700c00719210546203403003019054040100003210755544002e000b1071851310501164160884000a06540b41d0200c02000c1c000d007031115201c0380304410001410606100035240c0c807a030711400101d0300c07003100401c034061a000745041c41d5503006d500c8024601d0f55070164004c2c00143d102c01c7c1407000f845000ca52000001d03010340002d5000910507a9440c440340d82110842c403001040e54001070403a56004000c401684c4000740e01075003401e05004240c014070700413100f0441460100680e503100c03880da46c080400c46a0010000c2c52040d10441114810340440102580b00d60312000300300c540d82c0c800e503030861080040e1a003c42c0d1091007904d00c0e0040da0360590141400d80d14101640020303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 666147194 1250 666145944 666145967
    0x120a0212150f10051c03020111030702250506040e150102030a0e010f090315062d03120306030812070206151003090c0308070507180b0901180f050c0a030c0302040510 73
    0x2d401031000041c1603170b8001203a810b120101c1c100513400b407218031300a07086810080108103502420b001300b00d07070607402191501075034040e03124501e40710a4004001511124503009680d1164001c90080f50311003c3c1d0441c07a214214544060003818441401640d8900802c1c4980c0c0002d000d40807896210f520400000c407800000307091811000317403030307a4415180c1c082c00004011142d640740d408000700d07214a840d10100304282c2c158440071701c09445240804000d540009031800c0c810505064135684071b94041401140c0120403503031503040c118955540313a80c09840c1c00700144140404076400b00c0e0030283c004040031005200340d01c0d445640c0c106801030a80110191042e81d05083c0c000040782480004206240c81072028009290501003000c00b200318405030f1855075450100b801340c9646442c03001605441060002c1c0d144142d01000110182480d034200c1160a4205800d0200d4401c150340900340e0812240c40c10310180202000072001c0740030394881e169101c452046100f5546000b40e0072181d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 666148444 1250 666147194 666147211
    0x30f02030c06280c031b0c0206070620070c030c05060a091406040e1f06020f0a032d020705090c070213020c340e010305031c0b120a0212150f 62
    0x303001e44100f0b10b1500315004980014007203900c84120041904035403409040b040140c0c1801e10020300c003500407a000d4016128001c0c140d80c1d640852010b424010718400c581c03160901040380d5203641c0340c94008046501c510089440f01d90155010446103000c0341070364201c0c0381c0c0c0c1d580c3c17000440c0707081d100c030fa0301d094219050307900701500b08000329a001116086c0361003881a070002c4903c04403e042210031007606944407800b1504905680070440341c01103100120241c06142c0100c450520300883c400324a500040e03c2c40c4514241c0c05003807120f402142c850100d0300700b10ba4443c4c985c1c1d00c1c8081403801e4070801e840258000402d224002c20301c0100e07070141c21008050700843d12a034203e14505020001240b00000c40c0d01c80c414004004201d206400c5c01c00781c25480300b40101949169102740c1e071b900403aa103508450303142d80710340c221050041e481548511001045552501801e82c28a0703110541d440003680110005001e12000101c0021951051003060030751680f00c3e034800700c0c01284034001801da01d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 666149694 1250 666148444 666148501
    0xb030910150503010f0e07061b0b09190303050405010605010201050c040e0405100914010f020f1801020c0a0f08190506041205090301050109060504140f0105100306170604030f02030c06 81
    0xa03483d20244140c001144600c180011140e09081d805407905080b940564100494141414011081d511848410316030102c001c1c802d544079940c0c0542030144c20050318091003c0f4100000601d41d2680001c0d004500690080207403039280c0004900b60303442126003803d15882004204140042c04021540c098080d0083c1c914100440c1040070556603441019240b0641c1800601c1150000784a000312101b4032040071843d040c0f40c00003195503401341c04503c00d4400d4031040d60b01c659034024041e14041d440000c00910305682c80d0111081d0700c9174140248001441074a1100351741d440d10216100b0103540050060010395034507569a10360403a451000701c10403070288420f00c1103407403d025083c040c0c40c5829001c9096403c02c170074001210f0b17601c49040555000e13501032003000b8003060b0002d4155803094822441d515660311095018082030351180004040303440c90b4204a450200b10710340264071a40c2d4482c0e808460441c100c0c7d880c01080c2903100380e600700389e01081c0640311845010254410301c80341c41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 666150944 1250 666149694 666149699
    0x6010c0c08030c0102070b07261305011418030f03280c0f030c1d01030b010c0b0103201014091305130b1303020303042904050c03070b03091015 63
    0x20704541040f540194985e4001c9a000c042211402c034065100b0201d00e8080f06880d03007030281e0a0a0f094100e0f403041e210b84400f002c118103020a900040c0600d8000d0000c0c01085461552444e50700000c50350121861400c120140c0e45400100031180e00110500e1010705645400180c4001740f0f81e07421580300f450401480d40e085c507220500640d00000c00640704ca03580325200c0301029041d100b0403c607400800c1408081603280d00b441d511384000f00e41c000c1ca00040c00c41035610040e140560035100150071070401100020130401c500a5840c1031040820007115110035010034800e07030318040c6001c40c012031201000c100c19000d00301f001c0c003180000200700900018506100384c0841d001a280309600e003500c500c148060100300b603c16034008401c4490044012081d442c02500c0c0d000150000307182c213038404802030008510724155421041c00840f40c1040c1d0405262859881480c00d141c0b90082c0a41c02e0f0006003030350003506592003080312002070a01070f483d580f42e58005088032994010311001d201c1c0013 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 666152194 1250 666150944 666150959
    0x50108120d0c0315030602130e0c0a080606091e040b010f050304140a0b0c12010501180504020d11120f0a1515020715120b04050c1e04091a1c030806010c0c 68
    0x64000c5018a0f0010795a904072020800e0310700e070a4000401010270713007043c0320620b00144122800c3c10494a03106666888140000d2190703c03400301082d0784440c210282d4078140d940c8240c00c0c4020401220b040000c240e1a00c01900d0b8285a080801c01190083c00042d004c5100890813504004420060392007405c9659200700b01807009071541c0041980106041070784030565401715000d41400d0070a01340180c9071006121100e401c0d401200d000b15000f00300519041c820303800501080512415030f41d00d6195208a001c800e520455020204500c0640400d100100c40e00c114125482e90810480f4850704042d07002c0c03031800c00020362000314810b0310300000303012906000a1085d40010b1750344a240b010001648416210341c0f50038181f25502c2d1600b4031140640340303000c849981da2144040140c2085040301101c0d54050f5902040c091410300d4141065450f0318170305040145412a01c05d031842c0740000101e10705c5a031048004020440c2c203008a9840c3d8018600703103c2031481560a01c0200c0d032038030314 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 666153444 1250 666152194 666152231
    0x30507080a080402011d0618121c08010b030105100c1a10060207170303070e010504030b0f040201200a0303020c01060801111317070b09180f0406050108120d0c03 71
    0x81c03400036164a0602c821903074004000780e05941159181011003450100040b150304c03400c1d13242201e107402007a0407503094450700102100030341540e098a6030400d034032040c001c01034842d0b10302c1f0b8001404030002240000c0f007482546c1c16102c02900c204681c145d201070565070409514015070301c1604071a820f20344049449084c600c103002d640750740d04089180c1a80603140140e2a00508490030314044104405100001580ea0003c0c00d03140004442e084500141c40e00d1240713400291440d0400420807042662202103c1e0040c1d10070703a0b69000c00140f0620030092603c1e40040c5202503000000640003003446500a450052005000094050790321a030b501d00312010484101251000864926800003c50f1050002003442e200f05400d140c40c00ca001646a050703e026000c680000450440c46903226440244445d04181408500381d00384121401238206c8121411203002c0c0c201000800d850f2070225210b00c00f00b544000e0281800940107910000d0041c61010754101507032100540e240308603c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 666154694 1250 666153444 666153457
    0x5060705100c050c0a0b100b04030b10170c0f011209150e010203060a0b03100306020a020303090d140702090402030316081b06061f021c0f090f050d0b0403050708 71
    0x80c014111040050007040c1518501c400c1e41c1c05000b03050010361608030022441c400d10f82d51000341c10b11250340f410b80d5542e80c0c0b0b44617044417064000224020080040c1c07040082e005610010040250541d81c0b108078245a180721400039030340d0040802410345080c808103e10000d5014104414901d00c102401406c40f072103400143e511408180c400001c0c103109108811041442c40000e41c5189040e4000c00c540d220b0b81c3c41031201031240000014141005c182024001d0f50303001c0070075981d5440011000796290810354485170140030301500300c0d6503d809250b403100001c0380b14204608012094080102c0b0600092003a60940000c010882c00403c1c107040d041c4900e849031041a4842140b046020318501c031481d4504141da0110041c401c1650700c80c2041207503242903113403601e0080c1240c10124180481c0349401c0460200b807103da00d02180d003081380d88406803d10740c0c504c06484d81e03603003c0d00c0050080c0e100350343d0000c3c82e0503001e601149989003002da100d4040e040c5189056402c1d0f0340c900d0680d0149 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 666155944 1250 666154694 666154703
    0xf230c01020d06121208090307060920091b1315020d1701050312030a0f0509100e1902010f091a04140d050d050c01060b070804030b130c05010e0a050607 67
    0x28002c8010442c40c403c07400580b00042e100c012248641d41c86031030311400b201014003401010400200859000c0044a214030b41c803c4052000c04020701e00714000268030340c0100184241048001594281b110341d59100314034500c01c1d45071014004249a0565101c0d0f20b004034804124103021506141c4203616404806d01940288480f0030445001000504081e840c2d01c0e140007200010086070350001003001c41942030180c681d6490b1102d811990003405810280c070b031101c1c106030400c5140350780818a1111020350701c0003803000740c240b1494103803a0b05d0020740c8080b1545065007030344059441040200320642c6079080c164041619201108107490085a1101c00c2610029003071101d0105505040000102500c4001c2525000d959440d01c1b01c0100e43e1079410000045020704e9141425000500101709a0100555800c404c6c1410482f950203800140d0b41040d04502181b264070703000c80b411507c15080b003a0035040600700001116003088640006a005108e48c4010580e552080003c0000d03506c603 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 666157194 1250 666155944 666155947
    0x1b0815060f040b03011703070b0a0f0f050a0b1e0d0f0204020c06090106030c0b030f0406090845010206070f030b040501090b01030e161404021e12060604060f230c0102 73
    0x10a20031254943c41d80300103001b590001d101640000e10046d4031540c000c4140d5002141c0c10741c101000d40014002040f0046405051800f4098280e5107680301c0700c00c203081690105549401c42c416090000181041650003251030407444020545620014002a200500140c034080107151aa45420016200020300365900d000c2002000441007001c0018080c1d0746440741545080c039030300040303003c0040014148a031200022001c0080540c111010b01d2800d0102c4003020010385072000401600200c541031004400c51400c4220000442c0b144014005a004244559502c0021a101c0710b541e03100c42c013815140c90303202805940b203010b01e50182c5070000001480189040c00101622001e0030402c0e06504100708014203d800400d128064032440300140c0b00020000010400920481014948550f410300c042a45412800000c084002c0d42c0c0c0b2001c0c0346c503103502702040382c148a28407500d030200f0052100310490078050b40c2203044142060401220300c0f500315000084c0383c0d0061006d9600b6950 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 666158444 1250 666157194 666157199
    0xf0f1e06221203050a030b0a05040e012309061303030b0405040b04231b0109030b100513110313110d0c080111030103021005032802030403031b0815060f040b0301 71
    0x340120741c8070082440c00314910100100c2e890140c9144900c888034810140c07a500c004165840e018081d41c020100640300704040841c8580381d030700910359400300c51080c4910b9a101c101c6450110103c600525038003015016a4807000c01d1550341d0307418000304909240d1a5006c081c42030b0346a204851023240075004280c090b244c603240c604d42001380c0300c0310b600340ca0104030202c5144100c00500c0031a42d440b5414411030139030052005a03107014440d48020042000c03070080024000494044138200ea40640701700110704030840c60401907664421402c04854418070014441d01180113030840664011819654109410004200c400800e84819600380ea0320400800c095002445004030f40040d48a41606650441d400034180d400c10b50114420050048080b50504c030ba20078084800510207006114102c98a2201d02c0107908202c1e003c0e0042885c10700241d50240072030b5850403000d0800c1c4e1700c00b541540d501c80781105221140400039080700050006001d001401c00060001d060b40400c51500e030361 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 666159694 1250 666158444 666158497
    0x3030c0405010809061e071713020a0f120201121b0c02010e01020d1403070522090b0d03081308091002010204170703050709050a0207120c0b060f0f1e06 67
    0x10307001d0b1041145034400303010029840b1b0180c01003d83d107410644c0035000d07900c070800e0480b048248400324428400b403c405100c0c0f10f50080c1d442903e01803003550014691551410010304080b6148107d4800f1451154a50010340c481ca104441e404458000042c8034290441c4444c060b05034045210b010030201c450744010341d81c12100d9201001f60074401001e211180d0000100a051441c1c0500040217010000c960710a010300152000d00000302071080c100418410a041d070300029209201100b4036003006100c181c1024001c2140e100d030503807104462a00e0300e05100b2418010080c05032005581401443e0640d138448003d01c0c0508100e500141e11340c0d0924445010350f140c0e480c0d0b0040281e00540081000803000b150000032500410400522580c40d0348a80d4068441d2540c01003030220203481d81d0841940118006141a0140200620f6a0390340303801d1000540104059940c482d083c4440c00c001032610401e00f0b0000300b901884102d20080e07030790204007160070810220344603501c4076624400c0c80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 666160944 1250 666159694 666159707
    0x26040e0f0406200706020d14071707021606120608030f040f090e060c13030510020d0b0901061b060920031506060405010e0303090a03080901030b010306080304050f1203030c040501 79
    0x400c03076050f0304803401d94544030700b0b00074491007000402c080c1c1c001c40c00b001b840c115544510708040900d00c0030012841d101d0002003043c98030003103c00004070508003051040c0c0c40010100b0200d186860111000c504043d410b50356044028464000d29440e44804124204103001600524a144501689603410680305d44d02400c01500b0460030186061900d515846001500540061401403003d41c0c5002c441c07a510340d041040e80000d070442c41403003402030b80101c2c0c07a070003031480c2c01500c9820000c0010010030440301c140c4c28400c420014901181866161456400d1031518503c5040b0004031510160745014002c6030031032000002d4002081e6a8503907040034044500c4050205401c0d681502e0031030005481c60143d0b0203010b041155684c00721045880400c12240000c41c0100143c44680d40c0e8944176030039030700080100d800030b800d0907140c6059500038000c1e070040c2d40c4000041c0d0700301800c000600c00c0c081c19150307220768004c2400e052414091014001075004041d81c0e0345082c0d4a60500c0000f5040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 666162194 1250 666160944 666160961
    0x609060813020d0f0b0c031005040b0901030602031e040c0806090a240617010f1b020604060f0204030c03060e0c181329060f0402040326040e0f0406 65
    0x34400c000381000301c1c9803030303004800c200c0582c11910000b02c10342c80c0c180604558181800202a0b00e00001441130a066002c040e510641d01341d040d448040c6d840b0820320054441d800c1c5103a81100b4031500520015003160040c0d42e1106901e200c1d0150f21000740303030b468a0080c0660301551841a801c070140300b000400d0164690224841008051060503550b40404c4c1c10240442075028120851401c0c2102907940c005800a003031016000c28500e0446164034000c046215041c1c40107403408240c040400c414204c1f01d00300303c24540103060582e9a0f030b214140500b000c5000150299803c100100014031000e0340d000165001e40d400080c0700c4400440f0702d2402380b6000d11184510080840c00c02e16103201000a544030000c00da04044003212840c04a440c00c02d016a9410741840c60a02810b1050f107a1004038400c103030444074006d00501c2c007001c1c0401c82c82580000f504800400030f100c1d1b0040c40c009045407049078984019490a9599a0140442841600c20881002e83c10703040c01700b0f0003064000c0c03160 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 666163444 1250 666162194 666162197
    0x190909061703041806090f1d0c030a02010809010b0d1208010e01032f0a090b0405060402070309060f090306050f071e05030a09021908030a1e0807110a1b060906 70
    0x1500003030010716075901940c4070b0802e400003040400314545a0304d4119100070203a52805001c125402c2c000b203809448008811503200300f5100130110a420001003800e00c02c1d80103009000b2441c1c1b650011100c1070002000e01d2100d64a501e203015041d00c40d0200c075124540036411035a08403031031006c000c0036410181e0101c81e1103227014006101040e40041814034181e12002c0b1145400410f113203c51440c403260405580c00341a040000603c0d4442c0e4001c0110988202c50400569403041c0c2000124042d006029001a8202509004e024000c140245c090001410400f480c070341e80ea0707101002c0d0b800c1190b140c09a05c07500300900501035000303091400141011403202b4003100b01d044004206003c0100001541610381d4481c005540b5201c0c0e03482240f0305e86500e058040c94071000f00c03035038a82c07050500c10001684610268080b10416028040c008038030394481c0c0094481030b00072251180c0035608800c10b030041c08034904c005000c0008607180c266540d01e000a69902c6c0a2010b041100c13550b00c00e40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 666164694 1250 666163444 666163469
    0x102061b0d020309011e0f18080904021b19120c0b0a0b0105160507050a050603010b2703030d060602071e090914060901060f0b0c030d090819090906 65
    0xa50a02024080c0c40541e041d039440162a0394503110040e0260442003165a2181c1c115002103e42c40819002607126100340d09080c4140c00042003c1611810002c00241001509103c4904146065002840e060003c00d0b52004d00c0780140c4a0103090110444410b041c00c95284004070400094868110741340d034050401c1242139015440d01c0754408801003064a81c20b43c0e41040544c568000c0042d00d5000784440c9480414180301d203015940c1d4071150050030712880c1d803d080003071140b42003401c990607180901080b5003032416042d039902080715511111117508c03084810b20401602e0402c060203882c505a5804601649070150103410040780c0c1d08001e940000e105400c071440840c81507500200c0c0d10f94180010301c080d40781041e20090311249052202c90083d0420303c8102c9a054210b1001d441041383c840056035078600041c802071090580c44000d542013031042051107001544180d00f41d40c01420aa442d029814400820000b1010241800314011303000902210416100c1c120143c0035099425 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 666165944 1250 666164694 666164731
    0x1091a1309150c0c030305091e0a0b010806040f1209031502120105010f1704050a05011e06081515010c02060c03120606070b13060608011a10170109020d0204150e010206 74
    0x14803180c84c010001c0d0034543c070744020444c0346400f04020300550741d0340c1c40b200d00085220076800703844d005801d1069075680300002c000308803c040860b003640150f41c888000700d00340c4180c0c0c2daa00750034100d80d00306105001c4034850003c04900103031a510784072444800010394502d80181042009107041e04120b041000400001101d150050030a0b2642d600d248070100140d0344901c0d11618024155600400c19400c2511154105e86001d1084c444502c0100040c08001c2d02c0d41c80540c0e039070510b181c0c58189011154042200c600110600d908180700c10301d0800c81807071031500480c001d544100000c4800c2d070b000103840180a5102c414180d00440c044616510300f50302070315280326a80c000b8200c3c41c15140303424081010042143e1155005045210090080c0340c0c611080b5103403180c402c483c00b40500e003a54001c8642d18440c0e482c0041d0030301488003a86682c2d080c221b004001b9044200401a43d5500f004049070a401044004000007082c0d940e02580c1c03c103407000242042806400c0304403180da0030440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 666167194 1250 666165944 666165947
    0x1207030603140c0f060d11070b0402090112050a170c07031115040f0303080903070506010f06140304030801060305060a180914030406050d182003010c021501091a1309150c 75
    0x220014070908440b0076866508200100d1b00401180c0d442203503000c0001240070030041e0001c81d01c0e200d0360084550100e10384e6900c80441009050100040c10b41d08020102d0340020411680c003000400700b161070350b042444805030140b611005401c20355000100c111411220710b01008a00c5241e101c12007540e04052910601d0514441c0900000b414018040002503000b00c0401c160f42d41140c216040b6082035940d903204400c500071b0390044200003854185d00c403142e2140f08084a008640c1552000040c1c0e103024411070003000041d020341d610050f8180c001443c480b40002e80c02125401e844001600304881c54050400040195140266041403000304111600a82500c82d0790180c075402160070301d00441d0304007604002040c014450184c8149903185e401b034083c4403144e43c071000d40003001184072103d03007607a45010100030000d04518000040c0440149500150340c0c80c40d00302d25080340f180c148000240544180700780c280d0ec03d5984e44141040c05243d200c0e10f4000a03182008000e4081413440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 666168444 1250 666167194 666167209
    0x11040311100e1f08010b0f0a181d010f0815011a04030b09030d0c0201150515071a1005040902090105010336020307051c0b0405031207030603140c 64
    0x140d078480c0d8080c500c92040d80340208903205840700b00419a0b41c1410b4840c25010303101e036820003200002100b080c004a05070403107204440c1d6904481c0250b905003150840300302c884020041d40e142c11090604800503800c803250290080b42d050341d408100c003941c144000c03020361081c0b0f540f20141d154801440050a007441e4400c0c1d5055403810030009200c10404440000d0780d12650340014001000101040b00c1140080040c01c1003801002062100c00038045049003030341c07a2810003c00301c1072030f200104020300e42200e15040c0c4810160fa0700742088000d4072803c460442c4060549040080c041c02c20030080010070320760005e00411201000680f0403500440c5002405001d440c1c18580e03540044210202513624009941d0014506114031485420b000701d070513007502c44101d010744201746000c00c4a00c0d00a090070500c1c494414031011050082e100c2c82c8500c0000380054807a4002040b10241030032812001c0382c400c0c0300d6514042800d92851400b005076030003407110076080780c0103401030900300e541d43ca1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 666169694 1250 666168444 666168473
    0xf050a17090114070b010b1e040b0406121a131803030e06130503180d1506090b0901052419051e0307020a0809040b03011d160e0c030a0908071401110403 67
    0x403500c88d01c5003101403070110200900746029032020741c08a00003802c42280801081038401607914400105c9a691210003512400c100070800f0700107440442e5190f040004030414030003481400491110191303003880d02c0d000501881900003a45500d40c0150500c000c10285410038004656602040c1981d15030540b2800341d641c90a21001c2401c1e4032105580ea20302d8243c00702600312000320300b280b080b510100020150791041d500740ea410f04000803050303e04143c9242c1228030240a601c00c002b894140d141d20218811100c903001007041c03009450110010144d07486488039070b01c034140e450300f180301a003034032040c07031401100b1001c410010489010740c042000444258018501c5850780418400200a411401c4c121038040d807030896194070006a070710780d04202d40c0d819402d58405d40c841c1c0503c0c084400e40d074052020010084804a0000d5400c4801543c0c050850840011005941d540d03590080d07001a03030a48046081c1c90028165070000e00c02e400d451a40004224500b615507552a8030000045 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 666170944 1250 666169694 666169709
    0x1b060f010608060a0b03070e13020708040b0a05210910020a0c02010809030f0c03030a0e0606090712090804150e1f110708010e030c060a0c0801030f050a17090114070b01 74
    0x20201d0610b481305007901000d04602e0303003113540307d140c030352001401a05d40e0100d062082100301e40703105802800d40300301e0b140319070460007051806d81004a0b01c141c6601000329103003084410040c0341c550300c008039801301003013a40121400060503c0d404907807520f507200034402c007440c2c070401031440840e400004040e444d91382030821038041d0384d403038201c0c074118040c01d202880800301c0021094003084000c0b000318850100900200015146480160390300d010444940d03030807403d14808104c1240c080e90040e00944869100440c0144003a80c505a19412550050701d811012201608080f5000600c8000d0303000190340c490701c100003051980000404010402041c001408403a0b00b01d00d606000c3c0c40003604808000340810820070640590329882041003414034021000810100e407007034040c00310101d0b00c9640e0841c4603400e50701d4044414501d260700300d8443c4203101c503042c001010004010300070004d42c10f43c80c1d165031840700050810181d584c402041e4034400c000080000784118074a506681c0c01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 666172194 1250 666170944 666170957
    0x609061e010e030316150213060c05100903052106030d14070f08040e1e010612091a0108071202060a0c051e07031202011b0e060409020705031b060f0106 67
    0xd0500507240d0500505280340c01d8000050803c4605a82241c043c0f0054400d0300c0100b55681944014001ca000e240c01100e80381000a004101c00f0740b08140c05a6a00d00610984100522210b50a0111001c01408a000c40c00104d03090404039050300b034096940749441500c1c507903032a00e50f0002c0d450310030864882d402d00c410302c0f03004c0c101c2c0001c45081c0c0d000c055003c04030420703015481c140003109400074460315040c003d04c000080c5100c00c00c80c4003d1022105030b0030300740c1281d0800a00744e9200b100d007101c07942083e036503031080c801040e025860151100300c0d410720105954106802c2504000150300210712860501c1d200d0401038a82c04101d80c0007040e9490300000100040c5070003414200c0301d8a030010141a814486040c81c080825001c00302c902c91043d2401413031180b0000d90907640304040162040d004282501c100070701030702c4240e440c0c1c4401450f0740d14068440c2e8650049802c8040c0a84041e40045184032441d4044030313410802000500c02080361f49802d100300c02075104d0500a04081055 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 666173444 1250 666172194 666172249
    0xc05060f12041104050c070f081c0c030902040f090f060f021e180d0503030604050a0209040207110315041509030e0904060c0320040b03250206090105060906 69
    0x44035001e03640205280280c51201e81880d0414007594000045034030b126034580004540000005011541c100e5032056074040e070700004c1d489548064201c1b228819270007040314030502c4140010b114025041030181c034006150601030062100700c5400c3d41c410071072030b4030340004040812001c0112481aa52001e00413a003601d80c0380c0c02001a00580300ca144d4181030000040c07216120301c0019100c405800c215000035042c1803020050f40780f50580020300207400c10800b0401c64101500035541c0002d001d0030151501038214042070480c0d020440035149428040c02072901454103200c07024460700441c008004500b01a20b50796001c0b02c060078140142c0c4c0e5240110310426026a114001c0750388000d06044081c542030070700d100500200003100703000078900190b840c2c02900181050000440031900740e401d0600708040980d0a03071000d001021011603095400a04903400103002003c0e00d00303503010381060b04141407001d007540c0016002034840c00c01c481c100001034480803209800ca211113a5040702e18003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 666174694 1250 666173444 666173467
    0x15010e1e0c0c0102070f15020307050a03090501060e130b161b0609020604060917072d05090c0406080106050702031f09140d020c1818070f030605060a120c0506 70
    0x2c5450011003095001041c2c0509002507a20100d10441c020f186145400321451403000032440101e8450010400901c40c420419100342c0c003650041d4401e50000500948034040c001100c0801c4441d8000608400381240800880082c81078020340b106407130a540d103c095101802042d100740040b0401c40b29000300500f40b1459400842d203131a0003030100c50740c03540c9981d0020401441e90240c2c0006603400100802185000503588040752a055051080c00805036054421030354000d40200d13030310180e00408165a9202400117000d00700e840c0300ad540e81c1d850088040c00d2600164008020300005104020160300c010a12040700103488014100d00026048024020204640064881e440c82c1e42070b4002c3e080d00080300864a1711a0b000c5500103003032304042090080c0c0003c01549002a84030204140741d01c190841c0b06001c522100f0346083e2030f121a00031011440c6640b0940b00b0035101c0003480010f080141465000d00b44030746808101c0b00d4152241503500c0402e202d081d00030880040c00c3d41001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 666175944 1250 666174694 666174697
    0x5131a09100906151d03060a0b0f062a070b16032d0206061e0402030a0e060901090209060f010518061b0604060b0105041d04020303120915010e1e0c 65
    0x1032003842d908100d400d84403c41c0c00d4000701c4120448000c0395084900b5620b12402100001c0403440040040950b82c3c2c2e02d40044000e020240c40242d0482600142400d41d07a4800010303022018040e50100348544000c40e80d002c044403842c02c500d0781500710031000c0c016a40079030220b0f018003880050240d00c1c008686400c4403528000d800079244404162070030209492000707a84109001e4a500304e81c0e042e00c0340c030304000e491440651000702401224855440500f042e40107950700004c1c03a800000d240c0d81469007a07003000021611603105035580d019210851800d17542d4241c100320140c403868111180342001918507c1003c2c114000802080c148449981e5001e0464840b280b110454060b00d90361075442583d2010180c4040712540d0621b01415005d51052041d101111300c600c2803c2640031440c40001480c0710050001d9825000800031b050030b0302c070041e80460085110030010f048403588901032041500040c0c01010303d00350f104c402d01201481401c1d0301d0081170030034144442e05403680d240c500c007103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 666177194 1250 666175944 666175949
    0x105070305090a09140613050118091b030f061a090406180c06051309020a020d1b0b10030b0618070e030705040903081f060f08060d02040905060105131a0910 69
    0x49170a0807040c0c1c091032495542a40180000e450720319402218111102c00d84800340500c125000142840001c1034010b0f80002c81000e001c0ca007590016042e8200101100981c3c5e0410b0303601180ba613020a0812905100c1c0150580300743c0a00e0402e03002880025902c40800342005d043c0c652118650207030000c1e40f06076034455582c084010480d19543c1e19020b005178211402100e00ea41030800c0001b002c2e442e5000b104c0582c03201e6800b41080c210321403000d40320b02c5486904104072400005065000400030f61035203018912101510082e80c0c55450604800b1000402885c040c40302240c244043c2252142e00a400001c5810709001d4910b100000ca0728204042c4d1083c1e91041c1001c0311f81045c03540242800b401100d000c091500c41420021046021950b2481104e0006441501c8514a54444d00c0e40070341100004000c00103060850300080c0030f031805001d0503541c5400001c010000c9240c0b0a03441c014440c42c41c1e50903c9402c05411980151000100307009004864000000d648805803880c032802 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 666178444 1250 666177194 666177209
    0x20a020411190f030b010e03070b0f3603010b13020a020a020913030305060904030206010e071125050d0203030412021f080f100305061306020c032b05060105070305090a 74
    0x8802d0036804000b8010305030000920042454460743d036103154415108418003110250042c142e0034030704545003456074080b44c43d55802203410b100c09a1601124004010f0b12040a08404410000c81801407580360401400314840c3c2c1c9440f40b4010035860307116a014201d0040745c40161204110142a0309014404000035400bc0e4100e0030802c802e840070005c1c0300e00074066034003004142d0340c99080c400d8a80c001e980140c00340c1e006000400144804d40c100d654440380c5441c00d41403001d801c0c8452460308030b05084800c02804840840d010301e0b0307040c003000b60061608482c1c84584400365008a40c0328843c40c01481700940038540c88d20103640b80c40004c48040501e200550300d4903002d0010040c141103056501300c004202c90030200340071010940d04101500d4001c1c0162920303485041000d03680e600200320860300c0c03035024424072480c1e41003070010781201848480010b06d40180c542c0e01c1c01c0301580116080000c01e24000600c11a66885810385801540c0b50428a6030307141c1c403070005580c403030741c44c3d01500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 666179694 1250 666178444 666178477
    0x7030b0112060f0905010b031b160c0315050f010b0906031308030c04061112030a05041a010b0a020601080f0607050a03090803010b04051c20011403010909051c020a020411 75
    0x32045100f62100c000c885514108200b140d032a411031110b13500c4191804d012400d4801c808c290600302d00750050142c054000401c15401c1003d99483c4490401944140c0b501c4000c00d1100c0801800c50089c1a0f100115402070455036041000d0200709000c4d542809020715404000907818282d41c080d4000a88d1f0000206600d900d001caa4a513402d501900031800068030f40701c9105e0350380c0c0700001c49020105954410504560381da01c1c03900001c14000303005443d00b9146c6081e1045229001440501814025000d640e80d07e85403180685081c0c1c0680c0607407040e621600c40000200c0c0d0200d0f8542c0c20015603d402940c0b0540d126007140603207203981018008034400000054200c84060090084400a075800d107484842c4c00003103191031186000181c83e114411000d13134826000040900301f03484050403e501341d0114a4003046550b003098000030109035440c984002440350402110035201c40c220081c010343c114820001352100c004840007130040d5128106490000780e0f100c2a100d07002d04142401d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 666180944 1250 666179694 666179699
    0xb0703021f06170102030c04050d080d1b020d08040506071803061104030209130c0513090b040f0302060c040b0a050a12020307030c3209060405120a1505090607030b011206 75
    0x620082840b0711074200b056003d204151115401030003507034400d60b0801176081c14149030070f05201c03110b004c90404540301f00003004100340024191040d0109041c01340b41c0311725504041c2030068940700c5d003918180140304c44241084005080040c0c1964410310303500d056221200c2071258035880d684d5540004121a0400c903514a00c041c0c00406070017183d008076241131450710b806192000c500700c541805003109010000074801c5040804100e104451403200000d0320640b1a124444040e209640848440c7c601380c0c1d2102c20304d41d04101712600204023008130361500d4544003440006100d1b0768500c200307102c2c0114502c1c2d2a540a20348035401060541c400395542d10380090014000c01040c0350320804501c500070b0701550400d848040c2003007140001c188001c90343c03d42c100796045400c4901d040b64410384c1004003040b96220030a003e502d040c0a04000e02c099441407404844006943d51204425450042046407140000862541060740350900107181e1003500c0040741d2070003064108030110b60610900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 666182194 1250 666180944 666181003
    0x41b0510020327010c1103100e011e1506180e071806090515030c1303031e03020a0807051303050304120c0803030c070b191107060e0609070b070302 65
    0xb0b01803803945400409107568a258803107911200900a00c1c00202910b0780d5500107200340d001080101e46c010100c42a143c0c100810500340d0f022511507403407070394441544414010302c014071030070040d4003688240000c41d0302d100d034417400074850311880c003c006500070a081644050080e8501521900e002c1d08001d02c1e00c0342d00608002920700c1849030f040c0020f040064800d100d0710841c07095800c024010340c101f03814500100d22607000a07000890b400e40800004110156000300c400080d44641c032182c460000f580317002c2e1a100885440b100034580100300500c4445d5000041c0340d4403030110305209440d45d2100078404a0390185410044c100d00c0b00203004910381ca49540c0c41345080e4407035800c12075600d440e8000b854036804244e441c807070340329000d0002200291401591b664032444600c1008001101000850152100c180150402d00d50003d101d4090000a00a001f20203a040d80181020305025040036135920051191119122000c2400300806100344484440c200c90162076180b0022800e00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 666183444 1250 666182194 666182197
    0x10e0630041218060e010905030715020d03060e040b150d1b0f0806060907110a0c0311030102130b0c01090b04050708060f0c0702040207021c06060f06020a0209041b05100203 76
    0x10180e90030030000e004a04154807a26003d4000c1598025200c81249442e10a491304814400300c41d040c0000f07001e001c00ca645080200700c006101e02071520150003010b200181c1400c0c10070480404145c1480014000303045220b0a81c0d42295020f004200c5544e144035144004901c1d2415807075003c410004000d013404820a082c0c0d40e1110341000d0350802550319600d0100041242c410041c240d084a00050701a00c0c03c80082c0344d003c0c0007400c050f140d02000c60962402c004206c50100c1c3c00519080b8180f007403080c41102d00d209104d041e4000c61614080ea421030090803810305c1051240c200020360a88265004c5d00415062584808000301070b0405142007526400240150341041c0708000029040c960480825805140c116201e03614010440d020f11010b03505c00d1100340d0700b00c1d032082c8106503204100c654400300e071070103aa0001681c50525684980d00a8254050302c04c66000d0440760740581d440c068803035041540400a040784d0a154001107a11060551055a10600110320a8100c43d0040b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 666184694 1250 666183444 666183451
    0x30e0613061d04140a060803120105100203071b061d011d040209030d02010506040e0601060f111e030a0f08070210240602030d0b01020a03050a080a1b020a0c14010e0630 74
    0x41046c0500c5490b698190b54a00600b00c6860199641000400c140d00788021003040a45003441030f00c0c030703040407600c0d03001030121903150b0303581c04400c41030042080a40c0b00d00d40e0034560030307004072144141218100082c03411042c0091007c1d4000000418280c56440d80e0456003030210103415a000000d103410701a0003040d040f41c6240c0114102107100d00c000d900810101e040e921161907951102c08004812980340340f4460f05201d452050402003425070142c8008403074030500d50f0303009580d41c0c41d1003600106100414107261f428003030034800b40301183d50085403400e1103d03115400000c1450040034425106030380050850343c400e401341f00200c0c40c281d02200a014020080d030040c850418440700490b43c1e02166203011703002800901103078227254030a00304680c224500707400120364080c00c01c0602004800d90148000503a100602a4003085041c122400080c00305048000f40d180c0c0303081c00038180a420a26041c03040c0d200003001002c42590100c00c402e0500202e00702d040c00b441c0203880341e1440381c094 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 666185944 1250 666184694 666184711
    0x1d030406030b040b0603070c030c0503030f0106180803041211060f03010501090b1c050723040f0b03090a030528210e0c01030b1c0f030e0613061d0414 66
    0x580491140d040c103000f1002400405481c0346d1940d82d946004a072022075806080b010809002242c0c0c021510130005540546e6221500090719403611034050060704c83d0174140d50350581c1c604410458000d0200c252821140d030020004419400b620303013a01f41403034405a440d0320480211301c1550301d414160180d07059410a80315901d14607107030b050b942e00034000c48401e001541d818421000480f0915042590000c0084c200817141203030004a21115032004440030880610116040182c14202d0404400030030011024500d542480b0b4070407078440e40708180190030f2040014820340c0e00510920400c1c02c220080f542800d0313a240c180401081d6640d80002031861319941000006141d03030f03e100e504407403503020001b4102160030b0340055002d49013355456a1207000d8040100c1c0c82c020880d01c4509140c0700e482034004e100d5a500d00a40069541800280620000c1c404071240c06c4104012509540c044e0802d0151030040c0c0042600b4004a401c0036608241081501012101180e401c01d0094009 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 666187050 1106 666185944 666185951
    0xf0e0604090f060e100510060207030f0f05030d020d110f12060f0a06020f0607020a0b040f11101d09100b0d090b090d09080303011206050702011d03040603 68
    0x4c120440d0503603045860b040a01ea50385101e035a0b881a6800c03d440b050505000f0029078540351800010400c0c00301d00780d0341c4107101c20030b2800ca000301e6212040301d83e9240766546210294020110022805040810140001102c4000e1b100c0030072500b80d01504204880b0102c0303500d168080c00054025558030b04078001078a5152a01c0060140c076002041c80c6940c10504d81d01d4404010711a8045400c100d41c0400020088103580780c1150b040152003100d8103541c1040c105040078003030440d41c40414500300044042e001100002114203281d1101a000000030900280701c4045814091542d0701c1c4209010201003c03001c0c00c0e459420f41d4002078880c006644060010030155003540342a4007400881c40240c5d4854440c44c09425800055400c551500a19015292000b08010102034840703002441c003d10075449800b44071600e0010f04081103800b40d045032650b02500400780040d04 = true := by decide +kernel

theorem cover : BRFrame.Cov 666007194 666187050 := by
  have h0 := BRFrame.cov_init 666007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 666007194 ≤ n) (h2 : n < 666187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
