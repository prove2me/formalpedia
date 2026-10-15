-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4554
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:59:46.24403+00:00
-- url     : https://prove2.me/submissions/cf710d55-f80f-4434-81cb-6ffdead16edc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 818884892 ≤ n < 819064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 818886142 1250 818884892 818884931
    0x3020c1c0303061d0f0705120a020c011407050d0c12061d1e060d0317160905040203010315092d03090b090d1b081b0a0b03010e0a0c0c0b1009 62
    0x80c0b03401c404c61030740e074408a5a08540001c05c2e031800c1200c00c002c41200c010150510324080c4480c858016140c0c107440c0d40312400c4030440c10f180c000080c40d49040091556104048511400e460840407520b00000d980a0324801c03401d046c0c004801d428400082954601503441207001450901181700c1510740b5140401100c4a860b014441080a03100142d51828800391150105202e850003110801b0024459900c040007554114603020528020b00c030810b5000750902d010b4001207a0031450b551542c3c1c0d070700c52029140c0104a1007180c44e000c049087c000340e544411019220300700b104c11204000400d0480c44030a0030000c401152480e8004544807030202d0030790381c0d18040035010908039407954035103c0080b008034080d006100c819820114400009008a11041c0c00c0c54006a4031110030307004000103443e4a4101c4007443c102071004012020407542110342014900e0000608100504021202e0b84a00702018107044910b03030a121446c1c1c0c030220580c0895441401c10001d24000d640e0000e03401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 818887392 1250 818886142 818886179
    0x1090c1502010b061e3016050f03060409080f04180f060b1806040b040807140d0c030b04050a08030c0c01062103031e050403020f19020a03080703020c1c030306 70
    0x21443c44a0290a0785d1024000e2a44d8280071458845034043c540c0502030512180ea0194a81c503000b0062184841c2c40030814441d041981c00c0c0603042a1080c2e68001003804010007107441a40c982c0000310a001c0d1f4007040307d44c884100168150f5440c1c480081240c00d60103442070403015403070855000e103101514170891050388e024110b49840c0080d0f90508008100350100380552000d0100000282c0800e8a4000c000420381100681401032905014442140e50356100600952071940c0c098000740d241c1e107052064a0b0300002086180e112418030034a01601d000004155540020a100d9803a00910107045070f5400740009205881c3c0b100c0b20320701002d511006c240c440200c1a8440c800081c001d8018120080369070603c40c11320001d000c11030056400654040c1c1c0940c208030940b800404041c00070020414019045451218030340d804250b072181c0c50700c0050b265170008107410003050320a2004046440000b04840b600b00d40c611072001000a00301c90450100740f0300080090006810013628007807 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 818888642 1250 818887392 818887417
    0x1e131a040b09031c0203060f040618060504062103030b060d0516020d142101030605040c0b0a14030711010501030b0915090d050703050708041d01050315061201090c1502010b06 77
    0x1c4e80031000014041e40014102036032002c4c010440c0c5141c0c4d282c51154100500880f03001d041141f10b09440d0704100c5402d50080d230b0059061600c14485e29191700c3e100300b024140383e01c1c914804100740c1400c8006003d1030401507030149000a085864041c03580100d8026035603603004c0d5000d4000e41c94141e1391000d0001200001c103000410f5880b8004281010b0074400c8210044c404407040c2039031103070800710300980007215541e5444d4140402d100e952190307100a0000c1c60005417a02c0364810f13010b00340104026010105a40000010b65102d10448544002c0d001c110020702031940c4900e402c1d07800000032908440103101e440c1821190b4003250b001c0d54020f804150240c4903061401c1c1c011100e55000365000d4062240411801d0300280300307000100028001450704c0c8d251008100b02100e0103020607408941301e68000310000c843d1f1030b02c80d9160794200004450405038541c1c80c142c200d0241100e1000942280c1c01d061002036904103840510400214682c02086420442000c1000d40e0103030b02603e111 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 818889892 1250 818888642 818888677
    0x901021201060c0b010611070306110307080112151508100c020c0a03020a0b2a07030c06030506090a09051911210703060e010f02030108160b031e131a040b0903 70
    0xc03560042c0052147d0b28074501c20340d54200d49940381d6105440040c07071064010100042044403e5600c05800381c09070100160360002045c154440032080890802e080c460556038101024500390400000030040c8003075810341e1000d02ca4000030500406036030f8201005401500424004c518040280c038003940d9009041040e10303800c0c8403910b41e003600074401e03440c90310f281d002c01007580c81c00c00c04240c90303a01078080041c902d007410361030101803407103480e4000003d01d0700742000c0c0003895440b04056030703010076001000907000500d070801e0f52400c05a2103130400001a1141d203078083c81602f109031030030164159030b8906c07411140d6541d081c1110310b02c19112684c0d00070b44d50a000040f160f8022000c4420440300108044150201050807a40207a02075240d951181d9144034060229202c0200101a43c0714842d056181002c000302505240c5d0121044800c01003000414464225246400c41ca070861304103900031180186450000f842968240e441d03841402c00103045000000413a0304034036904171901d8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 818891142 1250 818889892 818889899
    0xe0f3303151303080a0e0102040f032609060c1f021210050d0803151503061011121612081909020f010e01030b0d0303020d240303260901021201060c0b01 67
    0x102c0d130280240a005a454444042940842003400507101400380012413045191552811342d42400e910a950111407a040041260002005055515048081d40e4059603a00051161810500150000404141820303841c0081c01856805020b841040d29141134450f1184800700305515480e204450344003920341c100000060746007003d5071700305942144010040700e8000004841090001248028075004400c002040c03819800341c0d008207065007030070502020940442074580c41d0705031f685181d44000043c05c61418030b614041031070307081e00b05900c102582c50284000701000e0065a004c0386885821050344102d441e01d03c2004081a802400c0d0500200b645005440132400400e841d418150b441c2c40701d95041d00d451100400700e910a550050750340800c1c0c854102112110b0304422281802c03030400044d429544011181034079010b09200d00141d954902003050450021610a050001301c410311441d0001500a4850641c40c02402c1c81282c0e200c0900300c8422016202c09040352200300c0042 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 818892392 1250 818891142 818891147
    0xf0e07030807121205040809010305061207051210110d0b01110d080c19200f030d05090c0616050714010e0409170a0504140303040e0f3303151303 64
    0x1074003034075004c3c00d000b1240070f400441d10b002c850301158141c4068000054500480da814410075602290880b0341204040401d1b80b02a9143c15034012036005001180c0c002c0503011040242c00020282010b05206034942035600301c0c030320b400421050300702c1804c0c1104810b513980101d40c80c400c1081004020500030320010700403108098081d01210301c3c150b04125202c800d01400b600800d03042e1041d290401c1c001c9040c41750f00d599107606200350046030000300741c011011402000300d4404c04405140070400d43c40e0044800c0c2403100e00b03400180d10040009070001440300d2020324424003405070080e60741c3c41c0e0761441c0c03d04143d1905210940001d0301c00b05801e10038035080c4e000c203110b14005c00e0285800d070b40c000001c0e51142d0242e0310013008590046001c02034200440900110740c80d041d00a107007828906656402ea001c0082d180c040100340c3c8400099242c08103100704c6c1266408132159000d0110b01c403c140d24240440701c500c50190280040400b135820588428600407107000c484e1160905450302e04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 818893642 1250 818892392 818892413
    0x615090305060f1906090c080109021305010503060f0307060f090f120213200d0b03030702061204110d03170a092d0b09030901200a03110a14010f0e07030807 69
    0x41904041c1c0d1310140040100c0e41e4414203018140c9944001203907000f10341c01a040a9050f842400458010055a0a00700c40842e84804556007800c185843e500c90300b00060940d010250190381510071144006001c43d4480c0000b01d808580c1d032070307418809440c0d82d80d1868600207801014030300030902c4e1042e001801d01d43d0744c0000314410000c000407040f01c0e00c0c1102101a2981e200c0c0309441c02c011a41500074000307446035210a900032401986844440d90125411b03000c1d24240c8840035128100013000e001c1040d08283c0403e80041c004021041d040c90090b00320300780b980303021408000c050700217a00320615114031026180c103c42600000c1904607034501e940b07000b40c44400c40402100700342c54000350340c1450013070046000d14051904c50450000040032110701c1081c00c55241014810b04183d19000703e030b800750080d00751500c0807407009020700311480c04060240060500741c105c02c030120045410f607c040035002c1400400d10103034580c1402d51749d07114020300014103010010000a400110212131 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 818894892 1250 818893642 818893651
    0x170103080a021e010204050a0806041101054e100308030907090905030d150e0402130b060309010b030d021f0b0109080a050f151306111c0615090305060f 67
    0x115402207512000d80051101440c0f41e19085a401160a00441c6004990301000c4c1411030014481480c1c16100c0300d9107003184407191414041e0004680038400002c1200d52000080b407410460903032058000700cbc504c18004229044408032001c6030503038411049800a0161000c0014082d55609584400390698000781070446940f0803002c00184c4105c4500486a51b41c0c02040a1a100e0034441d000000341d82e1103118138030341c6240014041c000e00a00d07401854115406652100403140c481d44004000c2244a01c2e4a07444100841042000d10054001d030107030140540984251002001d82640c0c0c44c282130300440f203100c116008071940305c003040d8030002e05c170303601494000c5483d81d030303080658202085001d05a683c3d8005040034600c1800c1002140300780300d048000040c03545070101990350f2041c41d00a0042030140c8031a500e030200384c102c10940d0809500005040c408208856078580100000d206519600710303040e080307483c8240a9581c4504594004001d0086995802900155001c0081 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 818896142 1250 818894892 818894897
    0x4110301060518040b010803032a0403020915041d03070201030207053c06060d1104110d0b180c1207110d0f0e04060b160206220e07170103080a 63
    0xc1c00250550b00c00703081540080b83e1640703500c2542030900b05142041c0d4144c01140603030b4810800e000c03c4090300ca0400b0b8990306170a403200140c4028140b50008c038400d685c4040d41c01064401070010340c0d450b801605140d1002100d08002210700c10103180e244801e80c980006c45600248585003355029400400700c8902c6101500c40d410004942c0013064108851040300d02c030300d03240300400440d41d001c8107501c0011040000b400180740c00c500117113020820321001014040c501954861540711500404019403c5880090711204007105000c010415110790074800c20744400202c07035130b01e20780c6101400381152020361490010000001020000080e14a00401001c1001d229807254180080d81c0d01010583d201918043c0d04840246070480205102d03210340d140c800c0401240403410308a82c1c07440c044809200c0c080c6101e00010f401070045040b1144003000303100b0000c403075a9419000031f00f568030b00703108401e907a202d0100c1103610b000300098405400c58600700603c04290504040c01c3c41140d00d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 818897392 1250 818896142 818896151
    0x5060c03070c08011e050c030601050f09040504150f0227030a0b0c0909090f0a060510080703080403170705030418111204020310090b190b0d050303010906050402030f04110301 77
    0x1d03911078a0b500075990041c0001e0350f49000200e0032003020440741c407850740030103424012424081d10300e02c081d10002d8840c3e814008001051354400403030304140c5842d07400051080005180c503041401c03030010710307002040c020f5162206000781900d0520075079010000d820040c2d188a2080b0300000a503038901d610f8154103200d901400c8001603110400d20b8414940c0c0802c007034450b8500014058900c001504003860350b00002d9181e6400300740000e07c5a4242d801c86000704283e1960300c4c5806e04400a600415443e000344907010080c0200000204202c80c03207001c00101c010079100c0040311501076400000c0803a0000c0204201e40d144c10700080403450352620000902c0811680c034101e8079840b000d0610710008040341004290f01c0c0910002c640d0008003641805601c00c0303542e5101c00c0110040540c009507940441c528050861a400801c811501921000e4036000908000340c0e607070424460314100d14107150b4017143c0b80c00c1c540203681c0900d1541c900311016460310381c3c5203440150746040e860b42541d40c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 818898642 1250 818897392 818897407
    0x3010c032904141009050c0403020d030e0f06220e16050a0306260609012f090406061e05071a1513060618080705010f090315020c0c01020606010905060c03 68
    0x500e411180128044c40210400601d00004103041d900e0081c103c0e03c0304d4109020410158441c500301172181c65140c0741410002752414006a00005400c04564110a0100d80b8010410000042f1108900901d00c3d00c80e1195031040311040481c001c41d105034290140c6812540d80341d0184025218098050401044180d02c403043c1d2000c084103441e400c2108401444129000001400510381050641c4c00074031106210610507012207514980c65008040c5910304059100e020406880c0820801841070000941c2d640b002005080c11121084090213150886022140200200d4502c160301025001d100c1c0400d8042d13114009005007800c9400100282c03d04a47d5907801191192034001c54000555604040c40100b40c2552004c4400c207005c1009014041400d0008210040f20424607013070f92003001d8001e045480840c141d20040281c01c050107140000d4441d034011708885002c840845219540580c0120782d511019150f080c041101d008044c4034608010008040c692144011a850248e8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 818899892 1250 818898642 818898671
    0x140304050603190c0f0509130b03030a05070b0907081005190e030c010c1706270702150f07090b090102010e0a05160503032b0608010c0e03010c032904 66
    0x100b10b5180c010005000c000c040c030090180316099490b40303180342c901c800002104000e441b62194011640c4252a6101d51803d9140142c002c005094006000d0765280c0c1007440010300a0b81001c0b004071801005e850002d804403800143d0001201c01c4400240007c04412900200604004d880c480f105005514064000f0745079002d85c0c1111010708004556685080c944982100c60444503a020400340a21390381c048801c121145d0381118049540c00008240c1314510081c0801100c011102105490300b0041c00366008035510702070705a03501030011280d41e44081a11561011207103c00820641c1d50240102140c14001e844c8400060000080416083c00180d1510030000c50071039569000a1a81085002d9070f10040c00809050300150700709060100c1c1c40f0305011288a00c801002c0702c11508200c0070380650840e000a0401034001c106096107040000d00c156031410590707000c0d41c20705c0b818180030392003031180310704c80e400c800b0100e42c1e4a042203000c040f0005d1940d000d2540203840d02205025041c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 818901142 1250 818899892 818899897
    0x9060f0b0712030522050a0309091109041802091f0902090306040b07021e061006030e070b0a030603060c03020c0d0207140f13140703060807140d1b061121071403040506 74
    0x11b0080c2c00400c804c403030300d03c1c00404204054004524450514820495444414080d0751194404072008a04002242863310960704059001381d4405092801d009042107202c080513030f80350700b0b0031026584685449000c4142e205000c00c258055204600050100c1c0d001ca0758240c22141a01c19218040c499010040c0518580380c4e1080c6a0f40240741808540100c810450009207040d0030107006850105c0c1c1803e88a10081c4079041c06080300003a40e0785010320950100028643c800700c2000059200380700140207400000002581e0b00c80c007143c1c0c0406500000b40035046a03041d90a40030610f1410b0b00317109981160010303083d00710480c0b052041a0000a0040c1d11a52411061004040c5040c4000030b041d40c040b40c2c403a21050f0011103040c4648200210414401c0c0000c2d01d0165003284117240c10103241c1d283d04040046242e10380d0004c940c3c2d0b075101141b01081400c0608031850800d80c41c2264114405401c2c4200c4201800c0010100059824964004076201041903904080e603400c0410b0701507 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 818902392 1250 818901142 818901211
    0x33e01020a020910060e0312042706060305040b07082202010c080a080907090204030804090c05090409050303100b0f04061404090c020c040c031803030b0a050a09060f0b07120305 78
    0x8031031a12042c4401c507800300704600200350860007840e4688400c10005424441d5004410018000000580740381e80e1182b42c2c680102e045507020008140e481c3c50090041c5016501160900c5150000c500d8442c4520841c5025040e0000030480301454803944c070302c0c400c5d07201000301e0600c4040f00a4502051a51004d030406032000d84903102c3d070b441d08600940c01e044081d004a400588140301c02d00200d00d040090318180c510314000061304004d84002581c1038015216aa0351003410292486c2c20400c0c0400a10300030307004070500805403038a0741086842401005003a038101d0005020400c000c52183c1070007005494406481d900c0c29032140b00801c15078200720700036005a40407100c02c060b641840d205250702c40b1240d1404020602c1000d4440b100c03a1482400034003055203500c0d051565036038092640006107402010011480e40d40c282c000c0140c4854424030428040c000000a948e4840030112941e00e6405070760440d00741d00320036040d4020440680a003e50340340000702e0503100c0e20200d0440185c1c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 818903642 1250 818902392 818902411
    0xa08030f010801051e041707050a05010c0f0905010c080a0c05030f03340e0402040b1305101103030109090501021303150501080c030d050d1113033e01020a0209 70
    0x10360406400600750f6801501d54910038245e50700d5824241c0c0d041002c56007240d440394a2213a03501c422500c0a800d40205007000e0301074020401d10400700441540b240700b08102d01d40fa12086403d61001c162160500f40c400d5a020440300380000e40080e142d10003d02e000c3d20380d42490f03808021651a41880e42d00007145044940c5400810300224000103043d4003940b501c1c1920140f00742400410105000f0010344004041c08071405010f000c59589406030b401403e845402d0984a02402c0b0089050f55076511840d07000d04144090844080e00c0b41c044400100300b0a002180345900e004000401403100080c140c81c255070a01410582101050041004600980103000f03442e10103a50001101e0040e80261800d610482a0040a03140440c0050010042e0f051068445203688000c1c005040302009140c1c81c00800034600490390f028450907410b60b030080c00265415113400d10807101d69081c4240d0f0f01d1184190340c85007400c00f1058a481c0d0038424042c0305488481d0344035030208041c000b05580540c807 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 818904892 1250 818903642 818903671
    0xf0a061209081c1104030f150e06090c0108010e090c06030901090b0f062d010f172502010c0815031f0209030c1e100903120f0f0f090b03090a0803 64
    0x14007480038014111243c00c24144c152070940380d561345052000c08548006c1c07a5107010071145442800c640d0103500304000b60012ba070030741c2c58101030041e01e0b2000c40100c5404944070000110716428000c85031441094110000e0000301340510401081350802080110b0a43d00d45140000146114500e0740c0101020a1008550309116007006030b030980ea950300704ac0000000a1110000c1d408070404518003500382414005a15004070440d980803041540703650f0703100354006003c00c03003585143c2c8c40a4102005444260b900d03088808909070344e190380d1040f000030082d1010031900d10303103103a4411540d48014100c900440f001a51040e82650944451100650218111050b424180006105184102d9418807900b0800f044070005007101c3c50520301450011251400e01805540c40b030f0051a0006130122201d2031403500100404c10700c0e040440002c01c000e11182c000d038043d51065607045180d403a405046410900c241c001c0da000140078051034451111080e010401c56002140181c542000d03091 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 818906142 1250 818904892 818904937
    0x1812110907021506060307090b130815100b030c1b0a11010c0308010b25050a1a0c0909040303020f0c0304081504031209240f05060f0a06120908 63
    0x240964000c21040c155084031060311900107400c40c0107603004c82c040b00c802da1203031221142100c0c00032450b0402c66030340300c0000381d10070705100c11409041280c0d0f03c9001c6071042c0c843d49000701c0000d2f4090b1602200c0c0300302c1410601440d07600d0700c059070317012a0007150300d03041070150242c1c0c0b40141c0003100004001e03040f22807840103108c400c40002c48120801c0c2410740100640707641c020f007040e10520411200d01c80115444168060441c0142d00c9114040e078045545080d6061280c2c031459542021520281000300f60505142074900840c40380c6a2800454207107038213801442240d0000030421000c1543c00c0051803101d69282c0041d04c07298003c42d004540740d600f811681c625040c070580046010b100b01c0f00421000030f6000e04001c01081a00401141810369481c2c80b12031141201000841211051522801d130010303070b03014001d00243d080303041c411500d03814103000810b07000e40d01d81600044131348020310529001e84450502d55105586c0000c980e05a91145c0c00c103608020340305448084c2d0801e008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 818907392 1250 818906142 818906149
    0x90a0c090f0b0904050901060302040e150f010e07030f0f0e0703021801050913060b15030a140402030615120d03020a0906110a030c151b1d0a06181211 66
    0x500c0989072059a5405050074007100410900945444a1007641c840000886640080d0131400080d940a0420b214041503102e416403901d418061100c501c074110000100c0100420480c41d041314940f4001810946400900310007074017110005a44040d00c0b4200983d81c9606841045240111040900101b90a41c41003105048503541c0c503000c08510800180200d0b954078004641010b1000800d4203054154a441b40c050304210078903e42c0629840c10110110000d100118452003041000300094440c1802c4109400d400b03440c0039401d5801500015202000890042400080184042d980200c0750b003149213131240e403c480c500080d1300030954441c00ca800240801c094181d45c200143c04011120449950b6a840e440140800840c28152030034031200c1c00300b10340400c030410010f020134926506c7c00100b40d40b00007401130004007511446205041c40c3c402640b04c0d884000e0808004a10344401141c1465400c0005d1451150241000407058a65552071104900c1a014040f0094024040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 818908642 1250 818907392 818907407
    0x181109030d120c020c0319050709020408010207060b0301090f030509040f0612051911010c1a1003050616140d1103040b01091a01051902070506070f1211060a0515090a0c 74
    0x10541d8811450801780e40e07004214920704070b10345a50840750b0700490410030b1074200d0503030119820620001d000700b4070b10019001851158000c4409014010b02501810f00300c0304c100d00050000e100000425000a00c60320050448070300007000811510180e403001402c0b1342c500c3c0d1003200e1014545005400304001440050406000d605c0707404c0c1c441100d0f490f8070f482c20744c1c040c201c00c1c1003240e03c4100200b04071202c0801d900103408000c10076503a10340b025003600102440e000903942e41c030800d0002105000c903680c100c1003041043d96550014105003080d00515003000d0446070603991500c802c0164a00d00782c0180d03105500600c03643d00e065240c0041c510403201d01c0300e0700c4000c02454402480069030402c0454001905070740c5080058038507200201e00380300241d04416800400018990180300c17591000c8500d5602650928607803420015050300c036440d2014004419410000010342100f010340e0109a22000703013102c140030000c04000040c003441d03080b1a89100c4507500d200b41c2604c6a4030810 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 818909892 1250 818908642 818908661
    0xf041e08030a17070215040f050601140105041205010e24090105071409011e1706030c030712050111030115110a020927120306090a0204181109030d12 66
    0x14502c0c142141100828968400014038600101e50012609092003001381a9030152015803088043c2418130b0203446001c40000242c40a210701d01c004510000c1c40b007128146808145c46092515180ca8045003c00b02d0700201620749543c0c81c40e8088902e0024040c0403031100c0340d40c0c0302c1c001e0042400004c42c00b654025160041d0b41c0e240204011210713070400510380c17107003618490a070384980c0c1800048449800d403440c4020380c4d148400c00c2c4910300f9000300c4d861041c8880c50310699165910b00081c96a55a11619110752643c080401044600242c0c0f520f080c9141c0120000300f1100866001d100d03403a8400e034031080c00c0818841000109550008e503400b0203200d01c101510a12140e500003408141000d004e4002e600298107000f810351003480c43c510500e40110040c5c981140d1020326000003900210381c02402800108000b0764100e15038402c88003510740025401e0070b00c0b40354484400042500c1d0701d401100c1c01d01009003098a41e8108001c8207060810b40d2140000c003010760f03c01c802c1d50354000303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 818911142 1250 818909892 818909909
    0xc0102030615161716080d060503060c1603120603050c1827030409090614090601030c1e03060e0721020d02043801090614030f0402060f041e 62
    0x810341c841c0e2003c086508260010040c0f81042ea291000b400188a20100d003c504070780c166041040154200180095072001c0b40200040c503507402c10b1644901c802c5070ba04558000070800700102c0c015803403804c20168040e10b450083c900c41d42c5803210031108140c101340c0d91684902e001420505c3d11031030300d050351085032800b08924204005102041c006150dd5000705524414007500d5a517000c205403801411103101c18840008981800c50081c051000d40390400748083c5c000034803404000860074100c1703612500200b881464201d51418050f80000d0124650134980c03000000310754076008206481c01c00ca405006400c0c07030b150403c0c044c50601c030f08900041c50151058070150b980c1e40458014950140d03004103400c80c5440300303004410b40d0302d0401e100d5110540030083d00624030140300c84020500ba00c4206a0710b84580003aa0427074890390010300c48071800c00000d0302c0034000360382d010781040c4054400350503c400350071440220b0b009031308207407072403500d1414180313420200c4030b00e41004100b480e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 818912392 1250 818911142 818911147
    0x40f05071509151b0f03020c0d1a07020105010602150a11030711011508070621150608060906100c0212070801020d0b0a06050f0a0e0a0323010501061d0112020c0102030615 75
    0x1c4800c5199001e50f004c060041490728a107982410300903c10081c0183e801003d5500c2c220591501c89003444505002e000c8a400e8540041c181d036005100b005d060303403c0d540007081c884030340001c0d40c01c44003002010b43c0c420715100c0d0244901042080060360282290f0b80b50340142e81003c0c0d80780d42c2182c0c555840c01c0c0e0380e0b00c84c1da4410403406d400424140c01303030780d102d1410301d880400c100703811401540180020040286007541310318032801c806411006803511680c601034070b0f4079080c1c10060510003d440700d544c491081c900d1248401d01501d03500108078030140c0300f101000c603205401402c24140c0e500c5442242d400003020b00030b2900034031420003882e008440c0420001c1c14500014200c0c000d1102e80001c1c10000160441c0c003d0183c40244018070b0001e0400a0b25512880c104003920722036020002404005000807482c01d006000b48d905036081130fa2060b0030840207504003908600312500203410f11a40c440400d03400e049030b0004007401c0030181300142e90f030704101d0240620f00981e901c01c2e018a1006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 818913642 1250 818912392 818912417
    0x606040b090711010b130b01121e0b21161215020309122d030415110906040e01030c0b070c05090a180606181103040f0507150915 57
    0x354290300760000014580a6080040c0d000054014080070300461b50010302c0c103520021100540c0c11501c0c4046080c1d0b549556085004ca808054910161005007012602c1580c45d0072250fa55000c4c0340012801040b074030248205842d445e07560700002070700031680c2d00180c0d03800e80001848080d020061810007a080030110198450440710442c8205d2412403d40000200e035981c2420010b00c200d150301900e1080e9070300b0308252801070203c64040c06060100c2801403182d113000c0341d801a28820781d007105c268a0b41c0c0045039461030040182c4415034003104170034001014245c032000c000c0c1c80900080800e800313095040d4202004001c6e000d44c80011880010402100010114070f022412a00c065031b442d80f454584402090142c49410b42501e052484d0740d0941c0d0900810f90410380444807124000b948104c02c1d200301105440b64a18210403410040000c1800141d9440b00c00303c40d0340c010006d840096488284440c40c41044169100000c8c4c001c1200740f100c502c100f4031a800f070426504154542018 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 818914892 1250 818913642 818913649
    0x9121218030206150a0f151404291e0442020c0402070b0a060b3105040905031804020a09030f06060b030901021e03130b19090f050606040b 61
    0x10028865501c040313003c00d40c0c16444e142d0405d0310f000f602a95450214564039030030540c0e4010000a11800011008160304c0180c003c00c0c02101c05980c0c02215020151b002c840081b000e256107040e02c1600f1070740c10040045014007050300c0d903210500341030440703644500c1c02d41c0c0f001b1445c164440500d0420444240148400c01ca1540c1c2d04164050b281c4d240000b81d0048002ea040c405000006600030740001202c00402c0240c811903442140211810000b01d40ca0300702843c1140550084407142a500b800041c8603500d10301d506004858400c1c40c50703c2d809440320042425182823060803102c0b5480410307107035006d07220f0f00070342c14122105580071410058500c1d80240155000d00c000b8144040c0090b03800c00b44091034100101506003a2023460fa6410301d10207080c000c0d40610050300c00074040000c41d04c01c0c2d50000701241d0107280424215000c2e1859600c40207080c0d40d01500f00d42c400b4440c24041c0e0f101180c01e000d100c050300c2c003601c1882c503200312908140c4d0500c02c004083c144140c1c0781c03013a11a00303a134 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 818916142 1250 818914892 818914903
    0x80a05100c0e09040303060815222006070204141e0c030406020d020d0c1d06040b0f2b05010302130c1403150409050f1e03090112091212180302 63
    0x380440e5000c0f071544460906400409003600264054091841c05c200125900142907006000f1174944488101548040524082000034024a216001d01d00c1700b51004410720200f10440c030080825180c040c05d980010125007504000811f026200401c00004850048100c61144020340d42000c01c0d140184141e1980d2100510040020382d001c01c220340300c040107030b06440240058202c10011001c80746800b8041d10799040203505604805981074440e420b000040c2c034201d46010800794103000c0d00158402843c0c216074601c0400401c00c0b5000305c900000b1500c00d62410b03940000001b0a0350440c014444183c100409503038001c1d0925680100d01944064407151031896071007a00d40f25110980102c41200c01d4110301383c0d120381408581c105101001c0b42c020b11034141031003294403070038000c1c0010000b0303402142e0180458106029040443d4014500b810741d1196100001070b000d04140c1e5002d4100001c04043d0000420256200d20907004a1040c100031031a04240464124400c3d6402507a44 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 818917392 1250 818916142 818916167
    0x609121906201e070218160c0206070b04021c0602041a0a02030a080c090604091a030c030604080309070308030f0403090503071518050603090d08011d0604051906080a05100c 76
    0x8240c0c01d60310000504420603151360301e41c024030071070340a481101410014101518019032268054000215a50044200c140f1095002d80928180000ea880d003050403003004100303a030000503c00c608088949684800080e05118490068496040000c1080032504c07001c9015070000c010882a48015000001e4940b03440e21854144203650721195070b51101c5c05048040d41d04200041000300d8500303040d8000c84801000340c0c40d900122a40101010b035110140c40f18182c058201074041f5001c950000011648003041c1401c50390b81c1e5690b582e0340442030707108482014000c0d078540284402c00d50b1249040d0f00a0004130000c04240381000005003d00d0508a03604041c0020000040000c1002c0b0903808001c0030001c049607142e180c9803c03807075120507000940a001800c08000854401d100412450f5000d0404584441c0d55a80009100080c01c1c090200043c441d94141c0500242c00c0d01d006a0001e4110500a0040c0880d0f42c0303412440c140c41100c14006e00ca007454811a40a07500c022940001c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 818918642 1250 818917392 818917417
    0x201315080a0b01090f06260c121e040f15060602030306040b120d03150905070f050a031b0905030708030f091908070e040c080a11060912190620 63
    0x4081010060b104144e0303c0d84035a40c1e0000d0030400003121a00928812101c80c00c40701e8540c03c1180c0202c0c20311059034201c92404a51300140000b80c80310301c41540180c0e10103482510318500400001c003840713170f101c000c4808403000344400038801d017040444094010f0315882e6250038800c0a041c61406502c03408000c1801c0d000d607030368189118242c0d50304d5041c001c99813806070545003140e440c16030050203070031034180e5000000c0c14458001200c0f8464803c451103a40c15a03105080201950006c0380d80f03a001401c0ca008058903507540c140c00303222450b01500345001c03940304d00051614001c28103081c10340b150700a103026001400366500103c0f1120441d0b4452408458003078000591565a1184140d150803450040c803e0000118042100c410401c1c00b450090300707410107030f44d621199166070380481c50000f84440000b072103680c010305280018003c1082e000707010b950b08610354080c05240c42100c00c2074048010700d008200040c402d15114102200544c144101e581003e1443d80e4a5035204507100c0942 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 818919892 1250 818918642 818918651
    0x3090303030b010c08070b0601030b0d1101050d0e030a0801091508060103021507050d030221160e0a0504090501050406050711072d330c06020706201315080a 69
    0x20703c0e845204c108080325880030b800c5440355071a0402ca20041310890352a07000c24a00704040c0a180341c2a108c2c810301d16408105162030780000401107489400c800c525940c015110b40184603040b1050016012800c1c69a072000610344c5020040c01c169400c6112030f0340d0116080c5002d1169010120780541500d406030396440e05440c507461180c0303443c40ac010b000b41c2715000b0301d0b071256486540358000b0804a20b1030a52918400d0f82c03800140162041070705c2884500e21328841070003215019809012030100c008012120455a40021030162180c0510844150b55160100000c106148c0718050304064036192100c000c80d050f5803d20346d80c0055010724501c98000043e00c10f90482c1b80d0152500c3c0104400801800598a5034400c1c880d000d40002e488854061880c0d0090010b030840a220914450b42d031800088855a101c44000b03510020342603d600740c03207241d507542101c030b144401840c5420b028000c60345c0c2d03250100070790f20000c1c440e044415603846188621380710344e500101a6411030b100b21800079 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 818921142 1250 818919892 818919911
    0x118150e030307050304060917060c030112050c0405070e120303040b22242412050a020a0e0f01080f1f14040804062307030e01021501030501021b0a0309030303 70
    0xd01c2c5001c0d5460041540c070000801162071035000c0c140004450901121840480440114503141d88003180d02d0b1100d450280010058941d00030100700381140234100f91500c00201da00400c0c180c482c120340c1103020504e2040c01d1603150601401074507500480001850850926070350300c403500b82002c4c01c0000151401101c1810079400f42140c01c104d80c0d440000d07010001c0d02014502030104510003018071280c90411241c00c8000c40200c9a00c0780441058240500c40c240f004082c10307002100020b5a0a2045035600340068803441500c8001d4818100d10203c1c91402d04083d02c9100b20503042044241c0000a42036074005001034150411140c40050256000c42c0103a84401011100a4030035803006990521007804035541c0184142c1e1750b96655840160629414560384c16403502490340c1c0d10000b00100000b2a01c40d01940616034014815078124110000001c0b614079403c1e0002e035020796000441e02e65044404044078a1515980c1c0902003404040e18040d009001c588030140925840340c1260 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 818922392 1250 818921142 818921149
    0x42105030a21020c2a10050d060902040f050406060f050f16060912021e030702190803071103010f2a0203040815040b060604150509040b0a0806060118150e 68
    0x44140e40e0300c1c2803045490b8050480102c0e035515450040f8581c1c0c440b0080c440340428400c2201c03420740000a04596000481c040e1b046816500122011402d907940302004100c04505000500080c40b40300340c84c0c1380036401d10042208545065000303100707010320b01070b001c2203542e00107050311289041c154881e07854001c910300100b02b100c079500c001090f06203000071741c0d010031860084220b060720a640c21604c0300c0c060101c1c04181652080030070b10a03070b07100313100342401480d220750700e4000105142000407025a42e542280c0c55a00045802c0318000c03034410001c0043e040074810440b12048110003800740b40c1025410142d80c44040c0c100f0b1000c0e590b49102d210003079008000b150010b01030b05086a407107951050030f11402010030358003125031f0340c20140070681600c8d0800c01d607410350301c4030001280009807101c0251403e5120840c0c03607401a032a8415034500d5962401001d005140090180c50300340790100004040150024648102d00703078041050000e0300c0801d40c00c0643d00c46a0801106401c58113002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 818923642 1250 818922392 818922437
    0x816050702041b032313080d0b03072c01050603010501050d0b060d0204080712050d0f0c0b040c0305061f0512030715060e0a1802010305070c0501090602042105030a 72
    0x12008801410074543d0803966040c2e00c030b100c50318842926524448141d8518401548050b2010740d000c50400c103258001c10f800c1401020700c004850000540c0c06110408242003035120b520200e071503103009100c51708040b10840310405c005070642c0e0241c150340c1004c00042080c04103001f00c40c1005004603541c0c10550a42d403000c5004a402840a902e83c803191502101030b51260203008003074000c030440003400580c510b919040481d8850080d1031042140d40d021a0000364200d451420000c000580c03101213101040264021401070460340161400c6003403540c07911002402c1051500d4001e40070240503c8203010240546508943c2c40b5001640090b1007495800340210180400c04180c0001102c211035510200850f80150f54001b902d640d1702c0344600c102c40f04c115a00403502c25191464006600c00c0d40240da00458508040444ac003440c3c580c9421100c00a5041b902c03240d00240034800c00c009403d2813040c2c000d21102801c3d2600b0155102d07034403401945010b00a209010021449000c0346014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 818924892 1250 818923642 818923661
    0x2061315091b090606030501081e1f050a060e15150903011a0a0501080f0f070c14340e09010912030609060b07050a0308180a0609050c01081605070204 66
    0x8030340d00000329076020281202e554400c3e80388071803a0600003c0c3c0b583c000c6c081c00b03040740d558070081c185030b01180d12500c3d1000c03a0142000f0941c000c0e0241031455050140424600780001000042c652401140b518100c9444d50002c0044098003401c02c017480c0c140b1016400611f400b039810003000203504d85c1103011806204e810036410b50810a05d45113000c2400d05130350b01a1800c80307010f400260394000566a08100b85c6200303030200030b0340e0700040c1e21808407000c080d00a20f6607c2d18528078051601c9142c0c0b04c0014140000c0c0341c1e002003201d0254148424514a904a01403140d0f0307200207001542005100000c0c42a01ea11305a02000140780744d1003980000d420355002004d114440c481c1000c001e000b400d035070040c180100e19003200407460104003010307603d81e550702900170020b0203401e40f020f40d0701120003000060324007005625803000203021b02450407070900c00e103001f145c0c1317046c185003441c1031115041c4524100403d01e402c010341161107d45427480300c2c107107040050340e070801ca00209020b000101c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 818926142 1250 818924892 818924903
    0x631113c01180608090607170106260c070203060117030a080604091b0e0703060f0608091e011505030604030e09070c0209010b09031c020d030f0212010f05030d0206131509 75
    0x1e000180030740c0c100c0b50140c410705c42c9200b40c07441684da848040d51500803241000203003810400041c0010350044403000300b174610b41c80e0544076400481e0540365002da07084402c641c0120000c0760b404218101000510f0242000319401d45010703028903035065032400303080c41810404c1842400308a6a0300d42d0740c0407015131608a500d02c8007500d540710b108035200b10b0601c0f5010340322920900080b00342c0d00ca4420360701a030b40c0303c03620b80c5540c3d49413100840c0c86800140014103c1e02a182400401c09202002c0081c403408a000108100c503800c0140001140e4580c0464000d0b08001d04001c00694855800e0001e60030031906401d09888101040320345442c01c1d10000d40000c41d07000042500c2d51024058542003504034125003100e0b8980d05800303465000400a03e015910104031114a41c0c02900030038201030729507200506100c0040c180e02c0d5401000c6c0e0000f080b07901401da0501850a051081042c0c02c0002d00050106040035034002d00d2240c5020f01c0075105080040661100a07015000380d146550001c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 818927392 1250 818926142 818926187
    0x1030b0a0306023006030c010305070318150b010801180e030f0a0e040b0f1305060d0f0c06020607050310030204090212011a09060d050631113c01 64
    0x4c10313030100c14818503c1c1d03116880d004510011040506020380c91150b4800f0f4007411002d10000c005401424018000c0020305481d416081c00d13a0508a030301e01c0b0414003c8560f540301c400c198040004640d8110341140c1045040001840038580805900d544202a40710000d450a1501d045500b035004400040007420800500d5a005540c004807804061b070007280c1c1000038800c590104210408043e02480c0c000c15481c40c001c10300d001c0c981c04580d009801602d141c001016590740e2140d8080d4446080b280d010498030244000d9604210840d0300080c50700340301d85141450790700b1242101c082d201c000d210f00d4540d8050310442d143d0800e10440d801c0110005d1104105000c003800e102142007030389600a00f41340001031124130f8a42c85d19542190494082d090a803603106580b540c140103208080d00c290340403e4900d0b1030b5030105d818015160300450a203409004003404008c403001c4c103c1c01111601110390100e5078011030300001290110020040000c0b0900020010b80b0b101403402c1030000000000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 818928642 1250 818927392 818927407
    0x30c0a090339030209150103150915080c0312160602120901050601051602010e150a0503150609151303060203070f0e0303030f071b0804301101030b0a030602 69
    0xa4003000842c00241c505100c15a103481e921200d505241440040d6028840e1004115000c884a250a041400c10f1502040c840380011602000f010598072007074400d5515044d0442103e601c0e020407010340140406040d108248a00082d600ca030310b03001002c0701340d9001440d1410034621740c0d0301d5100380303900020564590b00d180b20030300b00b21401241c04130415400d10b0002407856209404544080da066000d02c054001075400442d50390800000f410340054110038005444480080a0710704008181d46180d0359103400c00d0311404001102020381e00440080c0401c1ea85541d4040d04100340034070500810b529400b0075140d02207509080d500141c400c03440081840503180e44405504bd000d0b21503191420b44000c1c00301415038a110031252031000554440216a01d903100d10800c904808228034600404081921215a07a0340300e644122482c07600200501c1007508510f0004031070740f003503174140d455035076054403411460f10114038004d04240e59800345605a41d10803041c0d0000c0d50f0032100c115200c100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 818929892 1250 818928642 818928683
    0x1080a060e0c220303121d03071b080c0a18090f0537120c050303070305060a060f092706031b0b0315131d0604030906050c03030c0a0903 60
    0x107816040307028000c107484a0020100c111881c2c013103a505540748031000c030000c45404010005404078a004146851511031240010806845102d00030202d0541505001c1c1d808001d40c01103500180c5070360003100f107800040c3e9030141c810b8115050052101c103100a87c004141c018860718000a02e80c40c11a2300c0d850620400061003586402c003001d04078428420780703450170140304915100a01201150700c5840000324007890510f005000c0c0c0c2001594650282d41c0d050550b0012148140029603a104200301807509a084c4e400170301b0360781403040c543e101d21940101a40d0050107181c428424400100780c8240091002030940e60b501c0c60104481912450402c2142903480360050518031204400304024140030304981c0100900030500740400300719404d0103621100d1032090030660369665211a590600008100e0350f64480b100545960300d0300f4a0068140c1c4515007081c000c000b070502c01c004052200004994200004c0d0502ca038031003050141c01c840d1003a00d5040146031a1285c143c0030350000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 818931142 1250 818929892 818929897
    0x50723031c061202030304030f050109080708090f01080c090f0310021b010c051303150b1005030a0f020313111929030f15190b1c090305030601080a060e0c 68
    0x100d6440240b20080d901c0c0440c420781251600043e6043e0401c000400000e116005000340c132920074000803901500c1a1240c81d16a0840781003aa8211800902800306d450003035200c90b00800242402c810741c9c14500045d1629008903071176980100310070a46111240d80030481400300d200c94940540d610155010300030b070300080c0060b40d10015800c281040030128068016903916411032000070748403915544469000c010300880800f07a817070b607541114449031513100780381d020354290b51509666410200c4400c012112003c5c1d0143c0014070610502150348001c1c914504900d8214454141c0c03943c2600000e4480e103000782002c800c96031101d0f000101c1803202280040a22013001900c0c40050014030801c0715480221108141940008005481d6034003050515041d590040e08044102501100704500031441d034125502942000c1502c42030107107024a0340c60480e0b8492400c1c0052034159074082e0407800060541c9060000c0c1e07600041e44071549520090040c030100c40c0f100340301c0c102149800040d032b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 818932392 1250 818931142 818931187
    0x1d0d020a0201021e0303072d0503040b130503190509060d0b0909060405030901030e0309030d020618030c0d030c110d0512010e0f06010e0d0606030c1502070605072303 73
    0x500030124a00101c0d506500040028000307034011754030b1641d42c1e4004842164210b0301007080c1100010041c18840025081200c45001586070190b9900341400c010182803001040507a051001e94195400154040152013110030394038040044540d06c91001d131032501821100300d403c0040407940f16100042500310f10794509003034031600c0c820307210500da464650380120b43c054003690040261076000c0d40310b603000d58411040001501e042802d070200003801c24065520240050f8050030074400700003100c200e0103c188043c1c1c07004516002002c005203841e1888a14200281551070864804160040d181101d0410312170013a0342a0380040c80003d8165000100400466000240042103400e1551052030080b01000002d00c0301e5590f85004460240401c2c14a941000d507200082c00061124000ca501070341c030810121007d242460103034038100d41154034400840d0f0112074104090f58010080719a0281c010304003402b0044004130200e0701680b034640c0110644000605000055070681034241c09 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 818933642 1250 818932392 818932397
    0x9031c060509091605012109060b042306090c3f060d0b06150423010507021e030307080309060f070809120c0f0304060c03020609160302041d0d020a0201 67
    0x150312100c41c2c80d5910500301d001a100a48100030500240d8015064101040e6034002010340302d0203060303045004e4501075507080780d0282d10b075044000186014060106004031440c5421040c050cc01c0030104107007406000c0d54050500e8001181d45c10843c00101c41d64201c0f84910319a9129500902c4414410400c83c005040c80d100300305440312a8142d43c080d0300441c8024121601542c1e030340c886601c4c440b070142809901082c00110b151180c001240503100a003074000800c900003403518600d240c00c81d40d80c07000d01d040140030012040180c0c0ca00c19801c101e625251a51035042500c00e010038130354822410081c141000100400c1815640010b2562150200c407602101c2070311010f000782d0b100c0b40e0580d4070603529040807694001665000020340301113040c0748111840401600704075402c66109420820015004c0d0441c01c00341a010000d8981000c854002802c050300112007800341100c00d400028400d03516004107800c0d032284008243c1242c1c80000c1914030003500494041d540b4210721500720301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 818934892 1250 818933642 818933659
    0xd1b0206060105283f020a02120703020106050303030109020703180f1e1a040518060d0f030210061721090603041b080106031a15010809031c0605 64
    0xa80d54815020b4a503a0069410480d0030b400d1088012a0a0b00855203090304110080a180d000188140401182c100400d444105101403466481c00440c05d21246200001e0040007170071403940d40000c800c0c0c400300daa08031381a00c3d01450300c0c0480c0940100c0c0d00c1690305100105c000301341c01d406980184100c601c2070b1904458080010346030800f21b92507104285015580394401c001070411b11000351902c450521041c003120341c41315150185025000c102282001c000304081c041400c22a5481c03407900c00d0629000380341d24142000410141442d00b00400c180c000c1a0044201802002503109904030000c00303020305900c8501110b03942180c0c0303130002d0840c0306500c1c07028040f03542805d0041c82e042000c40c410f0300c2c001c101418042e065001910446680c2403c80c01c00301d0301d44003440040080c181081c0041056413550800e1a119407a0100890413000a582800580e080f5044d01c001d64803002e00b002c1d40d865495036007040c02d60090003291641080094a007101020320b030b83c400320568030116510f14 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 818936142 1250 818934892 818934901
    0x9030d06060c030206010308032a03010533160605070206060f060406050f0c07050306010306140115020c010f1e03021b06010f030f020307150c03021e0318060d1b0206 73
    0x56442c2415000036015030030031001407001c100ca41d801544e0011100c0280d0545404a004600042841400040300c2c10000320043c04145814520f0120a803214002002110403202c02054058503420252543c1c45000039403031000305030030f2819041943c000100704410b180500b0040d455500441c0d02504c40d03500a0000c90403450702c80d09030b0f000d070b615540e64181003494508090305140d205403010000d51141c0240040c10f0380d8100140b60103144140c80100f5a400040104010620181c100c1c000300c840102212480d00d41c0002c1070000810246010004079004903001d89814441500b890640f00e241f804410231680c0580041c1081040412500811010102010744078803007801441000d40804000300302050000c0c00024440d0300040c1070f500b040d55036181496148038429000c3d00490403210f100390506406020300f005400c1039241d002ca030302e0415603919031240300e0b444680c0c1c07040030344411104564552105890070003203001010800506520040820405131100c14030042c4155000603 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 818937392 1250 818936142 818936147
    0x90207030e0a120b100b0a14040503010905150a0c1205130c0807030b0109060620100203040c21050c040c09030c030c08100e07120201032405010215160c1a09030d0606 73
    0x80080301c09025080d400d00c980d1100c2101c10403c0348c2481100c00c501404003098030340d0284294801d180c0300c0c0000309441d4098004410340014002c110b1082c9d1880c0c41c2540c9800f64201c98010862451607000245035a6130340128840c040192102605c034a442c2e18010816450006680059a0040f088850700740ea9980302181540c0708c501075440082c0c11141c1030140d95440c603031042d0764203003880241d450200880c00e5500480c0c10440e01502c5500ca80d540800c00744c11458846100c01c0c80055003000b500b1035940fa00e59881700c440c204180500c2e9100c0b4144110b41c40303208850041e691000c000d0003181c0e52802c020a50b80c5003070191012074084c11143d0746d18203005100b5a00c4045e00c02024003801883e00c0b00c3c0001c400300c60001a41456224600c10030305950032018000307109408805002c41c1400c000c0020706d0308100301c00060548245070184144400001107520b200000382c07078140a80a81c1d46410020300402c0880381c94801c004805000320b50714003101601c1d400200c03c00402c070003135441408 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 818938642 1250 818937392 818937421
    0x6021203100506030c040816031716140c090103320606040f020c0d0c17071a0601030612030c03020d050702010f0827070f09060f090207030e0a120b 65
    0x101d440d80e80030260410841c10041c000c0c543c031043d07140c03c0c1800e0540e10121a0308004020380c10254030307501c0080034010428480030340301000406031000741c213203140580b44040381c0710715100c0540700c0d8070003100300384088000b0045110800d80c050318100c06544d480c900307600003882941f0600d890805003481c808a800c02503902500c90503295009000513119002840010844105485003030b035020000c501e0410410001c141040d0099950005080fa41d400c14510710754007034400846c1c9003420070070380001c540c00e052042003129280c407807041c264483c480141c0040031f0070303070113824050020900707607003030682091501c1c086600a4082d1030a8a40c01c0702c013140c06209042c8024003041500740070911080c894841d80754030a4003500e048250900011543c07944200d6a110750f10141c3c401c11007031060000c1404441d009041040050001c18180b90301c0074104802d43c000c400c4196804110802414443c003e00c0c00c2404000c0d00050303410b612109904580344c029441914869080000b14a098410640 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 818939892 1250 818938642 818938651
    0xa0216090209010f08061c0f05060a0b030a02040f0b10121406060307050a0903050f0a06060f084303030e092707080313150c020604050d03052206021203 67
    0x161100c02c10144e89055400701c0018020715008038003650f50860340382000c4141c0c643e4078016028500c000c2520324143e4031b821001008010041c1c00c054001b1401c0d20005140303804c01c2d904503008541c402d1441c680c0d10040c4030b010041d590128007611050460360300700102052013a1140001d02c8800c4141c1c050088240094640541101007080040c9000e8031810190581004a2030300305078060303503038607071601d4900c14959402c400d41000ca05041000840d2040c400101306811102580303529042005071542200445160129010b42d010012142c6c0c140c01c183ca441012036008441640031192035044c0d44075400100d02081070030328a8032180c502161503900c0386582080c51f082d10900c0b505140c0400400f1285000d00748125500464103090600c040c0c14680b000102c4180d50901d071015454010030305040003410701c8400340c203100150b00e90404035000e841c030a07034a040307c840340d501d0300701c410744118601840d0342a44506866040c145041e041d608a50066003140e07000141c05550390014441541c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 818941142 1250 818939892 818939897
    0x30b01090828020607140c030c04051303030905031209030a11061306020c070506030a090501060501170a02090105041502010507090f0503061815010608010509070302030c1b030f0a021609020901 85
    0x40891004a420b6000700b4910744068090f0342844410756a1240760000f4810b519607641007444a807107036050400c80300340b40c07100464051000d410620b440703031a1445001d00140c1050384a0b42c282062240030022154034080f861904034062600101d607548a42002d0300000c00920780388041404058000b136158060890340d9a503003110381c07803652444001c0d40581e198201c140100c99000030795a4a0b40007a51041200100129903800c482c078120b421620306410442c188180212140848000201851b83c4110020f90050343c0c1c5205000503078045c080c6070b00c50703034022401008440c0c0342c4c0c1e81900f00d2805480c0ea40c4034840450b8031000e00c00c00c000309902400e500765000000159040000e2081542c081c1c0c0c41d0800da601c1e0a04604501400404c00d030012004518008010041800c20400b440d03071200d6140f03070440c00d6040101e01250603208581585c1d10102c64494503141c015030601c00c5513070380d04251804a80d103840000300039444110a4183d02200c4501e03d8000410b41a5802161024241613 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 818942392 1250 818941142 818941183
    0xf0601020d2102070606090e0102070f0f050c0a03060c0806060915030a14090f10091a1803040f24020c01050d0204120b04050f07030c060e03030705010606030b010908 73
    0x100890303900780e040d54906002040b801d8000c200c00345920083c84450700512000c070710181010401c1041e1400a0700e03209150f84100403010102e10030b0000100034948c410594600d03a030160404914064004d0761460340a181c08100104003c0e03241d11001c09140280c41310405540c8035000c1022900456030544d070006208500c0300c8e007014103031005650114035104006918a580305c95000c002d10102e649900640c4032507454030f0101410800b008a000024806100440c0c0540d2510105000d05c01702c0702da10b60100005c141c400b82280403071040f1400d040201ea448640e83c1c990001802058828800c81740c0030a13600c401e24807100904078902c0151070f00100388001900004682562080b0100c0c00d00c183d0078880800d0856807540901d22550050002c1c100381d00703107810018208001e582e00604150f2100328200002410350340c1d070b041100c41c1420301500c0c4005042c0840d08522461000034502e519019020a003d41c0507848100305403000e03031704c804016860302c072100d590319107517802c101d5400400b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 818943642 1250 818942392 818942413
    0xa020c060a0e0d09180f0f0204090c0801080c0a03080703020f0f010c0e0102060903071b0312030b01031107020906281e0b0403081207050c0334030c020d05030c0616080f060102 77
    0x41c0d00711b003020f80e5003508001000210041c1e080200d0b005904181d04a9440e01800d104090f0300c6001140504240806007080754600c03c000381505d0321b14070000b0000321002ca00081418000c2c04100f00003048030b01078401d4001c1d0400d84500800e6948000c0d004110f40d142e1055155100180043c0710303828240c000c6281c09803903185e0000d030344818050030030020382480c004030000303044484088020905480c0880d242c2d86e04400502a2071105010180544040c00b8000c09a9100792409401c07030340544002030b10040b548081910803011660003030140400c008001034514803161292031901c1301001903003503a51100420f130090f126134807000c0e2428030107104014100e01c0b0300e100c03980c00c407517503080240c6040d0010802c4d60546e0462045100c0d2208010701d442c90041d800c01e00070494244406002c078040e9520391f0068074403141e081c0064080c1c5001c1d0021000c0140c204100c0d10950491002c607034561621010340211442c81d11004000220800041070700c3d200416000b501401c4160042e2a98411 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 818944892 1250 818943642 818943689
    0x504061d0a0f0f0f020310023604050703110711040c0c05101a2106061002100f060306020309033613150f03020a050a050105120a020c060a0e0d09 64
    0x9900c40e0a03078a136031000500750010380d010800c41500e60a00c01001d40c450f64a0110306440f03000901010000d208020302030180f0141d601d1803d400142c080305c0006003912042011030041201048188400c5000980403040c044a401d02001c00c1c80c089130148490f2103802d600321068480c0e03610007081a4048422400c8000007500b240c4400003405644e45040144000002e200c0c44c0b4100c0b0f44d19448034142000c6520600a02015600ca00705903282d1841c0041100e00959641c0849541710130a50707035650035041c50b00c01c0e0300a4801150004019034030384c00c0c4440b0680c3c0702c0d4400480ca03602643c41c01c21200501485841189280c007400000e050714401ca1404d008800b1119509501502e50b1405000010400710305280041d0850310482c010702c50071441030000560303460b00540d1292003010820429607a00108807505100801104a26511400b80d600080c0c0518205a60280a50000c10040d107205510802c120066042210818600c00c0001c1c3c507a940740d8001c41440c0204400352104007072 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 818946142 1250 818944892 818944913
    0x51314010b04050d150f0212090123070e150c0c100e031c0315080705010f0201140114030f0601061805040209090411030304080105100503070816050d060e010504061d0a0f 75
    0x2004c548003003900106d50070907504076030104088440034151507003031005900b8240310710700c2c80036000114565801e0791444450700e82640140000704000e80200711101e00d4885941d140500c5801c0e840180e151500d21810a46595040c02100c0c0184001c084548180388107080d004a16440500580700e03000c10091300354a6800b1122845060640302d4000e41d00050380e00f05034000401e8074001070000319040000041042ca40d2101541c216030424020310807150034040000c0c11100480c10340c80c4000d4801000ca400d0203400d0800b035481e80030380f03000001e107240c012034080205042c02d000d0b030f010141c0361003c02c401c900581c0c401d00d802500326000580050300d40c40c0403d40d04030000307045908041d90754a1250a58200b1a00f1504800c1445810005800c080080101800e140000f4100c2600d40d900c64010b00d098030f1040e148a0102c01440390f0a0106580c440c0d2440e011040007132151b49000d00344030020f00300710349069980d0707207000461484030000410880c200030351020107a0340c004042c0c3c94540204 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 818947392 1250 818946142 818946173
    0x5041202010306030807050a02040c2d02120703030b0301150b120406060f0b190206070c08070c0312021c050c10020714010903170f06060f03040c051314010b04050d 72
    0x143d942c0070080007140380300001d010751a100310000c160640c410b1050105540b60355200000b8000d9442c04542042108014225400e424031448006004084c108a14000007079140014a482c002189401c0c568540c00444a10700700380d000f030085032200c4401007191402403003030b007030503a81c00d000ca984081c0400d582580c1140c010003000c51051386402c001c03496584294855881c500c00007400c04211000c124482d401c0841500107802c403031804d600b0242c00e40049040080800900184080c10001c01002900c042c58020000d16540401d040c0c010755211290000040f110185038551070320b55104600b03c411141c0340001400300c3c075008001e40700181d0411001100e803080034000d025500c003800d2280d03e032034038020f81c0c54608600800442801400020305040f084542c2c040402034036848000440322803001c8560807950782d0b0b0322810400366410071504156840b14200412080c80112604100c0700c181070000e18a80c9a6a204944604c80c0302c1d0b4400c1c160005000c02954001c1608440147c101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 818948642 1250 818947392 818947397
    0x3080a110706050702030714100f0c0501020a09080631061806090b0f04030f08040807050d050d1109240d06030b0a0506040b01021b0a0b030f1f060504120201 69
    0x11500024495081c5a00780c0c009000250000c0384140c10345c5401c20021b80100040821519203103c444003080302e20000e6103510307041c400010041d40143d0300c55074801e21419008402107450720301c11500106201075074420b18075188140c0300451401400c1d4682038008000906a4103204080070300140f500b00c400b01825140709565405200022004600e001171403441690001240713070481c64041100340c1d010b82100c030ba03004035400304800203800200f00c400c0f00130749040a0302c880da158a021001d074410884020454000d5510519800e43c10a001d060f2044101e0b400344502d8034020181500c502505080903803040003100c0001c0d401103820001d410103a0401801c520344448016071105a03901c96100321901801c190800c9501c104511230643c011034115010b00c145851080005e540e40031198011608013419100710049645142c0d40100500b040c142864982c45d0030140c1c4c20b100c9004031450030310200d864002d4103100e0982e03030800c402d44806890751810507040c40b54a8000d0a036a0700e00b02e06 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 818949892 1250 818948642 818948657
    0xd020d080c04120506180d0e010e040902031903122c15090d0201140105060d050a15080c0901050109080303011701060e13170a0c0b06150f03040c0503031303080a 71
    0x51021843e149040c0c0036000300000c00090030800d42111103070603611020903254100c1c056840e0540c1c0d00003c0ca4005560074603209584042e141c0001d40205030010b0000d51510850b075a00388661400011040740500070380b150101c60b83d03460145025075240f052488a007400000350441042885251420030111a40840e0100f29079112440c0c020b01c03090f82c000400303078404682c1c4203c2a0742401203940d01613000100c08a1549040c3c04114140114450419078585071000544600e140343d00c26035004205030205a100d61340e400945480742411000b090003110003100100f41c65006010b80d104589240b802180307141e10b000d40c0c12070441c00724030246400b552200000100c40301180d03000c500411134070a145030040881c0c506000c840194440b45099000240168003107540c02c420048545c036000f00c020180d0380c0c2c0308400110500301c0c0400342160a200031858200101d60a4041c2d4031440c411110500d01c0b645501c101941c0380110302d0f04100b0a00610400d200180c104000b5124803803e90a2010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 818951142 1250 818949892 818949899
    0xc0f0a27050f090c190501051606060b09090a0b0d0b07030f0c1710240e04020d020c1504020303030c1b0a260c12130b27030d020d080c04 60
    0x190340e010b4030b11400b4450b542d03040c4042910240040c03100d100c411501c0c140341200d4031560540720422031140f94140080480d03000705a014813040c000c04e1315480346042082c1d0751540d05502081d0401c2a042d809a0108000078503005294070940766401c40c0100f80c1503030b412803565a1680820b00070300801c02c25031034003404440c01d40a4007444c103001440d40c85055814002d541c0039284141c00910717a01a44143c0d1800b04072000004408943e040c1010004403400e40d500070701903540503800107410703400c00e10020f0b072104603944980c00381000c004c02505680c080040002c400c2c0500c1c2082d100030b0747c190410030100341d01e1034104008001038014202a0054000c81d034451320300b07040100e00700313444407201d82100041707800c045107503291640800d0301814109040c1c00301069030750502c0003a401d059100001c0b05411b55200000200042c00300070081d40d501c1b001602c0200c642e141a030f039007110010078807080748050324000c651080000a581e005106d40089880212100c400190203000d24510800c0040b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 818952392 1250 818951142 818951219
    0x115140d020406030c030b0d110414131101021c080a1107032a0c05060a0504081b01230702150c0f033a1e0e010506030c0f0a 55
    0x18410364010a20058441e803a1480143c10703241d03080c2c42c1000b0545007030b031001c40c595a1550030580140d0000510341d11240b0840128000700512203414048901600802010159607060180d03200e2007039030300841e4402820f0040e65100540c41c14085c1d18520f000c0f0074100e880c4154603540d88a018508042104461011b0352905540004002d4001603910b1004070096000440300f4251034516160840c100501070b01c2d480c451804a0140070720602d40040c07000d030254414000e443c080d16030340702a9000103175226000f060895503540c26a01003220302150304803034032a003074540c000c280c824074070301c0d26091282d070030000115036065111030404801e00c88000d0000080010000c101c400b140159561010304d03d4480900c1581c03401f80c0c00e403200990204414144202296002c0d01c6005000300d44494000926803c00c07941c042d521803030074a800000899040c05401040c000d100540c1500c00002081003413180e03504196046507040b034024081048540700001c10310102030324107581c5401c0403418007002e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 818953642 1250 818952392 818952397
    0xb0f070204091b0807051e0a030b01080618060c03180703081611040b03030a08130203030a03330512010b040203010902070b160906030c0e030703050607090506090306011514 76
    0x140d49000c031080f0340c040c103c110400e084016000e5440206001443c1000190103481c1c440c50054120b1140c82005103282c440003004806103510900d070460303540c0c458030003d9030388500b1920405a110030361034001c180709000c03520301d0042d4024100702c0d00e960f9454440084164810a005440b40f068013000008254400080c209030715021200b24108001401d1001001e070008400a200d02d02c0d00f040d11415660000488030307000114184150603696400f0500422401d07114065018000000ca8081c05c41d0305501006031034071506020115000c00f822854030300072904120b60688203914200740302c6813030041c461407400c900d0070b40089890f0400c85c2c0440c041ea0421780c40100c840da004554041040000c4801326271040d46552005400b5a04500091192845100d201c052603514002ca05206104114886481401908565030b9555a1034240d03170315070045840c0700020b60b6482c8082040e1501c40211000003100070b004040caa424041c851580302c01c0851810140107108011241c40c81c0401b02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 818954892 1250 818953642 818953661
    0x1b062d09150415151a04121e05070605030f01120b010e1f140a0501051e0a050d0c0e042708090a1a0a03060e0c070b0712240605040303090b0f070204 65
    0x40c8410202d20346281c5041203c2d1000081c00c006005100610012107c602e41d9045c1641100070058829100b04095a41d01e00341e03880a0300d24014042d0100e8480e81100003107008040203003074440381d41c0c1d03156030b040030279a01c81d5001020944040c0c0100411002d00b03600580095501d2480c003454800c0b80c40348840b1078403aa20440004641701c0d1940c10625168074401c004281c20309115182c00c0624204180901d001c0002c841100300119000c00014402d80c19142c1a1480000801c400300704c0440290000f18804031043c440d0b8106144a40b07026801c601b203101c018080e5405081d840180e9441030f129401000b139040e00148444c1002504144000000e4400b0b1001000d203959683c05c800700406450076a001011856110024400c00304001001c4503d4039410041c03200350b5440701013084031355183c03040c4802800317410842624032101940c0c4004030000c01008013004507d43e100d10030b80702d9008521001d0301140302e0000402c040e9003003030b000b4026104c07a102800e10b400d2282c0e000400700c80d1040d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 818956142 1250 818954892 818954921
    0x70201180b040b09060c16031209110f03011e0e1203010f03060513030e010c03030b090c0408010501051801031209030503040e09010c21021b062d09150415 68
    0x5210510040d0460f40b40c01071a407401501042c0741010410f1424850b040c544100d41c1007411400d01410302c40c043c2e00c500717801400c1062000030300c24100b64182c21800740380c0501c600252154601245014461a07142a1810b003200070705035503002070a4000c0c0340d201e24552150040c1089442d49440c0751000f14003800c160441c66220a0440c1000c400302d90307004286241c2c03480c2046e80703900800d4000202c03800b001424a0f0002c0c60142d1341c03074100c01070515280382d01c0d00700543c0341c140184000c0300806003060300c400000030016a82d0303410801405209403030b40c030a1441040740c01400442e005815207081a8101d090107848150b030390366030b540f440d03026a2020907a0402d02c1e0a21203000000c0c0070321052142c0d5890104107441c0e0314140241c030b10240380b41440105a0029405c0c1020082036001824503007040162034892800107596a40b060321140d1040c0f6200010700522081d0381800755141c001c41c9468014202084a4681240c000d18050015500342e2100d500310490300381c072400f07100f60b602240c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 818957392 1250 818956142 818956163
    0x1203040210170a02070f1202061815010510200c0112090213090f0b1608011e1503230a150308030105041107151b05121512060a0c17010602100507020118 67
    0x14a000c600b903003451480e54a141c01102c1c00031100030402f618603040d40e204888078051003000c0442911004602c1042c0c0b5400540d10004c0441c001e80801c1e050f442c044280c0340c1e045946014070342402142c0d01d89000179440301d450002841141020392000b5801032188420b5410015140c0342c00c22100c0c41203a1142c0c2a0360075100c08100213030b00c202001c0c010100c507a011641c00119080320000c130400d5000344d0841d9001e11010701002e034480c0c0c009900b02c4c4980c5617207040240940003c6000040700311001440f107810418482c0b2220046944103007240d4100030103038156400c200c2004050700e02c40361001000201070055502096020358142c02d028100d99000480252034441240c02403260f459001c1400024060108481c3e100e01c2030759400010540c0c00d034105884036000039032070044514400700610417070341000b070302c2c0c14644e000848800a81d01d51070780104041a9905050724240218401030700010380c0c0016080702c83e00000d070030000d240001300300c00318034914410074501c4015042da5102040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 818958642 1250 818957392 818957401
    0x1207060908041a22080604060525230a020715050d02120601090e060d02010315080105040507240c0809040b040f0209040e06010e0121051203040210170a02070f120206 73
    0x4004d4680c00c15031458074030026103140000481e124100100060070700c81e100d20006041c0c0a113081141c0303140d041107401140742100c42c5001440c0c250034800c1d43d040640c20b074158020088041c000d0762204c2d1303620350041a0050130858541c3c24520600070b030030f00340082070003450b2040c4c400c4d001810003241518000c1d02c19141003000102640c407070742d01c070700c6028200000303021540d21501d141491450b02800c0120310440200c072801910030f095801403009502c1d01d0140410441c0119029044488840b81411580300441c08040812410075601e8041040c2800740e00000c0c0710f44001c0e06002c0d82c02040012103840700d1001c40d0659000112410110f40c0c00071b210a0310f890284203030410840c903440100300c5503042602d40c076900780301800b40460a807042110074180c45458044c030508a58480705441c1d24085040461107a500141c400b2403041000011301500d940c4605403122007203600621a003007544a460310140254441101918140c2d04021843c000c41c03080300c070b000c059240d1940241500d160 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 818959892 1250 818958642 818958667
    0xc0303010b18010801062f0d020606120d020604060b030c0a0f06140405060a140d020a090609060809070b21040530070206130909050c01020601081207060908041a 71
    0x40d960b8854140010b00006200e125800000c580102850426094001100c140c01d43e54241c42c00c1440400c034410741410040e02503011414030b0181d9001c0d00c412142030f480701201c40d1100c808001c140d005a201000207030102e88541c0040c420130074040c050f900c0500b50b41c4041210310b0341c1c5400c180180c01e00719404111603a071003100d0000003c03101c071085003814200000070700e1034403444580d41c0c1000700402154000081080032101b041c42400310465458824140c041c0c130800d9507204140109802c2100054040d00a0311464404c800c0c00c3c000c0e0540d103040160701d000d280c209501c051906290040080400080301100c603004e18050401024400c0600c5000450f00840010b40146030341c4640400c01040700c64410358a0b0340e40c2c121801d50711070552600440c540c52169218540140c2442480020702202140740c02c0061001c0e800d641c281d03a203d030082641d80c027080d025910483c50801c488000b00b1255404405603a00c20b40d1500d01e01607036100c4040003011000b506482c00c24002030120381042 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 818961142 1250 818959892 818959927
    0x4060312081b0403050705090402061b070323152a031503030a05070b1f0909030e030f07031e0b07051810080601230c0309030c180403050706020c0303010b 68
    0xc0c6002020b9103024150350300e1a03100c40079803103141e00900c07a000102c0c04558564041d240f140076240307000301200700404041c940d1040d07a4030042c0c40d00a1f00180c2c48140c54007070540028001404401011101074400503d142c00300028019042d440e07030003000410050032030300030044903001c003000e840d160705240d080c0c11070007043d201d4924032a40c01046114140c0d5040741c165003015407c8654010780340e44081200d500e02035000600c07019041800000704480000e58400f280c00c0303010b40d4540c18079100500c01d155580c01c007107000c0f4000b0340c0100d0b020400200100c074202c2008610000003507010f03030142c1e5a001c02d10429035540001c80e201240340210750341e10300340031a0416030849108820b480c0c642c0d4040d044c0b010160402d41002102c688140c100c0308806604000d03541c240f540540d5410765000601e403240c0000020a21a0144000e01c02d41c1d1710700412a610f40d045c040345600745030f444980e01640e441c1d0100d50101d0301c1e60340900c480095400140051070082151089040d910f82c40540809c800030b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 818962392 1250 818961142 818961181
    0x106090c05090a21081b1501030515060306060f06120708011a1206090a020c060c1312020603010501030506012003040e0a020a09090c030902030106090e01140c0a05090406031208 78
    0x4000b08095513000340106074600d10707284c00885060341c50a40301c0c540c40e54910000051032041c0700300c0030710004a400030400b29049901600584101300c20808071a9180d40703054031030f2a0b00d80c2c01180490301d540340030101c1c6000c03508000c14040c50b100000c4d10410600c43c2c12180040811340314001000380403a0741e0141c0200301082d04815207030680c2e801d2481000c242c0602210302903928200040c28142640d411102c1c842400c00880341c0074034007440600700c141d01944411040c2c0720074a03400a07e41c0d410011b0202255401413409046a003041d0044008000051100d81007004010781d0b14003020070121045403484100003d16a16130610980704c1348042d01a040845044c0b04105c10951294003c80d510140e842220011900c00d21007041100500518000030307501d540390400020f5041030541c000000560300d2802449005071100c0d07980c1240c001242e030840c03105000c04ca0b1810700381c407030300c010440d40a000b4000561a41c884d2548052503801e0140742020900c0d40c0d040c070901044044c0d503c03198 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 818963642 1250 818962392 818962409
    0x1170f04020f01050c0a03081b031f060e130203060607020607050d1724040e120316030605130209180708061f02100e1c1205060603040c030803090106090c05090a 71
    0x10101c0c0d1405e071950354211954081c04108816020408174105d502d106145942d0315061a40c40381803003809425450b07140f134210515201001c50020f04c250085000800c000c0004046991250441e180440a548014900c0750300071800c110000060b80d55801428186025100418120380e0a10001d46480c0314503502d429131040310000c1102c849484805600c030301d50401500b0b900e0302c0b15840401d02800d42022509254020300541c801100207a501440c070902d243c0300910307140c4154503816421a10301c0d005803900b01405a40c40c140c2d01c0a9a0001d000e0140b01034001c03e4050700c1c80c0c40e01e074443c4505898000000e2054024000c07985801180361420201581032100303040b010000c0a99180c1404680000c0b05407144503002012009001400503a0418219058050068000200404440040e07041500c0c0b4001c00f0074034a080ca4400c0c2c03442107520540b5016054110b485080e0140c000908841181d0b40b640c0d804100315046015104051a036904c0d503a0f01d603030000c0300b041208032991304207414 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 818964892 1250 818963642 818963647
    0x140106030203030a18092c1606031509090302031207110a082706030a090c0f06020309090708010506030402040e24011d090c0d02010903080f07060c020606031b01170f04020f0105 78
    0x105a5054901036001f0f08009402d400303d42c4c91200d0050a00840f80c01400c2c0c80b121034100001c4103034158000c0405200300d01e0240103090745801c13062048450444002e070040c0d209002059a02c64181d007003507046045400c200c0041d182d088103081c60440801022a49140041454030b510a0700415809500c0d03c4003241c3c241c580b01900100d41d150200400d0001e0894550384500c050100046900c1c000d04030645040a03100c0c0c0b02c01c8069900c7c4d10042d4400c1c01068050000b801c01485180c425050b40c1000f400075103140c8454003000090161840c255806000f08681158006183c12505419002c1d560301d1846542c07400c402c0304c500d02d80742599400c01da642101000b079040c9000c1751081014030100d5001c0c0c011003030b60004840303035003181c0c00041503100e00050914003818488050314a03a403040b001440348580112040381c0300c55051300d07103d82640c408001c0003a840140240d145040e1810f140100300701c00a40003028040320281d4a011560701248148815818a48801030052070b080c02d0691 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 818966142 1250 818964892 818964911
    0x50105030c13020f22050108090607020d080601050d151e0b07200a0816060f0206280903030b0901050103111c020f0c0f07050a0f03140106030203030a1809 68
    0x20400070800142c2d1503000e0b8001020b880580c1c441c1d041c0c03404000f00301000d1544001c8000b5144071001103004680c0031030b542d000062030824001508521901c8241e000d03009840d03c60340d065682d05005030590f81407003020700032080041168800d41400c441010503000c0580c1c43d11144108141d6124180296a9a1510140a02c2944404507044698448000110000000d40d0082001c03c043c030340c1c07513100c1c86020300068624000160101c0040d2071101c04501c10fa0f8030301050302c400591104d40070241e0803403000103805078602111001d03207980010580010920615071581214140b82c1c0c118040307940c88a1100003400d0018405016042c00e003000c010803065001c0b2422940075594810202c0a400c640411001805070107a80c11132003079001c0140c5901a01103060384600000403100060311074580300044514014100d03078120755148030021102810364580742d030b078048180100400da42d2078400010041e00c04000030403208070745a4604541c4090828030250300805580515000c60900783e641 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 818967392 1250 818966142 818966149
    0x9040e060f01060504081e0a0b2403060f04080a0909051801110406140a03091209080c031203130201021c110f06070e09060102010f05010b0406030c08040f0f020d0507140103050105030c 81
    0x180000c11f25030308240c0c4000898403240c1d18120a05000401c0d10030000305020041c50032001c114684142c0000060941800c40e042c181e42d030004941c0c2d580a0030303031640402c002c1002040209600308951410a140301e403030710111810354005139051141032400c0300050400340c50030310550103184142507586282510781a00146075a00c52403440c485000c0020b00140703900d000790b100f41c484a900014412500c2424040a230900c0f030517108401d154001c1c07141c100b5039482c000c1850002c40f8082c0200a00b1900d5610319002c0341d10216600328158414002004070f4640c4882d100224007040b540e40d24400f09c400102d8608003018000207403015800642032003619038011044224010003a106030078255207500040340941044010781c141d10f8170303120005c2035040e5050000d04c10389800e62000e11041c841800102c0d000c8104844c05007601b01e0503964080000c410358054040d1900051007541c00703401c6074071228140070b40d5901c25a11701d070700089400c0065815000d01d5005140440241a0440d20318010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 818968642 1250 818967392 818967403
    0xb040926030f04030807021c030b040e0f0a031107090f0b030d09030305030a0504080904020711011115160314100e0f0c071b0f14041406130e0309040e060f0106050408 73
    0x281130085005c0020036141c400c10100024052401c1c101c0030300c1c038180002a004100015220b0301807410034100c0d42c0c200e10002050042114550024148d8124035201150310034103e40d001a0240034a0700009503128140c099408403503070703000c40011100156000c06280c2400c2400220034071003003606c2003020a8001064940c401c00c00315011a855403181741000d400d202d41135403281e1040c40400c21b0000c1c825051000050f100302130321361301130b010400c6001603500c503030309144050742502c54000a2401c400002c20420001c800e41000316401b4045050720b2101401103449400022505c0401c000040240d203c150701f01030048181c22480c10004c4c4520554421024013920300280000c568800c0410404004001c0142a52512510b07446400c181d807180c1221000b01d2159043c140b101e06124280b1310094000c02004105060040c5d102c0b00100c0941011940748000d40824040c20384282c44601914400c0700000018010505e040f00101c103040c101a04180200301091000b40800e0800050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 818969892 1250 818968642 818968651
    0xd030f180b0a060e101802072109270207022b0620030601080411030706032306060a0c05010b041805192303130f08071703030601080a0b040926030f 65
    0x6503c801b0400c056500003900ca1040014054000000c03034824401c446445021020318569a209001c0d90ba0050301172400c0070f181e00021080345561104042007040c0d8001d1041d6440500401059010516804c001c02c8441102c180e240022030401030800c41c140c440c100403680c485110940c0c0f90100032b445080f40c08000c020b103040c420300310702142c18000c0801c0321411106c001001c4071041c41d00e484004001d04940c0b60002c1850240c00c1c820001c030240210241d1094030042d00c41400c10a00b03aa08a4102d07000010039240da55030340c0c42d02d2100c2c2c1c03076501409840071180007481220003503030700d00300385051441c8114800c0094034580000c00250102d40a00c03030225500141210181128400c90440c8606806802140c40c0c0720130002c0e002d00300c1c84009045178000030940c2c0a16980c0c0050090407a08018280c1c69034200300002006076000e0010300f40c128a400f8000100c4100c0c240100301214160784055444070120703801c0c1641d5030804202ca00d1001115000c103400c40c100803100103a90f680151 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 818971142 1250 818969892 818969909
    0x100c1b0b1b06091b04090506090d1b0203030a080c0c0d0c0210180504020a02100207060f05010b040e01030b0a02220e15030303240a06030b010216080d030f180b0a060e10 74
    0x200f000041d176507504076030070454200c01507440e2820411052503851180d40c40d075030b0105500c030064481c80030740c41072048030303840d000f4015525001a03401c045445682c010000760002800744041141a04d0401900c2582600303078880101d5008540108484072180c01311560801c840c4000e605214100840a0300c05c40d10103441c00350b203031813907414142d080c020400c8134249924404113402c01405025003000125074400c41c01003101342d80303c0600b400b6034400ca01030410b030b009040c03004000040c10702e0300751603020892034001428280054191991210089030105150270800c0b81407040c142d13000801900140c40c011041b030300e120307510082030704d0b8000285156204880b030ba2180d83c2403c4240d14103110141d000b009002840e0701d4020140052001e001883e00510a403038200032040896041307030301960101c0c8001c103e07a400d440011005002500d80b0413146e41c5d01c4006a0b035401a900026401403845020b10380305529200700a45c08462950340b00100100c912010300c001c0d00803c41e600741c00c2c1c2d18a071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 818972392 1250 818971142 818971183
    0x51605030c10091a090a0e0601020604080c16030303050901050a05150d060b090405030d181a062d1f090b0708130e0103030806090402100c1b0b1b0609 66
    0x21401901c1c0240150f01c2041c0c200c098000040c660500c0700c0041030840c00c00c0302c040d5406c0e92107002c0007000d81c800707c4a0303602592011000c10b02090780c19014005118203641112240783e07000c100307001d800f00c1540c012408241ca035414082c4010007801038551110110030204000d140c0a4811005035040428180c065020440200f007404000d1700004540140039110885030b003031501d8901e64a80c8080e4054054514001074840c029000050b007186140d08440d40d4070906410321034034100c0038400f800f040d600000c1c0f40e01030007480c00c024001540110100e103e0451440860080c005615401880403a660403410561440c00e078010702c0820a94007031403070b403039110719917071a26a04038400c42c0310301e8100841c29400040c00c00483d19046058a200359214111629004240040c4503c02e0b940250311901d162101c9000c0e5120f44620403405010305445941080d02801d1b00c1040d03140c0d45c1202d01c00701800200943c1020201c41090b802c489900000c02003032038215803080e1101d005407480c2c0b8400401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 818973642 1250 818972392 818972419
    0x1202210c120412020109060e1e040b370f060e060c010f0b100338120a110105070317041716150e0703080a03090b010b07051605030c 58
    0x400c00c020414460718105a41c2e41e0300c8501d84030000040c440200e0020710161408a240342c4180740070200f403e0090804081c1540f1601124910941600c4594001d6a0b139214086a42c0d40c203c4600d0b034418914081d2998a00c405d420400b2524081c0902c1c41081201c080c00c200b105200e2107408102d40700c9151817503d418450f03000800d40d02c15415200314075070800d4002d4980201d250703c2103c10607c125032030046600b5042042e020707a24500c1c00d0b07564048501142040c6400c90312a8140040d840981c0100107040f6800011180100c9051080c502e42c01080c8500811281030b1036075003000301c242001e50030044203070303401008600e011b04242c541c81040350128040011814000410a0000103140d489848448211b008800040b100380d4003020b00c001c144002009a00c40c500f40c1810303401c00b80c1b10660840e1901c981c80c2c0d0140c2c1c0711400705950b5406110120b42410f030024060201c1d40203455030b8180d542041c62600c0280301c010420103688401c00c1005a800162992418034140e4074055070851 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 818974892 1250 818973642 818973667
    0x4020403030c062c060f0610120c09051203030a0f27031e080708011e0303140702040c0504080606060909070e0307081c03060b120c03100801060e04120221 68
    0x4101c2e10788803908410000c50462a000316405e4881c1e004004031b80300f19641c140800907a0650408020045101821585200c810707a0b0004023883e178003030030300780c040b25900c402081e406000c10107014410b810100a20481c105540151030000c4440081444500003d00a006103d4120020003003010018004003041602a65468216680d455104070b04000380000240008004585c160001010310001052001c0c4e8444d03010031083c0c018251780070650442c0d60545034084202848045040280a000010b035941d010322100082d0f0b681c0e4098842d4a0103c414bc80c2110140c040c52103004140a0480707140c4800310360a0b4061000d1078256000031902c13020a05191483d0040b0502b401200890403510041001c030f00410411542c0800c02c1a070344003002c07003030340c050048200d5015020002141b040c510300c502460308160036a2801c010700b40d440034050b017100c07680e6126104029400c8100014018025801c0110071218006051161303410300300e00ba40000b0522100320021000f02d0107001884 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 818976142 1250 818974892 818974931
    0xf11161e020634080a08090601081b01090807060905101e080a020d0c08090d0207030b01260303041505090c150a03020c060f09010c051201210813050f04020403030c06 73
    0xf50b850300810b038406803030f003404202c560042d082c06000c100f86102281881400141d0141250404e0000d0482210071031000104081103420f41410851100000b0610243c02e101d400c009141c2034540b044020f20309024000e41c4c1c840b40f0740320b0303081c0281d1303007540100d50300007207910808180307145425a4159036640441c0000d00070081e070a2003030b030b00e840c101800a641150550f805501c0e0482140c010b040c041c6000c0340d0f0781001b400014480f104250041241c074104e950704c4240c00c08410082e18031842c0d0600d03140e2442d0400c680540311100501caa0020114480c450560131000080140010b4040c800224207101c0f05001c03001c21800303001071020300880c400c0d8190356403011020103880d0682031419000800007801d0b0303140c0d40705500c0d05c068410002e004000f02e45a005011a00444a07031804038465280d400312000b80c1c04803502d035844180010b0340c040040c40d0640d25185030500c943d0506091240d281708080390940258410001400400d41214003013145135480303000464006d502d2110140002c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 818977392 1250 818976142 818976217
    0x309100306120f0b01050d0c090504020312071b050d020d0f06020c1b13060510080606130b0d0f050114120f0703050f0105060913060f11161e0206 64
    0x80407048900000c200100d50b0342c03c8490300542c101e51060741c07901e040044e40070510030010704d9040002c030100001e22030760b00160780c0940000d040d14216104030200d82c8480c0d01142d411220f10013080700c018200654044000042c14007074817202d200da00d186e40828650302d1401000751003220103520784d90401946404a0300000340e000195000000c4415002000715044445036126001c009008105440c0354865a07048400050440c4070655200d103040d6140c0c1409004640c00c080d04010380f0030311109031541c0d00b005081c603048882c1c1c1d0799014050581110000410000310a050000400903211211881c0e10b4941086500016600580e00c90901d08000920035124a01030380c4030001c280000420740080c041603220003804503039a0b00c401c0000a6004039035104038111003900c03c90100300d01d64043c89010400c080001414280300030006501d82000080884411070722651404029882030100c0140da100300030081d4100c00b40d40001c0e414007800343e0110302030078000035100894040f0401041c51 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 818978642 1250 818977392 818977409
    0x171305100f030609051513290f030d05030106050906041a0a090909030903170c1204051e0603041205121e0705030f0c0903070b1303051e0309100306 65
    0x1024480c0024205618002540001c02d00d0a44001112180d80c011548200b11810200f0041c00d04401080140701d18980201704990343c17124011aa040201c0304800c0400075180740004560218082105182180306458080d81011241c0d455407a00901600d056078002c2c02e040da240c4001e007000c40c50900443d0b00c01c90340951b11002c1341c52140b426030018060392009039a00100d80351150a040103a4551043c0280010041c52007040880c041a1605501c00e024814003454031003068840f616040000c5240014100300050400152610340128400703868290b8141403541e2642002451a010080000e4003000c0e00b041741555651081342210982c4841c41442401c50406000f003000c01550303110400d00c154a17150101d01005e000d90180c034402c407076480d5042403956590150304840d03080b201500390507100c2c114000c82d1052440c030150221107902503418134140c0c518140b10f0300d081c0707000d18002d80ea107441032194089100080110f0345010410740d1190903105894100310020010b590000c801d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 818979892 1250 818978642 818978659
    0x17100501090518070b04090b010c060207051e070332030a0201060819080a0c060209030109051c0906020618100c051c0606120f0f0c0203040f0b030103171305 69
    0x650344400d9000900030440e20b607507600010030f021402c641c1c680460150f03600c0c0030707414081000f0006c042c3d002a4110380701803416092040c020769408040c1d0f0094007080750244c010030603003070b843d90581441020b1038200310020565a4030303644030100b05000340e18102440070f9106404400d10340c2107603d1203421007036050887e07584607503c0c0030080c02444d0030b000342c540c1070054140c080f107036242d9000c002c4032460b00141402d140c05001c8600b40e4a82511031030403a040c41d0207105508050f5802e1140c42e0580e40940701920040074103460400c084d034101d0015a0501500382006d020040d400680c056100305280c15181c0d9801034402c54038500791440d1495595542884009401b542e4047c0141c407810744000722801a1000e03041d40720081d1440d9001d000d002030301c00e0101c11600c210075004100d21070707800c10300098501202e003a0b41c015520035150303007000b681c800141048442c2403641d18030000d0506410942c00d550650780e4155007010240d0300d086401101061481c401d903a0398081c0401400010300911 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 818981142 1250 818979892 818979899
    0x405120403050609070b1305040e07030605100e06041a1219123011070203060703020903060f0f06090601021608010507020c040615050c1e06010e0705120117100501 72
    0x15610002121200014040c41e800006e40c3c1c004070040d54051906030200044407800e250500c00100807014000c001c1c0e2044100000205045116150046403407440342003c203810241442c880784800391242d8019446c208266201c07905020b100380e0010002c489039841d007c0180121807425806000184031003000342c06070300401c012404050084206600e030403030080341581460080340101c42283c21044042e04041080c5000c9500c10b4550040c40c200c014101803681c1c0202c0d14000c8110b5200d0046503001139080300c5450200080b40c0d200700154410f40c5a440c00b82e47c80b44240d607000d040140100c800c0c8000c41e1540e8000c2c0201d030b00180d4400801c840456503062402d018003010384a44000d40150b4444070100e0410340542400e03500003003d000000d01041c035045990342d018821070042c40c06240d042448201e03c0707031010090105004000e00855041840302c9104c07000103007100d82401000c0000425500c050701009046800409594200d02d2410044d0f42c02d01d1840041d10440519080021 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 818982392 1250 818981142 818981153
    0x604180501020418110910080c0c03040806060f03072306040b0d0c030e0c030601030f110a09060608010b030402010e04050928140f060a0e03070c080c0102010b01260405120403 77
    0x1c00e130052202c400344140804000c000c00144110109650000000ca509800850040c1a116004206100024a040d802009250951b00507070414071580d00040180191458850506518404120040c10344640b5001205003101d519509048001441c034115543e169214420b0b2802002410240e40c0d0b503c4402070752500803c065114100868a4100b0003100818001014580840041d00500c256400d41c0c032012881030b402001101c2d01084a071141c4e4454072811300400090a050340d0109002e41400005080303160160030502c0703441c800303108100141c0c0c2d005420744500700d01507030b0025891311b03000a10f84c1081c4810ba40013001d404241542402c401c0c51307156000500b4003584081c07543c800b00c2e50034143c48021100081c14030358000c00200b9510740301030b84800600003404044038500074559581c00702290040e880014160030441414196503028000d044800700246421031030903201004890789035105110500e401c24040d400902004420021094803203240040b95803915640e260a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 818983642 1250 818982392 818982419
    0x30304030f030c021203040f05040207113003090907030b1203040b090a090c0f20060c0d051501200304120b090f0f07120f1202011a1806041805010204 66
    0x128017a0343d20581c4007607410380200c150340503074801c2581003c00300e151508100107900001e078117403101c0380380701c0d01100c41e42d48210304804081c6080d850f4800c45414526000d100c1d20840d40744051a42081112581070360f01c41c20040d40c49000c9003400074a0203800340c0410000324405081c164948800540460041000750140165080031240c28203480d460300d6a986c15102c244900b02c0100b00c400c00002410b0b80156581f03d2015079081c07150300c102146107086454400c083d0b500320310681c4000b44041180045005450b401074a480441d0944800d840000b4403050f84100c545014075840c0946200e02c3c1b00c280304440091076200340c24903040042e402d00c11100181695450080c0c41181072184a03c01b01154081200c038a24024114183c51f107120100008001c00f0115000b0000b0600000007480d8a45107034003108450380005200712524040342e10003d0400d551501c100c1c1a1181d81c040c40c90782100065209109540220f40c0040150b90003440f00d000010007002540086800325140546100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 818984892 1250 818983642 818983667
    0x50724060f0b0c0709091410050703060608040302060c0f040537031a15100801060f11120f07080c0d2a030c0503091009080616021506030304030f03 65
    0x407102019544842484051154604001c41504040820400030b1813540c0250b864074043c034103400b61041008616403c140d481520701c00c4242d6510144110b0b0341d80f502c940405480642012602401c3c2038034041d5031040c00600451030b9071710000e807a040c624602c1059500800e4098418161403180444c0c000102c024801e040c90319000034141c014a2080410154081343e820912522080b8240305000c0106040203080c401c0d81038141d41c144405031a110031000401d240b55659071600e5042c46001000d02c40342011080400c07880c0802d840c04201c3c046403001c0d8603202c1c440c44030f596460102001650340039007070300941800000720344103015540120381c0321003160040c1e41d03a03804000c40c0040c00c40203401154148450072400000d4034000303400340600c1c4e59564064800c403414070b407101d4006022003009020440c0082c3c2e0000382044001010403506420556143c80780c42030042d500320003941c0d0b020114000c0104582100131800944051041701d015607002006a8807500c074504024008250100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 818986142 1250 818984892 818984909
    0x30405013917130203071a09040218030a030503010617070e0910030b01080307030801050d02100c0809040f050f06100f0f031b020703140307020d0305072406 69
    0x4401888211114201c24110074459003040c001c54480d01c06000c4004054040c005110304035142d00001060300191a02c1a1400c1200c08041c04091040c182043c1132036110400c9480140301d86625030581c001030740e00504e4251001611800b56413280c143d40c0f0078117480e06401d4044c2d143e9038000e0680c480010742c1070328200e80b51000442c07203034034280182c0c030003c40382c2500160300d0f98406441840c090700c0254100703130030484440301366403281c8038080216420380c0108410303440000c45408240c1c10516440c0145000c481c2c0b510100f61580120710340d0411101c8400400400b21612010013004109036421424083c0040000c03044040401000740340c151015402a074296000418a00c1c1006243c660f018141d944d0041c00c8074013000981ba0055000804424142c45135400c4003001c4103810b031264545440c0c1d0081103460b00d14280300d10203800c40b034440001500204408000340c4c46403000002c0140e41458903179903881007400e298051010700d07400664440340b00d1030203c0c04514550409000d40e03c0c0d09 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 818987392 1250 818986142 818986151
    0xb0703021602060c1e061005060c1005010b09010e0906060301030b10030f06140606090d1103030d11090901060801030b1b091009050307120302190321021c09020d0f050c1503040501 79
    0x72505660701012506030f00f503440c541409008c0741c10003a01505030301103a0403c0700c2d8080c1c4404c03d0441590000d030008c1e111058003140d84109580d20805891a0b04002c0d140301c3d000d41030900c0810507506c014040580300c1c11108010a05003410030f104036004540120300e80310110090300e804809860898124041d100101d00810321a01d40481140c3c030070b8000030551075076030500c0c0d50b03407003e41d076a800b003265450300081c040329221403140d004030550003400c0c003a019500c500040070007080c0c40040e0403600c1042801401880040c01048803035030131910915601030100b0302d84050048500c00c004105405c00c800ba0503000c1d6040d0803404444c251441181070b5141c090b10703070343c001d0301d056010b100203401a40103140c01003081d4400322102c1c428501038a0034000c540203480800301604070f202c0d80241d800d035002030780d01c03001c5102003450206e15618100503c85886181c001031543e0301c5100c0042c001c111002410000c0040070018540d06500151039051a1074111420b002c240d04200d50554055081 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 818988642 1250 818987392 818987443
    0x41d190b071d0118050a08030d0c03020906040b03090115080c040c020105131712070f030c180311040e0d0c02150403020315090a0602030a0902040b0405040b0703021602060c 76
    0x2455600c2003040c60402ca034824a00b480b0044501000644601160403421007021a545c1c503040c0c0c142c00502030110046a840d80ca0310010402c6036a180b402030101841070140d003000d40e0710f17581100e0071100710402094481d120000d07a1401040485a42e18498a0103480050307186004a4103a0141c6800c54003040303c241c0b480b0040c0d080c2c1c0c00441d500e402c00d2803081d000c640043d80741198070342c0340e01103400110305014030b4540004103450250364071000b181d9080a48001203900d8000c2d0507109400d890321100031503d403400031801074280d0200402900e40059142242d031140e511070244420001d0441d0607040c1c401c42d01400d841d02c9014268000c09840c001040c11a051604172030861390f000d80103001f15090344c002d0012022002d8030801990007052a42c0012900c0342c0082c0d40074140a5034006000381c4284100b10490b1020a1924000c0741400e04200100c1c006417403e50f4042d1060402598444452600b0316405002e400000d501c00d90114015200d144005003c55060f0124106001c80100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 818989892 1250 818988642 818988647
    0x919060e01151d0a0513060504020c0c120307020a090c030905010906050901060512031207050705150f0702011a0415050d060c0e060f1608070618050105010b0c06010302041d190b07 79
    0x444036031481d04180d50013010015414071101c5001780b40310074070001034a151a0350008090b40e01201907111130341e000740c0a4403030601c1c048400100920324200218685030842e4007184018140c0d101360210342c0c0d0303500c0c04001c01a01a4108101c3d5a9002e002088041c8030740c17a084004040aa8001d542d030344c170300480412541001044001c1f5030714080011424911405008951040c00074114010010240702c0000016010006202d907407081e00000d0307402d443e0005039048103101c0100130800b160b04102c403c40709003413078060103203001f0b006a031b01144100daa003a004072800c8491b030049402c07008030700c8840c041c8412a4020660036002e6612030700004c0e4035000300502400b4468004641c10802c100e202c0d070010880402c0c0341c01034440d100c05802c12805840f03541c21114800304000342041e00c001c4070341c1081000e115540c09492828581400c20070b42c480c640c1d940f03040500009010720796400390400da9840c8503400e21455205542101c403a105100000401c529000314200c07160710442c40410089030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 818991142 1250 818989892 818989937
    0x10504061506050405040203090a1b0302012303180f0d0e030606030f032d190311210c0c01022205030706050d02070c09050a1a09060919060e0115 64
    0x4002e42d851a08107400d0408200c000c1d4009003a1110621900900702e00242e09020000c02a602450244120600e540009061401100c60b940d9801045c04e10020951200c04107a0f500007a004804030b054140d0f03034032200e1a00c0c0318041050354903c2484220321000341c1c4010340740c910300d509406495941c0ca41406060b83c60034020903109890b003091006190505a004e000c044442600c0c110f42c04107485078204401c1a400150445a0a407108a030310101c260540110f850540000f40d4291821501c5043d0b031006d07098034032048414100032404200700751041c0c000d0b980a5204100219070360402c3d100140001551500e440300d006281c924001400d01d03010030304004440254803490314020b4582e021400035813005000301c0c1c01290703a4030086075902d101d101e000e2144820000005542c40910001005044040001482001c00e00208481500c83d003c4c13080d084108001845c0c1440240a01381014208903040b028000080c1e0000007408491031107000c01d4110741e611611030240e00710243c4841c11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 818992392 1250 818991142 818991149
    0x4060e0c0312071403040b1209120d02210c31080a0c3204090c1e0504020f040e06030a061503061407020a140106180203040606052209060b0603090105040615 69
    0x2000c08d2021503044907d1000c000c0d4042000002da440500c000411410160018029a10819800304040b4070702c05d5002c4142030002000344a0030300600d00100751040a10442c03924440007900300d41d1200d05200c0c50603882508150360904254507540f2407901950340c0340c07140780a40342c07000c480d4000030302002c0c1e1200341c07008e1114402d0004542d4040603024054540300c0c03030420741c22a503101d00200116050300003403006007140d07891008010302542090556170445800051180344108030031491400e4a04c2210102c4030315160f901c0303088c3e95450020b410301c2d0b4280d40103011039090150841c0444a00ca0100050700e00c41d040030043e80504850741d202c8540100c4000000d641300c2030818010854004042d142c403a18800046012174854006440c1c0108140c0e1400c1c1540d0003000f48810003440c0e0090402a046c1a00c5441c507100c17110300c56144400d5409000c890040e51103406c1d02c144909600000c0a030200a00040d17600c1c1072080380c840c0248403c403003d503035a07444c04440d90004000c0140e10000c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 818993642 1250 818992392 818992409
    0x32a1503090803130b16020a02100908010905010b010f02030a020712030c020306010308090415030b1308040f09020c07120305040e0a090602040b09010306140630040f030f0e010804060e0c031207140304 88
    0x41d00c003e030327080c042c6200c029082c550900c059140000b80d800c0702405804143e1b4880c60001c9401043c0c540050301c01c1c0c3c003540d000d0042d90418000500c1c11940040e0b20800c49030007121808140860741019100380700b481201941600032403002100740070b400c000404a01e07109440401c0303004600c1d542107800041c0c50100400c450324440120303400180c0c5c0c24610107101d000d1080a4609691404480512022035200d228140d1300884c44200311102840844020540007001801c1c42846960092441c400e901980d0b84010781200400c0e59148158009202c041d8030a100715a29038884d58840c4003500302466050019042200c0425403002c40c508214452102070301c01820320b011150003100320310f10301034803403c25002c101038540445605d10020340102e000b003108209960b0030b820010700303034000243c1600502101a252aa4a036880040c0d1644503800800c0002c071916609030450404031603140707843c1e1520134102020386c5e606007000104401c0d4410219540155105c14800d902d0780900e2140110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 818994892 1250 818993642 818993653
    0x212150603061507060e0f07050310060e0f070e13060918030f050a050c0118030809120304030507080909040308062707030b03160b04032a1503090803130b1602 70
    0x300b00320f040c007034141c4070f00c02e00c004503e44800c1d252142c54001018030700e6080e41c1c041c4404024500701800a044000f84140041c085c06040c2a03c90541c0403003e8890804205a40f001468561103041007044c101001040500c207803825840b01800b071700081c00303038007400c80c43c0c40c940400c8803030703402e102e400d605506466041c0381121004056920342c1004003031800784003003000400b02d281028407400000e1440000c1e40c0910550314200200401001000d440c000d0303004800020764800043c059950250b410325040d0358070381c540d00e015140d601610360500d41213070f0342c00180410190001d03403043c800e020a4a5100c1a5140198511003100d40230700320038980842c190204101e0741c0302c3c0c1c115041242c4090304072400c0710400c400c4c55401200c164401890036038042400d0041003000304081801c405514900c0b040104140d0303601035416040c0c4074140030410b8010035451038038040d8000484d03060304151115282d01d0300036100340091040010881e8512002c000103400a24503111250014815900401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 818996142 1250 818994892 818994919
    0x1403181c110103020f0301080d1b0528060c0804260702060d060503100b18010620070b04080f060619090c0507060c0509030111091302031801021215060306 68
    0x4002a0807074001e68101038080110103202a0898000c40c02011100c0c0180385109585a00400304140c4c003466151203c0585110320225000040f5207440c0718509804400095002c1c941c01c00c50301da4200010209410103007090b00c100d070400c08047c810b034020640001408508041e2104e1006400100b070400d041c1407142c54003604111000e4030aa81d00480c002620302d4407600040c0c500411300880503502034541e074001c0381504111224030804e20040f0001c150a50404102628080c920a489402d0400700300e004e0400341010440d40004046c007001c0c1c540e0340c50311081ca860b01c1e4450542da88107144115800308050b41880d200c48120703103d90085070f1404506000210b00a050801c1c150380811509020500110b0018820500b0341901515103d03074a030042b2003414256800125404141c020074071158030291103e45041190104001d40140d503540e80d12120601009507200e0749900390b101003010300039049516140c0c2d0150080c0031018006003e0041049424401101c006421202151107072 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 818997392 1250 818996142 818996153
    0x1080124081b131e0605060301030b0a09030309020a060906021b060a0516021e0f01030501082808030a1e0504020a06030c03090b04080405150306210a1403181c 70
    0x340c00c10301005040f810700d107801c3d9008100341e40c0c240c030054040500e82d40070a8040d41042c420301000740019200982198550307200c007020200c00500c8041c41c5901e8211007020107200303500404045500514441116803140c200a060300d4850141d0009032107404035a040350070200800e82c61030030009115500c0c00115034000c80d01ca0304828044c000d030340081108000103943d8100b03000711140d0340c6824050424a42403c120244071149481418940b41800500c00e484010030700a00d01181303c808007814003811209544030605036200541540e0010062103003901c62600540e94082040206000d00c2c05c040d412a411140e003514021350005030741204001a600a80164101e40e656080005285d442d0391121540301c40c048500715010000080c060100e450051400700d80c090350b580a1601314605140480d076015a002a8494002c518003640c80448404000303504501e41e0088210500840c0240c0b41ca90b281c0000c032031021429251960304d80c40381407040001e0190713400090031031902c041c0f5844e030307 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 818998642 1250 818997392 818997433
    0x315050d02014b0801050f060708040e04054e07030c020405013011030a030201020408010c0e010f0806360705070b0711150108012408 59
    0x89040c0101c084000d40010300e402803082070841510880c14522000b030300c00310200072600a201e4843c0c0510145540155444030601c0c1c103569043c0e80c1c503e4100d80c9840010554051940c000b003800100140200f00c01e004000a64050f0303201f5400c035050252010404540f0140c1205d240c0b1340281e00140614a040c03291a042079403c08170b44210b6207403083d07010040807d501c21842903001c03983e514890021400c151107001d00400d03c03650b810501e001303d1402410f00500c0c1a605150004100ea401e205100c0000b41d40c603813092005049400719012498042d010390418880d60300c8651070b040750000d01034014100459600d0301652503005192410300d00b40d44980c809001d8942007111480309040384518404c00072803042036510b4800c4428401a69501010b6004000504102d42840603c00181e105180329800001c02d04040c0e1401c440a0301017840c0c050307440d1350381152900440c00004c00380c4066001e138002c0b00168001d40b0f48844240f90705654902144071b10314141e0b00403101040e0006c040c4e5417 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 818999892 1250 818998642 818998669
    0x30c1a0912030402040609180c060e0102030d020f0c010213140a05130f060e19150f03080304081608040602010e011b030b03070509040c05030714090c03040201050c0a081801031505 79
    0x80006c0154880070b40104030341002e1551030000c9100c2a4801c1848907032044a0300800f0180b918028881038100000d46034004d442009908940118213007e1444428042d90100585040215125011100d0701c2c6400e480d5480b941c031041c9458040d0300a5410000760b00f800360b84014000036020300d50040152b0040008a030301c000055a140c101113007004503e131095000b20340c80d00c804480c0d040c04885060444007041c0f100164250007400030008806008803e5007282d400c0b100140d140c0d41d46052605a920034602006c3d848200c0200c00e40030824000082c3c07068952507402004040700c030400003801c880340700d00440300c60384112600d4071a0b1446504428413000c009810b0381c056603aa4004200002d4080d01c0440320018107000a2009080802c40070000b040640100031703e00103001c0216030030b203002a10850b10b10700e0000000b01564014411141002e0610048440500c01401c1207070b001d070008041c404c130301031106098004562007070064000e80088002042415071a002c1041105109030a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 819001142 1250 818999892 818999899
    0x30c1d0303070c0b030919050a0611040905040804031709090f0601020109051c110304030c06050a0e0607150f0608031602040b03060708040c0f03050d030f0612030c1a0912030402 78
    0x41d80c400030348810403c0005041c1c840c0603070f48038104503100508010003000101c90301100c6c400001c001c12400550490314903009040000d050079100c4c59400584105e070401c1d1902410001440704001c515401001143d0180e06a0301c5120b14121110546100341cac4041c550043c498400301d070fa100d21201c442038000c081400001908401c40d52440d06004100118900540704a100b00319400d030007405020300c812a0b9809903140070301759540c40f5003458550094100308480400e096034803d006001c2c5c00703007004008200c5501c1e10124038000103001002034880c0c2c885810035a04582541c10750140e0811380b17001c0c0d4041c40c10050024085030300d4641e9104d050364010340350025107030f6a45003888004e010b80d01e9a6685045850310303013030014100c000f540c0110314001d545401003003c5174003c20f4560440045280c0854094903400c5040c0140a03190004800d40460214400425402005c4690741500c0784c07514070b031000c46480200c0302a11007120180c030b050b0440308203c0140d411902c001c40e030191005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 819002392 1250 819001142 819001147
    0x20a021e1804020a151202130b0301080d140c1f11040815090a020d06050411040c02070e0a02280909091a0a060807121a090c010f030c1d0303 62
    0x5803440c01c4041d4038045524144081c44198249840a031010f0516840c1e120b11080d503842c402009103218440c540c94040d0b0200c1c0b031075208c03400b8291140052160540c09900e951310348002d543c0b9050281654404100303900842c92994204605403070340405444068420000d540c2d03500000701e102c201450307030380381c0e642c0001000c514071040141002c0c041200042c11940b0203561042022200a4200f5040d42d01c0003031070714016550b03088945a10355100c5000b090989035460030b002d080350842a943d40c0641803e4005000076800190013007100c1d21b41c2080b040300d40b200c040840072403050399984112901211100204601c3c0104140881074192400241e915900d2051310104c2d048810221400031b80b040c41c6e001101a81080242c01441034078041112070303c1c1c0080300c3d5503075486210300354055040d007904800740080d80100030200310400c5d40d031601518182160310f0300c6102c9610504e02049200300c0d4103000520034400c6044000e034a0b01c8511080c0442e40c4290310034104600728a6040c4400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 819003642 1250 819002392 819002449
    0x50c010203070c020319080d0b12150a0c180303030b010216061e050313020103270b011505040825031b0303081b0f070203031b0606090109020a020a02 66
    0x9200071842903000f5910401120098410542070000007050589000ea0b5100b000c0003182d102c5c0f086800c010300a0900190302e43d06840400e80490944208001c103003c0e0205070602520205d18141c0f01c1c0180060030071106030200b00946030485500c50701d46020047c20800c0c00064003992180034244c00500458084505640c554078110a0941001c4002060300302050b4134980c1e80035418005850300e050a41c01c4d0b24001800d8801d080d15944080c2c10103071a2200b0860200c0740c130090390000816800780400b491401d041c5102d08080a110300b51180750ad00d01c0105d209485681520305079070007075014046803800e404a082d850b10b462000044251140f410010020b02154090856200b04000c240d10082c41e50034050080c2c480244022920008001ca100c2c03013401c1c010484030b440010100243d02c4081074000302c0d20714080d1000070060b00462200c800810760001540d10702c0b0b080c00f01e804800d00e07030f00d901640043e40100304002d0003503440b0b81c01c036400500d0720a002d4110405840c00c0c40045070350 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 819004892 1250 819003642 819003667
    0x40f17030412020d09031101120f090b06090f06011e020309060c150a0204080304060507110612011707030330060b0a1404030515040c0902070311010e0703020a1505 72
    0x56804441e0040d070b00741d210301210340600062001450328141508441d256440f040031001240682504215000c4a4001c0e40541b070350203412034441d1362004100000c130b20310b0003c4446000b030b15101d104a080c0e100045210700c2c0f1003038031445444180e448910030079807071685d1000760a40001c4036080d400280510354490310781801a1050040c0c08004200c4000f6410b205500100003914030301c0820700400042c00030000010840c0c0c00c4519902d0a50342d21100c0307040ca002c4e01850701001c10b9010400003418141c0d8461000308034140e8894400c2c0c01040e462070030600b5503500e00381c800140400d0034031201070742a000e000f1580051034100d43c0c01004403124101e4080884629410000b49281c0c041502d002983c0d1010710002403510b4101500d01d0142117849142d560401c1502c004c402100c000300240802c8000d05404000b0824074005549410440c0340141c481c80350b00c11982c07690340c6400450a48490000341200450380c0203040c9440d41401c100c00144806100c500c0d0806029040186250395403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 819006142 1250 819004892 819004897
    0x5100c080f040803030a0903110627030408100c171b07031e0306082406060a0c0501020f09130902010e0f010903020a15030e1203010510122904020c0303040f17 70
    0x286d1868002070028607030b14000d42030081c502200e103265070141003040035214081e005400350b15215a1081625200480b00c103266119a42007000d040c02034069481030510b241d080204a030307080c0e8445c08a00c1d08a1102c001140500311b030006c09800806094940703411000c40100029030085c50b10941020b01f000c6200c0c00403440c03014002c0001d580310380400409105022921040c034114034544854484c40340f0302001e498004d0281807180000141c2c10f1030090140502e040101d902000039500c840036105c2098944e0014804a40180c103186203a4202d02d0441c1b14038403100f41c2c142c64609140410109001c80d050b840101e190600124540100140e070342c01e90a1801089810302110399289a010001c013039406245240046501080d08038110440500980303054850907901072107890104801290020300e060340d00070b1890b03c1c2103080310410a6520803c045684528031428041508900f40400c13071084010b0f01c890340e001030000c100043c8850400745403550061203078850760f4400402094055 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 819007392 1250 819006142 819006151
    0x302090a0b0d2001020a05031b0705090411010f03020f0d0507120e030d141b0c070b040b071109010f172d06060117070f090806070e0a05100c080f04080303 68
    0x145074801115082e52004080d0f0b0011107007840034240005165942c03070b81d60f001301d1041b0940440318030641d00d07440808000030002400c0051101010707042030f007041e64041e5a00e030040ca000604940c52089450300031b00840d411608528000c514103c00591101d0040801401d503404120685403009850485030007808040000e11001c2e568414207e60b10310101d6140d900099040846c0008100710307981e20700080c1d607412403529171072660303150a407002d1410048103800600c1c02c041301040104105164001508200d8410fa003280c64030041c0b4010031110031004d210744000413100c0344080c0306040f00745401e140c080a81504035000590307400c84c82c90302c560320040f0000b50094054404031008008000d440d400c0402801c4c40202010740842030f049a00c0c0045c2144140420781d00c80c60403030b5100d00b02490042985c2025a441390501c4030005100c0300d0144000c0d4400c0d8100310011039140741000d4100c02401c101d03200d240707000d0110f91b590103140e004211000358100d001d00001906803424402148103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 819008642 1250 819007392 819007403
    0x10e0601020a0213020409051e0106110a02060315031009150209060408011803180b090904051006060503061003060e01060c05150a021209010513020f042a1e090302090a0b0d 76
    0x690b03052100d45000c503600100416003174079071008089081107222780c0a0341034031b4091500d18010310003442c909282090514009411200010070015883c10358050041c4c0030100f02d0a441c0c408400050f44010355061400150030248042c04100c3d80064940c02041404406000181880d0303032054440d007101c0314000d620300c1d541c800d401c01c2c00800d80c0c0812035458944000c4c000780403190500f03016800d580202c11116000303001510118050100820010a65034001e90091064507250a40103141d5001178400a014044002d404c01740d20303020740150000d85903038606044841e0320708030046522010070b072019540340c02020540c9140700310a2003050b11400448c01c0141c0d481ea045501007d012000504602c404d0b4589828000203c4c5c5505900c071015804541c2c01d00c00c003004400190080180c507031150003206030703400c044c1d802d80b44600070740f0824540e41d00e41d203a014801100004400701802c034021700107101407130180011301d020150b031f68005100b0314002030b40b40e203080045002c01e6008d4909860 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 819009892 1250 819008642 819008647
    0xb1302040b0c070522050a09230618060c03060d200f01030b03030a0e1c060f0b1c0b0c120403180504060f0e2e030302070b03040b010e0601020a021302 66
    0x2507104103e403a0042106440c0c100100e064048154502c0c5a00c00300c00854a03101d02c0401e005d51041e030065050150011100003101c0c0100800c0911090b0007460441c0030301401e00020080c10300c4041010f10204c590001d80915958000c0c201c02aa00c010714640d44840c21400000119445002c2100740c110640580c03100308520200b00002c03600c807201114105410030740e10b625251030100c25555455614100b1200c00c0244100090071580c0e01c4403010240070001d42d0301e1701440219008540203408192003003102ca2080070a1000ea0301152401008902210201c0400240c0d030010340c0307901500038200c00c0e040c0300b01e01c403421396454019503060700010380443c0c04012188458031840000c1c48111001c104842c5003004448104035540705a035425800080002d4076052907080300c181c600303600b29001e1410002040403000c01056808242d00600c07800d240461003d00c017408490159030040c0110f01c40c0c0c3c2c0ba04144182c484801080941180034061540e00146c13648501216402520640540c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 819011142 1250 819009892 819009907
    0x3122503080717071d0f04020c0c01030f020405010912081201060906122f041e0f06050403210e0306010608180303130f02060f190806040509060a0b1302040b 69
    0x100803e44010402c000460700809000c8400d4010807034a1107001c6040400b0304440d244000101840c20009941d80c00900024100401140c042050407050740262400c01c245c800c8000c010b0124041c3c0d0080070b000c44ca07a180240405290300103880100c40c4a10f03901c0b454007040501405901c4002e034885804100c10950500c000d0b81c0001c503c814071003003641c003003000c0700b0912039403200202e484c00c290010341c0012074040088036544003110098007000c1903401070903600b5000c2981c2d010413481143d0490001e1403012030494404d004490480340c01200345142c03004107c400354100544092410240412020100010b0310184511f80c000c3c1040d031a04400c41c500200c0881030410480c1030513040360010402c0003c0070480c0c80001610b541c001c11101c1850100c0c0c404281c0c41d2190310403480308001e010828100181202c840c00801c2c03500b9a9508c040758440030140b1041d40c074240c6a0070115008000025003034003681c0c0c480042c24400900b1052401704100c03c12040340e105800c05200c4000008040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 819012392 1250 819011142 819011147
    0x90803011a0705240c1e030c1b0a1a040b0606161a070f141c02041a0903100614090604020f070c08120307090e0a09020a061e0e031225030807 62
    0x556024132050001494030400e4800c1210206c2c0700e00d00315010a0b000720100d40e602c8084016107101e155480504210000d12403012955008001000c403800c0f40d16441c681203e51134040b2280c040d60348185601195220401000f107107403c05061121380d40d04500d0400040f0302c18154040348642d01c40d040c980d03c0d040031171000340402031088480052100500d40c0c00320b0f946095017100d00d11741440002407008001200407101903c42e688c014001040351842003401c803000080284200c0100f101210100003400000106556003031041e1011166260300648407406d00ba101164040300003070005107401c00001010085400084068130140346080050090400070010310070b01c030110a012a0940c64154001400715040d405001054004400030a080c80c1d200c3e00442200c0b90700422240000d40c81d050000c0000f20070b008044000000c0c3c0d13079030041c4a0700440e010b03050881e0241c0907000d44422038804843c141d026840c00c80709004030592012807600d101030204a2030303209a41f405194184220700 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 819013642 1250 819012392 819012463
    0x5070b01140a06180302091006030609060b03070f090f061812081c150b030906180c01052505010903020f19020405090312190e01090803011a0705 64
    0x220364039a0703154160a0059482440c04002c4548916108504480b0b07a200f861100240e070340002d410440071418020292804909442a00c0c6260f074200314566a966028007581c0003441070b03400045003000480c46c160302c00c01d41d100e904041c0b4206400c000d03550302440c400d01e5005905c0200000e90003110740c00d02041d045d8200b40100014200e01d00c00000a4440108501c101001004a9011144000c81401054014206444e1981c182484203a036038005000c107648101c030042114081d1100141114410a034215490703121000107000c2c00c0489401134803140d00440b24980100300c1140c0540c0d00d00c900600c14000e20748100300100c5c45a0352803801a190012284124038a600319003081e000c0c03201c807181c281d6012601102c0114054580c280c1e00b505500c9503c001c054448003000810080030040c1c003100001105041007003141c12501104e050880c1e50342e01c0028640d8008100403c05120380c070650080720b81e411f45d90720346040400c1e070365185060400880601c4070b5000c881c120b2800f0305c403041c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 819014892 1250 819013642 819013649
    0xf300e041d07050a0e01030c21240c0f0e13020d090501060515070b13030c0f0b0105010905030f0a0b09030f0c0c01080c03160c0314041d07031b030c1e05070b01 70
    0x165414554116500d0852448090007080042c5003080344907271010400c1e4000600254001c617100f2047c0e5040030203240200b40c0680c0301d500f0310342054a4912414415907006100340724550760740143e4001031080003000c590301a02288116000e03c40e42c20507a00b1481080c10003481040006511840c000600001181c414032205088a00b406207001103030040c81d0f002d80c0521600070030000b126481c5030aa0300d040c100e0070003902130540b01c81c04c40104441503485a0607100300740c80741c0c0815a980d40c02c140c1d80300030042400c030181d040400c2050000d80d43c98102a00f25503241c090302d051a15048031966681c008040c1d603201356100940880f125600300c203d03240c00100504566181d858500c01420b440b20500c841c46040160940c000c40a0600c40d07205143c204582401d880e94960b52841903455140c183e0000c503500707040680101e005140244995100f07041030511010030030601e03550076030061400d06125005d00c03810540d003031400c50b92043c08440144c01501c55948403090b608080c01002c00507003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 819016142 1250 819014892 819014909
    0x30504081e0c0f0c060a0f1e0804230307030809190503031503061605090409060f0f0513030c0b091c03060e1b041a0c0a0f300e041d07050a 61
    0x2015008a41c4517803040390001d4825003082c480c12200709800b00c4041e503d55800340900c0d84000100c2c00581e03400f59010307020301c2c0208181c0b41c404026602e00c02210f2143c514a509aa008000c5a030000340a81010365100b00389000b5502e410301c0880c4448258521030000300d0302c0741c100004100200c8040a200644200207034010030031441d10755860361003c000301e04840b05011011520b480c841e0f95680004260544c421828084004502908005014403256501c801e0b0b0a00d030014018004100304600f400d901983e03035907250701d019101c0103031040b400352070004940a00d00c0e80742d00c051411400f5030550002690000345d901e18115a007031320243d014001007100f4900200407040201d01c403040d0707010b0f1400103849215003a40041503044620032030455003124007031802c0e03402c140480c80b12880d0403980201c1e812140100c0001252081182c92044182c2403203c01103800d82c038030300c140303d8100c00c68000b8000050420303584070700710240007205c40c4c109800d52042200b0700c854104284520f00806011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 819017392 1250 819016142 819016153
    0x10e0708070315050903090d05010e01061d0c0304050a08070503040608010e0f010e1305190c051801090f09200a08030711060f0f0f03072c01030504081e0c0f 69
    0x40c1e54294001d808100707141010f41d104c0c004140c202409004450400c40000c1c48038000490301c1c90000d001c2c00c441d2100050552034003000040c410410801d161843d0801c4406100341d0b6950201c07500150005441070302c003881aa003c100010b65204000c0c403082d8000d4000310740b00c0f032a02400400108050b0444044c465441c0180300081443e0140c4038103580890803e0280d90b61808980119640090b0b0040c1203481000c0c01013844007407418005050500440d1194021515103080c03041c1c42c1003d155021190040300010050400a1341c8511016103500101003000740707a545500300b10300460808602078504d420b0742202503140041c0c0c0c5000801d0401c0103103040c880182c450304e116190501f0024000c010000e0071600d0480d6a40450720304c9119510503544035491008404495003045540c0ca02151055115a031081d108140c3d00c0c02c44c050306d40d078411000f04010300440c00381c040500200d03139410061244440200850500e03039811901480300680701c0c00800c0d0024a083c1034000c00480a4011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 819018642 1250 819017392 819017399
    0x50412050f071206051605091014040e011802030106140702040b0406032f010203041e0305031902010605041e09210e1503070806010503040309090203190f06062a02040e010e070807 79
    0x4000e5528428084070000742c1013809c2c00050722005800701c41000f83c503800080c08500e203440d0040090503540da4145442d00d1100d80759503038040744820b00801010a000107000301d0b009040400400b5200e102034004900000200080ba0945485400403070f4102110100c59600981c0804080e510040642c40358040200910000c1c5d20380c466401150010202c94541860301c80441840d02c00555220048a507144150a0042d178102c002102802c015424008001840e01e03150103403100c1c0089040c012544207600c0b46108009141c406011940060108849440c1c2c00e5200c1a101c00c01526495041d40b030015034003005000c5801d035000b90401034092007408019503001601586c012401c1c01e00a0b92502d0f04e040c01e0718040741c2607200d01c1e5030314000005c001c0c0e66030311040c11a4400710030400a0021241c1c07800424180c40b140c0c014a0000b03220207a2031200c10031020b5405511810792405500000d8032500840d003529085506001161744862448003a204100221802040d05402234201c803400c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 819019892 1250 819018642 819018647
    0xf0a08240609030a0f0f0c140618030a0641011401122c0a03020c040f060e0c04050a08070b0301030303051801051305160501050412050f0712060516 65
    0x10821409014049441111a03c0030400280c0c000d0f0811408141000c0c60b24001914401c0d0000850701c3e4004840e0015449160082c00089140c000341314508001c00c0700c070b080d024003081d00f0b18aa0315229828152010030400d1040c0b4652102a10140840d00482c420102c000c03030b0012a8030400149030020644604010600c45056079840d014034403601b50a000102d07200c048041201c40308914003451000c0100c0904206000610750b80440d02480142085864a0b501c2c030100c0030340035810103600101241f800c2d43c000007040c02104000904d441d1103580b0740003440c10860f03002c100001c00080c02c0c4101c1ca0014152402480c0410003000410300300310150181e4001803100906250300c0304003041c1c1e4107031084500b0b200111040d00822440c50700580c2c7c096902840c44098441f0700071401d4040d01c0b244030051040c10b40e04182c507442d181c1450600b45940200c200301c3c00b641e15016200004400020500c2600010603c03881c000c40c842c40c490401c1d804603100508101107003108441c1c0c070b018098 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 819021142 1250 819019892 819019951
    0x91a180a03051c0204050a090c12110703082a120a0603080a080601031d0a0201031a0d0f050102040e0708040611090f0d0f0804060314010503070b160305040504020f0a08 74
    0x2201000015400c403c0402e101029000316041a035001c2a10440404c0c0764803507034800300030b0f055142c0e154014041400c8085e001c4603104810300c080c0b02c80400403400424060000316403c43c200c03507450f0700d2400c00e844121a950064501054440d400041c04402e0342903124080d6411501485040011520703643c0d4907455440f0781d40ca000107000da0900011840d038000d07030241d50110500c0c64103061001d141c50250b6200d18003c136049020a1400a9150502c030390002168400355010703064034160785180c0c99400030810080b0003106c00c0d6400300b20100d400c10100070440e000e1034950f1a00e03460740c2414039000d400d840c04485820101c000034400749101e0b0380c43d800c155546840030f440764034083c1c42904108146d100382c520090070103580040e0010721203925520881046c408103841300082e90b02d500c2056215400c901c544448100c4c140041c09101c1e51020b03262004501c00d08089281c82d98643c081020b030b030000500851400800b00382005115080040140d000610310311000c2890300f00d07000e00350701c0f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 819022392 1250 819021142 819021157
    0x108251101020d0c030207021c0203030426030712111b100e030f100e06090c2116050109150206010603112203170f160303091a180a0305 60
    0x88608004603200300c02c0d8115456081c030300c10180a1826034080160103036011030800ca008100726805503421a0303602c41c5800b00141d0040c091407805140c451400d06880c00401502200070050040848522040009150440c800c11050803410700b05c03140a05052410425101c550300300542c20144040c900e00014140c02c4200c0f415040c02404c11401c407920714411280300e130144070310710b403002040b0b400007104a002e00c03d00c0c60038001121707150b429645030207094484020300d512096204106144c040c4000840707501900d064070301c1d100b403c0b81c1c0394a4003448034100540841045018842ea507801440040500303212050308281ca4400c100081d034580301403068804040c0c0e61011402d007402103a00311000c030744c80d000710380100c0c0c0758a040740b040c07044151108030307001d01d550b010354010302c885282038038034618600110b54240000b00c2c0c0540010010f004040303081569238854031000813228814000060003d40c201c555a150110f0680166060701d044620b55900082030140002d07030010440301070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 819023642 1250 819022392 819022397
    0x60a050604170d261009020c0114060105040e010506031f0611012313031806030605040c1b331a010912020103090c090603210903030507240218010825 66
    0x4d5a07582035841403040c1c10740c01c1854501c2c0002407001c00703460150003500c04020190400e0341c4580307810340103580c1403080b44111210b411114004118510708480a9a0f0004a00d01147ca0101c2c2e103040c0a01d0600030307608801c020503400d4403c0c4e00c841c6401d105105121040580380e11921030000c06842110b140186030500c9114203403010380825201d09100070580055603540d4007403030f0700c2d07030b4010b4003a001034094103005d07918003548807803401d229801004031a10075005420340341009458000d10110054007110415081c08550303031440350400326515a86540030000a01c0010003004074190014010030541000318000c0c0621502215a00e0704c0c5c10107a09084c005031806040c03401b84045142c40e4414061149004000800c0c000b82c150300e02e4480840c10120019070400001c107035014019800003400082d024090320300010803600e115001d6040c02d01000c8004c0d4440007203030042c2ea0020001c51280e0329155110190342d60071020701500443e010030030140c03119503240d400c00c2c01303110601a8400c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 819024892 1250 819023642 819023717
    0x50f090d0f0b09070e1b040510020102090a120303050a0c080112060b090708040506072c0f040c05041514031f030f0c061713020108060a050604170d 65
    0x801001401e080d481039409809420103240c56103031241c031804140300e011030109080001800841c202c100100810104425030303030a09040500b4456000700e05400581550f608200d1000d00d569801c014100901c100b034509240f00502c1d14006060790070241060031301d1400c14016108461300010318a0541e0b0700340c070021426400c98149500a090b07100001c80d0010300e01c00600a1083e07100030114441c5008008607003850321395080881d41c85500e06144841c1c4030100a48201d1180300c2e1010003c120401401e00801c072045000060448500c4c400c0200422070000342088903080e00e401c202020070701307410801b10541041c02c02e031600303200003000111110848001410004240800038001c0c541144159500c05003500d1310a801c0c004d00e0080c0e00200c0c0301c4443d40c421a481c4100d2051041010101044c0d0301540c0b030303005590040010700a0382d0302c910400c80102d0251a500050401422580c603c2e1441110b884d404500b40066030400d08100600e5411223551503030204005900c3d00a10648102c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 819026142 1250 819024892 819024919
    0x603020f0d140411180103081e180f01030b03060f100f080d1d030d080907092a02070303090e0c160311070503070f0b030a0b031203090d050f09 63
    0x30030a100306402926414a848401010403692180d124483c9204901000f05090058204140d4401000340d480c0d0b20641c800050001600d110050300140303161324048015081c0e00c0c2070346001038102407202c2404206143c1f00340720a2a00d6032201440480a090400c04407480101198450400824506105c41c1040225499003101e500501c018400301000803509625144990340751004800f80302c0004480000d4032031443c91042c40c80c0c1c030202005004090503050200705440c0080003d02c0c1401e1070090b0040051070309440c0c0185590f029400000c0c00b0800c080748a6080103032201c09821003150b0154906000003a0420700b0007041d5410362030352a0040d41c0318803c000c05482140b18800b00c1305900c0c3d10741420143c204070704210f2081c0c0710040c0c6260726196011b0540c0d540e000e204804010010100400040c0c00301c9000350b8100090b18408034003612004082403070018241e8541420310307000010401100b4082c0201d401c0c90300076181051820401c901c942d5101e01407440c12500c1622854030b400c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 819027392 1250 819026142 819026167
    0xc030212044709030c160f08070605040e151203040f0b030f0403050726030f1302150a02010e0f03041a03090709020c0c04060306051e0609180a240b010c0c060302 71
    0x2c030307440c42c641d07021100d0181121821b441c009486200d40c0c40d4810004d070001c42c5c42c0780046191400d50381c10350703100c5d401c4c240340005201210401402c0341c51915403120701c640150301c80200b10308a44401100035650303185080d002002e40c07071a036400b0428080303081c03042c0b02d0003401c50907105404c2901840d103030340c0700c41941c02c0509040e8001c0800700340c452181c03000200400b558038003540c4100d00d0351030240a03940e039020002c0c0701c3d20824030300254480c00c01100e445070000d0150107028101500c1c4000142c088084803000e1918050000901303256101040070031030460510061102c21414040359400c40c14503d1490f80d80d01c207a0b000e40c0b122140c02107007a04d210f0b10200300e440001c2c240100705110f5651f1340d0900c0713002000160b42c00000d00401d9948400040740801c445409518040c01c100620b0b40c5140850b10b82d0050071040c58010302403002c020003c1011103803a403031780c0580c40c203450f544c18010b8100f13401210070b03161a050510a20801c03000100d001c039009141115a03a05001d81e6440001446 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 819028642 1250 819027392 819027397
    0x409111e030c150d0e0c010e0306060f121e030909011a0d09060f0c1e020703110d1e0302010f14130b07031d03040302031b0a03060c03021204470903 65
    0x5101c2d030301c1ca86503185410880011b04000d040400380c0300c061203440d4081c01d050711170004580e03454018642511440b41c41c01d02c044078038104512041a210094002101d403490000101590017440e440800c00a5003450700d04040e1b4014800803505198412014181c0ca9242c000d5400109015940d807100d0030030b111241e00302990f030b1010144208200d00c00880e01400540300e403459007084c6100c0080030040c060001603601c05494100a11540001c900d0042100340b1008070700c02c850000fa200070322800100780c0c1060000140c030a4002241d140c0404803049d00302c86110303680e161052210003d0000d10303003d9500c1c1e9203680e50440c8030b0a0f0b05a940c54010b81c0507000202c440715000e411200030059907580400a4400e0300d2080341628560304242000303038400c0b501d03c01040c0e40314880d0710040000039503a0384146900d034068280541005440012440c20200c200da0641d40490300c0e020511480b0284000f981c0301154001c001c8004109038031410f04040002d141001c040702041000c10140c6504005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 819029892 1250 819028642 819028657
    0x9090712051504030f021c05071106040b031315050411060d090b09160902040b16052d240622020703180602030f03041e020409111e030c15 61
    0x90b821282d0a003071a0042010b010702034000014046c2540b15a03000f4084c441d1107911504aa580c2400c2042c0380c0c9030741c014800381010482d403181d02044000f441484a4024500c00d0803047c901130400707156401c00d200350454000072603240b60b1502081000282d108402d200b8600d40c25030b049620380c09510341a000909914901800c80140141040352100c000511407140340016000f980c0f0050341c030b1900c6030a034040c0e405208001c2100340072609160100809040d0020f000c1c05c1194154203004506c4030340c0002c000c090303929800050315200043c40c410000c0b02280d102e84030540740200d49184070410304200113041c0920441c3c1000c050280802d1104810340c1122098a045648544074070700544040c1504146034080f104030000019028000310a60b000045a100082d1035640c1c6e69468404c4200e0350b00307030700e10fa088501001c540940c44038400d0030203d134803569190200c0710040040102d013000d42502e10700f20f4001d01c40d0000c02603c002c0340c022200c42041d158051030b10740c44907142c0b483e400341c0e06 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 819031142 1250 819029892 819029923
    0x8031213052a030c030c030c010503190f060609050d020a2c100510020a03140d0f020a030501060207050618130e0307060902091e071103131d060909071205 68
    0x20a00960010030321825429080102c0407a13804030340c40303400c0c151249131110680d90b154104071a00b54087d4018001194009030071606010440d0400c01c590044942c45818544020342d1041d0602030702c1c2e044000301d00500802c6410590b891801d50000d49950f0040c0501d06240840101e42e90012403610700414004d65030007104209403a01c00003070035042100b44103481c49101ca4000c400c200500201740c540e000f94050b0340316900108410380b9042c8582c40100d418446660f40e007a0b5041c0400281f02400d03407507429170340c04900b07540f4000000780b414503185c110364411003040005e011032085a0001080008080d40d84000b084200340ca0313880244080c01e220301c0306002c00505901000441c0d44580c3c4210302c01c4031041c0c05600c83c2c00350140e000c514400920820b0f4076200110300c51034001c01c4984041e58100044074074081c010090f2614411035039103c1f05c4d002481200c080d030a01e82040d80c03158810303c25070f0355801c50700e041d8401307580e6102c00d4130400c0c0050841401030001d00100f44900000d260201 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 819032392 1250 819031142 819031183
    0x301080a12051c020309012d09030e12030a020c1002031804060506040b0703110109030c03110f070602030c06152b02090f01150c02030c06161211070803121305 70
    0xc0d1503070000395000f200d58011551a00111b108e000c10b01d420201c1448030010701e40d01203461081d64841c0100000082501804012800c04001e6600e0340d028410000703050b8003035500d03240c5003040039180c000b0f1001801e2007080b0316503503051802c1c3c0c004185d650900074001180388240c450404500142800c0d041203800050004002c0b81d0542810000c08100f4825601c0d4540100021030701d500b21140305000900040b21030030500e000c20700c0741031025056901c040a03035003105058050240361020319440000543c101044070300440030103000e62075014025210180e40c01e038a230070020350000058100d0001442c2e070808225422101d000c5215203441d405410380b07489050100010720030580900c200c1c2041c40003050350034506481104d080354a95400382c0100002600c2030101f05864102c06120a100126100b000c40400d00350480304218516035107a0b140907150205103241030010301c4d004116030398810403003110310061080c0c1059106a1002c03484060001d40e1030304604000c015110740d602015170 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 819033642 1250 819032392 819032437
    0x513080a0b0a050103110904150f0c030e0304050604090518010e0a02090a090b07030c14041d0105060301140904020a03080304061d24040311070303020a0b0106050301080a1205 77
    0x200d80e941140100c41c854825900c0e044490306561090000038124844000e207107445040855586400c58030440200307248107404c503400d03c22104095808071415071501c025082a5415105142d0010703103c0020b1b5182606010200d5100c6c070991080d20200e0baa00c0340010005d042210342d007200c8010f228001e2103461030340303c15103540d0b00080f84264800eaa1a07004030750251420310608107490b5200300d103048946c0c2c6a50302603004040c0c551150050055807240d102c81245030f8030040005d010740d5100c070210051252282103482c10142c000314028201080144003401000380ca42c414014221140b00309591a0700c0420501551a80010000785021090200f005540e81100714441c001000741c49d080c200c024105a0744581500b012010300e402c04c41c0542520f9014445554458003034144400e60789640c080862a002255205500680100e5412410045132115450042c442d44c40c109055504203810aa110303140d00720b00170403041e44802806c08813030003842502e001410141248080824 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 819034892 1250 819033642 819033659
    0x3040b090c0913230a060908131e15091505041d0703050a15060c0c15090801180201080708040f121101060803030720070503011b1e05190513 62
    0x5240e00e040f501075003044c22100f051408080486441d400580c0204031501442c0c46a0b4014592001d003680d0b1424108604460031031100b400c6002015481941a600b601a00b250201c0214940141041d190002c44402100b42e106403481c064420707400303081c04001410303a02502c541c40f0f0341d44040000c0300c50807090712040301044405441204182c0b42401580e480307895910849000b10403000b121110160140701903407007000007540e40c5200d4810a01d5494903050384148044044a1000c0003e106000a10100e242800780401300c035000c0d11400070030728032035001030402003004100404000d00c14001a050000b00d01807190240d80060301c1d03c2603103080303480c010075a49001d60480f2642d0708141c800a1b00b04000800c42c6c0c410f80c0159200c1c9a8040c283d1520381c100c171800c0500000c42d204814003c209550207120302005040048104101241c1080014280c41112011950484681103603102019041000c0b00d0050020340500c0610030520f800c00c0e80d07180503168030510342440c130704408200d109 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 819036142 1250 819034892 819034921
    0x4111915031a030c151804090506040c09050f06100537091404050601090906080705010e030a120f0203040305010e0a0c0b0301060c02100507020301020304110f041103040b090c09 78
    0x40342c0c400680c006504540505035500034809420b41c200c14003e0101041c1c081030000b600010603210b2111101c8406e080024041d1156034006413482c0e00103d050000300090345030003100510b5490001e0044d49000c1c040c40840410082605d402108803202e4084174521a001301d41440f4070f01140810845e000c102c40184035005820007a2074407203842c406d0280c01e40904a03840c110b0300f2080e01040c0303e079400c42c02d000190070041c10701418440032460100300803909c0c2c00b50002074030300b06c0f009010051501000410006512501c3e81c02504098a082d0201c0c00e080d52410200c1c4160034840411190440100d20314403417543b001c0d085500e003109800d0040d802087d24007000340112061005281c450001c0e60852100b0b12402c0d0200390911088001400e01842264030440e060a19074140840e80d000b0a081e41e00c100c0c0c04507211004460351000520b02251010b6200c00c00380d804000e06070400140000c6803001030005000116200700081c0c0c03548080181e14411080648038581900340070480c02c0b040c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 819037392 1250 819036142 819036161
    0x90e0a08092209060e070611060621060c0c0d0c0f02041e090609020306100501020d121b0f090602060c04050f150a05031009090218091e0705011101050411191503 71
    0x4d0281e1900050141c0c0320301842145810a100580780700c2d00c4100800903681c4501c0c0342f00c45180922040b440c071164007404027a1041c2030071288070750340d5010701c400700d070801d540302040505200204480c240800e941802c2614525415200010220084000410540758080c3c0902c4000d09040c484002c110443d00700c100c2080c42941256426103070444030400500d490b010700c07401688a00a01045988a1072840c109042c20000008040e20402003e01c7c0070340d492a41200861400362900c850241c3c8017185030001d180030b10140c0041e04141c21718480e984100e00c502c0d441281080104845543c82c0c206100100a459400e03036a10441c0001c06021a082151110340e8800c0a4000080b400243d028035403c05500604420a0340c441e0744050700714040141143c085441100107103141c4c07a00801c2e0040c0459840402011010b280400040030003880d0700c18500c003641001c0078000050800c0f44401000f00084561403081550000c25400d2150143e000c40d915017042200842c8040e00340e0b2291014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 819038642 1250 819037392 819037421
    0x20a02010212071e0f0f030906020d1707110c03060f100911030705070312090809041a031b030f03030c030a0c0e0d020609011b060204090e0a0809220906 67
    0x5948070400203003a0340074644020b0039a4904e0301850742c01c400701030704800e1060710a00035440c0385240e613214040e003105007600c203d0204607050003d00c50300c2e0f0100700d05080390b81940752100450495079012030030140c02078148020f100320692000360111050040c411a40e1000c0c00b10ba00303a02c0c0c22200712526000913100191070f03a19228011130800780c140185c2e0302007040144200e1864642e104106c61070b81c04003805504022072601003030b4010f1b040c1d002c1e41c0c04203401400d10341c0c0c031038540c8020082103905d0707030440903424640d004142c0115100451500c1e0b01803000c240c80c5540d0400c20300400d00300340d04070a08803e5400300208201103000d1020145000d0900d158080292203902442030b5012041c0381000b950202460440100610f0110001d1446502c10f00d04036040310815030488a10003070420f000c8803001c1d00231a05000c54441403007a000e01c07142c00002060321031040c0e158401c4920580500c00c2c0980c00e180d0130207243d0004102080d000402104003004a01d1103410818010f204403104a241c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 819039892 1250 819038642 819038653
    0x102040509070908070308180301020a030b03010b060a2312010602100f0b030c130204050d03080a0b0d0206070308090106121b08011118040b040e0d031404080301060806030a060c020a020102 83
    0xa407602c508040f20994140030000c007466404c6407034208480e04004072000003051800900705c10368030203001500d4141a02e07100413070402d480b40c003090f0a44400b201024003a820a01103c13051680c0300003044110305517a015101399002582c1000721510420441403c0600c0100000440301c1d800030382a000000203000404c50943c000341c0402c161801c072460a5490341c03100c0c08200079403034101c40c0c500c42071802c050014035103965100031482080041d801500480e00700001c20031884e841c0c0c014001020f00407070381e81d80442c003d46e000820f64000c0d44400b4040089600014561407400d602c0b4001408001c25a140c03181c0340e6190800250100c1504500441140c810000d114501409010038580500c0505801c080301c2c880c1e401140c500c0840085d0b405502c40c03d10300c2e066260b80c4640c10f040610a00a40b004114008016041e1550000072011052800c01044041010340d01500e0543c2c0680c64481202d4680500081c40e0003c54003024012514090314180c819030005040aa864400e800b80c0305e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 819041142 1250 819039892 819039901
    0xf060524030d0518012a03090e010305072d0b0d140709140402090a091b110d320406170c04060c020307031a06041d100e03070209090102040509 63
    0x140c480700144500700120b2010b1000c48030103040252014500007042c504003540c1b120a052480071250503140c004210020801c5c1c94041c151301c03007408005031124960b000203651469a80303a43c0d40c6502c0c4240c28131000f21506480c07504580440303601001c0c10740c2091401c0b0349c4d2100843c00a0fa40840101403046103004004458440c485c1e81052042d502500c0c5c00910a207002e8030314400c007102d210000d51013542040990780c1aa1030740046009440e807054005441c2001024458910100040d09002e001000345202814080041c0c11101081c851900f000004040c2400da108e421150341c42039000b40c1c95410307033702c4a04411800340048030300e99940c80b00c00c40b20903e0074815255061303038140d214910410090103501e01480c2d908803070500c0a411a05c00d2364bd2902d655403032032850100b00058144030350900840d0b03e050f024405800503090b144d803400142049045581e1542c1648941e803c60306d6010109508200b441560341464002c0d101c0045c505e080420103000354003600420b032003604141c0204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 819042392 1250 819041142 819041149
    0x4080f0105220b0411010201091502040f0f12170c030c15150607140c0603040c08010f0506010e40050c041208030603030d020708030402040507111005040f060524 71
    0x865000d822851420303032502c940d1907045d201d4500311106410b642d00c03125075034002070022424000c6100115001038903541804c200000c404006d600c02601104111010302c00340c0b07132000b0680704040d4065000d9100c001e13941001c41140c0140c041ca51040c1c000400e040c5a95040426070701c0100022543c13655056841d68100030741c48801d85081707500703c0d00500200340000c1007101c0321740a110400d4216400460240c0002e08603601c111801c988422001c0020882031109004480076000c4180c418003692400d81c000906151400d40d81d10f104200050030a000042c44e200e1320014203040442c0d11040840c01d0003c1341280c40d00a07142003000e03103008006010310401409503000c2d11428550f02c40c41e1071450b2a1110103400c0544130130741c540270812401801c81c0c1984001c0001600c520f100c1078480c40c090041008807207005013080c2c2400600b00c407036107255002188404103a90315117400282ca0701c80f0f040034403010808100007441680b400d421300c60f40325007101480c00b00c54017404215510850080c1031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 819043642 1250 819042392 819042451
    0x70e07020a0b0403230a0207140a17071e0b03130c0b0d021209070303270e0109050a0f050c0a050c011d0a021005070201050909040510060f06030f02270604080f0105 72
    0x80c90b0040e000800c06000441505070001c07204a0000c1003c118540c46224bc850f00da4520003800c07031031b035008003410081010802c082c0740b441010300340e403110403a180c8003940d14517210003819031040b0720050030400c0400c0601d0807140050a0558182c0351107908018014000790301c4035203118840280340740052a040740014460058941c036641d5484000110940c2005003c10188500000c40a500340440c00c2d4a0341701d1524000c001180d008501c83c01d01a0300ca404031080407031080c0c00d036401c00f02044091134201048400b403001a240c944e03690748a00c2d19a80c014980d00480302c14044052452617810000082c2005a65000f11010042d0030701468065459100e01e003c024042101400b80f48001d2a0081c1c003540c0c0180500261102540b9006030b010444810750400c01c0c5819641c04140040c642c140304200b40202840003c52404100400724a403071080c9012181901c00b85414280c0284ca664041e0740c001e00301314040740c1d40c90704d04004441c0a01009c8400104504d055041d904140101000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 819044892 1250 819043642 819043657
    0x50a080601050d020d0f1203090b0603190308071206090f0b03060f060409080909040c030b0603150f0c040302100305040201030b0d11010f0201020f0c2d070e07020a0b040323 76
    0xb4059501c034866080c071000f950080f0058880c446d80080c2d800204820302252060010155000030f007086e0545011461658050040390095000c2d100c102c00da01751501d6000d0006405040012065a52a004503540d80f421038445d0022403e000f00080c01c50300a8201803180c5040000c14401003016405040e030340c94049139413049080840c404103c4500305948480304031030041c0200b510b4010b122010640b50721050710704503480000751030304005219011040541095040300a0b1880049010480b020144046c100e00d8030342d410500418401003030107040303030b00a50340904041000c07004000050018003085a080c2d01090820b011050a841c100700c5050080b0350140d101c0b10404040e000465251000d006035105566080000c80c90801001c40a04456002c1c40020410002e400c3e000d034a00086000f44580104000404003031400d00114030003060b550001d1624076540c2d1001012450f001d01e07143c000c2c04910300030040c031003450303800f5900c40d83e00b900e1854200c080300c0c00010030f218188901013 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 819046142 1250 819044892 819044899
    0x6031103010b1309050106080916141e0d150506061603030507030605090108070504060e09070e0c04050a031505060d030f120b040f0c020f19080903150c04050a08060105 74
    0x6124066140003d808000c2030041d1140c2c1850b00c80880204950081c1c00c400c01040300c3c1010007210103020420003115026040700c41505500c0e00c9120340b01900c52802c03180c41808800307412030403150306801d87c01c2c60000c010100303c07040589080a0041059121504615070300345400640075007030050450324901e09010048c203100800d134034214020800035046004060301c817500041c0e240d480300750842c00b81c07902d0405400c40030320340000c1100b07d0f10036501000c2160f40ca40200460000d0204521088415429210071607035602c9542c0750b0544030741d400143d480560030300048244803108040810050300344d2810050307a1200000c01034040d8940000030002682e0003e50702d00c0391300c0740403c800307141c40341e600120b4668103078800101540c03181c45500b190140c0ea19078659409504110328845201d8840150001c0109007a1181601c00300300000b504015002176a000304d510100700b402c0c1c0c10b42158038080c1720381c1842a066452640030307114107846508429000700790910003080c3c1d94120348008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 819047392 1250 819046142 819046147
    0x60f12110304022101060b27060910112d0c0904030f03061206020304020108010b0c06060607170c060402120328030b060a05041a0a0c0201080901060515040f060311 72
    0x66081100c035004c42014030182e4400a00c405086001c24000c0380040c0403144082511900e039000c00c1c12403141c2c5818154888c41c01030340050800e44924088444a07007040c2c405081c0708141c1c21040d5080c03070780740f0707890710f010310540e080d007100740b5102441c110300020411184074020410403c0c0315511501c0141c2c156100e092807011400090281054000e80300e050308000c5250340d500d003041900c0d0341d1045000d8a0160300041040308540e0f0140205024010443d81541040c62942d413103507603060000c01c128042c4400241e42802d0200d20501e40d4019031800b06c1050b0344410780508aa1100c0081d0b038101d000d900004500c07404844d000c01540c9948405001e101d281005141d808250320600140c1d1030141076a40742c80018a032a8100240100d050070345800369550b2401490381200c80d000000700d1440d881c00e05c82151020750100d00b8070900b42d024a040d00b21034490000c81130040003590300c400d0b0f002140c4055101c0c48281c1070003400c1104c500ea6041160700c5d98824043d010349440c42209804560708 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 819048642 1250 819047392 819047401
    0x14031314040e151f06020a0c06020d0f0f0512040602071403180d0212010204060f080709030b040b15040c2105070c150213090b0418030e0402160c060f121103 69
    0x4a00e80a80c080c0020400d02d0070b04801c074140c040130120a40105006800041502c020302c03446240c0440140941c0c4010a110007540d44003d10f042900201e45041100c000c410780041407084050b42c005005401c100c61140c01c05203003010080d400134074100c1d018040002d40300302d00b440100640e0310801c628078220201d1070400041001d0100c1e0401c00320791101541428400d00802413010f080641555200c0301901c00482c4006001f19200504000401c4501d220a00c00a81000079603604160302007883c01c0b07151209c46005201c0c2100d001181e40007454803402e240344aa1124181d44026902d4903480c1040006900e5042600d0341151180d0201d50a601348200044c81d0100045800c0c020348001820800d122000a0091086034480c82525443c0c0ca841c01e1503291520401482c00e1100d00441e00c0b0b05c4841c0c0e805040392000c203040510550340071a0108400951201e0741e041c40703901071754502400d6100e0002412140480c03103820001819102d110b22201c0c560721602840c10b000b01c042d01d086654 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 819049892 1250 819048642 819048673
    0xc0c011b08060f15030a021b1f0209131e060603050c0403020906010c06021204150e0d030209030312040503070b06180f0a020c160314010b0609040914031314040e 71
    0xc8540c52500546540d043d00002c2c0303034007006980075601c1581c6c056503c611401e4081010201408000116048610310703c050800054504c0b24400d12400c1c0961a001181c001401103281d00840c500402c3c20201d0350b0325256142d100c159009403401c0420002d050b180c0e80124200c07001215200c0242800700014809403420b050001ea2022051500445170b03186a82c9220698010440c4d0020601061051004124a1021812495600702400c010140000d000140d690380074008403020b065000421442c140c8090003103442c500ac12a81140003400d0914041e41e580d2702c0241c080e142d0601e820041401450f01403810f8072083d00d000c0341c0e940c454403103075103055212a0160481c103588e0340c00c01c212003128006000d13503101c0510700c901c4581c4062960804500405500031000380070b0345050a070f03076107907541c001c1500c2c08108180c0b00014801e4661400c803d54080100c42543c843c400401c84070100c6042181d0131707040c0e07101c2004000c0904a02c0b42844180c4072009902c1c9100d410503000d556803c032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 819051142 1250 819049892 819049909
    0x11150604090f0b01060f0f0f0c02010e030a0b0609070f02061b1314150301120f0606030c0e1b090a03060510090203070513080d051902070b030c0c011b0806 68
    0xa00c0022003070384590366141146005001210f0102d0440c004000403038110030145040c014508245908003140704008140b100c090b5448001d11007000404425079105800c80e000d00c4001a00b12103202c840360811058107d000c9800703611402c01240000c0610f0300c2032382c0c5940da101c499002030030181ca50050b039891410071000e201c0b81c001c9080c0044484c800c10300380100010480d10703a0a007052080741c002e001c0141070440310ba0550420400041103003030221300603440c245401103c101000300c101c1c500302d0007810a550025104480c141400715480c8541d2481c83c1c06042c014800c0d00c0107900703160040c091402390340440340c0c2c8000205003c1010030b10310b1f000203a128070a0b8600c040c0140c1c07035500e01e06c101d81040c0e0b90040014000b01311442c5155034191410042d040607001000760119981006146201d080800300030200001100c0311914001c2003118064041d05110907202d250690185c400c03500145102e451560805004003100074500444030441146c0c2e0380c1c0c600f9036940b1036043c0490740 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 819052392 1250 819051142 819051151
    0x60406050c01151706060118090c0512010f05011e0e060306010e0901080c1201050c09010c020604031e060f05090a060c0c020d060504060e06010612090f081207020d1115 74
    0x5540341e03280143c60004608001002c3c00c454084120300014000760325240c180000c0007181841034044002010071410341d6404111200135002248502409030304964034001c048140c903e1000e880000b05007005100c449405403282179075540004003035032180075100c02501344000d0104041688404d803034207201009581c4240b0605042c0d04060540000c1900b8410982c414131494000702d05004403468061071000306031002d04020b010301c0c109030034203035168800d4208540c18402011030f824119214081502c004640002c480240c118802c0010328101c0c4003180300f2a80c1c00d10300364180c3c0d1000c50701c1c0f03c1c00b030080d00c02800a1160808a030707129070080407800c00c01c80c14410380301c4195005998003034038890000d00c58100800c150415203818025602640c081021941059005021627540b209407406882d00034cd10104402c01c072400d01e00780031064103e0140040b100050f101c076160803040b000501030301080d800c503078407010445000c4500e01000100c0c450950001c08081600c82c00d60040180c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 819053642 1250 819052392 819052417
    0x3021531050312010609080c09131106030a09172a0f07080102070c08060f070c020a0e071106090f0307031107050d1a0609010609090c0c080c01091103030906040605 72
    0xc805054951a2454000c0b00d0f4001e140c21441c40140503c0340c0c42800c0b18010400b1000a1502d000c0d1040000d4104c20b00600d0a003007820703601d422906000002e501405400000b0303141559034200004000058141f00c00141c03401a40c40501054103550342040f660803504200300c6a504c16080c6144541c01103a0b222020781c0c52181d2007800b0500b910901c21180217022900005a0340c1d800c914140c0ca0b03c8205a012a8542d0048001c0298038170301c6940080d07210800385403406180700307644001031a0380b80079000741100881c40c0c000c02201e941c20030210034404800c0c0c0704456079079031800b140e0307070707482c1420042e019107034009101c0e100c0064001c2e45c0c4068510040070541d070b1449e8407600807e0a580300460240c40301d04ca50a25884407407240d04440e90803d0013031313030ba0201640c1045006801c0700300900c225202c041d6118100d00c469845010442d07486540014801e694415a0b12058082d0880c0d500543d011074a001803d80203140000440340185000b82850341840d00e8040d090b10181c00c0050080345 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 819054892 1250 819053642 819053731
    0x12010909020d0219080705060c03120901090c330905040e01060302030d0504051305151c0b070e0406060305010e04080306220507080c0726090409050a030215 69
    0x10303510550003c4c0c0005407025076054107443d121480f450407095031b0055014000810044850400100486541000049068541d601ca01d00914010403001501504501d1380480101d64441102c01d15a01c14505c104610030020792190b004030880300091500c80456030f400c508205900f4107401030000c55401400000e00c2e10f540390040b074107011450b0780d5200001c400080230b00c0309150800741d03410880300d00c0c0400c001038601402040004510f9000c8688607410303482000880092500b02101100c0e4000341c07181050404c9040a00700913005230202e84924140f400c0829a01d10074800c107412264400703111100c03904c6645820325540c0c005040107801084100700c10442800c800126a209824001d0000301c5161407603000380031103000741c0325140118041040c2c0010404642c160040c010490441103000b2080d03090b91a0117124442a05801134146044c5100748013000c103010003254028ac00303072080300d08106242045c11504862220700380042a03c5080c81100c1c01c0c902c03940344141501340c0c0c1c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 819056142 1250 819054892 819054919
    0x30b121510051801240e010c150c03050612121e040e1504050f06010e01120e0a0c030b1006091505071a16260c1b0714061201090902 58
    0x2d01c041c4000083d0500e5035240380040040c01400000785040395007250f001008108001402000c0e050f10441d00c604000248031548240021403251139102d5182d404100400c030300581d0701502130b02045809034810001c03038203040000c00c00441c80030f280702d01e4008810f1500c40a0900900307840056800300c0c10285050101043c1130720310000490003801240f0070601103e103c40d04200c00c1d20070050407a11960b0440301480001c1c0d0300202c0b014409042420044058801624842c000f043c010041c4084c900c164051303c01884000b01d1790b0720641e030050280211030313940c4404140440c0780c244142c00005d4040e500030041c1020103200440e42494514103030746412603580358809440d41519400c0e41e0a0409000d010071181907a105024201e0340e0b01340900a0b10300041e1a500041601c240b201d1030420650000310040d1100080720180207000d0108a01d4080102c84199035498602900d1540340040b0181040c5107004001d03900d50401d2641c400b507040c0e0a101c4800c0250068840032a0006502d80001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 819057392 1250 819056142 819056149
    0x62f01091b050f060a081515070309090203010509070f020a020d061b02060f071803150606180315092f0a09052203050c030a050a030b12151005 63
    0x30200d015000c88041050000c0d40c00000351550340c019481450f01241d100c20b580c80b07481c103071268010141005a0280e64806121003901c0c00c070421a9440a1509450794143d8044006030000d94041d907102101c0a8480100900300d2000380203103070307010036a0000519110300c50607822807404054410354101805542c0820070840380c0c24812190340340c85906c00da01708a146a14900d0480b41440140f8442c145a0280c040c4400d02034204001c0007420340c608040e000d15040701600a5520411210804040250b5000108041e004a10003e02030807050940c000141645e4029260000a0288030a0300c00203031800078815903604455110032000c090b00d1011000e0701d10711401d00c403560582e448800800400091a005400017002d03180b500f02801892003e903030981c0050111802d000d000030102d42070a44860280030281d08241c8800188922880c4c1e00901401040105403002d1010801020400011204022640b030050740300d41403640c42e0400f6208240e03004000c80d000f580d0041c1d10341010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 819058642 1250 819057392 819057401
    0x7020307080d0807030e031204060e16080102090307080718051009051e0106210b0d1e05010501051c12111027020a03080715020a0c0311010501062f01 66
    0x80b80201e40c0d82010010b41940500901c04885540805540f9181d040f020306201040301801c0540181d682e4040209a05400c000182c88952410791a204640c0d44a41e214085e6221884440c01307401100000203031464005044000e8411560010000103610400c8600920b8000c0c00070300401c0c103c130385c0002c0f21291442502d014045464001a040d50300969015890310181c2c001070030411551113901d0b4041c5280d00340040c2e44e2503000c1c013090200c0984001102c40444da03002170300c0044d4983c01401d0800c82032440004280c1304000a2000381e980701c0400109182206100d502ca5848006820008070260703568074840026040000840071510511841c0803564a010068903a80d102d420085a89021100046410b09414a10148025804105168950301c401015654080340b0201005000c0021000e035206110046480304409000100b00e01d061030002d0300482c0e02d00c0060002e24106008041c10b9408945030315541a400c51811001400c90980c0760781c54006213003200102c00c2d028041d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 819059892 1250 819058642 819058663
    0x15080c1303080702010809120703051e16060b030a120810080d1106090d0507080c12070b01060305090c0f0f0303090a062115060804020f040f050114091302060702030708 74
    0x2c00b540c070b80d10244000750070408041c0010703840d9441904070b400320030013071821102c000d6072602d442600c528882001040f000c080c3c010643d5a024003107880b0001615504070740d000c140c061101402208144003d0603115a150000605510a0504614001e5019813101c90300b0005c05000081c40d907950b07050480c1400f2100c43c10707000040901c4956086d0500400032150011000b0b4058001f00e90310340c1c0003030818410710400508001000c04c00c01d518480c180090a8a003490402c0b29a84020a00c3d242100110074081d000101f45000c3c04907489500009682442c0c88000e012088200e0000e0100500c40000d082c2c1c0c2c5505220410001140d41c4580c000039000b0800c6880e4100c0001201d90254200000718816034815803070440f081c070746214485076000444440e407c00441c291a00d0002c100034962249546400c541460000a1200019800303541200d0388445036000b6502011b041042d00d003410355410380b0b13241480000e00d016182800042034924402030440f4512a92900424100300f5640e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 819061142 1250 819059892 819059903
    0x2701060f03060e0f0105091b030126010507171003020409080901030e0a03020a03140d092a030f06020a0507020a120308070804240b0303121e0115080c1303 68
    0x150180c1031150907000d84000f42c101e144500c0028030b0b01841c195200003051040620a0440002044890001410140c0048041034215940e982c48551010304c0140c3e01d094040c6c80740310304042500d006010700c105401100a03554035805001210011056100040c021580101510700004010f035518030803090414440d50405803950501d0001404031099003500030703010341214400e4400684c1c04508007180b180d05040001e0080394900b000401409102a1110114941107824007031007951844d0b113100c80b001c4600042c402c4e01050381d10120403240d100040003000c4a00000000070007540240c82d4900311071522034140005a00020442d1040ea03000030000178085481e9401d01d94807040d80e0340d00c851982010400d0b8105641e80340401d0300ca500c0c5940010000c61144a0340008a411903c40d044c80101100d444406030400e5541110003075441e80e40140307660f003403014455070100380e0074100c4041c040c140348080081c5401340c17000480200207500c449420800c42c1825485040000c02660003031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 819062392 1250 819061142 819061157
    0xf160b3f06120a031b26120702030f160807020d0f110d020105071211010606022d0c130e03041205100624180b0a120b0f270106 56
    0xc1030101c02c40100800c4040c0ea004800c003040401e42015100004408180807040c42c101c0504248110701c2519419007010741c900c00211010030f0100c000782900b0800d5a400050711384921005907940c1c032465860380780c450400e110301c0c46030f0002d40d0200c5107214015018245009c0696000800c040c240c19011942e030000c0041070814092802007541c2a440c0c240c900d611070501c00d80020305207004180e0018000300c044101a4445441801c00c4112001c407100240314a544842020351101d19070a0b010448800302da440c07843c0081c1840b6102da868040340003400010501c40c091001241e9400205d81c502600c43c0c4010703030729100400042c0300400c03420080d61041d8035507140880c10800d290300320082150600d10b0074411900c01005201e10f4a900b03000d01c000600d83d0311400d9510814104410044d1004858006581e10640000b032178071070030a0780d41d803505001c04940007040f1400800c000c1d07004520011400c0d050704112407112100c1c00002c0130700d20952082500240c40c1d03a000d810000008668 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 819063642 1250 819062392 819062401
    0x1020f120c04050a0e09031204030201231605090d050a060c4a21072405070201031b0e040b18060d0609050d020f160b3f 53
    0x1403040c103a0300001e40c0c14110380303400d1a0000045120805024481d00d6211042c0480c2041c44c041040b58200e19508140034030a14180c00c001c2d008101011041010f141d60b1404500031040c0082d031584030f02a100c0c02860005022401141c0580206003a230ba04124501541e1000c1042001004510341c0708290204400c213410000400c880c205101c4001d00d40781c11181e0340090b480307440200d0440000340307440020711400009024a001c601302d1405400c07500c0c80b00c0c4490700d80c40343c0340c081400d410716004a03011243c3d00e02e0700f81d0032401842d2a4031346002888002c442168071480003041c02c0c1e40140f42c080740d00a5043d9222805180500000010039000040403405091901030864440800c5510000481520702d81c2400843c00a10041c07056001429950070090258040c141c0c00d0f8000c1c040341d000c40301d1700e9400b079540c01001444040c580310b05a0580b03000c0c640100c88909454060300224140113042d6001114004c0504035000800c3c00c085200104107803c0c00041400c1031289960083e5061 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 819064748 1106 819063642 819063667
    0x70b061504290c19170a030b0a0501090b09150f13080115050d030c03120f02090a120f021201090204060621140105100302040801020f 59
    0x802090218140899401d4080c400d40044600c0d0309911a40560001d240100085030381c2d290701c000c0c981c80920b0711413408020a14850060518605c50f40c1614a030190003000507200041c1d5100c014962500d0305400d03a8006000c2800d01c8551a420000b8541d0075104800d0090700a0314002000204081c50a0880e072207004110b510f5034681000301281002c03880c0500c1580e00642c240003045c00c403441810300c0e4100b04e4400411741b011040265400342c4800046031802c2d41400310481440c01d80b00035a0043c2041010700600040c0d85040b010708110801155411481d1101d0b0b160040900068143c82d090f91b100b03404852100c105114a07441501420600300c0094200c2e007040d0001900b190010a032009401103031940b03402c44041c8110000480302e6a0b110149140d042c0801000702c0d0401581c1210703000c03158a009442c1680320a241d6081e40d112a440580410001072128403058 = true := by decide +kernel

theorem cover : BRFrame.Cov 818884892 819064748 := by
  have h0 := BRFrame.cov_init 818884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 818884892 ≤ n) (h2 : n < 819064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
