-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0366
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:26:30.918984+00:00
-- url     : https://prove2.me/submissions/7c10f42c-4b5e-4873-88eb-df6a5b4108f7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 65647484 ≤ n < 65827340 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 65648734 1250 65647484 65647511
    0xc06060501031b0c060b0603010e011a0f031f030606080102070201030b030d020c06030c160309030203160b03190605150408100b03030d0b01030b09090106140a03050a0201050a0212030a 81
    0x2002508403074181800c024440308865035074181d0340324424440c506000380b81c0c41420a00c00516202d1202504840300000120b1103480b03684410381210a840040b10b60721401c61209039890107201002c40d07100008002242c2c0380d8411107207a948900200c01d80c4000160749a4514080314150740c841d01a60350080340c040150768140c0b00e41d414030310054002d418900d80c0000000d4440e0b000c030304460701c5090f0100c00b049403820303410182d0380d000f604c81b01ca90b040d01c010350801230000e06442c40100e200344541ca14030700310740e81050440802c807211000000c0c11500da100c0e094034070303032042a0740c015025610321000940b603441c0c401800c910b200c1030110300e03555030804841c1c604185480c4800080e41c1d040002d0000176460000448041140200002030b400649000481c0601004a070349a4048891010b003c800345041d840b0700c0444440c54050034802c000f43e000d1012020513407001400d43c0d007260640c0405540a50000c00801e000c1d407040d80c038415244082c4080d20307081680c0c0038464555031070301011901d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 65649984 1250 65648734 65648741
    0x60501020f0a0506060d1401090605061e0f100201020d06090203041b06020304140a031202010b040b040c120911060a0c050613080d0e030415020c09060a03030c0303180c03030c06 78
    0x1c410718014041c840c80070385903642e0b5800d02030300d001c0c011031181c0b00600c180228040484c407005079140090047c007005040549c081c00c0306440ca18440c42c01a105550407240d050b070b18102c0d01c08003070010720f4080084c00030003441d62481440102503540030402c0070b0100000d440b03000c000d000140780042c0c40f82840d040c00504000300707131190700d9500103011080c00b2564000051741c0444040d0750003460100215404a00c480403541e200800440a24031001c0900d501034001e0065400b090381d082003940121030030002034a80b6500d0b10701c049449110b000456001d9600803c450601130407084403806240d20100314603a000600d1400010345000c44a000c200c0244052500030700407640c0116544225141c83c6468802c10805a403495903500101c11110310601c10f0342c00600d50010701064808a4140c080d40700e58600c50400d20231156080007403224644100300300c080c0c039010750b6104041c081d5590150024107000703800034440c00f1107454000005903800c001e00042c61196807814140c401c61300e498401e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 65651234 1250 65649984 65650003
    0x804171315020102030903190c08030906042a03020118080d090602060f1012030c20040f33050d0c1503110d0b0604030c030b0403080901090503040302010c030e031006050102 76
    0x46900420070303c06e803040300206440140303900200345402507401e054240c511301040100100070050200400031250808a0060300c590700580080380b20503010100000c001c0c40c0d003102c4c0341d1100d4901c0c8013132015502c950108250a60142c41503c8040c0d19084554540070b078002140d0700151040409210540e8107204490300210b04c2d005040c60390411010071803840445014021340114010610317014144103130035420385290080364141c041e0f0008d00d1504002c0706130724002d90007141880c10920704110684690b862603088414014029242e03071450003d001980c10341034600d00c400d10380200d1155649600160746074401c4000c50a02407601c072980e561824103c6001c0c050500c2d0a0402907510314900440b003c1c200c041400103040001d0307000103042400b4070340001e0030303120303e112010040092070111140114003980f00c801056a0300c10341c1034282e50b000400200690000d002c1000154010051081101c0c4642059209009a00c0102e8074101070f6003030802880f81c803660300704400e58051260004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 65652484 1250 65651234 65651237
    0x3010906061b02030d0807021005010803040f240311040e07020102130603050f1611061f0e100e060402070203010e0a1101090b030c030a090f0507062604030804171315 73
    0x80e42e012580000703840d0391544410200b401007403400580128800d019040c215151151304020650715840d403240d91b500140280040cac8000403d02107403958030b00b0b001c50070345a400c0c091000003001c1714000320068580c1c840d4801d0802d40070f010200b072907079101c0a1036104086d0399000584802c2c55158814a460281d030120090524200038040c00ca002c0d4444103a11004002d26410039407040213003102c603030420441d490313807078001e01080c000e01d0111090003c3c0e07a0000350000c404981d486000c42d1410102c01c0d0350f0a240e2100c10501000f508403d07030170352907000e00000e000500303080158000c03a0945000c1282105950424400c00c01000751507185050781903020318100c409a410400503075074512002d8529002c000300840000c0325110310360450001145d11159540302c1c5031b014030780142d0b030b20801e0041c10080340c1729a4050422101e400507020b150051040321034066222510180e5030100d000c0c00c01d40e0012800084030741d145c00c0d00002070010f10029018440713214600030000c0b0980b071090400c0710 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 65653734 1250 65652484 65652527
    0x30302030a14060303071209050301110702030706050c190201120908070b0f0601120e0f0a050a051504080a050306180c090315040c05330a0806030a0302030d200301090606 75
    0x4d40380002074502107903202c00c4084080d002d0070025514120a58070040d415801c6c52f07802440c40005e000a451102e109908886503c1d4507400d040c0c0745802601036210055010000c10304d45c0c070901c010800b4149006040c100041510070401c1020383d0a0b180c0180c0da1030100144040800090440255100980203a0500c250407c000003c10f26041e0003940f100721a03c62148510126061000c25100382c800e00880b6002c28440c541035446000c40c0406030382c14050308240381042c0c07a00300701e29880752703601107459880c0800750402a107013074001031f0150740c205401c11140c00c004810015214003c42c0345051142d11100c0707e8080515100c042c45800300701d01300c113006010002d07840c0746452056400488800ca00c010000c0d4100d071071038958407925500076001c445041c6211480d240104018003455482e160f42d036955405150780c40706a504000c0c01a80100b00c140c0c0c0c00c20b16948540c0d90f035041010710280601000d003842d00c05030801c0c0c00501909030340d028204041c6420000f5036402403c0c403108013 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 65654984 1250 65653734 65653741
    0x50a111504150605100e13022a06060a05100e040c09140103181103100207030518060306100e150c0c0102010b180a090201030b030d081501020f06010b0f040506030103030302030a14 79
    0x11192045e40c910728041c065041141720040d946c00790100b83d410b12050301151034042a6001e1414580e0340c0103007032400412a0306003110040041f4000c1e00c1104040c050310012450316051181581c08030350b42d001080068090b031070350780d50340d8040e00c003c41c0400d580380902681000002d1444e02a400c410074180740c0b9009c800d000200581500d44c94150b0401010a00e1204020100b070070040854070300104540300207691420145c1081c00b404e41c07403841c1007560711040b2206083c08000c0c842510125400101c0540340702646101c1c408018002c075014000c80301d0080081c0707a511207900503041d8440b8540200c0c50501507940e092003400310f040e03011070740d00706500d24401d6042c0b14000c024000b920300701e444190701801c1da40aa000024680c5e0050111141c0010100300208032020039a00d000c50344001200c1140c20b907100081c4182c8000303400c8040c0980f0791034005506d4583d4030070009580500d100b030000085681c2d80c14055402507000740c8003d130749c9140c0112040b080342e1841280e00e24500603181032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 65656234 1250 65654984 65654989
    0x15010207150e06130b040e19060605120711030a050711060301050d080306031203040b0a050a050c16021c050607030e07030f020f01030e060c07140106060f050a111504150605 76
    0x1c1065124161145542d413907186045000200706038014541598001600140c800c4c124860144580d80c00340c40c20040960320607a00c402e9030f04510a003030000c0c0e020301141e1000c001c640009038008a80382400454580c58030019802c45d00040940400b0410126080c0b05111800340180c0015408807200c51170341d0304000000b40c2210340554050481c1201100160070340d20200200364820035428a138a850786424581414601000c40300c3c1400ca60404000c200004654051203015400600300f00341414800e02002a9081d4440010f07a40403c00071704001c0d00031402000c0c1001540030380040c003207d00d0882005010744241d441007111680c4100c03070030004074103001503c00c3d00c658100c4802180c99121b500480c040c1142e0488141b00c0e004401c188241482d40c0f100600906100b050300714540c0b13003c540c21508a40180c4074100114140740c1d490444203115100414600d40e007400e1000c0e02008a807415407415411491500883c0e00c184148028400c0c0d0701789001d00101140c40c10300805050401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 65657484 1250 65656234 65656247
    0xe0106090b1518030a06021902060105150a0e06070309030516080a03050c031b010b0a0518070f1404060906090b1306030c0504080a0c03020108061f12060302091501020715 75
    0x1c180c40c042c0c0c0105071403c00c2800d00709074034031035080102110200c1000c0c1c04d01c6002540031007501c001c80704880d000031000c10300110b02d403412190300500c2070020a4000c030050900e94004841c1000b0031580d101000410b1762014041c00500307019594036095641180b50052405170440150000e18170015810400c0050001e05d40c3c03200c507850715146442d034080c3e03540c0904d903001e12100d11010420415005007022015030210000742070813120030a01036036a00034015000c072403003202c16045a03140001001580585041800c4078168a0024000c7c89804500c01407034005811910007da000c80080205560100c1d00d40041c00d40c80000030b00e0040d0302c110900f10b0f0038081c4101024103031141c152890b81c9010350240c0d00101040c00540c0c2e001010303480c2c84140c0f45082d010890100d14008041801030400d1894a400410301c7e11108000c021446000c2d1041d650191446c44c000340c4901d030100058448429050041400c9000c025000318500d0000e030400401da00120300c0d600860f0322071081c0c9503001e42c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 65658734 1250 65657484 65657509
    0xc0909020d020d180203070e0f161407031710120204110403020a0306050105090a141503070801020a021e0c01050d0b130207081902010b1c0c0f0602030c010e011404060510180e0106090b 81
    0x504d111804052050540b000302d071100c80d0b14011040402e040c024036130085083b4030140c81640b0303002c50595440280e0f0720004403a020b0481010340b080c01d10030060034143c0c441000c00c020302c45607509081e500e900103046c60400c0c0d00111405622480100802d0a1032000b0b0381e00956000c0d130600450002c2200003007100d80050002d460724518a2240080b601c06000d50350141c40c1f01c0d8000c1d5555080c920003e07642d2901201b0f140700d82d519001c21250040c00200d414200d04005030740d01c51819400d002c10300c01428440c00e20a60006880c19904d036514007910052252520070411240c0310b10711100c001513641030018010003964106015901581d4405003481050703031051441407004202c906105042008940210b482034102c407002003515600000034180080d080c078002e208807816280c8030303402d8503ca00e040c0c02c4105044804640059616080642e0040700e1800c0f542656a9034014244108400c0b0400c0b0140c507519124244804c1c001c0c000c00028012400041c851200700c80c0100d5040389907003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 65659984 1250 65658734 65658751
    0x20403030c110d06050711070b190f1206060c0209060f0604061202130e01030c0b0f090402030406090f0b070908030903032b0e0d0906030c0909020d020d180203070e0f 73
    0x34018026694444803c241c100d0b07040b101c00c102602c1c0c10031010f8203809110441c0d49491080000005224000800310f601409016540c0e0410030132100d4180c0710140c9200a49061000385d50b1041940c1c0042c1c07042034010441ca0352103c00c4580c041c01400b100c0c0c2c002504c218040d4096011009980c0c0364081120100c81c92480e20102131210b6080040080c0210303441c01040d100d6028001540c2d51008070000d0580c0e00070032005942d2903950b49501031612610400d804407240602200b074852500d41c0c0034603032007405280302180c51481035550070640128024200d0f5031309000e44c00c0c801201c1c1d21501c51000b50403000c0c0190700d003d03590300000b075590190404018a81c042540103544428a085040c007442d600c00302c2c281701d211191116151910440310400000a40d030f0361001442c10f04c607001e441c480c124142c50300440c060034004050080e5000180d03a00c0b125408100701004c80959101d444002e83d100900c44006243e00d104141c00c103501076200001c09241c0c403052082c011220155140c000112 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 65661234 1250 65659984 65660003
    0x60d022a100515150d14090616020a030206072109060f0b0103020c030412110303070b0a050c07020d120315060305040203010e03070c061805100e0301050f16141603050a02060901020403030c 83
    0x80b800700c00c5c003801d1075982d41c051584644042c069401800104a401912050100c12500d00c40700b400b01d90b40d81e0b00a00250040e03001e1800314140c580a0007400301052003000a020303030741d01c45054032001d4070300094040720540c0e91420000403050541c407070001c0c20707142482c040d40b07003241d00c1405660728004d501903100100020b1400d40100000e0001032203c000340501940d46400e180e060541c10035004680c041d039900c1c10308002525044104040381c2406a00078807881d00a14151070722480c45018008403c107159a0b040c143e440314403100035410003440207942c017040780d2600303205050035079040c0160523956520921030724001803001d80f4028155013880c40c00d0f81c82400521110b032050241c941c0410b400030714040442e0030706640140703103040d010002e40003031249842c4c22445400d50031040301c41210389145441d00f0b04502d4030503412014022510740c55035082014040701c448071035038034003002c5000c13640000340002c0b8903405000306544410a036008509003491920060841c0f014154001c054803034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 65662484 1250 65661234 65661247
    0x20904020903011404170708030a0c0c020402031518040b06010c170f030406140f01120f300809030307030902040f2f09060d022a10051515 61
    0x125a415100c14601c020300070b1241d4203041c0c643c100e02180545095a01070301700300d800038007103c90504460036a54003a00e00ca24640d1810307601030003040e09001c05001c0220414100c1d0141e5079500103140901040300510080c40d0749a03080102401c078001c09890b06004400400c00400c840c1122154004001c1c00d0084026427289040c4090181480c6500b11302d01020844042c1030303842001039841207124a0040150075003202d0101e014032001ca403013200b801990b030010301108a403600103800c060b10400301c800300401107548030071210080308407000050803100310b200b555800c4641011805103450406699a0600d0485c01d9201e220003000740e81807584441c072410454550307500558144807440401c00a00384c40261851203110b0b10300b03000e00c0324010f031000c4040d01b103410001c80307803403040003403070703070b80351040d0041c1200180d04031403600d1110588075441c200c02c040c0c00200f0091029001e402a001c515101c004034802c80e500546112200b10103030403004010f450340e0380600010710a00c2e00c11178035081c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 65663734 1250 65662484 65662489
    0xf02040b061204030909180507090209040906020301150201051303090b1c0f0501080d02010605060301140d08030a0504120e03060609042105041703160f1e2009010503100209 76
    0x1007035040b03038142c0b02c400c5003c010030f1561009641e0305850008400b4041e445043c10103229070f00c0700040152080d04211020046100c0c070b50700419807200081c2010403101c0d40358903800c04a8000f60301049000490403110900c240d8203205907907014601d00d00f48940700c1710b0344e00c0c0106049580d0003001c1c00800005100d405801e034400c0c00305041980c0210910a500064000270040d00b000c0c42000c1040c400c09503010540d60040c05158242c0e9030182500e401c41e0b28000c003d148003480341000d5a0000c000020f40000b041010b001903124100d550008507280c185894680f1600780003505607070410001946011841c0d60210707600d5048802150480f0761f9842b1418103a0b08200e91014404010783340c82ca8842c14190094050022100740d03251203c0488500310103140c60744580c0c0401c030310712401c2c40c00d040f00040d80303403551814003406500003410310002c00b51004030040b120482070f2402212140c1c01c00d54002507108880c1400019507010806525041c0400c1d0764801c0c014504001d1038010420b0284c0c2d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 65664984 1250 65663734 65663737
    0x90206071202011a062106040b030f15010e0601050405040203181f051b04050d15020a080108010b0a08060612120d020a02070801021602010509040b0d050102040914040f02040b06 78
    0x3907003168011041140c0d034007029008105820028201d4541200114100c0c50140240c400e82d80f90003924100859200c0d80c0c1c130300d80610080c011030b0b0007580c9400c010a1600c082020002d2125901d00070501c2400001d400041c513041640711500c2c4116040400c542e13039901400b56001c440c000d4030301580301d07190030000382c820700d01280c00d4803c148a414019003030004203910030369411203002d07000c01154840000500645030700041c0349401c0c0f04100001c00c101c1c03e011310705d644200c0c05511180b8026481c07003a050140d9008030214000940340702e0050024060a1181c401c2d01c103001c40c0d02c485140d00d050101a121000104074601c035903180103126178084010711910f08050041170146690303a074600145c8000350404030300c000041c45804404a030002051080f2465065208600c0140340380e1503004494076070000b090701d5005501e51010741415280d5844004130f0318401c0d0005a221404d000741041102c5441d60440000c4070100c0c02c0c4004611403540c81014544c041c1c0e03000c142c0d03903651400b003080c6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 65666234 1250 65664984 65664997
    0x1807030f1e150b090405060402101101050c0304060c031b0311090414090d08070804060c1b050c010e01020a0c120f05060a050a0614060a0320070f05060c030c0706090206 74
    0x44480d880799441006000c4640035002e9100160401110200000340011030500711001021340e400500400c002d80f801d101000b4046800c2d00d003400d00d90074144041403c1d16000d9480d800503802c08024081001058020032400700201e142c05c202e105910760400000c598860680c80074160380303040c1441d0f40340c00c1000f2070312000c501610602810108100288514800b1aa0030109000d44a8804d25036881520400d000311101d646c0c0340d089172620b4440600070003800c00343c14203200007000900350903000c0c1c0d000030003224080c4001c0e00f00c20030a08005059401d5213200f06045402005440001841e1229105c00f60780c480b4049829030400d61034000b90f481c481e08006090341c42007004218496413283c205e28480c1e00d0b200741c18003009070360300407102402c181803001c42d5001c1d00c03d02c201041d60780b20740d02030060846581c0c24245000d503020200400c80d07101a40035607902d02140c8080e020320008010064020150322040d614515011800905500603154014600c0c0d4942044070155590311040e0f40c00e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 65667484 1250 65666234 65666273
    0xf080402040b060a020304030606050d080f0a0e0d03020a02010f05040812071106031008010606210e07030803130308060904081c0f020d0f1b08060f01051204080a081807030f 76
    0x142d13202d107920b0295803500288003ca601d203052000128680c185030030540b40c1c03c5e600080701828842304144952072500142809420480c484000d10120780d54000003040c668082c0c0c001e403040540900004280d10009507000080c040c00300010800d440300040d411850010640341d098440201c1c3c50095003803d14800e40560194001c41442511410340d071400003140c5400300208a81c6944040075102a1101129009100e0420901e101ca510383d0790400c4440e2005030041c0e03a203264880c0c2d034601081e00240c41a4a8108641907003600301900441c010390046812a90100b503850b16943d00d4106220340e43c0d08000803036400000010000044d0441e1a0070005002c09640360214203254800501e001c0c0862a41141000c4058451031508000c48115101036543e90701c055442c0014005080a0707901c07414104002001150402c07031142c02e8660149105001a50307a03008110301c0207085003006400340400400d0021080d0b84090f000501e0401c59900444440c880301c1c0c9030400a00035551001c4481 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 65668734 1250 65667484 65667487
    0x30e060a021c05010b090405090f06010605090a050114040b070c08030424170f090a0b0a020c010e12190306080109030c06050c040f181d0a05100c0f080402040b06 71
    0x10425625005080355038031654000b5058086510407405660003171284400c009010442c1e0313081c40c2410742100754400c91040c1190860201320015501d445d0099008030001040454480900d240c0400c8a070002d040c01d181046005e4907860b1103214070301ca5481403101210780024440104514010841e0003000c1e00700a0b2a12903668000c030710240b01e07a4605100400d4030605070500903900401c42d003040e00403054500d501d00d41e01c80140d00b00c0d000c806407800700984134800e44a000074140c194441c0c401d142c8600090386440708000c01ca82502c3c10204503100b80c0c0c0105151030503158104040e203030100c900d8031981410040d420410307002011140c00054030755003014004818182c01951a1103510712600b000c1000c0ea46205000030b01d805640108400b07415658410800414440f10b24590151400c030005640e42510402100c0b032a04500600c1d0550410a2a003003805801d0008000325815107109001c42c0d140752000800662884608109100f840e001003410341d152135010030400c801c00340c03e90303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 65669984 1250 65668734 65668741
    0x806010e010602060109020c0c0d061509140919060c030b0a031b08030c07230d050a20060306040c0207170c0901080106030c0605220b0a030507022803030e06 69
    0xc640300c01d01036240984900c0b070000448100d94400c444011204101401c0b08000000c10800a0313500103c00b0340d0031a03210303070b020000260390090150090100840008006030f1030802c001d18008010020011500011980400200815500d00383c080d889030001407150500c4100ba4002c012084c2103e402414003200030013006560944a00710044400026441981c2c60540d2540c034820786e103400792130783c00c282c8041001c0c0401d60302040c200001ea40c10380b03001c07032804d801140e0980051358040c2d903079a100e06404802c0c06110344003442d050a00c20f01c1103080d04000004244540b00280031a80141d0b65810004160782c0300340411405004030b0010184601b4001a18540d1030200160843c4581c40c20400002c2401051040c4012aa4000400003010349402c00075a455000782ca281e448401c1080540c40d29601c48001b00d101500179202242d860340d8041d580181116401000c103025503101044040c25200f264110214000881d07071190409101031400302d0240c440030070348585a10030501130 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 65671234 1250 65669984 65669999
    0xc0105040f02031006060e060a0e030307050a0b070906050304021c0b091b0105030103020306040b0910090614130b01050f0411120105010e0d0309120201051903090c090603020102070909030207080601 87
    0x14058981e000f141141c078409100d480031401c880d0366125030001b055550800c4012410800c0240c500d1400c282418440100d00101080c11903000a034100c41d01e400c422481c03410440014582c0d03070410818549080e80a041140190072844080d001078841c00d0910502001c0c6e00140c5012400d050340711803a0b000c50b050030a80e0b03d41e10b070300407614146803411196070b03581694843c0069074100c03a0020000c05c0b154a81e5140da400f281703000781203004e850241150307241d8840594003c910f4041e100c3c540000300d186022a2290489901600d500c00c0051413101c87c07404140c0c09510181510b2003100c120b41380c0c0260000190090101c4a0004801e142c0451000d4a42c0008041207040f2003080e2121003c40c0003220411200002426004020600c0400103004500200551070f9030f040c8107041103868512550f0444441c0b81c220100c01c40000d888101036030820002c8403a0400421804500744206400e41d80086e445003803c2c0596001c4942e260b2920303007858420040f000c000c09e244410380b00a561903164 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 65672484 1250 65671234 65671253
    0x12020c0d12051503030904050402040b060307050c0c0108011508060310060f030203070501020d05120c0720030705010e01090501030b181614040302010c081b010509010903140a08010e04080c010504 86
    0x8550001e0391500d00003c1c140541103084181d8048010091071405d000302d0204001040054001c9e60400d80e07500286445440320801103000740100e80783e050f1181018200e0340e01d441603062040341080720003001044540c262481e2100f240c42181050b020640c1c50501003464043c092800d0100d981c18510300180c600c00055007241502c6c0250141c410244e04d410041e0b070399440400b9100000b034420042a01d0380e808880e01d2a402840e81e0881ea0701e400d1151311500040c84401d00502d20944000d0907089071427a0800c00303500189001c0c200061b00301458400070b4240b5040740b05450606403280368140507662003280340c083ca50501c149140d02424017003c500c1d50040b400d610503020500300b60070124101c40803410348040b00d605030b45025800d1801d92f00d101460300821102801c801c01e0348400c0c81000420b0040ca4800c00b4180000204d000c48c50400903d00b10b10001240d04c1402c04110030110075600c215400d0540303c02e6001905540c40d80c1c5028029032168400041003540b80c1018081048000c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 65673734 1250 65672484 65672507
    0xa050408060a020301030c050d0602090301020d02030609090703051e011d030901080a0b0d1e061b090b04080303060105070519050705180609220c0f06140c0a020112020c0d 75
    0x80c21241c4641e580e4520004030b120a0002070001c6222031303410030070742c50715240788034040d4840d50300542429485400300b0f00b683c000c045140000c030380100c200311540c00c2480340d03284e103c09504d0090002c607141d500c40b10b0715070600c0001c140c1e000e4401945100b5048094001c0c1c1054100a5040d034a900d038610006903c0790000301c003490000b04030b280441c011841c41c0c0980c0000141c000c050603283c50881d5030301d410034200e1140211102e8046101c3d040130a425124041907042104401c68800b09000e03401400318032a41c105007003910703003488144001c15001042e29405107080c00c0c030554505041c10030520f41010b0386060302d0084c00c1c0ca1081820020040340020854800b5500c080b03191051030500e0301584811584140c0018100c0d0024050008801c03620f070484079a815840c040ca0f0094490950107074164001c42032030f404120041000c17685c000b07001603065855009603400c0c11041d509242d114414100044e0402c450b80311260f4142070154100c4290500c81b401700c3d00c9880310650701400004596 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 65674984 1250 65673734 65673749
    0x10e01091707060f092403110304140c03010207030e041107050f030c073305040503010f02040e06060301030b0106050f0d14150303041404020c01060b0301030f0b0a0c0c06200a0504 79
    0x2d501c00c41c4c800b0b0054080d031040e104840c0010010f0550800402d403800d6072162100c041549626402180e0400035009600603030080182018006441d0300c021b10b0b000c44203050b107000343c3c810081c0320f010a6209003104400b0400312004180350a119050712140e000c0d80c080a86213000b9608015030343c410000040042c0080d060650304038030766481451681d00d6412810000b040d10910310b816103450003410817001c0c85030b141030803800c2544405c086400c599803240c21000c11540080c00703010800116520541c80341040328110b1a40d8110303a543c0300742540610410080c06804181c1c0340f185c01c10f030703410b85040041350a01002154040e14000414039401d076810790140b10b03001890255070401008a800f5288040149590210844188002503200201000c001d559540003c580100d807840150700a50090407100a00c003864103008054401c090710048100f1300e001c0901180c4c0c0d81002803022100c1e044440010401c5844e20341c50a9803689940c86582c058000818410464019001d80142d4509 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 65676234 1250 65674984 65674997
    0x209060f040e070912060e0106031b0305150c040302150705060a140a1104061409060c010c11030a0801090504020d02030d0f0f11061302060f040303080114041a010e0109170706 77
    0x80305410390307025441303004d07024a06094060302c3c0040f950540016447d42601000000c0c000d640e41c46030b00e81030314078841d03448811400f61410410300c24200110401a903800010000d01c0c00d01c10f03100c00d41c030701c11480000d0189010039100b4240d1190582600d8410340c0200c241e401524048a40030001c0c00d21155000c0071514900c04240c40c01c8840c03007841c0400100c8039403d0310341414440c055621040c9105040ba00301c80c02c1007000066140c10028201849440740040f031019180d20f000360034510a001c1e41410355105005080a0990010340981151f440c104002410348660020581210305114080c2d018031400b012a000207500c41d039641039050302c81d550112801c400d000f04540c3d640140208504a40c00580880c0245c040d038a04800701d0f0784010059840d00415104c0c64085810552058000c00d4015004002d4035944080d40400d441e0200c908006c0503038071016481180d0340f5524004d042001c6c0c81ca1130b500c540d0140710060b0140118580c42c00c4601000c1d10140c5e41c1d00302901900b00003456 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 65677484 1250 65676234 65676241
    0x2040f06110a02031005090705120c030c0607030503190207020d0b06010809010204080601050f030708071206060b04080a060b04020c010e030d0c0201140a0c02070e070c05010e0714040f0209060f040e 87
    0xd01150180006a00602034241043c5100c19003000d0706c8090700ea5a0030f4000d1240000310740c1c0c3c54418810074000ca29019061801c1c0010405090840542805000328800c000b9a0000381d0300c00700707c982c07040c070300580fa5840000d9428040021f0080d480020f4008440f040e0744001d008a84900c0c910440d0300343c0e240820ba0b0364844166080c3c0c011417050141d1350740408010300c414a800364100c00508c2c00034048940d03e44d82d403a20103180404683c007115032400d110382034100744840c90007007c0c0501041c0500620b024a0f103011280c0d241c00780342c8043c180315074a076040403440c0e646804075042e040c2124024440358401c0d03540603032a580440d010700c05542c80e111024191038010701800000c2144c3e800c030a0071940d15883e90402910a4000401c1103000302c2d600411080003004509006108966442c2c0d4200710b103241260031034007803046265050348003140401200ca48a800a1400c80c13044d07a01040403110403c46c94040e00808046542c08400412100c0302c00c4d0030b078009801107070540ca983c03416036103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 65678734 1250 65677484 65677517
    0xc080d0c03020d0c08060f0a050a090e12040e070905010c12030504020312030c1b0a0206120705130b0a03050a0509250e010b03040b150d200d0605010807060201020f07030e0303070602040f06 83
    0xe140c0e1140540241c002b80d801c00110807550301200711017072001e0603248424aa0610604a03500036084a06160941d2040c040d83d203503c40404405444c00303081c054005403440d00c0f01414034050401240401d6201c00000701103450500010350590380074040746459003407040b0f10290941040c40c80140301000fa45104101c00b000241c3c03060b240b03401800c058500600501250f820703203002450780d018800100702c400c14a00c100403400d002840e804100d0740d100c03c6440030041c03d41d20050300080c6181d01b0322040c00b40c0b00e1000b01d001e2207080088140d4a0401981d20341041c00b1100c20350000c2a42c3c4104400087c4005806004510881c403844a14060360b5810f0750030b4a1100901042075000107030701c0162800900c9000040004035910205420300480200c000382401258550842d46103440305d004200c2c9045c208841e07070103003c0310300080d030030210205004401805441c2000d0b0820000040d00d000f903032400d10894445e40e8003c0e0b800d6540d81e48900d41c09081e490755104040c00030300419200b00010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 65679984 1250 65678734 65678749
    0x2030a0315140105090d050609070e0c0c0705100c0b0a0606030b0a0806060108040c0509091c020f0a020d06060b0403030c0210030506281805040507060c080d0c03020d0c08060f 77
    0x1c2c0c402403000e00010750b810300116072540001e148141c11602c55008803010820400402d0712aa202c200140780b45420580140d16254000d80590600c55041c040301c500300e81d010540005480040d50042d00743c0d150080101c40d18540c40c00c0c0a011856141c050158490712900480107885103a1000d110120504083c807501c00035503c100f4074503812100108291798862548160070500680d0482200e42d180c3c800528000429038000c034150b032003c1d0702551080219503140c0b840c81c4860016142d5403c0c1341740d036a070f220142100e000388110b40c285100820000349a0110b80034160081440f0b0f03d40c0e0300c1740b4000e810f00c035455405034443d801c0681920f1100d4828003809119003806051503d210020710500741419101d0303400019915481c100104032400e6910a4002c140880403010030a810181081824940240c002d902000f5032101280049211881140e0595021103000a5004800c080450090007407094008419080001400c2e4155004070894001d0000301d54074846200b44000304400d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 65681234 1250 65679984 65679989
    0x2040b0d141603080a120f05010602150f010b04030204050406090c0305032205010905010309030c0b0a1d030703140313020d060219020105060a0506070228061101090b130503130602030a0315 83
    0x7034603400c128440d207280c403c030340c4070441b03005031708010800c1c03900085031209a5000341c00840c01030748451003000d0000b45c141440c1d40c11041c0b10507071240e00d504020b43d03006540701310700010f40910307180c1002ca030030000342e907106c004015045126114410b450b490840d80f0b0354410b610040c800720030080d028103034204900d246003c4440503100d2071071151030440158090600300c0c2c0140c4c2408a107400601c041000c03070507914410b801c02c420014032060840f00300900d140d0751000620301c9600a220b04000690841d540131140320b884001c107903c035070342c0707403000103806a58550080d00100502030b52030402820381c024080d8034030303400c1000101d5510504128201d92040302c1107030380600d002e0700401850030814000d001160019001c1c0054802c00c002a00b80d11414240d01c80d050800b88100304440347d4028000c1c004185060000e0069143c0c8c1d40ba09007601c0d9020b0904d0031100300034050b160404c8010801c851400c03529500400c01640e41350300203501c0ba00016103d02c0481d003001c24410100c0c3c42c142440c0103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 65682484 1250 65681234 65681243
    0x40905071e09030f0609050706050a1704050d140c010606030203040b06120703080d020f0f0c011407080a02030c0417100c0906090b03060307050d05060105030d0c051902040b0d141603 80
    0x2d2151841d2607030140c150b0303141020340b10940c1c0ca55800300401d00520095000d0a0f25445240d80c0d0101c2d00f0b4001e041d80d002520060300800800103000019001152900a2103450310b040b051003c03440c04a281544601c043c003140c90340c44c000b40011b400d50142c0143d841180200c481d42d16541d00e050500c525010381c424100400d41001c502407001480000140030407090b001d80050810682d025811505c1d032000a4140b90603034007152141390000240180201e10703060750010071440c248042c002c1d08600f0003403d00d0b4041030700800050b01070a1200180c0700242410316003840000340c0d00d0b062907160803080704900121818080202c0d940c2c0c0c000c4c01c0c42b0040380c015540394242185091214006d64001404099160043ca940010381c2da40e02c95408071501e0180e00a4503080d45000704161130404c40740c80740f206014a01e4902e0000c200f01260510480301080004690f208080c40098002d01d000c0d00d4555102030382c901d0b204248500803800440a40b9114200ca0994000d241c6d0507a203204180700042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 65683734 1250 65682484 65682497
    0x5040506010e190503070311030d0e060f07110603010306050a060501091a09121509070f0b040501080703092406050906090115020703080304240e12070215040905071e 73
    0x140b4a00b8080c03601c0030808081a00394480540b0b480c00241441c0c010f5000790340d4084409400700b4a490705004251300701c09181802034529030a00c010601c540035410041c08440b501251802c14004c140075040031061000b00310035541e41e140d1501000030281903e00e030071120715180b404038255000d15022003c2d1201c2234070070041e0000c41caa00c042140d000603001500284c0142001c00401401c001ca91030440f02d6284098030340c034000400300d24000c040c1d4032454110030070350f404000e13000c4003108440c15a1020b00e00842d06940c0c0e003a080e80a0960100024401309028001c1d681088500202c08903040300b942091200550303507003c002100c181524403550004a42e40100b000740c10400d580160402c0500581d4000c60341c0380c1f142c0245030000c841c2a00c2010303003800041c0c5040409142105400c41d03c07034040207100002c040c200e030b8030b040c0b032034050f8407480c1e0004003401075558042d1090f80105140040583d100c0d180d40c00c0b034001e0035041e80c2e10004908000120380d0300c01d06a140c504081441035540c20b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 65684984 1250 65683734 65683757
    0x4031e031202091306080319020c0d0303050a0212010803130603050411060c070e040302070e010b070b0103060506030f0709060e010e040b0721090b061c0506150402040503070303090f0504050601 85
    0xe5000b54081c0394110b911481032080da01d004522805505d0013801d001010315207420450516890340c211000c003440071500103904010055440c81c1c400c00316682c0503d400245652031401d290000e1190701c104001500c01480002015080000201200407004072500741e1155501425030580b20241c4001b00911505952643d4a0504401401d905561401210f00007a030301c2038000c144400a42e07041e00160410041801046074800d440ca004080160025103452444e48642c0520101808020308498075140850144d9a04108024540b007000060326805555400d000b0001d140300e00c034400601880c80000a410b070340140a0300e2180b5005185900c40d90303200e0300200c030360607565038008850b4107130318400021244c1d040c4613030704265104225001311410b00a040141c549411014003c000030320010301d0300000d60210700740307400c40c40603449003c1941038400010083c0c0070325042540c1501c540d110000034903610a1100088031a4101e03040b10303080d211001c1c4800e45204807103c6000c40c0125845 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 65686234 1250 65684984 65685017
    0x1503121215010c08070c0e2809020102121b06161d04020f0c03070308220308060315090303010f080c1c0c0801060602030c12280c05011104031e03 64
    0x4041001d10705240c0a4086650343e60341c0c003a0394110a00c00d80d2864a0048244459600060f145070098a0040d000075400c050303c55008001120051305040251184086c40071a4000c00c615100d4000402070a6125200a80041407130070943c56286014451000811a00d010281d500440181c0550b04c01c8001e00594403030b00c84c01118003401540082c0c1c01c1020f00301c01d10003c03000d00f0349180401c018568078101801c00070710300031020304098030a0b40d5034102e803400c540c0300400c030040c59681420548420b50381c0800203400c1031b006041e0320f0303148102441007107072400c4040000e6050301c00008801c11956104d4030b4803030781d8004c103c1007a504054038040a41ca00130300c900810711200d2040002c010801d4030342d0251400e41e05154008005a840455032004140c0140a441e403e00d000614003401d1a03241204003e00700399422100641611844c0102e42e02403150712890345060f0000001d0200342d400550704407040d8400d2200361544c10061081200ca808415102404a600b556444081c0030b084c522 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 65687484 1250 65686234 65686261
    0x41802090c0405031f1506050319061d010303140418050a090501090501020901120504050316020d08120f01090c090e060f030109060209010305090f0a0b0c04030203010515031212 78
    0xd0700006030060000042503601001407000c0e040300e525241c62100110500380b020342d1940d40305203a2601c1040010720959034400192070b4071255038072441300302c007081d0300d00c3c80d005080c10341220604000c01c0c0020404001402c0c011070481740b281c2e0b101c1101c8070b40588801200e0003503000d00c1e42003440710f480c003d4882c0600c0d0003c1c3d8200f200001e0001e4006016501c82c0d08490080204031031594011410070100d40c0c102c11408e02c10903042038113010a18155a501e901d9200d02111411590f407a5000780c015516030b50404444264003400703440e650100c1c041460803018080303a60107410401c6000200c3d00003024000c1e0302d940549611801140c034105600c4481045004040710b800c013050310a00000780d80c0900030000a00d0194200582d110f0034bd40005051710070003425071825600142156030080310024542c000c65412030750b900d01d01d40b0ba001e4070944520940e40701a52641c208814000e4501c0c1003100707141542c00c201c4c21241061000003d11070140508103003074000005050019140c10980300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 65688734 1250 65687484 65687491
    0x307050303060f0f1201140709030503040b030c09191401050702060a080c360a0302060d02070309050607050303090c0405070c1401060f0602060912040506180f0306070e0f04180209 79
    0x2000703c0f04c13862521011072070303a0b034080c045554280e440b420143c40300758907882e810380c00500d207103000d0300d447d402c40e01d407603030b0341c0c4181d100d140d0506000000095400002c802aa4007004000380002c2d1f4100403020020407400e61405440a0081d826a441c851580038800703e8000fa980540900d080541190003980c4424000700f0002d0192420012040049000d42c42c019030310081002c00d0050f91090150600040c0b111038985010740346030401800035035211030580350010343d2444007690300c806900c1c003121900c103540d11040d089a40444e4070410804044080d61040300c02c0e004940182c07250100b00700640f0720568030310010808400d80c1d04042040f0340f5001045c91103460000c901f90b0303500d5200c104540b045138804001a0031550a10808041c140040030780d9100704c8000754185400c3c13030001882c0e8440e240c45190040c0148492400c25111844070300c0c4003400080c196001d51620b06005031100c4698a4035901c070350b800040640907071900d4828403001c440343c880440070000d10365090080d90f60000c1c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 65689984 1250 65688734 65688739
    0x40c030219150203040f08160308030a0e0304030f021e06090d020102010209031905060109020403031709100f2003010311040c0c0f0f17031302060f0702030a0606030b0106020307050303060f 83
    0x40301c0803408410b829060100024264000d55403103151850b4404030042580018006400c000704090420784000510b005407a008600d80f40d907a12502600001050455607100c03c0340400308000050203440345180c1e010900a6682c2c1000103e100316012450385400d1b41c3d551300410a000603941c07402e1012105406610600005103171170f0a42e00002d00c0c010070702184503245c12055040104100050023024010f2000100542c14241542d801502d041c5040d0b0070300100e842d0f02c900180c0d1582e001c00401c2500c0f07019800410013504100f5aa1000d056821809520003108c41c124000c05010042120704890f00b0a1204400d8505401080054094000404208030001e140c40c4040b800e0385031b01010f4a07200308598050140b00749003881030f101c00d003442d59807448414420001c4a80024820603c4540d044903c0c980c1c0310252002c8903503d00a02c4006901442080800d8040011550210047c3e0b801040b840c41240c3c2d0301d00c41241d40707210b0315400034026002030000c42c425090044402c0c0300071000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 65691234 1250 65689984 65690029
    0x806040215030a090c0b0309070806150409032106090b0f0a050405070c14070602120703020a0b0a0e07090f1b0903060f0f02030f0f01080f0d08090f0319020c09040c0302 74
    0x9079110a01d2150640d00101c504c0e0746d000061185e400170411102000385101c0025200300e241c07680c8044501c041600c405401103480d100c800c01058403070782029440291600d921a40070b042c51070100001c1600b40aa5050715240c8802c1c1002460408010820140020902d4280a0400707040c003020744000340400307060000440320000060301e52140c01f441e414294001341481c034a400d0000f80b42c003455800708090300204000c54000b0030b03404502140e031a40c10184601c1e064031a2070401000748426070380d240c240d000702d10011403140d485800052140c5d50216042c40f401c0500104220104000301d10720000c01d90824041001682c0d0750808100c001440500103001800318128406a1b48111a6101c0203e828410000045001c9198602520a503002000303100381505d070040d601c0b50700820003021f01090400107400140700b0402c40d4070240c4500306680d1213034102c040050300c2694040c40c00d070150051003a85101402c048407407510483c2c01104800c0e81d02d00c0c540a10440101010141030b10494 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 65692484 1250 65691234 65691251
    0x90204050603032a0f07061806080c030402040207030c050d170f01140d0602120a06030b13050c0f0a030f0c170d0e01120212010609052b02040509210a090806040215030a 74
    0x4080c04846c0040c95a034a800b034403400401d042200c00f0003d50014018042c003e8144128050820192684140d043d103005030f842c002c5050a07291442503a500030901d224501da041c1c1d41e640e218880c0d43d49000300c051104401c1e01c90b24155082000240074612409a01d20407207a000d2411030382d0105a140541e100615015591290100c3c014046898403091a2109401c104000140031031710391001c1500105242903150350b4525444042549a85104051000508a0540d0359040c48002554407080080e001c0c403041c9409209140d19101ea0a080c14110703544040085000c01c5840d0411250341c6c03010394281c1e1960043d1602c0c510210580c00480e0700740f00360a01d28103200d2001d4040c014a0300c400c4141898201001103100742140c40c2440e509050309507001c1641c2e0618200c90641d411180800d80355160841207262060a007080c1e07641c03001c43c00303002211040940080000401540ea84203196403100704441d550503040d5802504954403040303000e982501000030316000140d8100100f8400c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 65693734 1250 65692484 65692513
    0x504020117070201020405100509030c04050a0b0a0909050111041a13030b13020a091104031401110406050705060703050106020a020d080c1213060f1d01031b03090204050603032a 78
    0x1107045030000007517075000506005524180b2042071a1450702e20f04a0314004514011075141c60703a214403e40240d841d40085604c2c42115000841c1030380024150183c299601c0703503a00003403c0c03c0a003c1c0c1d03603546400c519120510080c0216800d803200c00d001e512181410b11a02c610648c004041200440040d000200c00a841000c20ee40903016646280d0744e19000c0b80100210421183d02107944140b42c078006454516860054900312908590303104050384000643e2400340030071124600084200142c0810340035040300140c20740c81d004404880d060f6039800c100b44c00301d5100f80200340c0942e0204c142040145448082c1c801d00c0c034480c0d110141809120343d4054a4940c910f44003202456010400d13104003844044004010b007401d140c00105070889080182c50450004c50200e492010004000c026134082c0e00b0200e508403880c030035100401e00e00350004009060858040f8841c42c2480081104d600c0c0c00020349142da40f650301c0b050002e03100581c4098200d0a50344600c1c1041c055640342c6140c10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 65694984 1250 65693734 65693777
    0x70f11090702010b0a15200f0102040b1b070501080103020609010c0606060e0102010f06210302070e040b1602010c052d070c030b010801060b04030311161502010e0309090a05040201 79
    0x1001c254001182e420400c0040004c5405603410503d0540c011440305265607a1001e074820503ca501c1413403000311040e56405a0510005032161070b9250f0000400040e000c850744018880100d00b20a00c152a03105400220345510f541d118240c0000c55400060016250a2004200b440d40c1410303c03240341c84941d5500e906941c001e40c05035011840403441c2c07040e55602070251001c940e00f83c5004010141c10044040010012214035280d481040784007902054003c002450203030003860010211840c0c5450080c084520440740d01d0301580440c02040f10640c0140107007080108140c81d02030170078000080800058032205004020561000001e110170030200780201409070081e02001d01c0a401d50070120740001040c4d0007800303030b1707854004204444180501a602079a905240c843c0d4200071100e5141d19054000300f01840c1040d40b14000901c031034404108540707080c8590002c0c8200400b00c510a40c480c090024000c1e080a40d08000803100c9010f9440583c1c45841410181c00000e030108007450403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 65696234 1250 65694984 65694991
    0x2030105010807051e0d0b1b0f030402011e0905060f07170706290103050c04050405100806090307030512060105280e0a0621060801020a020105060a050114070f1109 72
    0x101c0d00011400c2c802c2e410514040c1c20b00001245c0c00780d080e02c6000d40890080c0e9415107000c0d01003050400411000e0040e0607640e2500018040c0407500e40903540500790580e0b100380d400300d01090030884402c42c0349005a41c29080c25403507403510060140383c04180f05a0364001c09401d810610204202c400003915060a014504d00341c1c10000e0701d0715113034a4004201c0d000c180ca130040c100400d1204140360f0742804907142d9120307000e00c2e011800b40c070781c100300d00c0050043c7d4014076405800d0004000c440c00074105400e084901034000c4600076164042541d84a1062410140001d1420040a80a0649410320a801050601d045403414500040b0900d6188044107503084243c1030101d002182d55000400002c00c0008440301c0303288a140020240c05020307040f5204031280d8030651114040d4050364445130080600c480255554240504024003d10341240c1d143d1140c0d81903c00441e0b030f5441800006012501c03c13105c0d41c030300556515080140c02d01e024013107800040b100706280342c644602410030301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 65697484 1250 65696234 65696249
    0x10f0f06030c080f1009030302040e0702060601021002090d02040e03040504090c0312030b09041b0308040f1d060102031605010b0406030c1d0702030d0e150c040501020f030c12160203010501 83
    0x100e05003903251110b04041c066005020b030f035104e0040705124850110383d085441c4210b900000d5440918601175000c1d00a80d40100441400981000211600031440c14800d0400f44d090b80e038074600f4002008100d00402c4190358000700011310540040c00c10768010580050300c10f08a034101541c4000040a0780d0301c0c168201c0f015000b150b420410000c0c12886080d0003103950409000c50540840071950511006001404a152001c0400d1582c0319052154000d90f402c200b0080d5200e031107407481c441d40545031080030340381e50400b4002c0b00440540c0e07030381500651050340514600070010064482c206600d4509841179540c410b4804260703502c0d4802c5d40021486408111552803910480f40180d030b982044550032032851008201e2541e47c0030046507003600b41c01d5000241e507020100e800740fa045001481610b900014000e003e000c00c071050251044560982c01c403112403031001c903072503280d01981d1038900d00c507030200c50400d9000c421500580101d00c0c1052900f0765694141d00042d081d03490a031b10682 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 65698734 1250 65697484 65697491
    0xe07020c030d0e0306060609060c010c0302030612070302150318010603110f04020306010c1209080307080702041508070603020d18030f03050612060402060306060c07090618050106020c0d0203010f0f 87
    0x1449081c1845034a410410038105402c02240d40000b00340c441300c1c010950761040340000b4016103640d8803001503800c0603820f40000c101c89008000050004d41c01078801e140305038001c0c1d100507030720640081e1802c140c0f5400784c400001084241c20380003182e08080d0040c209045c403058000c401410900c038960081d40950000403a006100d424802d080c076140c000180258010400c004160741c0082d0603401b166444101541c15009081049400e0303881c582240c0e113a800700103618002e000b090805080818001c6a04002880110f00070700024080c6208204c0c0d1600f2442080080500960140880441c01c400209000c00080454001031030350110840220f8484412490141c1d4984141d82d40300d4002c2e00d40d01c1c1441594407040e5038801c401000244904800030000702aa1100030903503000810300340480351410b0b00e6a903414054903860007180d004c829004d00b1000d038802d040c09a2030484400c3e0700940404810f2806008201846600030790301036484a2032000c6840140c40307803080b8001380d0207001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 65699984 1250 65698734 65698753
    0x612030216061d0d02040b0d0606080106210303020903120c0d0806010503010b07020904151401030303050f0c1b070302090108070503070902040b030601051303050d052808070c0201090e0702 83
    0x850144910707401c202c08018400b210210385182c00490f074441814100c0b00100100841e1001502510180031901d030400c2200d43d28030100b00d000d4100100f600e0700400203010080e01c400c0780c80c40703c0260b04007811b8070011319106040846c0c0aa402020912800740540f0321810dd50040c0742c01c19409404074200c69400348100c440c02642c0080d9840e04090246404c51a5500d001106072035400346000107441415840c0c00310b01003094078403526143c500c1c140c40a101070300306500c00007128802444141c001c24102400140e188080341d01180c4291800200c060030b03d00d5241c82052038040c0404031608601c6a0b8001101580c0c40c0c41c40e25008201d030200814040f070078881414107001d52940b01d0300e03140b0300503c81840b1619036201a241c1c84070b0b007840c10743d4642100e800c600214443d02d5102610702e0198404803010030754004010160305540024420360040284058003001100002c11400140c040c0007151100e1312900c02c0c1e28a0500500d0241501034417400b6072480404245c0d508409a800760032127 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 65701234 1250 65699984 65700013
    0x30a2a0f03210c020619020c030d180812030109050406021209010c09060e0607141204080703030e1801151701080a0b06060715020f07151401090902060d09020406120302 74
    0x44142c1e80038140b800310340034881039020800381e010741846c028030400580910181c131842000900040e0b20003c0446100c00405000078100e80d282071039078040f030400f2060100da210800218140d000100003080c5203507a18003d445401050090407c840c0c840c0c0800c881101c811800d40050b000d094080000500c0c0d0f90440c41c0a4090b00c0303143d12040500139010080c8089681351800d9034105500005c0062003102400002c90609488a4204030041c41c080340c0030800c0706001548205030307486911540c620840d01c0d01040f84540fa40701082482003504801444585010202c014158041d03081400904108000c502140301007600808035030303400f541254040c061850501c6070450b000b0b590240c40c007441c90301c441c0400d4603015140f2120380e80001d1150399122107807048038092504a21400c1404640b011401d01030200c26495000c018105000810442960321a05052943c010304403413500c1d1212311028050180c0c07000680e4056501c460020342d443c0e503681e020700110b100782e01510b9150040d451 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 65702484 1250 65701234 65701283
    0x6040b120105030f010b090c07020f06040605030a060e01030203030a031a040207060203100e1311030c04060801020306030f01021c0b0a0506040b07051005100605070f0503040f0f05030a2a0f03 84
    0x40015180e0f05088900c582c079107c113021550006140c92626503905854004a40076a407001d09140d04064002000a2400d51210140d40111032103031061048598900c0e1403004403c00f07003c040d41c940c00070820041914020b03841755201006004411410ba11914005400c0703803c412002d40c0c0c840c0e00001041401e2402006041c050040300c000201c4c50305010b00178030320101403454010041c90b0841810139856601300218240520700034130900c07603241c441c50302078044c1d01306845860007071013140901c25840406000f034803403040029030300078001408a940c280180c10341041554110080c0a8085000e40f150401000581040c820f40c56a80e251480d01d170f46072850a1848000c501e10b04424401ca07520010040001c0301e51030316103142c4450903403c1001c075220064200030460302c00050005804401c41007280c0071110f6888402c0c000360380c0e61090603200c0b131225400800c070021210482d0480003030803800c40d01c41c424004c0c80100442c0c41d81c8cd1038003c118140c205540d1704240c1094200210020300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 65703734 1250 65702484 65702503
    0x60e01020301060c08030a1e090201020105060d0b2e0305010204081209060702210a0c0f0e0910020703020f0a051b100c030e0301150f03060c0203161106040b12010503 73
    0x50003103103158904000103201d51001e10b0300501181002012071020181034121200800e444101c580b551500b11100700014006400103c0c055420f11000036620316080607410910354001d101400c2941d01c144c516454040442c038070341c408486800407610700000d0307013503c4c1c80517522070000141d41c1c40c1000019850803103d58024a601c0c4002c000041a940b03135041030f00c030540e40c151003011810b05500c4a60510442c00080451944500079000040c02020b1038000200c1c0d2602040001d46500c460b8181c10300c200455a643c2d00d544220740c0601e641681d44c0c000c102042c0a41f060718a030301d18100c0114104460390200ba48c16030300018200201280c0001a010020000ca070b0081001551034405040511341140107014000e105d01681c2c0c050700c003900305180c2c400c0b6103801a00b005864858032100d0900500082e110240341140c0c02c4142c0e40000101c85c0b0808015801000041072035440031001d415241406800904c01d101c0042e0b5900c86501a12a624201c01d402485605010074580f0b40508103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 65704984 1250 65703734 65703761
    0x3151a130f0303020c040f02040905100e090c0a051002030909010905010f0b090d0213021608030a0c030203010806010b0d090b07110d03050106050d02032203020d080105090f06010c0303110307090306 87
    0xc4401c02c00203400181d80004a0300a03100424502400d05001d002402150b21800003607003420300b04124a809140b91030240e07181d42000580a07200c046d926955000f1502c8619000300a01c0c805000700e1800d40021000110b407441142e00d81034501020030121802a40030415007625240103005544a100400c2c010300704492010703040400003800242c800c4180300f0040d003d081c002c2c104822241540d01201c10800b10072460500c821081e2070064071650045a00020300c618065207425620b1003802181d0480f0141c100402e240e07400d0140285156100c5c2c3c0b1015420380d501c140d00b50001c1c0131030300303d6881113140382caa0700d5144598207007140c1841046400d078410149440014004281c000c000c0e96404468501c0058882c2d0304c47c0404405041d200390780304244074072040e0074410503600042800c0254040c0d503440103603990341c0050080601060714a407105074001400030321a13510a100c850035842c0207290120703008041420b0030070217a100b9512100049ea460400703006110290254401d1407040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 65706234 1250 65704984 65705009
    0xa090b09060a21020c1b0d050307031412100311010f0203031314030403050106050a0b0705030406050a18170d02160b1b0706030914030a0f03151a13 65
    0x10000007421485103481c0e007800d000307103076601030040d00c108502d9031402600e0f508219a5405403200700c0d40d45c3c3d0240f0190a601c0d1310940000449801d24a10780007106034490003d5040c24003696054980d00c0c0e40529041e40481d003404400355000740e13503648a0054200d150807510041c21401c0035500035502c000018148a43c1c900012880b41e0f000040f0395200d407144460300f00f4a004e40c41d100c0ea00340101021150984000b00f004418401c0662002d01196030840e250621030f940c842c0028220b0040c2d200243c03481d08184070820990740103034000c01051010f46002d0700c9810340440c1e40300c00050346030028a008a04440703030b008081d070200040d5001d501c044c00200850400840101c00000e041e01a402d18698081141012801a8255442100c0200c1c00380c5d4022500c50304010010618250143d03100ba0052405100b0b9010101c01c90780c8200255440380c400000c0c180094025020107a03944005c400301440000340500d0b01e0316180d02c2c01c12035403902651600404031034001c944c00c0b82c0018011964 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 65707484 1250 65706234 65706247
    0x70f0b010504180f0605070c170307180305151504020315032505060703030e060a02070201030b0a05060307140d020714060106020706090e0907180e0f01020a12020708040504020f0a090b 81
    0x80200014503560b07111a0102d026a12811f0898244529420081c10041500303002e288040c20107001d1441202241c1d00c0c1ca50410f030342403050700c000c7d240703120191094000d60701007480e15000c5885a5801000759001a42d05819040801c003243c2c01110304029008403050144007514040c0070489201d00c2030782c0324103401c200e01d41e4003980414131840341c01e12641000820204142c042d401116070380d0185001d551403854060700e004081d5000c0075040b0300107440c05c024280743c4e203040b042020a89001070455402c5684002d020396100068000340d0000000074480c16072880f0040c0000c0c0907170340c4070740748603804440c80014041c58139006811100540d00315003405c0c0000c0e85c2c86429042101c214461444003034403148038090625089402c15070504c442c0085804030041c0035001700c1303e0a0b464070211506041220340c030368203c1c000d8a9281d40001c1c4125401c03040ac0e1030a07009070040c5401034043c0341c9010703681e100007012a03011004031540e074800401c800c580c1c1508014124001c0c1142031080d0300d4401d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 65708734 1250 65707484 65707493
    0xf0403020a180c18060818030a0c0b06010c0b07030f09021e0405010b0403120c0f050607080f07030b0609010e0103110d051608090604030f020f070303120e070b0403030e0303070f0b01050418 83
    0x503c5c0c0109001c000c0c0c03240000d5903813200f440c40000d0850920040d20343da8545080020030807404504159000c3c45207a02160741944280f020742072040e00031b00c0702d81e1076494006c41240a443c80307a64901200d5201c10107940940c1e129138403040e482c1d41d040500020402407905000035140c050b032202d10b0410301440b040000c2010a81c0491001d43d8034034204003103420601e0701054510503410090203030300c1001e04101d8200c0d0004d046a003c2d0440c41c80810b6950780e021011410766604004a41d0000130134403181000d0350003501840400340c414180071034550411400301d2896004003428903d003640b520140300f100110100c10041c0603080d441e06440038948100111381d038280140c801420040c0c40a07954580920922500b8542c44580302a194565601c2c1001040340607408500303400703a481c00c4150840000c0006802d004c40310407221207070905141d0b44064500c0c0702e0500501c0d403d030204200800008088005880741c0c5441908400030f02e50510301031000b140c000c02c80a00b800070004c3d02220108 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 65709984 1250 65708734 65708777
    0x703020604120206040b04090b040509010b010207030201140c100203100609060912082505100c1e0203130602010c0201060b0405011704050f010c05070b0f0103080f0f0403020a180c 79
    0x4400b078410b103014030000c503c0401c01c14840d6a001c040ca011000c240070504a842d0307004204a400201d4040c081c2e611404585800c07684500981805a48590130410055008000c7e040c40081804103a074241403800c5c801506256116105d6802d20303500204012081924410560180145140c000280c90421300c001d0301d07104650040f5400ca511400c0c080b01042050743c101c8000d03198001c084005c070f20154030306181c80040614122200d02800c020500c10400d140304246006020795200e10248180c00d1510340396001210344c030030071070004010b050f00e1040000501c900600b15613000044ca0394882c913000f4212192500300b80320050f81040300f008a030307901116044011001902e500942c0e101d078a010342ca411080c0c0c240c0f0340903500b80103203091202d40010180c810382c0e0103030600d851540d0b503515241541c00c070f09000040901c5424803e00304a1248413000d02f005800f901030007460319131a6000107c0c1e051a6600007a00c0b411a14a44500403140d03000765a800030340fa090038031b00002c184017009c410703 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 65711234 1250 65709984 65709989
    0x6030f2307060315050a03150e030a0c030c06091b090501090506130c09080d0504030b0f01030b130f080403060236100507020a0f08190f0b090a05010c0203030a0e0703020604 76
    0x101601d602c0d80503060128286004d00802000f003a82440d40da0702d14007400c0945e40c1850280c140340c60040c6148200f07001000700c0c0c00e604450b64038404104129a004c0e02c0340c030f8409a055179480c1c6d03030b40d220100040d91358441054800322080d16120036441d1220180503210140c0210840300d084c00148681900c0e611517201145031040b5022801c0800c5c0d200444116015503c4445207101310303408444001e4002c3c004205a03801409164060382d100d12071000c0040b001c0c44010b0000e500350700002c08408000c4100c08040b44a052405550781450310380906d02d030810381058410b2580040c1131001034240010380d1a4848803102003005003508402d420071f85e00c2030300a410740160300506480c0c151034401c00c100d425503580106102d80c40c46c1c5816080c408000706024032050ba10440c50346134400910340d010591519030022428100140c0307551030316034032440030308a07441c1882283c5c83c020000f04203004002017402c0b203070300554480c03810040d20300940d0b03040c075020f500c2a042000c0034005030301c41504490a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 65712484 1250 65711234 65711237
    0xc04081908070c0b0c1011030705160605070e0406060f080a0c30060605070818150c010e0610050a0e0702030403080c06040204050c03130303050c0d06030f230706 71
    0x6034012141009109031144403001001d41c60942c20101d8148010405000501002070031101c03100f21485440017201c0d01c003201000003081c10310002d01d100717220b80c0050038000ca00e4646040344600668402c019240c069402c4c502084d0400c01d1206d00f410203100b10402003a1501e0b02440c04007001d40c019010320310103844129000e445401c0c58000501941680410403091007108005489200e03410782d17074a24400341c180c0c2685c00c1120006a8900c40d43c00c0e01c031141c3e080010036143c00c0400c00c0100341c00c0308076064980c2004a490141100d0310444005d88001d00078603001103018240225000c1c100781000307200d81000090600305106d191900c3c3c1d000c1090703ca0341c0c02d440099440d0020280e240d801141d10042c401c100003c0e00c400190004109640070b58400c0d5402c0c032154903600b40400b02e0340401c03110010100d00d40b4020401080c4280c0101e50080c04902d0868504a100805003064407403c1c0c10564020044565220400c05103400c00e00b600d90825022100011400c5041c0380c568005210701030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 65713734 1250 65712484 65712523
    0x3082d0901030c27090c030b010206150307051809120c1b031501031b06031806020d1d070e06060702012c090709080d0201090309121e0b06090c0408 65
    0x11007aa0240303151804130788285a070030b100d1400c640d0700030120051038001c1103c0f050030b00740c5c0c9105480c0207010741210500142c010b45a160344509803d803190f2042611280e040c0b2035448005001d896000c02c10765822501d9848100030701c1c00105043c540f01449007000c00c0b0349020441c120b18490301082c101e81049041403060400307441880020303d03254111403a2500503203034200010030018460b1140c4507100c20260103c101559400c0181d00b211038125008500b40f0300341d00303902c00007140da40c0100310304e945a120015495008a80d04522102452042051a030042c803090000071070981017190712000440c2c6840c0340c03041590000b05503024040410520368140c09202620034200e800031850448060940040c2d03280ca4030000f402c4642c680b08481060040e490740088880c810300452030740b55050b4403220031040c0307010240d04030350011000c02d40c1e001c0031892107103620340a0800d0030075145004032218a02c1e030500404020807503002501250052030108010010050041a503244107043c202044 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 65714984 1250 65713734 65713751
    0x10090203010605040f0e0d0f12020c010e0d021f050c0702060a0903060f0212010b160311030d020f0304020a05012a030509040203040506100f0b03160302090a03082d090103 75
    0x103409002c203508a41c0e031050074084800c051070195405800214540341c01c4070441c1359480b505484800c0e80c0b000f0280052034006440f001035419400401103040d8000c000a03501c00003140301414020708244180050700803107115217541c804103000e40e10a00c0407410030000360824604450080c41030302c100a0085130046601440c00f80a14142002140c00c094241b100c0405d90401c04002c5d40014080704000c0700650000c03c8109130402030f59441c6080308040d58188203241c6003a20b50100110108540348420018443d0340b02c00c40c009451851840d00e4070584a00b064810001c0150075900f1442c1048000d1420f120060564081401c1105d603518a0080485031800d00311041e10410807010342250000040c48100301000030001d202d46090b24025640c0b07500c994401644d581c040c03095580f580d4051011403160b000c030a0201c031515030340342030042c503100031440850303c811032683c0192040f09020030601c0e07000c00318100c510680d60440011151a2584055200190113003901c894105603031101c28 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 65716234 1250 65714984 65714989
    0x905030d230c0a0f0f08120a0c080403080a09020f0d1b150f05070602040e01081506040e1b030a051c030e0c0901090906090203010608010603050111030921041d0a1508100902 76
    0xb201030341c001101b00e642c0c05205071440c244c950207860700e0702250324200c01c0c40e518500c01c98a0501842d4555150045600c0d42007280003d40390b404000d0782d01c6044a95600400d95807141c0108540784182c007079414009422180300413043c800d51000103034602c48200c01034400e034400c01950702c071501c5090007519880b1500303054009014a0f00040421500800041125030000841024000d0200060880c0d50380f05070510081c1c42c80d945214487c0e034030140f1020810159452031110fa01d0000e0202c4085804903103a040c5007403281c9440000740d015084407842516030500440701004c0d100700003014082007000208203800814400c000c80342c1c1e0340c3c20f2801e041140940080059640040090101c0d0303850b100d10600800725840b080303c2a61070080e0683e1660841d10503a440f030142c00010b08040101d00140710201881c090a07460511400c1101144000c003c3c43c0b0740d50005121241043e942c03a145a482044900000070310384966070141d0700304030510780003035182420006400c01140c1040607102 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 65717484 1250 65716234 65716253
    0xf0501080a0b03011104030b16050d1a040c0305090f0d0801030809060702040c020616090b0901030b060d0f090201110109050601090c020307051203060906100f0f0905030d230c0a0f 79
    0x20b240d03040d401c0c07031000014980084083c0054038040d04540c0010380b200d824202c0402a03800d030b03042c040784092000036810b0903240e20030416800c20036454000803e00e040014211494851018082940ca409001041d2000c0054141080e0885d008100c41110313444007038501c0c02c05120080140c0000a0351a0103616003100359080c0b581c0c041c0c8140148295076074069119042200c80c544461455002c818040c0d01c039403116070486209810492402c0804001100901000001a40c001c08200015000d1440500c94180c850b000a03400081c0c40925200051054134443c042d00c505030b04002c40500896008111030741100c03030320103000070340c0b000c0300300c0590950244030405006405006401c0351800601001540b15040840c2c0d40107083e5215402c01c16444c0b96802040001f6218080420406005004034540944182069200e8a6842c0006460800a00f2489001860130304031800d4000c0030803010707070301d035504c401115040a1944070381c16607410382c00002802c0001c09020540a0250404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 65718734 1250 65717484 65717501
    0x10b160f03110a0b0109050a021602100315080706030506040c0206130c0b04030c051f02030d02030402010504030b04030309050114070c0809040e0304080d0f0c020901031119080d0305100f0501080a 86
    0x70903609070030303c40d082144502c0424454140c0160800000640035007241c800c640340d0100c601c441090081140e000e02a4031200c094680040c55950030030003071001c80aa6000c001001141c0040500c1400c040000302070b214041c040500480c20320f90301c02c1c5510340106030590300c8107041100944550380760400035101075a03a40001d200d40400200802888903030409041618002d507608103225003200440351604000c4011580180c006100001c2c40c00081e400a5400a00500d0301034100768490301c03000000f07101035030304901090f0ba51203480c0c10000203000c0d404040c5d211820741c1902c4d14001801600082100100808072000010074070b60665075640004001c4c0007500c01c81c0d440f20388407441305540391000001303040401d80b100820300c182885004461a003d601074801c04459103580d4480c0b4143e8400e0141550100301c1d00d43d0000000300703242901006000c444010562a500d420000d000c9690140c411a04240d0303005050090079480f040301e1044440a284c114160344d1440400710040c1682d6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 65719984 1250 65718734 65718767
    0x17040210120e010c0908030301030b180109120305190b030c060d0e03030901051b0703020706030f0b0411032a0702090408040f12144c0f05010b160f03 66
    0x3400b40007407450305502400c111181170f100d1000c101d448405890766800b0034440108071102410004040300807004200f45480303e104000700e0f645556a03164101000402c515000003a6544100003903405e410140044031403182000b041200c8c045c2e00030a45825500d0401c50040900249104d4664802e17840f40500d214808203994980c1000400503019040685c1c4107041c03152001c0b101e14000203004100c88a46a05400030900c071031603c00181c019185c08004000b82a42d10b1f0761011a40c0c440f809111500d06011842c0e564914107101d0202003100305101035200e14803404070446441c400e81080710342d00c0341c046072202840e5565152003200ea100300d0b04034180c420082c0c038000803104181d00400c02c4440c4164680c4603518181030301d030b0796118030300c41551002c1c4004100c1e401104204501031086040568000000030903c204940451010191220700d82c5540d140d900005851074860540035041c0036100e85d15103040700e0b49400b968800114040c101d50440d920b06001c040c05104680d4808624 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 65721234 1250 65719984 65719991
    0x605010e04020103060518010909111818030703080a020306060903160303020d030203060d2a060203130f05220207170c07050102010b0d060221130606061704021012 72
    0x1100c14500000ca401da030201e02080c1000004542482c09001d00b03c1001c0380700744000e101d42e10780700c0c2c4038000e40400780c5e00741e07080d090381d20f10b850803900e501d61003040c26607202020300c00600b4500c19a07041c140304a611014240c0003401810000381d44108d0040c1c100c507071003801580720345507100022f120b4030440390366951500c0380c00010b44e010008034880c101220f01a80076107002c4e01800308103400f03a100c119100c80d0320942000c02c3c90300003165400c80018003001c2d5804615880b03103911900902c18102e400480260344046040e0034420068810724010b8481402103e154a14007000700707110304c900c040950ba540f1500f11030001e1048884d8151480340fa0000c2e400702d03468000310f5a9a401c0e5020550f885e4040c042d01101080c0c0d07500501403075100c0b8202400b42111900f542d00c42c100250002e0124041d840110342a01c44d2514040200c00d01807407007a20280c020a4140c17510108850241e840744040c84100031004000252801d215035120750151410003e80c41c80813800c0710050307058078120200614 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 65722484 1250 65721234 65721239
    0x10c081b0d0906030b040b0a17010f0f060e0604060f0e040512030109060e06030105010501050a05070204020408070303180603050609070507020d0b040804050a0b090d110315240d02030d050f07060501 87
    0x5100b040c242c225686510204a82c1d00c0034010301040e1414500b4a9030415140741c1d04020012099841c600e540b000c60000148100419444906a03100d0301080c003800ca803505402d100c2d05408205070343c0c21600444080282d18604443d0801108036071040c58000118a00003c06000003444400f11030300091106580c3e941e15803101c1c170020700f8540030300c03159442d03118001019401c05206481c10385405850b110300382802408111465440810220382040c1c0034400090100720400c03400010358401c0d00c4119062007035050229040c503840c0d005400305070904c1d003841203d4464841140d0007982d24a0000d40d01c42d640d0000c02c14810304800001d00f550260001c20050224880c0908291002141c07540c101e02d40c1c4a220b81350602800900300c0e0b1104070580c122002444181c040c0c036442c0d03005010703648203040d0342c8018a0030303034011541c056505000e8031200c08a10024221202000011201042804010b8000c0ba039180503401e00c240034000002101d9030724070800300544601c254002010300c0b11b9038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 65723734 1250 65722484 65722487
    0x18010305100513020a1a090d0b0a0c02070e010506031e090105040309080a021302090a030210050315010306141e03120d05070906050706150e0c091806010c081b0d 71
    0x3020020001c0d0418904804542c1c1c000b100c4071952038072500201a042001e0501890007461031150f04100705084003008080030a0300d50784603050b0310078043e81d00000c592500c61400001d84290075004411508501c0051001c1c0c07032010f0070181502c40544909491b50340f0b0b84c854041ca000184100d28900c2c210500304021103205420517442035110380e4880a000d903481a03001d81da02d2200a00950081850342850283c400d680c2c003810320180010102e00104da0b42e0740216030914419030034030300054800810030080049524a1030903508080c0382c00c1141510342b0240f0316940152540f41c0e44500074908540003090b0388084131800d1180002c05071002d500760740c104451160f208010351182c82c0e09040009401d1030040c2580300032103400d611214a03059081d901d05000300a55800c41c070710094140c201140f940c51b282c140328458200762000b1aa113107403101c20030004d00002d003005041c440700e40d810016070fa40e0101c01148026030003c10580c840c0401503030500b54820750b103900c030382e18071079030350b82c5030113030b03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 65724984 1250 65723734 65723743
    0x10b0102070608070e090603010b09090d0e030706090e0601110d020c120d090308130e04080306040506030127060605090a02040335030910151409040507031118010305 73
    0x5440980032110080d40c0c40105491142c1d088a944d0f0201c2c1c10119a0310300d508010f00350310b0380400c004000203668004040060040c0d002074070401e090b0351000c1111000fa46e00001c00380c07600320049004001851030905e00412010340790280841c02c0310740101080c0a6402a17038000041d40411301500c07285528104000c4da0b811001480030b104402c580c01c0000f24040100c0e1040700030750150341c0c991200d4107503282c8044a07880440d85164180740710800203405101c13400c9080c003413032003642d9a580e83d0800e0720400050701c0c00601264400c0e413400600750b440c00c0e00d00d051417150b038038803040981d0707000c08608082c402007009600181e08807407210b0810007007030300550007002520320480c5003144106d456118200d20342040a00c54503003100414900341340490744406541d000d003a55040390802c1400341c1c807070015607142c030080c038040c402078000030300104840440c600141102951200c04900d032039101c040d62820030384030103043c952040d005200503445070322480042e189005480c00444d6542d280c8195075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 65726234 1250 65724984 65725001
    0x20406030b1f05030706050901020f01020a0c060b040506030a11031e06060103060815010e0411060c0115080d0504090209030a0506100906061716020c1c06050106031b05030910060801 80
    0x1d002e01c0000707408522074900c00b190103940c1d024008016031428494142d60320b81c07100c3d0400f8190310440203e031040e18801d000422016403582d99140c2040c826160240a5444154501e88110300b800c00b000b0f22500c00240b500d5115400800c0081c079409502e0129051038503040c00b680600d803498000c2c0008800008201d409581c085ea4100201541c3c0c0284503196840200e1101201c0010401007080d4401445800d81181c0181075040071200c1440002c1d1851784002100685a5114401c2042a007a5254aa00145003802c05072400b0842440c00411030300c21401070482865001c0342d2028a80c904000d810703d40e40d8040112a96030820204807080e440350740c40798032007450801c0c401054880c400c8280003d14990b0106249480c2c913039107880032000749a00c0729041144240158501c140d43e8105aaa004c20070401c00b19040c50500d082c02425500c050700032a040c1810103100811030f15584020a03d0709500c1c0c80c100d41c61b80c0310b1104081c240010080c0308480c607403c180f4046803004041d4043c000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 65727484 1250 65726234 65726251
    0x51b040e0f150915010b0705100504050f061b04120804151e030b100806010e06160507050a081f14010308030a1a010504090c020a020301020711011404050922020406030b 74
    0x3140d0350783c0031001c1c0c0d540003180c801c0e090807a411801080034884110142201510610558100c41000400c18046038411901a11113911654080e942c045052201d643c0008820030351030070701d0184011929103407245110703500322240c12066010501400c44151009001006544001da00500710000e0002d10040e8440000001c200d00c44000c20f4000d115402c042c040c0582016201400000d05580b0b840340100a60305200c803100300083c250780d42c1c40007485020308902003039095448506080e8074021142c0c101c40e018100e400000c3c80303003800001d8110300300400c0070440480303c031206e14090064000040c0264004001800202c02c00a460002e0f61061560200410000000038481150581144105030104404100520114000390054022002c65004884c54461235034046402caa10208050301d1031000c1469000466901c8440f00d09102d1040b0303810f07420541007134001482d80c000540001c860004006c4180384041c01e0382d0802005a800500c100700340d41d502d04068000c140b04580010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 65728734 1250 65727484 65727523
    0x504050307061b0b0405010e060103030203190c051e1204060507110306060a030213090206160201030e060c0d180615080111040b03010b07080906041706070c051b040e0f 74
    0x15920b44240c2080c018014503c0203000d03404059252104210000f40007a00c69540b40e10b010340d408102081994001c5100b0340c01036585604007141c00e0789001140c1c0c00c010400540503d04804100005050072303e400c0c0103c41d0080c0c10f60310011151030140812001d01d8100700102d00051b40541002c05081540d000f14000724980c404a0101034491000700c4000d40c2c0400210001d001500381340394107440640c04800001610700e83d07500000c0541c4c1003408014104118841030004551b81401001e801001400c020585030510b2520300b1440e00540094002c0d00b036441c0c4925034070005c02601c0c44a401d0b000744080210011060b20700e98900124001e014030b5608107a176000c4400d40440443e400c940040e107466003180d00f0000e014815a001030401d5445400a0003c5110350b0307070b07001c010002400031820410480c111411003900700381c4010702402c1881b500c846500702140f00030400008180036110f540e070f02d010a140c00100107001400b08048188101030b0b051580740800195103000c07011080d01c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 65729984 1250 65728734 65728739
    0xa02030d020703200d030f050913090204060b030903030c07060908040e0f0903180d0606092301061412070908060a020a090f0b04031b08030313021201090321021201060504050307 78
    0xc00a495134503120030b400c1001d00c2e055101007407096184500c91030132847d0440c90502ca01c800244002010964900742c0ea5403911080b0840c50288543e000410b05007201a042d880c007025030310744900004041c0c00d0444030005500b41000780325800441d045920502d12a203a98a55003110f5072100101d42c000705210f125004a0f9100e0400815146035440d0322040c14103440858040c0b1102c42002401104c24940301e600c0451000240d0240714002d1098100071038061941940144880750b048c0d22030404d1012010003180388148120441d031455542e80d00500d10387d11190812503403013040d03901140040c00b0302024020281c0c2d6030303001014541c44c640d4960b2402522120f0315003a40c1e00034401e40700d0051301004208001600c00000c140151100081010095501e882d507509582c4219213040803200c2070281ca804500d040d11a01d0f5a02501000030068070a0740d0b600170346420074003882029240c89000454a250703c0d42e8044440030442d4040110b040e50f9940009041a0001e0003864464091140701 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 65731234 1250 65729984 65730023
    0xa050601090b0406140f0301120c060f2c1002060105041508060406051306020408070603060e10170f07150e0102030309100b0d0f0f060e01090203100203090a02030d020703 75
    0x418050b5401482e01034a890301c1c0c440161203611810070214120b00c4180300b180d40c40740c04100a10700030541c8000500e40345042d0b24200849800030f80004040c440c5501c3c0052150303620903044594400700c0905003a220043c80c02401d41c0b0114280450b92150001ca421000d065000c90001d04031103085e603090002c0690704044142411041c0036825166101c2c50010340400d174284c00c0942c0165100024242180c2d071521a80240d0748243c12648050b40042410032903290705104007030080404008a6410381001150300e506601d45104a010390500300350b180b40908000d01007000c505040900312a441c541c2d170b989072034008041e680e01030080b40141c5540100c65001000300d07481507900102030094406000001c1006005d40030b20359030004000c8200c42c000902a115208070603024884011200710341d49411416254010720140169040c5440000140c0340012018601844410f000d0703169610903000341e25100b0030100281d071500c22601240c44a0f50085014030580340038201d44280070100101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 65732484 1250 65731234 65731247
    0x30f0b100e10030b0d02131e0905070e1608070212130905090a031205040f0804230604060504060c0609050d050309010b0102030a090e130605180114040b060d1506060302030a050601 79
    0x135030381d0082c211200c4080149480c5840c0216500e8101c8009035152034075400d40c6040c002c1d642d4141e1401c1d41c40041c0c00c18008204151001070060009a03216460402c041c500102100387c0c4080c01d1140300400310318968000d21242104019004a40d91078a00e5400c0001801803940706005401e480c0070041884030b40040360184440340c15441d1106c1c0d01102910840c004c03c8010010344140d0461100d803000100d0300c82c003e00c01030241000c4030056880c915111034444841d0011140b05850410040100b203420005540c00c659090406460f60115424540d0207003007179501c02803241c01006100100c5075040ba01440c000c50008000f04a2075000d04d005990f2440307a8104c11012608500c0c04201a240c0484080d41c425010420b00743e0303444055840c0000c1d0b510a035800b02c1440482d900010b4201000d120340014011200340103500c6051580b00c0d40301e61a4054002d41c05103280d1000b802c1844010600894900c04650040040507900c0c10700800039002034802d0800c8905290200e1201d41c4100e8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 65733734 1250 65732484 65732501
    0xe0402090c0f04080a230a05060a0b0f0d05030403030906030b090a1a0405090607120516081003050a0303050106080f09120306030c04050114011103030c0406030f0b100e1003 76
    0x18000c081035122928944102d80111a1140d010310003000082070580081c030400b01d10324071440c8007404001c155880c400720030385507400f1000305030700007250100031402c0000c15075002205801c0c00106040c8031001303d103000c2c0c101000550020341e050100f03c02c02c900000108107d034000e90706c0001d070075100c0318100d050300c40f05400b060f030201c6c031103010420700505540300e0381d5481306101c1c0a800e20420035000c10244d60f011261414030350000401c00449075007100c0042d107002d400d07d004120364504031640e250401c1c030380c401002c03c00c08054005848103483c115081c018513040802c03a001d041e094a802000382200340203000025030040042110301c005160100d01640340c0350054039004000c03041c508659040100f00d16858030070840042c03e10345491007001e010301f00103070380c940d400400c0d5000900342c503101002e100c2242e8001c200704480e80084609031420f40f11f0b1440d0114031000901e82d070b68003130b0800d5281310343e003d44080200100e55400c14982c0312403100c02d03110100d500603600e0050b01159100f4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 65734984 1250 65733734 65733739
    0x50f030a02030405091e0a050a0c050c06010e1008031201080c0f0f04050403030209040903172203050906040b03010e07030e030306010f1107090507020a050708060105060d0f06080d05040603060e0402 87
    0xf44000d01c01c44c0342020b0002e07407101c90800c05500314a090030b205044d50308280d420058199881c1d090005019190041210301c9005040003454240350003811680c0e036005100743c0301c0f01490b980119034000b0300580460010102c0004480d1500303058085410174080a21400686100351401c116030f40c10215420034046038000c00005894800f18140000303400005c0003101050f034200305441d61903a45228500c0018004d03030790456403c0c5a02407400d1040d40103000060300345460151f0f60700d02102070105454071981890000e848940c40300c086a0b4070700841d0800300c50303a0000f1002044a800090342d9070710030f036400c1d90248201c107182422540c4034401a281c0a0000c0c0490084294040c01807a1806882d003608045030003842d03a807171b03543c01103c0050f02c4000c0160000c12038601486000c03c20030b00a000e040b40a04160352401002502c60f209205061200646882541034040c249501c100020718130072041da4203804075884001c0031580316010b414040380c40e1200c0403e040101c00500d9100c0c5138003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 65736234 1250 65734984 65734987
    0x20c090705030a0b0604120b0a0b060f0a05090d030e0306071e0c05150a29030d0f0c02030a050f2a0d1407091a010507030c02040221010b030103050f030a0203 69
    0x25040e086600e50320081c00c045039540c560b401203201d910b41400400041a0a000c0007104103040c3c50420000358014000ba4100e5041180c21200341e607400302100d010748100e04440b503446030300c15800d80f042d0107200304083d807204900268138149604040700c501c0d8203100320159030140ea91400180e4031001205d59102c44840094a021825401504841001c1c0d01400031569849000c04001c0480300302114009581034541400f44250710091403004014005c06407049440c85143d8007007540c6081020131a000c1020803031590724154094040100c54a8024040e070b4840c140314140b09647c0c4101d984400c0651103502240d03503420900e07444480c0c1c2004101000e00d0034110400030003803c14289038054540690061284c2c101d02020070040b0000e040203100480c0c1c2c81290b100120718101104005414000c0c01c100100010f60b02001c040f0849a0403240141c58644171070070600341d80c40160860441006c000008540f90f0701400265048034490300c1142d69800150300d045c0c0c0c607405a4211031001d40e00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 65737484 1250 65736234 65736241
    0x2190305040515070e03030c0c01030b01020318010c080702040504110f0f010c020609181609140102032b020a050d180305040909031b1101030b03030301050a05040e070e0709060f020c09 81
    0x90f04190541c009070185021046400d001d000641198001918a1060f5100102100d0b040d42c0500840d0701080090003d50304041950507041e03000000c0c0340340d41e8100b201089805040140b40c509649040e9000341c000c101e185024a001c4e00200c68070224144140e1054420303d15600c0d140064411340001030f5a100000c2c00c055081c001c0d181c0165682c560f211150802100a070300644000502c1501c4c02c42c80c031801e10359034210107002c102140d0040e064564050034601e038542d0300082120004005039a00b4002180d1b0440751011005610401b0512307580001880c5501982c0310018190030352180c0010444184d94030601d04042d004c6d44001000b0800a010401405603284d01100006019081030b48402c4c0961506c0690f13a16418000c0f1156041b031040350714903591505c10b036910300000790001c624650500d8001013051190b403003814451600c131880b43e003000809215020040014041000c01d50a003401d01501f0301d8018001c101c00509100f800c000d04a04c0050040329264000d48200c41a88 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 65738734 1250 65737484 65737513
    0xb0c0a0f05100e0604030f02030f160609020a0902040608010b070b06010503180d080106020d0f050f070804090f0e10020910050a020c090403020f010e03070203070e1315021903050405 80
    0x969001080d2054002c2c454242e0a902c500e00480c0c8003250200003500a030302e01031a02928850608440c3c404552060010340350b0305c18a40d04a071088160060410740604591810001034a4007400094020000c0c481c0016441c103a0303009401542c0254603400e03d0390707803070b440c02803510b010300500500500c0c49a0041515540100000c5811040c205280c54900f6403566100f854002301d2b2210000107088240100074095040c000758914480c0ea18001300d40302c00c0c1001c02880341c01508005c445005000a010f41008100b200f282c0051100020600010760b1031910300b0002c2005405042c5203014101d1841c0701c001041c421100c810790000c00040035030500314001c450a810681010040d0710603034114038015910055118480e600c69801003c950443c440c100e42034070390315801603a103940188020f00042c3d801082d14800e480400003035840070780e120b40a00401c214110400b030302c400c5200601c40d910341708940007401081c9270070b04450340b41c00000004a0460344200c4001d0700e2500000c407003c0c14070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 65739984 1250 65738734 65738753
    0x303070f12020703020a021503270718050103020307050907120209040f1d1006031e170403030201090b150906041d0f0304170d0507030e0d060e010203040b010b0c0a 72
    0x2040c0750030403007121059400c000303c3c0d10030b0348103a025034040c104000444c17a02000203000c290306820f585045042001c03d111030b19058901070b0821540034150b900c248030041215800400c42d00101120b0840710000403402480e0a0100360701070700800c88045101c0c10840411030107091180e4802000105812030440250403103c00c1c40e81c440d0700c4440c4c07600300196500131207400b40301514403d50b080c2c0246403120300d0502085d9520a1070790a02038200702142e840700c0d8600d403035030110003018501241c82c5090899064084801c04880070b01140110034560b05510400c0d032940314018640c0c3e9604c1304c03000c443e00380c0840e0f048542d000c113403034000446c40c0c02d090700601c545802ca0b0000e2000820021503c40c00d05603152740c3d11440e903201003030410a0100d805010b00700d0030075010181190700c103840002402d80c46107000150a10000c000c50b4401503d4464002c42d0413078100303008008030100c009202c0d010b58400d80703080d500c1e0100940081780d50001101101c500031312200040c01c2c40003030fa5840c0b0303086 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 65741234 1250 65739984 65740007
    0x1203060a09060e06040501151209020a0f03030809070e0105060a03020c0f03040b090f0f010203071e0206040b07030f020705061b0a150504030807020a0c060305090c2805030c03030307 80
    0x212003850000500d60459002c2d0401419448a1001142c50000305120440300140e00c41e8924031086500b18556030b4020418402c2500540f00208041ca414004508010b6560b400f0306a0300a40d042d00005069112011600420040d400c0c1c1d43c4031980c500900100708802c2c040c0a030b10000811050060501950003071814240002c1a144681911a1002e0864009500000c142c80d0000b94007541d41c5020001d2440501048440c001886501c5000035503a025043c2d008103880c0a424020400e0800300080154182d402007029640c1c03030b100c080c00096a0040d440c218080741c101f0440c014114004680e0340705807040a810182810091480d00784046032010484855000e40380040c004508402c200a910a1908030003082ca410180784c01000084000d01190440d00b000701820b0010301101480b204480d02841c0114aa841394200141020002c000403548240081483c21462501c1c0001448403010b08400c025200d5982c410315032034280800410f030340754104000180f0014010b0405520 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 65742484 1250 65741234 65741239
    0x70b010b0307020a050f060603010f0501030c0519030b04060b0108090d2312090a03080606120109021c0912020d0215010306050a020f0403111309050d0f050903010906060f0f0305120306 81
    0xc61400b1340d1115070410241b043c00c030115030014010007841c1d0400f4002d500f00000d069500708090362550f21001c40701d00755402981d10602601400e4001300a2a44d0700c40c0141d50810300302c0203582003901c0c0a00041002444150100303003500005001080701085030304441045480705241008400b41960049010011100c20b80b0b40a200c86400a1300c0c2203140e900c6007151100401c2ca850f00d500740940910001094580320700c404120340041c0009007400c017030450b9040364025031a0348a2400154800f040c00790420045460309650b1004e00003824100360501c10150207807030700288540412619150340d44004940c034103881004000144055010682c0440031650050810700c114181c50f80c55803182d030013a241c0c1c4c0012441d0148500d01624042819141c00b0350400c0622010b585d0940c0f600c0960b1010014400000340d03544030540038408440410a000f00204080051490f0000c01003555000c0e200e03004510f4840130407210362405500c0190b94100c0e0040c04860043d030300c2c0c0c40580d4001842a034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 65743734 1250 65742484 65742493
    0x6071a0408160506040506011e03030302181c06050c0301060f050c0a0203030703020a051b0d06090309030b0118060509060102072c0f071d012a0c0303051e070b010b030702 75
    0x402c1d00c00b124a10500300d611800103000e140c00c10b1b007401441c01106030000d58030000081e00c550343c4400b8949050b011250305040160300c4d80941400b001c6444d80c20234480d90031000c0a41110207607141e4140c00c00f0030a1281c0000c010365224480006a140004d010701404500e6901815401b580101f01501a5009031821107890312140c0e404282945c2010f0b0086000d49d0040c1900410080180325410005038070511280382c43c055400010164000c083d8042c000b16660f04445046c50f21807681c84015540040c500300465960b2525028081c0e280011001100d103004c101007458649060b1032030090005a000b00710320341c02e1030041880103010b50201001c650041800c14580030031200340500c945c2113100b440200d881c0088001c0c0c01c8035500ca1680107000024849045240c4c5c1207450701c00800d080c44500c8a240c5ca02d0480c0303c09a08082401400540c2d542000008055100c802481c55114001f00034841102d51110441c55004440008240c15800d80051142c43c03011006542e0005140c4103c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 65744984 1250 65743734 65743747
    0x106050301020c0c0112090f150e0a05030901091202060403111305040501020a111501090c1407080702031501031e0303020d0f05040210090614131a040306060506071a0408 75
    0xe402c9a000b075050142c140c012400031007003981c0000c034a02103002c0c00202408032440079510406001e01e406002000003415008402280c0d80a52180c55080046d03401c0f07480200250400d07640d21303000b02a10030300248850501003030a248043c040fa0000d680038204c00c1c280b5055540c1c0000030b2030900c01071508290034016100040c0d60900500c0d018a00507800140d5965001d0b80c024040c41c01c881c603e00403541f11100410020050310012811980d0101c8001000f80c03410030225400c004011607510890030205030ba005010021000f0705c2e00b24800c80854076055240b401d94690100e0902c000303450054002c0310200c07400011207840ea47c42e07201c0d03d40140380c400034040e2001120403c84034804c190740d4540401007181031140c900d0000e04460b0825290203071810038024510440124080000302004c692130342404020005440686502407408c9103601c0c4159a000c2290811322054442c60300300000042c0a040c00011100f1064105180340101c240c035480c003541440003d07000310340c030000c2000711 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 65746234 1250 65744984 65744989
    0x70f1409040821040b04110603072c0a03140f010908070f151a01020607030e0703031d0402030405031201090b010c0201030c09081002040602060604060608010e070519030b03010c2c03010605 83
    0x3a1132140740b240a20680c9418a818000c200b922a003101c513001b40c0c42001488002c035080500742040301d0303501941150401c009600d104125104600c466048240150080b04024140000000c5180420212010000d80519150030390701d0120b4080c018038420409036003c036600000b0101c2041c01400c40d01c514501b0b40000500b1500340108070300c0ac0b01040440075000350f0f41440000e030004401c0c902480b00402441d49183c0f80c1281c3d00c002030902800a01e81119022200040760960300700030001c6440346030a0510350748913808111024002040f107030000c0796800851007520800c030740603920401c11a0103035005500030945602d5160910450750700004007a90100009400d415440c2d50142e161071a20502074544400644114030079800c2c800107100499118148504440c01a00041c07000e40f5201c1e0140d030f0f6442202c49840f00c0034550580710401c9500b40e04440c804540c250001c000000805078101c801c0766203522202821850594151413003102c2e010b43c4100c800c4010000104d081e6039200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 65747484 1250 65746234 65746297
    0x2402090a0909050105092802030a06050403080f13051002090103150602010b01020705040501080a0f02010c120306031205030412030e070801060312030b030f03040302060d02090d0302070f14090408 86
    0x604582602c51a00c0c0d0200302003805402e4001510304014040c2c1ca10303201072145c52240fa125203102e4091180d00020555500704003114141d81c003d07a0403c403504090600804101c0203c604810040d038103004142903042c80d140788900c41c2d8000c00506a10140303110b10901030360001d4180d90415464105600d40d020f040c0c80c01400411540d0000103010040500190510400f81c0c4228481c0d85401c00400081201081d01801c4a61198034400041d42610041e01d0403500244041c002c4040c10750040e00e221f8155000c2030569000c2c0c0c21140c0b090100d96400c0760148030846d002060f59650201401c40280030707800c104015050a802d6a403036a0f1140119401c4500a50044c6c40b2021075500c1c0006040d018458104012815000f81c800c02c0d980214040e6070f803182d03101c02809080000f07810005915158190713841d4810062500e1030307901e501e0800a646086500680104070041200003c804689074400e10303046070040c0800240c3d03543c903210340340c1c0b0360440c1d035007070009001a03500143d03800c0301c000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 65748734 1250 65747484 65747489
    0x308071214090f0106090605180601020307140102030105041413030f0905120c100e061e13090207110102062206060e010806070207050402120c07020a0e0c07060e07032402090a 77
    0x200284020320f94414903a095a00a511150445180000500c425160200714503d80428008040520780b11040101e02c0c40c40b42c804050520300320b0460701800320106400460407903004032070600c80c5244004846411001c25035840140d141440f202170002030081c000822818040d09040d41d955030303900d0200e10040901100e50159801c03480d141b4200b071810259024009213281382079080700c25002e01080c9903100765141c07800f84680300044c410401d104203044600e42e141088010302079075075a0b80d40d08080d400141c011501080902c8045c5425440050720a100b4042e080c080003401c07410070005014090000404d03110952242008200310410030540c41c028010700d0004c2c10281341c0582c2c004e040980b1030b041140f289004100445c0c48400c061800c6030083d0101700d4142e581c0c10140300284d54258294040f21214000c10100441c540c003d42c042c240f00303401820103121001c0f858500a803142c1e503a0000401154003c802050002e240081012207228524001441d01c0401d0000900b400e509a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 65749984 1250 65748734 65748751
    0x30705070212030903060c0c030d021305131a10140a0e010809010203070206070806132c0106080607051c141b0a08011503060915050306130308071214 66
    0x542904600b8500000541c02e5120b00145051040880c0001c2d12a038000e000924031140100301c002d40c5003806d2013120603049c1e07048030071561102c10911703010002505104440c40b406081c40e2b4901002175900a08c21401039000c032024001075a14100616507a0a540860421031000b0399501700f441003400070a10710a640d03c4151a0420f000001420f0910081500d40664010b0044c49186070b00000d000c2e4105a160524040c0795a44502040e0100080c00354009518140062080c40c0d940100410700300802d003240caa440b842824429500380c40c024895801e41c0c3d84100300040d0031078800c201510403c0c403071009070644021410760a0044d5114030743d0440400c250682840940c03006490901858220b8102c8a0700b0024074074009400744205108541d2010900307412440a00e110307601070005000c10000401012a5014141b10046e0050040074080e21402c40800c034060f418428031129298903a85e041076540c4c2d031104c11183c3e814503151018160340c40340c29881074006038600b503900c15400c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 65751234 1250 65749984 65749987
    0x1051608070506040b180a06090f08031602011a03030306090709031b080c09160c0204020f04140a08010501050904150b180601120c09030b0c0d06150206010503030901091211030102030705 82
    0x60801c0c81c20110f000e405000052404021b4103e961004210f40c13005542042d40003901c00c4d40c60400784031100079000010403150f000006c100d0142d42c00e80900c18801d83e542c1c02000f840326003040e50415a0748100c1c1c0030f64107034002c0c400600d45240202c211580180c503032400c00322080d41c030342c1c809a032002c1046409a9800c1c030f4270401c1c131999804010346481d2900c22501c98400d810104071005160b101040c12008000d800c1c80c00340d09540740c680460380d074682c00258007542c0300d40e9071004a0080c01100703000e40c41800d0031180012a54414003507541a94002816442e0545a40c1c0d00d503030f880404e0a1a0070b56150700c5082c03a0398507580d00308031b0303280316032440c902414645400c00004003040100690395450502d441050b4800303ea1151030076040e01e40c05800d4810940301c1d444406441d0044550400101d42440f10110701e80e0f81012416401c0f5006408807401640c07541d040580f240500f0801e00c0c00294072361010072448005860050104d800745a000c822a00840042400d903801141c40e000070550 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 65752484 1250 65751234 65751241
    0xa050601180605060706050a09120e090c03150d15060f1d150607030207090e030712080106020c101b031d010c1203051815070806060703020c01051608070506 69
    0x400291503007032141003100300991800e00f40000c610780100d0801410155482d00018a12001523000003038039504070040c1100554100402080c00d000d4000300c034029100c4101044018194506880c010800000010800019202801140a150081036594400c0003031094000741c9507200c0c100141a0001005040350308203649000c000e54108000042658aa003c008039103c006007060f20900c0c00f1103c850351021181022854018103030464464a0f282444002d0403036000030040c1455449105511603281d0740d44004c0c1c58120003485a440560000c2e10302810714609202d03160300911742d0f41000d00e146a50941704c2440e000e0741c28411004208101c0c3c1140c22990a4103000c0078900003464145182400c50b514000808101280c80c0300340364545010504903c07410340007070000c0200104680d82c4402080e01c8460415054841101040202c408a03800d402c00c9011a44142e8040d0000c0166000d940300440f80d070790040a52890f21140d2008180000b005c190042c005e55018000a001a04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 65753734 1250 65752484 65752499
    0xb0702060412020a27180312020d06091a0907050301030506010b03071106100f091505060c190b0402360403020c0a03060209030c0301020307170603010204030b09010f05070e01050d0b03030c0a050601 87
    0x10300300c04d1940540e044076401b210002e54842c45d4110310804424000d625412840c40390806000b09400100c8a1810b041c400071858180c40c1c48120100b0b421100c0300c00d0364503045401c0d2031500c820300019080780c1150f0018800312403042c0003146c0102c10741c60441500c04407c04414201041540c502c2122151808100014102d071880c64000d0b10245008100706071413035940d5020b141c140c0c403d07035026070b001040086c10510b0600c1050945540280c00741aa048203140c2001c410300d04880c120302c03070701d6444445924003003400b001410100b081701d8551500010f1034280c80418000800c21402c51050b000d00d20540d03100d0700c0280000b14403c031405a01d0704104e604050802031882d40c018080ea1061041003952540105404444400c1681c2c0203540d84039007020070301910840d00040c090070740341014403000820550019508640c0101c0410480d100c0b034008661303500740341c081a0f000803420b008a80f00142c1da039022000d1048010201c1e4a000d6050000c5400c04c1b00d1b02c84242c45941140c0010000780 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 65754984 1250 65753734 65753741
    0xf0d02280e0a0905011508041403120a0f06140d150e0304030c0b030c03060d060e01140a0b01030b03060c090414040f050607110307030c11130c0201060b0702060412020a27 75
    0x100700480081c40b05604286c43d4002040660841c1400c01010b280401c007400750b4601444155000201541d95400802172144a090000d44000e002949010801903140c01c0c1803150b40f05a904000a145494980208125810b000e414045c0c8005a1511102022050710321034510b44080c3c11000c4c43c4c4903455404c118060180c1d40e448240065000c000f0000d030016902d04496212a040350081d12034081d5090004c02403541c140201d100350b203000d0b860400f01e022180c92510811040707030b0a1264081c554011001d03291600d1103590180e0014010070780b050030000103040440d0001e03100045a00d0308442d055414501135806803030900340b01c0c94040a009080c403025500110302d040400e444024041803541c0c0740310702000030b01041102084201000b0108803070103150180105403044c41c41c2e003500140001c02030303080c00da0003642c03a21100190307074240181078413003594004203803906152404503d15200d00001c3c03003c90380b0559044c0041340f10090350342c00c0320b001094032100103a101b10004112049 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 65756234 1250 65754984 65754989
    0x50603190209010509070c050106090603020f0f150c03090d06051e010324060902130918081206040b03031803010b060319110903010f1505060f0d02280e0a 68
    0x103100030011a03000d0b031a0b900c007441c1104d1091794042803c0e80c0d04902207450306070608006000b9405c001000480d01816004201540e00884980b4030b41c002110400044040c02d4050340c0e00284600780c1518901b020402805500c1590010b407031500c041100001c2c841030314110215111aa030343c0601c04210911800b0030319148122100d25615411900c45500d420003001c0c43c2c0042c02c051030120140d140041d0803290040c18021001e40d1079010300e5403800700400003070082000c3d85160a80c0e9254121040da441803030382c2c0d005076202e0300e082e0780301c03010600c812002081650003586881005886450400003480242c5110300381c084215010020542518039008019200d190140240071081d603c0070304988540b2200d880004041f03008400c201c2c0c0a0050180c0c0a0749075191400112500070359400450250740c500360203030710141d192010490b10703014407800009040024001121741c04807035401840c203007180e01240711503403410040400324003800d0043e0700700203002c558030050607060406080b8007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 65757484 1250 65756234 65756263
    0x1005010b0903030f03090106050d0f0b070207061b0804080712110105040510080703110408070617100314070506130302101416020117040309050915060301030201080a180303050603 79
    0x1821001c100060383d00c0c0950218010310890000105088200c01d502010080c10003428691f00d104060803c03082c4c010f000320b81600c00041240c0007486541c40428250b00356050b80c1ca4201000d90b030782841d01c2d0f43c60b8042200702d071412400c1001003803120080100c04020251202a43d00c03942c00342c81c00084c100b01804815061180c10311060140341d0b83c255110b41d403072b8110b190000090b41c0d5141d04030082e11000c8410380e40f80c1d10025000c1054440443c48906a603510b460f0381c1e104106407036108414000440d034840b444003e411051000402800440d20660358510456410b0741e180c00000d203242d170111040140518501c401001141051007005004808074205250401e6140c00300810701d00c15840e2001c03040d0790b541d035024116809100d40c088644040001d8548500d090300e4090701e40c29840c018a841200b6400c001082f008451180d89544000a0511411641b95a00660382c000c0c028155803c01d548458600140140501c00c00031240e0080d9404617403410050240350034017051034030110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 65758734 1250 65757484 65757487
    0x2030a05100611150a090b0702030901090f05030c150f190e040c081605041a04140d120e0a03080d0510170a1202011104032004050f16030b10021005010b 67
    0x24030360f19000c200c440580e282d0450b108015550200c0e200010401d081000306105918020b010b0150b6000010300190071003a2070b07019202e5202d506c0000b85090724031030340740c2c1a030140e9584402410300c1040d41107650705c1c4000381424030300318404035a401e0f00b01250040504000c14072544010368030503160f85454106840c00c00000310310b40d0340241244001042c481709114503011500f0aa0304c680304a8000303142440e18403020b002d02d090700071110b40c400c1c03207441c40d10304400031890f40c54035150800403d15036211510659103074070b420056a04145048140e0740c4201220b0001000c540346000914140c04c0070b0800203124070f0f114580c40402078068001071480d0348207a00803088180f00160010105410901003180713424070b590b04a001d0980450300820088001c2400002c122002d0040e4040d04a03802d420f8403c4940078051000319802110200d5004100d140440c1c084038808402c011580c84610340810007031000400700d80e4034812008c2000060740b00500030b81c840e40ca9071041a003d06034401805 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 65759984 1250 65758734 65758757
    0x170321010e070e060f040303080604060b1614070b0703031401080d020d1b020604170d0302180409020a08030c070906080c0603061908120913200d060902030a051006 72
    0x7140681001419142400b0411424060603a500025100340075240c40d01301d43ea0f540c507840c0c0100381081c00c0d04c040303002c1d0b810042c0214503441880c1c1980d002ca41c0310b00140c20840041d88810460b035031018030f840490f002c0c034032002c00c0c0f0b0410440140741c401c2c06a240400d101c00443d50715100008164800300254100d05401c020709640411119580300750361602d240d0281c1c04000440e580d005910f002584200002800070388070320000c9070400d0000c215400e480c0292944481513003688a440c41804440100d0703406401989041d40c842d00c0107900160070890750a417980d00451665004c48a40700b00c0c8d6108802c2003001030340354054000644104400340c83c008500c000861002c2c000a0f20311031003225a151013880c400c0480d041c45006124903411115080701084401086034030003220b103070050015254034840710105001b800540a040300c0c420f121404e0040340a60b0340d41280301081c5049403500c10010712900280061401400b10100020300783c1400c810683d400012a030000003801080c1058 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 65761234 1250 65759984 65759999
    0x2060a1407050a0e030a12080903030c030c030702010b040c1e02030c1002030612010c0c060b01050909010e0901090501060e0106090e01240507140109020f06040305210417032101 78
    0x1155084021402c00319141d0509140070780c0c18182040d0072a4043c031612a0920900c862968650b00ea040b990300e80c010140c0760201303010b071039201c100c410032150320080021910081c0d00e100203503403000540c40001526000103001a041d54400d4003258000740904010304840529180c0c0100da040c0c490000b98a0200712400040d240c1000c041004145540400000c43c1c42c0c80c0d280307000180f002e802000704001010302c48003600220380f20b842982c00a15000d885101940202c0494804043c002c221221030382c60051007011401d0010000c0d40195265641500015801d0203418040e0084c19103240303a540c100034005090030b11940c000d4404401c80d20041149080008561085900419900260201000043d1958883d41100070300c0c5032490517145001c548103612040032107100f203400c000325204920130804280a10700002e0401c2e00800003444e410380290303405030f0b0340085808429003001d0751220a44400d0600308049100758000048481406501400e5042c0008443d4070341040355040850 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 65762484 1250 65761234 65761271
    0x50717060f0f040b0409080a020601150c0312090507091d011109100311090d080318070b0901050d0e030f0c0d020d09030b1305060a020403020120150c0403020301050406090302060a 79
    0x103002e4041c0fa80d850b841c480d40e88994000c2d00c030075a0424a22551030703462280080da541402d00c41c158a80581c0502d283d10148200d1540e0303000c58160303880c40c8480e000c0a000030010302021a00321602e1096050010740302c52103006603041d510044a00955044110705040d00356001e5041d0001001780420604641d580d0307085541d941c20340c4074a000a2040790201040d54641300741c0e040582c0c03042d484c1007041c08100c0010f0045104480c03001d004440d41d00c096191a42d940d02c28000d581e10644180000341e020351090002d8500c9060714040400c42110000704103003554480c2c0c0d04540c455400041c0702c0d500290400a10040c070340f291004020341d00c9100c40060103013009000090902c1c0c41c1001280411200f0408540b950360444c00307542c02400c10b04400070003903100e40710407408242950145039860b64460108540590010301030714003c01e0814242c00c0700c940050034110034101c1440b001c4056242403180c10f1280c0d00c20200041e18a61701d04000c0d00c0d110340105034000941c1080401d41a40320320a4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 65763734 1250 65762484 65762509
    0x1c020f0d030c1205160821040203071a1303050606150403020d03030c0302120709060f09030c05040504050a0501020307052701090905060a08010504110916020a0206091201050717060f 80
    0x62051604140703040f0481d103600c1590804040807510b180c80e0024071103808001c0a000d520003984950000c002003e652441d41c04440195054214960411007025655002c1c03000c1465010002c0c6001d01c00301c2c0d8028140440d400a655a9010008011850510b0304550440800b107145450a007031071640080c0d88003c1030359004042585401c5507445644c0290161791201015040e403680d00e103800c030001040364440e882a6000241d84400d000d803e98004d01c8c0740010349800078950101607041c6000d000c040c00020384204c0741481840301483c0801c1c42803000d90b0003803002d552400e84d50301c4000e410885451f0f01c0c540094440c04180c2002d40640e0304500c0718012990b031110040781130303900e55002030146401540205041e5090004002c10414038104c260010b50044441e040300c0d0700e0b0611b1440109000c0c14508026902c0011642e002d8500a006001122001030002d902d0240900030642991030075a07050000c101d40401c8810607200900c80c3c0e40c0d100a083c0c41c6264054901000115001c1010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 65764984 1250 65763734 65763743
    0xc020a0c0b09040b09090a110f060d1d06090d0f050a0203030402090402130207030503041a1b070611040801150501020c0d150e01021902010f140402010305090c1c020f0d030c 76
    0x10b584802910307150000882440020941d0703040307260018440380c42d40c0c04080c0444603078190440078502e614108000104480c00940b00300d042068006140006003103001c040245003502600100300300da41000a203120f031040c90080c0c40c15000c40c040103030548054a1100c0c050003005d1010400640d4008180c039403140d012107012906881e540082154480480004d803661400090550309258100c401035000e0340c42003196402d003410b68410100e134050103990b6480c5041cac68460301c4149219000207440c0d124040c98000074003c10f20200c002e000e5010780d00035040b69440f554000d00c2010000c02c800000d0000b0f0019040b2000311400199032a003042c0030003001150b4a8419038040f09159001034210000d01001715511040360306002014003162285600540c00c01404407204600d42c003541e451140070600030007060311180e005401401e00200604054420136810311825941e0f135000c0d01000541d5500d0400502e018014004980340c804100f5000b511841c0b030540010390701c8180c90b5a2103800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 65766234 1250 65764984 65764987
    0x207030209160e0301020a030903020601050a120f030e09181c020303070c0501060519030b010b0a02030306040c12090c05040e06010506090418060227040b10030c030b031903030c020a0c0b 82
    0x20b00006560062032656810b030550300c041200c0d40000d81507800194594065000c54000faa41c400411200104a00038034420300040c042c00e80004503c80c0007030700014440c0c10062030075240f5002060020740100d43c0b440e100040f11050704110701c014020344140c0c3c03c0e4403081340c00d02d00e00305c08060b50724071002c0d00d04000c2085a03642142400401c0d031001f13010300401484d01e4940003110700c2240256881d800181c44800d101c800000d42080c8402c100c0b440c1c5000303034001d9401e5a549801308401003d48581e41020302514000e803070410714403442561201c40c4100d0182d0051410601400304a42c3c070261880c00540c021401400b103641e0341816200402c00444000c03540c010880c400440b40b0240e00e400500c0c040c00420300440500910f80a005269008003c0300507045010b404c01c0181d44c10401e04542042c203090160040d54032941150054482d1805d001c41c6501e40000402d2600f2980b0546a920038018401d80302010350500582a030300c0c5440c0700405500c8410344420101c0101d034441c403941d4120 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 65767484 1250 65766234 65766271
    0x8010504030e10110f0607030b010912020607031707110105060f01081906030b0a020307031a01050306040e21220609091e1d0606040204061b050c1504080105070207030209 75
    0x4c100540e60780c030b602140c00c0e980158444000590744260503203021002c64101100d600d201d512070b0fa16902110701560304541050107540a1042580c005141502040210720040301c2195071194100e019170030686c1c2d403248032803000700d501c1d01312040070b003402d407180310802e401c0c003084c0c0c5e4000046078028080360b5185451081051200c2c00410302c507400140560080000c02c50201899400303548118480d850621003103000790758180001d020840154040b800510105446041c60b50251886100d0310b021280112107519103511080d105420001c894007002503140310581c591244841a0301115440d031040074141070b4040c0c0895141d00a44103041c2e541d60442c4007080c110b132200c0000e02803104007009108140200aa03086588401c60304c02e80c4035207000300709982050301c00c03502166002d55910724860350342506040040c50038001a41c80e442607607001c0701145c2e20189500c0d510302c0d0b0103a040d640c1d10b242010850941e84000c01035015034204030000c1000d0385a02144540c000721000d0002194078 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 65768734 1250 65767484 65767487
    0x60e070906081005220e070305060901050103080406030c02010b04020d0204050111030c0a0f05012702031b0901050d030e1003050108070909150207062d060b190c030203120c0409050108010504030e10 87
    0x3417505440100f15040500311402c0d03035008036110040d00d010b40c0c1643e0107541d6402140d82640e100384401045900200001c0210a1082e03012015102881c40007041860305000000e01366040744801300301030b42e8002410003039903802410050398281070102840c1411064081c00342c540c01205406089038401903005c4081290a5104400e41c21020000c459185c159904000a107212500100d000707114200a0f0300809840e500405200c1d1001030103514680e00781800d04c2401d82c6401400c4041c05056402ea40442d51001c8403075480050030b030380c009410345c90061118035250f100e031b200410039031902607280c0c00300f81814105183d9003810300c00513a0b01d01c5a0302d490301c028102021000a55441c400c0401749450b000c0340d5600c1c0c150741c0790348140500340e05c800e20140b240c0704010302e00082e80b00c8220406281d5014082c2807621501a005aa00b006c01004052801c2c00d0121000148e0354030020b002c0c0b0422206104050241180038000c200034681554040d029103040781f103261240000b010300c84080d6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 65769984 1250 65768734 65768779
    0x7050d050c0123041e0c0305030a1d03060106110f1005041e0c09020f070203010507020610080c010816021204030c06091401080a050a0204080a0515060904020a03080a05040504060e070906081005 85
    0x2130b4030030035040c00d440d40d0f0b04142c0c2c0c503a040ae5821500081d40c443c0c040c400788407940c26403c621400240981a140d203421000e41c0c29188000d6005228041c52a41165100c03042c860341c4003481400308040381510349454250300c1d041000102d0352599200c1721040001c200286a05c2080e240d0904006035501c412543e550701c24026200b0095056080004201c4403d5020440e035025964880003941c02540301c18200303403105000d003016400100c0e07000c00a41702000e050354402c02c0c00c0540c016580511400d180e070224aa01542096801c00700700c09081001991140214000342245211910701a0541000070b10001000d002c4c0082d0f26200ca020070124544e40d41210001c0c400342049640d507158070320f0100d85983c45016421010130749071000a10700d003820b032400d0b403140e50f004082c241c10340d0456440b0f000030303002920451f0821105001c089031710f80b40c5d172003444003904801c200803040d4078000000a200000d03c0c0c102c00100b0643c842849000c0703801d4030b0f19000b070b158111a42c01440ca16519240e420 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 65771234 1250 65769984 65770043
    0x207060c060b0a08010c080603120f09190b04030c06031506180e13110f01050a050d09120c050d030b01050405040f0f020f030603060a1506030b010507050d050c012304 73
    0x100e000c41d40c001444160540c0b04261001b29500c50811542c0c4180416807600b00140e411a4010010000d40d11500c035508014003c1e103100500d4841090460280452001c142d80c2025100d140001001d006004d030644001008001d6450280902c0c01401c8400d650705005228920502c94800314080811744807c140e80040c101600203000c251405070070040226150500580340494103001521403410041e00155210354182c41c4c0f54030b40000720400721100d9202601c045862542c0e07130082c00014018000c02da4a514859448480b8802103082150505a10500460601d4071f80b003402202070b40c10509580449104480c000b6906410b181c1d554081c20714110944812440050b01c2c2c5a002019800740d40a51400c1e81244d08a560f0f07000c01d00121111852607640340d2404940401209202c2c1d00310500304001850424241580c555546190a4040100401051020521103000383c402d210b550010041d0b00221203405010302a04040d03584050000340a120307400c4030348000c18501c1741c00e6044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 65772484 1250 65771234 65771239
    0x20f040f0e10060b040b030f0c04080a0809042409050702030c010509010e2107060b0a030209070806010e2709070308070303050a060f03082d0c0703050f0d0207060c060b 74
    0x120304104400d072034076002105522941d1901c0c1800c0071035460078074010344003901c0309120381920b19210140c0e800150240249441c3c1aa03808000c00f05550328103210f000c8015120b40c6005403100d52750820001074604c04600da03440c00f44440c0486001148440d541c8080742d2402e400018280c8800501304c2c294407504012404940c20001132010703181c4150b00c6030028407000070a48424015440012402d44100e400e40307100c852041c010000450541c0d07020f00c11030f550080c080c07000d4607580d47c0850113408c1d0841c0c2e100003240c0103100308846075070018100b4a00305000c86110b041c0d00000314001c401c011b1b07c2030804a198000b8400070f01d003107800300081005107401244141e2581c0052130010040e00048407070110b818146100043c0f01441c0d56400000d9a03030100419003484100c681c40d422140d10035000030090040c1c940d06a0318074410600030310990109902030101c5d9811400c01c80e18100c0b400c5103032199a84068112007c03594042660301c19076109250004d4000300f41c1c208200a000c4c408619075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 65773734 1250 65772484 65772491
    0x120b0402010309052d0d0e100e0604091409010e06010506120604090c150e030102040b040b03150405090f15061008040512031503100b1c020a030c0305070501110a0f020f040f 76
    0x5d02d0f10f030f595140d000800d001d0302142c4850250002c2100c5041c188007015402c07140041e242c404040c084e0340c85980010f0b010f4006400c1c15a50482e0034250740f40c14021001703040c1c400c400d01c44001028042c0f440d094071001d0041035554984804609103204000e00424407a0340903010032607079034490700401e09054000c1d01062540e502c5000396100240304107080408508000700c030303040906043c001d40b001c81d00e0200140782801d11b004a041d580c2d40c40200304650032510402a040560794a20890f806410524010101561159034091420700c7c0502201c050b942200c0030458142e840001240c40c44240f482c000019840d14035005e46401a1000c401c511480080b0400850311071140000010103000c4040360b015154003442c2038112074010f804a50000e050901100c2c03d12030b000a203410552020f07202418250384c0307480380c8812180342c2e04101e8203908100c0c410003a0390703030058910800740b9149020f000c0340c1e6500d6880407102c0300c502100a0050043d60380d181c50070360783c84d03104a0200740e0703004051 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 65774984 1250 65773734 65773783
    0x6021309020a1107080c010f03140c0a03150e0115020a0812060f0607210e0d05010203070f090e070305041505071808070f09020c030708190801120b040201030905 71
    0x80d402c4100b2030400142c06810500038a940007868a0443d448040504011244c0800440c0c4803050540ea038010b00d501c0d090280704540f030700b0720310500c5060301c81c2400e6100c40201c000142603c9000c03e900914107418941442000803128681c3d045032010900d030103111184490682c02c04002e018080c161000c0402c06068204a441c03a140c1300e508110b4491405445043c200320090064030405441c40388808031102c12a40340e8491202c10b008207041c4680c3c06030b0b4a600040131086000400c58484c1d4012090160f03042d00000c400c1e45100507410100d08450611075040d0f4480402480c3c00c080503100c00104040c0134a5584150040c03003041d10903c00c0789001c0c14068041d010141900c8003001d85501c001030014004121003042e0703010015481c440d80d150a1624000c0c0d003025201c0310b518001007104100280b49030006000000440c607109465941800e00644882070591100310004254100302000501d005c0b20207902c26130901300050301200b01d0800510b401c500d03100b001e080d0803848491 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 65776234 1250 65774984 65774999
    0x4080301030210030621050c03070b04090f0605130f0605040509010207050609161403070905040317010603020a0507080a0309080c010e010b0f031e03130609290412060213 75
    0x258140c0b0700a6441d28065612103a048044503424800c4440b45645501c981a05000f802c0c2c00700030580c0140301303c031081c00261000034102212507210240c4440001010055000e06000d2f8141721020b5804c200000c03840c00300031440b0306440c088403904240c1d40e81002d240614840e8031420260a000d0700402491a00040c094000e41c001c02c41903032240325240006000c14000141c0c0403030700b0511b11030381e50200d15140100c110003010751a55a41405a07aa01103201c0945114207403103a0301942c0c039020a0f13031003500d90030019170040e0080b1007051700420081c0c011680280072200340039032040000d6036420080400f1001440b030400001d107620000507145424040c1504050034106803100204030398001f140c1005140c0c5000341d42690160400f1601d1111644540c0c000d010750b1b0080000e070392030503100701003c1000d0101c941208011540300ca4007488174400030119410403403c0c1c0548184001940c01e003138016405244580054401c02070440c00030000113805030f8a940301040746030040c2d0703a1107403035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 65777484 1250 65776234 65776237
    0x30403080f040e01321f020316060501051504030203070b090105070221070e04120c02010c05030304061406010c17030c07050106091d07030b01231801030b01080d120906060803030408 80
    0x481d055061001d401910251021100e610000c070009055414442e01061321307803640b800d4546c030070003940814400c1c1c0c2805e8040c05036845040f44105800205581000c2c1080701c0c184400c0400d0982c030405000070310050710002001c038161000101401d07100c44c02440102d6940c45210802504540750489032017200c001102c500c1c0201c0c1e103120645c0c02e81034075110141072200044a015080102c10540c2c0c0100034000c9405890045c018544008100500c2d2a214615801550112641c80e0741d00644011260707940b0034560041c0003407801181c00c00c103649a2101c039410548110200e0f007000000b190003030349202c085410480c0e02200901c0080d60307844404c0d0003400c490120b00c44914400710311090614002c50241c00340e0ba40260300301126400e200e400541d40440170758080c02a181c40000d181c0d15a186015a000e0010b44c05030302c0f0b810342c110303d0000f024640680c01000c441e8010242055130310b0f044441d1154103107446400003441001130400d40702074000c561020041d404000140014490381c5030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 65778734 1250 65777484 65777519
    0x60406120b07141314030102041a03060109270c02031b0619020403021507020a0320040b010201060602070317120f01080c06090603060d02240a0917030403080f040e01 73
    0x3143d030b1103801c1d5400e04010341881410103484900682c01340900a01d0070030700722026403120180005041945841003a01c08030100b6074084541e04000c400c116941d0b0340b160505015151000c402c3c00d10300c00120124a840d8010810180b00c540c40d080600540b600c01c006070b41e0162072554a0b00d4a45c892491080d803208011350708400740d48200e80341c10303a8049035402220708603a4003505620000420b81000c100c1a08506000c07039000710040300000100e8031542100c1d00080142088900c021035100070001202d900015441c15641400410801c094020942900f100e40200c0c2c580c02009052004500a1180550340f210711104074041c07003031200300c030611030b8140c0750f14004075800343e0050b80402219020b04810a139000f00c041000440c04e0801241c1103c80c5840034001503000c1162180701d0181d801c000b0504040f48001003039001146500a12000090144041007603800e000c50001c95241c0c890b03800701800300440010f03840420444401101e00404e444100d550055031038031901c00b880130302c20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 65779984 1250 65778734 65778737
    0xd0e03011a0102030712021603121206030c051003021b0708100501150e0d061e2f09010c12050d0c020d0f0f0306080a0b0405010c050f0307030203060406120b07 70
    0x648107221401c840360200c0650181600118200f200681c0d45c1540c8185424000c0214000c00c110007211106035045a4061362040400907050020120014035505084480f400380d00d040c428200003003001c01d90101c050b12410346407521072050100040c0c1c0644111055030460445000f10b1a04425000c94003405444a080a0f1071440d400c640031902915405c0c010001220042c0c00281e8966000d40c07011a01e911000c0d06902c5c2501c4151110b4084405090500c1c240200c91540030018096901c500d1035a403681d0070424514501605440e8001c07600c1c00100158203100007200416070f0300507a548868550322644115403c0c0641c0707801080c58010141c441d061609040c0000c2003117001007840314006036550ba850289462020040b135001800b09024800c1c542c1d54640410b41c41000d0040f04480c502607810f024031030806290281c2160340f0000c920041001c10300c80981c40c0e81c0e2380c070104c90f000b0185150160f160f4842c2c000050082026a02c00c035403003140242500c0400480400c05441515203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 65781234 1250 65779984 65779991
    0x7060204030c081b1c0b09060603060709030b010317040b0a0905030c060405030613080d020c01061a030402030304061101150e04110a0b0702190503030304150c090b0f070f050d0e0301 80
    0x442001641c0c482c80b03001c000342040407828a8112505020303800b000d8107880171540302c410300882e84580544020640780105540c005004021140c102003005503003085d810719040120ba840d42d26800c0794000107010045c090718621a110840002c8001a203001c0c0816500440d6501005080504040442d10a4500030300481d002d000d424904032007600d0848201502400ca642e8640c441303200800b1a651048030046414071130070b0030700c400a00c041d0625103405400028481e08002c900010581c40c6450000c1c1100f04008000042c3c40c04000d17281101c41c039062006071400140c4e01e080c09049268803020485084c000b00040c0d003109204540d000c0d6004441c800c80b008200390a100c8146050b006050b910a0100618401400c0c03a0b0b5414411180000c4694805600e81d40083d00b5988140c070252810b90001480400200b002c1c03082c0719209540b4104050007904d07040e10203103103000e20103121300020400b0a5810620002101c6d01e000c5c20b520206482d00035143c0c8201500e1818048042e40c040d619 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 65782484 1250 65781234 65781239
    0x1270303140c03010302040f0e1606080c030103030207050904050f0307030509040b090f012102030601080d0206010b190f02010f060b031608090a110117040302070e07020c0f1e0607060204030c 84
    0xa500030750182c5940005907180d0b03800d42e000e2101520240351020407184c2d40324070101000e5424803100000c4900540f10b01e00c07061424000410103000a4a6280c55640400042000a80000d921011034030166064440c50f525424201e08140c003400c9580381d9800006804420168401f0080c985000212010001010808103120f808202141c0c80a448195080140321000d4008103010f80711020584081e812202507001c00d0908600782c0c0100001d5109480c0345441c5501481400d0141082102c0d250400b101000c8040c51a680b060818051000c41800000300f240700b90800c210301c100000f01031151070f03690601d04e50305510480c3d5070354041081c8800c0140e950301c00d1412500a032440001440d134501c050f00c07180c0ba0040c104584505120984522001d0f1b082c004102601c55030081d004ac00c0c0036460402521003904000b031400c0c0441d0403840316038005a846103041d0145c240140d481c0800d03564a24a845600c82c0e840c50030076400711010800e00e040000c581c00402c1a6032242030741011556 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 65783734 1250 65782484 65782511
    0xc050705070b1c0218040b03190209060a1707150201060b0f09030f06010803030f01060804031710170318090f0103060905070509070210050c03060102070902030901270303 75
    0xa040000340355401c40603007000400c204801400b88080701d04400b120600c409102d2400f01d034001c6952100034410000d5003007503032406204000c0c8450042d00a483c40c1c03a1f41d4034040402d1407900400a10800c112804209941c403882124130150540421301e03400c000d20340302a07658500799032082c101038840b0440d1020a17144103000c2e0340d0403034003401200c0f820000000d1034a0f15541180120790340501ca60002115950010481c50f4001d1201d007002d983d072824903440000c11500160004000d101b80007040c080065481404070204450407485603040c1d0315030502049007880b055201100411141b80c0a452518000c0001c108410b180c100126120f40c00b8418000303004030071603404956020120040000c100e880d08524503062203181500c03409030b1079600041100000384c3d80c480050380401003001a0b95000e10a17190841040c01c1e40038110f1901e440002d6991049028510030303d034010000c50341168007500109002900f000720740c0d520080c0c21480a105606e64030080c0c0000b0700301054200c00c80c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 65784984 1250 65783734 65783737
    0xf0b0403021e030a0e0603040204020708070f0c050d0209010302010e04060f170f0601051f02031e03190501140103020703020c03060f0f1f060509030a06050f06030d08060603040b0613020304060507030c05 89
    0x132516512400310700c901250400046400003002a07130026000c2003608009001400140901d510030f071481c416001e002d050030007030780c4c90350b40025005540084902015036500b0343c523581101c0c0c1c2481d2031403881e010b03c404240680b0655000ca1400c11365040003080004100e5100381028622400b220210402c02040c00d55604082c824283c0049080d042d2030303a40001d01c207000340d068035140100e0f441c003a85d01c80000f0140340c0008a000c08a41d003c0305000c03401031180f2040d00008034002c800c0c0055414003c409820240c1e80b281d4606140d80003400204040c001d015001c0290b0006041d139010b45000c12100350300c00411207000c40410000000140440320002450b8003c413071001400f000c0e182000c00598a950225240701c1c4c0c5885048062000120345006280c8a183c0500c098889802c0203414036141100d00a0035078180243c00b002c010158445000740c80d4003907000395011800752200d40109410441420f02010424000420402440001d41209005070015074081000c100c0b01c0c0c004581e035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 65786234 1250 65784984 65784997
    0x90f131a03010b1f0f09030803190c030b030709051902071b0510090312050c0d020f06060d0f150207050a0b010501090e0103030c0308060a120b01090c03060e01120f0b0403021e03 78
    0x6040000030f500004c3d01c6281201d520000e24248102d00c40e0b100d07218018250411100007104044c40c488481028015015401540320581028060481c080c0000390301c0361202e00804030440c1d40c81000030328042410003101e01ea401c00301402c644c0c4182c0c42c1000e2625018200841c562021400310014440c1403d1541111020f22580c2e051715076811030b6108038200095882580030420103000702400c040050040c0140c0054980044c84030310703040380c045810720500410350351013107100d1300301c0c6c0010a010f041020030440c0e10002107100c03140084000d0b8000d019080019049200e0911040100a0644007a6050b1082603d407010b8013682d9817a01c7e03e8500d42404000d00140194010300c00090080c074200e904164000c10302d581c481e841d0241076200c0b021000e000c0e9121404000100070039403441c464021204600d24052100c1030030280d0780029110188211101c0090110085080c81042d0005a40440d80001107412504042c10000c0d41c840c0c0c86c513512214070b50147c9038005034000002c11504c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 65787484 1250 65786234 65786269
    0x70b010e06010c1707140f0f03040f1a070804030c081507050a030209011103030a09060b0906030c100309080f04060f1701140d2306150303090f131a03010b 68
    0x145014166100201101a01d40313001d0764034028000c2000040716810084070009905004040942d046c0d4505407074100f1001c1c08440d00d8208110a00c041c241161000080e10f444044100046e40880302c0224188140d00d00500314a41c00300e80401004030780b80b00141168003050494070015006c031a0016081400d840313030004100c4c00c00c021849140250040c2c40b5000050618101c0140101c1c0800d0540d80204e407a14020780da03403d407040c1008810700c981e011108041c3e4130788e201c0380303002c4003c640e651080c40c0100d8402d00c607261610a14070300c80d4002414291f80020202d4441e101d40169048a4101d0300407480800e4985000070282c51041e420318401e6421411a41c045034a050b11310540f1003000341e0000e40120303006092002140503403000411074000001000103100308440190300f4214060005020740324001790840075690004140d03400e9100443c0c040480c030010310b00080321801e00a40009110741000b400d2503501101c0c1c40203003e544000d40080c4800ca400300d0401102410700da81440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 65788734 1250 65787484 65787497
    0x90801020f04120206120103030f120e0c010309051009030e09010902090a090510080a0c03120809030f16020415090c0e03120f071407060906090803090d0204061208070b010e0601 78
    0x7001c0c0f124106035045030f5001a04640c580412885020b201d6007090704140c001c2141c5904ca45142548501440e60341c07224241c00304112044560125210300040001038105a1520841030620106228141d400c8181040404c451942450064800020541c03890710a00f030440001130303001410f0003102d22018004000241c0d00742442c4404000b405c016061051041c1a0000860110701c2001440d500f02d004010103104603103189080200040d904680800f08070b0741109104030300e00c0000a807005104c0c84c030800c50722190011008008400d6040001c3d51217070428141489034058241d0210560f003240c80148000c503040101580c1d21401c881c4a650554825480060105540350140040e010311007015480c00700262224661208081c0c460b00458000c00b0b030801c08590002079100c0101044d04014491500d0300b070409440b0701030f0400b001e00804100c6c038008110750752580610098281c0000302c81c4900b5140c02c2801c4a0b40000004035810001540040741060341d543ca83ca00c2303003a05940301e1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 65789984 1250 65788734 65788739
    0x209091501090b030609130c05040218090108070515070203012c0c01030c0c0201030209040902040204170f0c0d03030902010e060318010b1906050d090c0b0702130c082205031207090801020f04 84
    0x400034615880d0040c0d89a404032500070400c2d92b01c0d4001884000766521444c4000e03083c240c01c105002d00183e20400c130540c030910b03040040342c9030b80304801010001c601c8007075155040c0f400800d01601104841160201c40d44440445c42c403030a000d401919803808048551800010005400700c41c0040b0740070300800c8480c142280150f02c070350010200a14040c1010542c100c0607404030301660416080400e24407210000b54075181130800c00c4d003040c000008003d040c1c400a08010800081710075030301500b05034079102c2840669000c0e00e1035004220000d09100da49140c440004036914010b0202d1070380b0343d420802003003014500582c00413402030032039603e00003903880d021054425500003003400e45116180d01c03040f80071501d543c55070f0004014407141195907419600c104405610600502e440180c80c020180081070741c01102507070b00003060350822580070101e107076804084c02e8094008105100002c0c04168074001c401e54a8000c000030f4884507489920351084500780e005651a6188800050004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 65791234 1250 65789984 65790001
    0x30803060d110907030c1103040605030103020f0609101805010503160f0909090b010302010311030405060703051f030c050a06051e0f0432030d0914040209091501090b030609 76
    0x108070720340344540007400036008140e000c14455081211800d000c29655441000855004042c0124915904026601e004c1c104a00070300f0900060201074010a0359461f2599281c1b00d403411501487c00c0207045d0402c800300e4500040c2001c030071007a080610440f040c00011709500842c140c0e0700a500784004098041e1001d002200d014040e040325404001c0003001c002600501807107000d001e54010840c141182d81140009800d0324480c00d0329004a100c20800c10000c614082243c40e0030854500e0301007025202e803c40034048a49d030034408100480030510002c108041d0001d0041100c40549500d0045540c440c8140c0d020301983c8440c80c480080b5501c009a0106c0034002400305404407c1210704050710307803034010f0905440100d480300c00c41200e0009100754002c4000d0a64802084008003c000b204880003403040740703284280c000030610300c031002c00360b981c032030301681c607900030242c40031a0501d461800c0e0b600a06480c68801d0200e8030300c2401040100301e8a00b264030903003001d0400c65240e20b5a050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 65792484 1250 65791234 65791249
    0x30f051603031d1b040605031906090512041811031302010827030d050702010b0310090f08030106030c030b040614060d06090504050303010e0609100b09040f0e0f01060b16030810030c0e070f030603080306 89
    0x440353381c0104088201c1d080b0710f07580507002030b0120281800f09400c00c080080b04403000c902d8818508a420300c04c001c495000040c4904107264280f9048405454520095038840d450b02e400e14103450f40c81041d03181014001001d442840384881c4184040e4489400607801c031907100341c2560701070f00040f41d0110110000e4004e5103086104540c004122409501e445120f504280c202000190716800100201641030244101001c13045a08010540c40c01800d6100b94485020f900d0142d1800300c1c0b0214520307041d901c0300c0010b03c0040414001403070070740b80c40c40e100d5000340118201c2c1045c00380410300c9410655800343c0b148244480c00c1e0740342070a10715200d40c1c1383c0008034081e0340a82c6030124900119024090703800a4201d440c0181008444425100e0139207145d45c0100003c3ca000b40040c08507038071400c6001c82d02c42d801d41000c0d40a5160710ba0505a00803160f00098070b066044580012040c1c2603440651144519581c0d05400203003041d0120f0a49036030340700140a90b1001d20101e21145030444 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 65793734 1250 65792484 65792501
    0xd1e0e1005040503010507080403110c060a0e0d14070e0a05060a090e030c1b03071e0b070510110702040b06090a060302030601021e0604030f051603031d1b040605031906 74
    0x10302600b007035501d42c0001e096400807502480000e4601042c40101500034240f070400c50f0340b21000e00050180d480c08600140070b0128014100511561034000c0d54868a00c0380c0e0b10300f500104041b0858074042d03d042d689404034404c44c0c01e4074049c6800281c00318044d11805008441c0201184003017460f108084001d0120580081d110340010002c9090300c180402800080e880e45c1402c240d800c0c4a40303000c00d400c001080d80020789015540480314582d811440d100380588040384206601c070340c038905029162030408103d6120041c50902400086030014010740a200c1c401c075070900c0400902c80a01c00325000340741e101900030012500a000260181e005143d2001c41807045594403141003c0344e000c6074103d59070184841c1c1001e0280320900d0b60100304002221003d00b0304074a81040c0c244200c42c10103541da805010103076946010020318003540188203081d46c010040701d9046250052003010350600c0340c50984103614000000916040129115074480b1810045581c841002c1c4c456001a01814 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 65794984 1250 65793734 65793737
    0x1510061b0b0c1204050105090120033403020306030c010c0201020c0d0212030a0e0f010309050613031202040b030702010605040e100e01060308040b0d060f030209042a080d1e0e10 78
    0x602c1040300d28030743c03215424403490007400046814200301c05040c0c2120851034403081c0d000d045022013520380140340100c0b41c200007900003d881000e8080755004188071001200090f043c05520801d801d9981900918064803040301a281c140d040d81d001550120a14500280913821602c00509075103004402e442c1a2070025107241d00100100740e0321800c541c490300c402c3e00881d039404084000760410004070781d40d880d020300341040050825100c9a544210060043c0a00d5860540340f0040502c103604410100e8850542507460700d8a990100d0250b80044a1103401586400c100090b289028007994600000640150924070303180003840c0701900c05104500f042c3d40d01c8000007c0000c3d2514000e0000b0f040941015890b038100550050a4070540d80c000c8a51022504060015a80b603410094109521001c0710a041000e041c1561150b5000c1c000300c514041010000110503401113500410301314565100014072a000074002243c0d00038021040014905225507070941c2841031099903001140d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 65796234 1250 65794984 65794987
    0x9010c0b0703091b0311040b0d020904031103040e0103021c031e05120403020c01110303010f05090a09060e0c1201110403141204060e090f190213081510061b0b0c 71
    0x90b484130603030300003811074601804000c0341080052110320041e41c4034074401154280414252540020f40b55120380350064070501130000800c04050080c2c0700e4141b9944124281ca80342c55807240080c940391070911040c0e0103081842080d1400b46840c595220086905856001c0700080f60013142c005c0306200308421f4140501003001018107502c1d5a82c0f2480740c0e100c1c1c1d0041000f003600d10001060103800e14500c4034a54802d0005001c2c03403480c1d208042c145c507819524040345075244904040035101c07881d0081c03c03032850050202c009120110311945410130a0b550021040040f2815500303c074000b24140203106001c0c401800000c2400e10403803c140c4054007140c040f012079030f403200c00c0c0b83d01990050000c501803d030789001604043c41178583c44003000002e00301504e03084101000076103080000703001d074035400990044d004c040a035040024050310404c9400e40c5490b00c103803110301c030000d440800041c0b69410300001d6881c46100200b40c030444400500c1245415982c130f03040c4802c400341404e01c500c5030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 65797484 1250 65796234 65796251
    0xb011101020d020a02160f03020d03090504090b01051002031305060c0106030b07020d02100b0603131e0f020306180a06020706020913020a0e030d05090d0206090904050604030f0509010c0b0703 84
    0x90010385203540141200513900c15901002901e4030039041042d54034503010400c00c2154506104141c002c403501501d241c000b2440c689000c45514519030002c6900515003040c000c00d005007110141d058581c203460701030120f03800c16426039807402004020036020200013018849828400050602404a0300000c60342985a54460000701c90072207514006038042c804510302564100100700188070601820001070000c035002c940d19202c000c0015075106c0d0082c0402d8100002d01103282414400c03002c031541310300d296140c00003645500781c0f4264800d00c140000320b842100107050886851000a00403c00c0c40702076079a44029400952007552100c1c1d00b8000ca207815103650310524052036003c20010f03624414588081c10010341d10840b80d00981c0140001d410540e040002c44903a008101c80244500600e840003030840d10981045a801011120078407007008800201240030701d1003034070383e2020b0220401088450b400b960112500059441e40e40c640458111103c43d41c004070a0720b0081861803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 65798734 1250 65797484 65797517
    0x60f030f0212010e060907050904031e120203011e0b040602150406060f150f02070806061507020301090f0203240a0c170c040f1a19180b03010501090b070f060b01 71
    0x2d2614102c042c4d0b503000f034030810003100e00910400000d07000c1125050aa0300b8a80c5009114002043da03801c46640c0d82030503400007a020704120342d031070b01c40c0070341c01d41d5250784900410000c4140d01c054009030b00c1c01c0d5040172590001c400c3c00d840c15100c07a98010000d4000884d000b411406020b80b058500c00d80d05c0102184612400c001140a06a01d4900a80c40282c0d540008d1180024140310740454104102c14000148003052103508140100c038541c0240c5d203014640d180c00d02c00e0070b40c0258558a40b80125081150560799820168002c500791a010580303008000c04c004241e0440e400e2001c2000002a010a100c1d800702c042e4410a20300710f121314030710302041c10907000265650044401d02140c02c000c0d0001d02e01d20000504002609a01c002c0c07425810b00d0401e020b001901c03500b002046031044075440c070070b00402e4030045a082c81c90040d6039541c005c00c5102e5000307014060001e00740003404142c00d000031040381e401c6e50f4400809175002c50039855140090903458412810040a12000121103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 65799984 1250 65798734 65798741
    0xc0d02031e060d12080903130f0303020705060f090d06020412030c020a06030c0905090c120112060c0e130b03010f0f050906060a060206010b09060412050a0507050103060f030f021201 80
    0xc94a800303641a07003400c03081c510850044020a41c0b0b10030358600034124000341e01d400441501903018189020309484a1448031704501400e1390300e080f1210881c000140c1c4400341c0140d9000c680c001c0d020740783c0b0035407101e06016040c420004103034030051042101e904141400340d016003403107014050050405481d500307000c03280c66517244150000f03115490042c080d440c2c84464040180900e05040107110700440c00540544217a01c1140e04c078421071130000f6054115002214801c0404908a500c0d940c1c46070b03490400c0d0700c8400025200c1910301108401e49601450380a0f50401c070003414560355052030442880600710150403a5010b548680320b41e040d00c00c43d0b000340341200750540c0010409203460312410b840c000c1c008200c0c40c0702c1d8890043c2044481e4001c03c000341511000e8a18999800000300400c19510940e8803a1400399600c0854500340000410904035180c815404d6a01e950384d940c0044003603030458043c0c002c00c0c060805013000060858a44202b00601c003920302c120350400a040f16086 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 65801234 1250 65799984 65799991
    0x10c0503071211070f200a121407060f030c03060f170a15020903060c07020f0d050106150504030311071511010b0a0f030c1203020616020a02090a0204080f030405031002030c0d0203 79
    0x5800e146600c010030082c5210404003011b405000322401072100000080011783c45104c0c1c514620044502c2c0014046c032502c42820400c9050210341520355a41801014000c0b49200c40380000d01d403602508029110307004100480d2086000d403100142001d04200c0c05140c3c80040ea0300740d200b00042c61300020400f1114440c9003d01c200010386a501031824181840d03001040c0305104c9404124110050b41c2c1d0710021441c0d04401d58040184580e50321348507004000540000303044c1c00028202c80505a4008002e105691080d1340307501c0c11245000e0b54a43e20038842c050003629030181c00a024072648107641000101c1c06070f40020806c1582c03c008240300b80b44035081100102e003985420300903c00018441c0d8000c08148100508040b90381d10025120a4040e00d00c803071b42c0c2c903115804520244200070056140d900280b00401508000e83d04100a41c4148100e00c20350003030a00038821100080161030171960064094030040c1b8645d80c2c3d0760003d41c401400210f940d0400e00840d00506402d101a611 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 65802484 1250 65801234 65801243
    0x21b03030709050118140316090f14060a0303110c13020d050106020610030b060d0506070201051f0f03060c18030c05150702030d03050a0b03010207050a020909010c050307121107 78
    0x20340c1e041c02a002041c4a459401c11818480759404034845850744001400407101310361144800390f0010b01c0024241848440c650441a06d410008529604aa0300c0103441942141040066114001c907004991404031a001c0c1d01c50660310007000424007644032020401d42c42001d070350903094000002848030202e84504088664040317010351a4509501c10703180988280c0c0000e180030b1421034030038840d003121800024401d04100000c80c4c0c0c5600c171040038a00c03540c4e21500340c1b111460450802402080c0490702d0814203842c80012401051184450340103455902d000700841c4c81c11902c600307010300310108102c0100300060700707040400048078903a80e000c0c6d8400c8034112101454042045034004d400c0140e03801d20303402040b030100180d400180b11944040d0a00340032405076142070b8000001d0410038412a0154000135000042100101c1c104404600c03c0722400003d0700e54941c41d034221080003117480d000c188104046203003180603c2043c440e016143d44003180385000c00c1d5440c0040d4100340302c00c54 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 65803734 1250 65802484 65802487
    0xa090603080d060801060b07031413060509030705010516080c19050609120301050a03020d050c0a08010603060513050606011809090803090f0c0307060302161704080d0e09040209060103021b03 84
    0x816185020304801043c01310700070710105040810400c55441603600c01000d02c641c084050034000305030030a540e0500c090340c421030502507039803801801c6548150b60140c442d004586011845600420a80d00ca514402d8a41a10700c2c04075039a251540e441280a0300e4140303d00b03403850902c222111032450341c161041c00038001c0c1d42804040340345004605840082460020700050105803141c3c15800700b00c0b03404031007145114095080c510708081040c618a900440855408105d1003015040300d02100e01c114010021030381c4503a030790f804020710a0760050450f0401e40c04100c8070361040c0b03011554542e0845144c000c041c0c0e9442000c046071640042224512070110420402580030b200c40c0310b01507036080c05804404d900d100041c2e1502130901884040c990302085a01c100c1c00300b902c2c1840160750044002d06460254180c000c1203420500c20418140700b025007840c4924407440c1500c1c0038240160840b07895480750f608102c5101001424681056424020103960945442003403007440d03031003000385 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 65804984 1250 65803734 65803747
    0x201020d0207030209060402031509100515040b04030602090a150306090b09070c14031c090c0519030201050703030e2406030f06010b0a050909070305150904080304030e0a09060308 79
    0x6400c104403506428159085150b081001d038031215050795200d42c08031070059480c0e4589060b0b101002510907800d40090b000400c000440440c40b42460584804443d290a1800d210b00c4104480c80380d8090a140e0540520081000603840d4000d401407460091820104980300d03850005c044540c455040002a100c600c02c000e60301d02e0788a01c0700450015500e8039030515140c0000352619030310010041500b9441c1e007080441540920569a2401e0824030941014150f640710b10080c1c11240340682d402e20035503000003004d01d0100c694400b43c0608100411000e4659001507969800c042c20507001c6c50f8580d8415486400203200040c030905c190840c80d00004001d452084c0d260303e00601040c001d074000700503204008000500b0904403103013916840d90790395410504680b18010b00c420941c0040201d028880180d0b0180c10083c0329080a0843d0100d40c0803601c00c10519a02c10740d4090800c1d00e04002007000b00c1d02c0340012003088440070307155210503661a8144c908503159903009440340307030012038003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 65806234 1250 65804984 65804987
    0x15070606051518060406080f10120305030103051504170322060905060c0a120e070504060f1701020703090605070311071503150302090105061c151509080c1507020d03020a0201 77
    0x4161900f01c0c190380342d80c1481d08100d4041c10348075002d0401c08090030320340d00007101e041d41c0c078502d50040c10b024035500c1031386038607450043d009410a000c200c4140c01045014030041c5503022a044c45a50442a41d01d801a161440000e940d8005003543c0d41c4881e80204652080c03002400d8070000d02d22a110028188516003030040c1000e40203030441c04502c8041111107000e660051640349502190a00090103a20012140d440d103030980c1d100b80e130020304100740001e94850505000702107403c5038410402e014030000b5550300f00d1044100082c0400c5405d00c0034401148500301400d03200c0d10030f0074000b06125100e1011031412a26500c03040c904120b0944c0b105500342c0c135024400100e100108107148480c207543c0081c0302c103503050080340e02500c400304d0090202d410702d000301e444440452900b0002591403d28080c4044040d0044081c4c1c0040400701c0f1030b549114170406070460345000090038142680740f0820001086041100d1241101485044007582c1c0d0148007200d044d200781c00038000110709200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 65807484 1250 65806234 65806267
    0x110307061e0f1e0c021306030209070207050312250503030709050603010509070f05070f05010c09080d08060402090409050f100b09070206010608040816050f011a150706060515 77
    0x40004000c090712082d10441e4124020314404411907104640c04071802c50103ca0750f00740c0036800ba522020781d0b221100d40142c0340c1e029005480c025120b0003081d80c0e03200c409907500d02c0b0a01c14541c042e805201082441d01ca00f80240019291f0081a02484101180400c40c6c2c4129058241e4440d04000107000646d60010140307002001c0958115013158075200015100e0f07034009110105001c00105a080c0b900d01c01e81c1101e42c03107135200c1e440c90482031850500c1d41c002c003015004040464600000401c024000082c45c14801d211950381017074950349d60b8140000307500043c0d800c41e0480d460384020800900284403885640b94120300512002205200c02020340d4000100c1a015170055801e011031542d011036070b40d05440050604c800300e038840c0d02d0149401e00c10b008640d028104031804010802001260743c80c1010420b000920800c40c0b0201010800c00710b405219500084184040e90b240d64100007901c00c05010340b0001400300e60f9080402c1903103860409030301040c800001c0c1c092002d4120344 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 65808734 1250 65807484 65807537
    0xf011401090614030408130312020c01050705060a1e0f150b0c0a080a0e09010608040b060906030a020d02040617070906081902040e010b040216150c0507080711030706 73
    0x107003600446180241c00751842a603880c81c2000020008009403e00081b070084a040d000141365502070036903241402407041228005601c018018410311647c2507100b0320603280400c1d042400f0f0455a226000c1d490003d003002c20380b482502d203021403c035a07580314a02c6140341d051181d40303002c500c4041d04403082c000452140c00c250380190f01030040d00400c0b0740018a100f0f005034400380e0309a94802c07114060315521461004a988400340200100d50154058049400f4620801c48400241c69850420036541001c0303406e190142c1c0a854001c02501e09002200945400603000040c55519801c00e0380c00c42a88419002459000c1c550401503190b05201d0040200800300c0582425080e420380358290b4410190007034031443e2100d1400350a420b0070740c000710a07080010011565080100068550715481c00420355601c1d08a00e40741c1008609070051660040941c0e9901e490310000ba507a001c1e603074200e039006881c00c9002180030481030f1800c0080c0f0018206a48540700042d03aa0039551002602c485d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 65809984 1250 65808734 65808737
    0x603010305060408031b1b01051003240e01020409060f06030e060a020702011101090c0504150e060d0f0506090618010b0901150309020405010e04111c12030608060f011401 75
    0x1000108042140030072901c1d001a40b00c41c5160f40e94880700510b0b80940401d0344d21608000b0001040300003503070301c48800c00c00101c5103002840241d9070765815041c001ca0390b01c0302600880201c00d05801421460b40c4103010300d11501030028016566038a000d08a8200d07411110045988100c28802c034a00b800311000200440d240520560090303a11050300c0d1800030302a55100fa070089400070031a0f000b1814400d5071690080200103081c40381c10300c1c14045006128060049140501d502071500c196480a0140c441c0740d22048510384922041c01607010307a030001551000d040108000000d00180a424059010034008050381d040440081000d0340e40b1440303c0e442170707161040d441c8040d21001e001d42d04454540b400401418903201c0141d014000d0075100a501c01d140c080080703180e0411806207405a4003400c12020b034500400184001d060006100700c031000700c0c14018400003044180d0b80c60b0554103602e0049030907940d88642c94945541a40c0d20341040342844010b00010146880c02c0000301800d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 65811234 1250 65809984 65809987
    0x30e0907020304030f0314131a0a09030b060d0f0606050f010905100e0102100c05070c0608100306020f0706020a020607080609060d061116050d02010b0406061205040f050d0f02010b06 80
    0x14200c007950341c0c0309031300c8010040000da008040906000d00c80d404a9200200720196541b5900480104c0c2d0760003502840d00d418038580b4158000c544840182c40010105d620381c08202800c5460b0001d8212004096076441401401e45c00001841d242000075200d10414012801600300000c00c4403c03100105111f04000900e01c2c20000c0b83d0342d006480b4181080380c1407402c804481c020040f41807104542c05070f90802e0900032240102079104001340141c2d07004100400d00c41c1c2d05d84400b1202070400741c0f4403110124404d201480407402a500501004400d5009589848007e68601c1c050360000182f080241c0c0106081103a1141c112010940c062001c03508248245070000000390351401100c8080d00da15030700c814402051140400304e595644840300e4002e198445850583d40e1103400300d010600550900715020701c0c908150040005072080c81d2102c0750310109180c520401000020410780b01c102400c4418000b00d58140f085c43d42ca034a2035551124403a0349614060b0070b440700742c15614002c510 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 65812484 1250 65811234 65811241
    0x3020318010503150907142704090c0b1803060c040303030b04090503030a020a02010b04050f06180105010806040902030307020406230a030b1501090314061008060603100c14030112030e09 82
    0x109039144c41d0380c00e403048680d403016858841c422540f690812000d842d10140c0059505000020070000b501c0280d850000980c5401040003808142c2d00c0759007009100407812031050006528240140044000c1c900c1c47d521608007800020345840c13020b50340c038003406800050900506030705005d0161455010790b0240607141c0240d840581c1e9100081800c60b10342d07408100b0110741e0b0304c00c5d002146003220042c0240311a007880342c02101d400409581c00351040d2001d100340d401d840819541e9604a4805840d00c89031542e50380180701c05041c0220381281c0c540810800c10f40180e542c0d101e050302900c0c0d08010700410180c0300c105280d401c0c80309103542d4413410245000300002009101d5490b442068032810b0b640000340940181c583c40016003000300249118280403001260000c2c041d44200d884c40382c01d5009903a9205407503220003041e152150103800c040505615003419030001d610210703103890120021144c9003440e210311740003a080302c0840d100c6421190f06050307200900804507072085444003014203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 65813734 1250 65812484 65812501
    0x40905091c030b120a052803020a031206180b010f020106050901260a050a0b0a0b010f0c030917010e060106080f04060b010203040510080601020d02071d090709060303020318010503 79
    0x141c0c000c5000c01010f80741d40300e145160303d60110b1160010015070407030349491500d01e4040e407112503c440d44007001b40446000100400c4e0114070b501c4841c0c068014040c04001910110750007045141c4002d04641c85900c006409081748010171781c400c4070950002414042c1c00f000500400b0b2041461045a0400070148081d949590010381140c0c1021592050b8000c810052698003100d0fa010a50340e01a0085490a01c040890502c000d64800c1c201c103ca1a03490702481001c80c0c42440358580003403074056458144e42d00a001c0720040a001c0c0c10801011552018101c030304801c3e4655825169440340501c00381440c0801070305015107a1814085254900700d102c0250b031000c002c0020f00444c0c1c43d00c840161690007401128007822014001416182c4150000703807100c1c0083c0d8950b8018811000b412419501c00310b4490256030b01703150780c01010304c00d41105091704480948030009500880400041801492140e540158403d80140d5100ca00c0d10920003180750f0910b4541c0c0c1801030070401c100740b10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 65814984 1250 65813734 65813773
    0x108031b0c0405070c030324090902030a0b130c092f070606030b0411040c0509040b0f060a11060c090f060703030231050301021303060e030f04090204090509 69
    0x403100803841204000003010581c0c500100003203159006450700e001e200e0381030350180b80c6a1000c0d00a0300c0610402c84a03805003c9080c0c3c4032005c000c41103a21740e10a00c04010710341c21490074180001c1c1140c0880e4080c2e1688607003028180d95244200c0c43c06d01c1031804100d025031800c0000e0034030030010000c011303e8901000c420314214080003840348040200e04a5032441d801956092070300040200802501e901c0e10308890003080d0b905a80304001c1551000b01480c1c580204140e1251036070781d46081c41c1c10352042c04003a083c401e8810340e1007031007040745040301d0301e034100503100100c460358555010082c110320241c00d1107805002059005820130006c8600d4a0f210701003000c61000355040c0f0382d181400d08048009006280e6000c041c50b142e00e16800030740b29641600d0000552030101401c0c144d0751074041600308d02c00c1d02d5a51191a0342d990080012a0f0a548180c1e54821280103682c03500600000794540303580983c006141444d40481e061207103903158030850380e02041d00002080c6400940c03000e003181 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 65816234 1250 65814984 65814997
    0x10f06061d0901050105031806070302091804170904020903060f071e080f0c0d0c020f01050601020304030f020d03030b09090604060b01050403020607060e0102040510030e060708010b0a0c0203011112040302070806010803 96
    0x18000300101041d800309048c110603000e4a0984203403551401d001c0c2c4024040d60103d80f04030f21030b5420700c90100c88020151815802103a10039404a0060144880520703107400842081e0345c0654240030750300c92904e003405218442c40051b594540189015038000d0058284c01c1c22081010290201484000340c10001d1150001148540c0d00019a1522003403181440398031540d4400c58105689401e03160740024140d1072002d520350090125959443c01240d503401240f2000e80300e200c240704500b0241c180a003800300928064070b8042040e011210100b0701d00c503800e0301d1802c615803090b0200001d0010a12501c040034409203042d81c41c141c40c41d0005011406100409814281d444004000900096040b6002000042c01744422a65801c0d0701030001c00c80e007003418460f40503042c00181414407800304a8140d8108500c0141031980c0100100d424081d402c0c0200e03010740d42c82d0603100c0e2502495014080348003d144e8058454a854070b07000341000c1003940121810b520000040c0b02d82080801a10030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 65817484 1250 65816234 65816237
    0x601080f0a29031c0e01050c0a0501060b1903111804060e09030d05090c06040b030c16060b0f0d030503010909050718020c0d0c05071202040905010f06061d09010501 72
    0x1030a4440004480c0209140c0c49100a0342d010103441060807a0098802100700740210b054420100b403c207044100c1c4500b1800c200000b07101345003030300301c5507001e00d001e44a907100390070490320300102e0341e5621402c40381d4070f410000001c040450072090107142110b0101c1514140c1c0b0302401035041503074520340c0f01d015107025101c1040366001c0001c86612150322000c01416032030108401401c00758026504c03035102c1802d06032000e05020015945840014054a111304041c1c0303c80c0c9020702c1c10103811a190409010200412030070003031001800316464041a030385024480010b0801886003c101c1840029503800340500c0b03901c42c1c02808a0780010a5a045920264000c230f08070b500c42c80d005041140d0303074001c000d0a4110560b42c0502c00f8490b070207042c050011808560451580352010741d851881d2580041030350b40000b0b424060400b41c43c0c0e85080305440039201140401071a5510341c29202072071941140e050751804100013941c2d0000c415004140700980b10311411400e00040342c11800d05020b41c90 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 65818734 1250 65817484 65817511
    0x80c0108060d12050a0e01080c03070807050c01062309190b0f03100e060906040b070f030b0303070f030207061110050403020c060a09030203120a0f0c0501020f0c07090501080105060108 81
    0x181c1c0ca0300e510b6518a9480c0d07106141001c0d030300c1408809001a0048001503001544040911443e540114200f602030003001e4030181c20b40e918620202c619440040c5000f00b0890103012061820000740100303405400b0140801130b8842e0144030004003101000d24291040041105000341140c2c010030b0389485880991021500340c1101001c00c0c606070760248647d4051041114050b0f00410fd5405132034506a044241c84c407940307507150119030310722041e100078001d1800580403a000c18061041e00b89000b070181004282005030000180c02d54015080554480c084000c030700082640c10320602c8058072050901107031326141703035035000d03070301c134000030090012960301c00c00704040c14001c000c01c0740e0348940207194a590350110b120082c011042072108070701903c59105405501a022015910110392543e5201d0b140308524104641241750f40800352041d550030040c00d2088840c00d00101003103048880103043d59403401031741c1412554140d00c040302030f91600f01842156070340034660642010b81c0541a8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 65819984 1250 65818734 65818741
    0x50f010c0c05060a030b190501050f0c1f050709060207080712020f090108030403140102071101031802090720070806060105071a0f0114030c0f13060306020c0105100f080c0108 77
    0x8815500c2150055030f444000070581e10394060781504a150301c9101a1244880d244c00000044420900c40c09003034041103050101030003456a140c00350140a980d01c0840c1c1d14440c00200b00d079200903080510200c525118000c00400b43c0d0440c016a0081c5160b100405000c2c1ca0400c0300d985411030303400f60f207018a40039042d001c1550345400400741c000e04002c0a0424650703680414660703e074044d2100b11203125041e0b0145036411810320036201c3d01ca03040110014441b0700100110001c1a07580c21000325081c0101042c0090303144c0c0002240f065880f900d50710441a0001190143e0030382c14840e00c0125406900c041c04100d1000c10f01a811403000e00b0310948850352486c21034001580d0a5004032010140d2041280711150580f00e24121a2201c422040b00001081455143c0d808a4071640d0171680ea00001c0b0340b01e0800d46000004c5034403007000090340580b655550420faa00c500142c51803a919841403200b06500c0c110104010840e200701d00b6142c0b880c1c0580d03942c840c900750184605000500000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 65821234 1250 65819984 65819993
    0x5060c0c04020c0109140304050a05040e1f0f110f0703050306030f0a030f0806010e0d02120a060603050c0913030905010305070c082a0a1e0606030c0f05090c04050f010c 74
    0x10a14080c80080056480b0006414028024000e90100303490200b410070801c04c442d4008021070342502c3e0f000c1c060a43e642e04181c18840544066402d0710004d201d0050710030b0200d914100c0842c00845051004101c10202e405801c0589045d850b20042d01d1008121883d5001007800407600055854100a6120381d141c0000900b04101041d6110762400707054168030030140d01c00b03a640c9840344241c558640945a040044841554440c00309801400c8110007202524101d20b11840c51880601160032803400c3e9520342054800d076900c01c41d40c03544811000327505850040c40d000e074080d0000d10161141f00c1140c034020300e01091481854180742d910008114014412110208442d80114400b5500e00c02001c44841444040700402d10b0f0089140d10000f03021408031700d62000c240c00190700c48090300a5062501180d5640c402228059540c0d60000300080d0003113440b5006110081030058030514040038018024801400400501c1c3d007040280500d544420540d92030200c207203000503039001c00340381 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 65822484 1250 65821234 65821243
    0x1505040c1407151d10050a0603021c08160b01050406080f0a03211113081f150521010b0306040f030e030f0610030c05030d0905090a020f12040201030c02070303020705060c 75
    0x115640c50161490b40481048005a03039405d0314103084040205959650301e00c01200c645000080d0312003a50310540102001d0141c440003154040d982041c03402c51400d4180c080121400c3d41100c030280e60100401c0589018817880004210140c05400303482070009035951240446500207060042102035408000c4902c64021240b422480c0c0410602003011058156070700408132800e0748100207400419003200200d000316040700400c0a8080925085081001800c60303000600024424401c0021712513441040764a0401000480310510b915141410383c20740f10001070240c02988001d0034440091101083d050001e6014541390000c403032401d00017401c0001104060b403c920998082c0502c000301e10404508a901c40d5000c81070301940d4400341030b1141d03200d040e040c2c0403e400d034100300302609125a580303611420701d04005190000114800081e90004503880c0f0b140301034001040115600740c07251814006a90005007180d44c51a44c0c002c0d5503140d14091a80600d80104d440080300c4000c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 65823734 1250 65822484 65822501
    0x7051c02131811030d17180f0a080408070b040f0b0a02011b03051602120405040b12010609061a030f06120106030204050c0c0d0503090606011b0203011505040c140715 73
    0x21800c0c0d0302e480725810710a00c982d1041c42c143c1e201c0d0151034866a007850050524402240b8400c001034020b81d140c09008041456a80902d513060081c00f0802d01c0000d01402904810781c03260b0300343c648450a00e403441c0d1614920b81c11811000c1c40c108420310005400c18038400072a402c1c140b5250b030f00c0c0440e0804902400806002c00c50403013245000840254050300100d2041c0c42c07400c0c02a2100e0468482260381d00c6540c0303589003160000308024000c50800c1c1d08800c1c000303800035001800d00c6001c0d8840d142121481d9000808081d9200c00910406022004844100082c0d501441c214140f4602d00000c07554090400b0748100300700c0032100c4105800b07401510045070014010422840e103800c0d101c00c6d591200809003034134001c098900d180c02d07000d0016280240070217001000035650b82801542c1000c00d54400024841c2c071a004800169024000e100140d0aa041c50003a803a00d440e09100903280b8240080c000c1c40f202c030b82c0200055401000390781c002c0c0c1d00b011005d038460138190030782c400518001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 65824984 1250 65823734 65823761
    0x11103040b0f1204050c01080705180409030c0803040b0603060a0605090a05060f030304080307060e03041d0720011b0203030105060d0f06051f0801050406030b0601080a060e01060201060807051c0213 87
    0x10f50400c418810702003021850103a0a0300d034481e01c0e40c1c841c401113131548105400d0045404000c545400203041580c40b226855100c0e08207524000c241303444040103034108440880b5030404a40030000c03079050910070240c00080e11030302400080d040c100020120480240180002991400011401e503140c0e03043c200300c241d0140c190b81c0d0b500e0710f40d003003581c981d03010000c261446810030108560704100001214111001d0300194048040401100400124094940d030f0070090242c801404142d003000810b01c80c41c0030080001260741922114410050300c860000055410900042141e516140112194541c2200000940c5030302c50344281c00134140ba03000940c0103010920216500348105054080e0b07044545c03100c498507070b80c030000c100a48206000081c564545c040101e2003a500a046668000441c0b85000c22040c3e254180c240f03180780c0990002005070f440710702c10009e8a80501180c40600001c3e01d52044900400031806102210444005c1c0172b110141c141101d202965440710310824800f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 65826234 1250 65824984 65825017
    0x30a020c1006230a0e06012610060f0207030804210510060e0f0603030702040902031507090501120b0d0f0c0f030605061e0f0405071103040b0a0e011103040b0f 70
    0x100c8002c10140b40810800c01500500c6420302c02d2185407240e035030f200f2905412005e41e000c0d501c03400112040c248503a00358181564104a100d501c050021038540314496542c094142c452401c5402001d60b621062a9025900412003d102040511048405951414105170201030f0301583d07001c03000c3c140c22405061802845a01103103400d4580001045688a041034080394036402000f400d040000e03203805525504c10011140107003840d4101d040030034001011346140d40302c02c4000c081b03104000c80d03200c4002486900244130755a000405040e204035555000c001503040358001c1898583c2e03000002d08200c40c20030314281081108810075001d07000c540460030b031046e42d0b8034281024001c03d60b81184901c00148004544083d10280c5900c260401000942180412001d04c03004110182c60b100c10403d0000140c008000c00300000c100a29041c4012913882410703c100500c84902d03070420340d0420440e0580e00c0d898a0300007064a00381c44400c52410b54442da49840003601c2d1084543d900c031801030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 65827340 1106 65826234 65826239
    0x807170d170a02040504020c0109020301050a060815090109140d140a0219110616060609110409230405030901030c030b0a090e0a050303100303020705010c0305030a020c1006 76
    0x2c10840051900d42c9030790200e020b991200d000c60410341e445861007808c50900344905580508110001c000007400c051143e40c0b0b070b140c180c661240d203030807240208500308001e51103010415840450080c110200f00c40342ca480f049160031036000b281d508074803800d084400c3c0c3c080300c09812440c0d000d00611304002c01103500d0881100001d8402d000042800456a11075000400880700940b0803040201424606042540c08607000150228142901c0341c03190300590b801d0324192070301c0e20303404101050040314101c0d6a9400c1c01e101102c01c2c101000f0301c000e1001c084010001e43c0403e076000d0098001c450020340a4410414041c0c3d0444200241000307c1082c42d44500e55884003403098400f4030207552162481c581095901e44110040c00c8002c008040c1c0401c0ba96006000030700300311075020078684000d003085c040204480703034907600016181d0508806000c45440d560240300100001078 = true := by decide +kernel

theorem cover : BRFrame.Cov 65647484 65827340 := by
  have h0 := BRFrame.cov_init 65647484
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65647484 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 65647484 ≤ n) (h2 : n < 65827340) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
