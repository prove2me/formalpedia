-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0469
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:58:14.462292+00:00
-- url     : https://prove2.me/submissions/10ce00ef-0889-47aa-9f3c-ac8b1ddcc784

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 84172663 ≤ n < 84352519 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 84173913 1250 84172663 84172667
    0xc070203150c090a06170610180e040b0a0c02061f1205150f04030507020f13050405010606081303050304110102070510030c0f05040617040804360b090106120f020307 73
    0x2c1050310303020350b0409800c40c0c1d21482901d1b01420360144916059080002500703c0c01c20008000c0300c05024504692074004088151105400a4000040d01c040000c00c020502010b0b038010354101240080401200c1050b001c000d4a808014080284070034650004600300c08902481e2005000500d0b10100f0807252031030a0750380c44044d00c05420303c0c02c050307100050f070b6040380c86007092180f6003540320741e441c0075001d50811610340300c180c00c226400410541a01c00303003075052050510591051000150b80c504100c005090500000c00104070342441d5079502002a0384102901d801550041c8a08424014040144d0410f00036411580d08038485032400c015580c0e064010203041890364941051100c8419401c13580342c1300340d000307050102d600f0b05a80b210300399924601c242d11034081d10a43d420075468031849a07151107060f010b8001c1e18100e001c4500005100b5004908010810204001f61040400030411a034414425a0140f00c014040305c440401180c000c0c002551810404540e2450b0610700 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 84175163 1250 84173913 84173917
    0x9171204050d0e010f080c0d06060f080609010b04050405040203011103040f1a04020114030603010e0304080c01020c090402100f0201090c270e031b0309030a060b120102040e0c070203150c 82
    0x1034426210340c111019010b40291030800e04103406950b05c0303000b83c0e8a21001e40b419640038189640b10340041110989005036441160050503050340c4803500c43c00031900007040c048000c3c201503c00c004c1c0100411140042d0b49c01c81c2e0440f0400e4402040b20364a030b00000c1d004103500102c200038034030000108002c0000c0c2400c00c1405602c10601543c00101c06404081240b40449000f804600391500c0801283c210750051603105400038008200c800314203c500d42107810507484100c407a40140d507540925a01804256140d44040c0c6030074559161a80026148210f401c056006226000f20b203412000d200b07400556016410600030b40505940300340ca40c882107402c40c554010755507100c001c03070682d403000c0c05066091800100103504103140341a11004106916809448520040000030b03a0364a050010300b5605000300c0300003070303401c05510922072416031f0440c002c660307644104070a01446042c16041904106148082521502e0b11703c0820703d40340c104030307043c6c20900706442000308112803400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 84176413 1250 84175163 84175171
    0x5010609030c120515250207080c0301020315010e06070614070905060910030b03071e060206010f030803010603111c06050f0f0a0e0403030915020a14090105030703091712 75
    0x18888405030360349445500188022100800b51707005402d103560f5070502e0000c1250021041d0340c800c02841d500a400101c12140c194100340560007404007005124001e0001c40741d100401c0d80250314501c0c0440c0740c5141100d26011f401d060121810742c1109a4455130142c404456214200b0070524003c1d000002501004607840800560100b00c0498035040c20000d80d03128802c05080d22141040380a801d40c0a000c05403040c0742c040c441d07108001030000c00395001912424844282c00304031400c00b60000e041c0311050f001a1040c0f407120400b0000952008202c1e0304583c030a180000c0c80b0a00d400d80f03400c16200e4030b06041480854a070003800d10741060740c090380840b0f004999070410150442d0621083c540e800741160f50103207190600300107960b003090000d50721920a00d80040c10402e01e643d1003400920b60181d00d00c00c103501003800ca110075004040e5051403420083c00314108404000001c0840c400240300d0030401d5240e161001c05c20801040710300d140080050032540310815000003a0105000b12 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 84177663 1250 84176413 84176423
    0x20307172503060308090f1f050d05100303020304030b06010c0c0608150901080d0305130804030b0906010501090e0105040e0109020907030b01031104050a0303050c0c031b3c130501060903 82
    0x2001003400502070f100790801c4030b601a5145080031403040402c07001c0e021903140c440d000b1070750348518103400e40345a6000f0010106c0340c584540703800d01b4a1490007100c1000702141c00b4080100f0061010903000015201160307030091301814603a85440c0125440188110010880b203c3d0f12804140c0319081200d040c0303d01c4000c220840100700c28020000c00002c2882202115044040305c8072400b07110707800c0180e0002c4144000341020344240c1d03034541e05a01c00d070300a48011703254805000b4504c4003449402d0041c03a0900c1c1c000650341c00c091403500180c03010720410b407280342d4410a08895401c00e400460340550028180242ea260203000900074090707220940303000914145546c50301c68165070568040e610301421407104141596005c0e6410ba0203041040054800c0c44102d103401c0d0b400700400d8480036400e40302500d00c21803400c1404010712001060112001ca802030f5004400d0030620944402c4000c0002207034500c0418010802218101800c507003030a05101c00401e10503086280501100e102e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 84178913 1250 84177663 84177721
    0x15080c153f0a0b15090307050901031101020d0f0806091305100209100c1e2a031101020f0d080c070b0c131a0d050c040503010c020c09060109061202030717 68
    0x107465503003224036480065620403d06190b803090384131010042c1c40c170501d0243c02c4600d03039601c3d000000d5800030240e00c1181c044407856020041c65a0610400c00a011203040071081e40901e00300c080c209490013055603024074a0b0300b0004071039050300b80c0e00c3c00034290082e051b1035410403034a01e02d001941c04009043c0c02032610800403138005110384442d805254210114085007001c162901e0401d0081c00000c1e82e03338440a100c42d0400c40465a10244250502c1d002c40002e40c0c80c62900d001220809044903065401c4a91211400d50001c207208071a4491486c0010869442c6400385410740982540900800d40704010003e00c043d0b02c3d002000d005c50440711a501c40c035901d40f440030b00030a20180c2200c07900d405004002c0601c00b241c011681044061a14070305154865000c603007118004480000164410940345005080c01c0c1e18064000600b880e00c0440703241010000b034004482c4400604400e6400000030340458400d84514500030015a072544241c10001c2e4040740c0c100c1e520985418000305 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 84180163 1250 84178913 84178921
    0x110901080c0108040b0703020c03040b0703030605013e0102070f0b060a03030f1103040b0304060b0a0b030c160204060f080a0308010602070e01122415080c153f 70
    0x502810310301d00503503c0ba11560b65076500c0d0714004001401c85428550207020030042c98406102801c0906030507502c65440d500181002030a03607410b41c1c882810b0101d600500b404181103000512604000d90420380c40d90702e89401a80c0322007030303140752000055101146800801140002c141d511a00500c5043c10030b40303d50040051f0801c40b440001c0100c0c442c03414241340ba9002d001040400d83e03082003983d0509a82c1e40c00071600c1d0340112801c551455648054182d140703044040b10000e0107200002030f04514090105101c588200c4540e03c01c5410001030480846d82c0d20740214014220038000c0080907a0307200c2500c5c1d81c420300460100d0100e0911400070400c80d00c00034000046a188510b0b15000e42d10307020400a4202e170b0f04406441d405a142c0b001c0c1040300c2c00401e5440300305544d060000c0d108460142001600781c881e00403151540102070051000d03955101428440340c590303458960341340501e0f0060301d45142c1052040c01c500541c41150101d80c5800381c0703504500c601001c0070f4411959 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 84181413 1250 84180163 84180179
    0x20307020309011116031101080709052b02040c0207030506150a05090a15240e1008060307030510090b130210030c0306120c0801060e1012020406050d110901 69
    0x4125851801a842482034035080e40c8a0301c1c00c900000808010303a603c695040899442c0b450082d04207488840b00520303140e0301541c3c0b0159a036031104241c60408038590a00c1c000400c500307992440e05038003042d08402c0030600c11140c000c2c9981554000d100b040002c2d03c1e200040c4d1070309140e110a0310305005e2305001034800d002580191001542c0240445015030030310080207102e02002d01040c06032541c03941444038991182d24040040c00710120541064141c090030b9041c801c0c1d01c0311000040001e80034110190792620b07038900c00b0003203150408014a944500120b460300b443c940c8064128895000031030800d0450354801244a80984904052583d83c3c0d1420700c80c5481c42c3c0002500402c1c40222828100e229900c58050700740c4901c3c001c41c1c001d607206028501c031506a4810b0781d62510f15507080041039007d1203020000e011242560542d46072243c3700144001561041103800340f08444010210756459105502500c001418001c1c425006d04221404540c000d1103180900d94010010078425 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 84182663 1250 84181413 84181417
    0x3100605031e0a02060f1204050109050f0f100c02160f050103051e0708070201021e1201060201060b0414030c060d090c14030d030b030c09280501140607171b07080102 73
    0x5411400038500c281d400c4e802e0200e2541305140e40488104240160802e400300c50340300c0d6024a01600020540600d01d04001d4106841c07000c040880354040a90941d00e8030b000b048441070522400c1d00021188141d05080c0d0804400405200481651035008506d502800c81c500302079030801c0c1e030100842c0d03070788140401a2032048583c3e0741890440300009018544607403412584002d4510000d8107254032400c40401d0314030031201c0c0c0c4c2440f140100c1c0490a0401d03a000b824014032040c8000e010302881c01d5040502c40c8160300500030011040396108515840800c0741141c0303504d014202d207035100e1500c607200c4014118402c0c02c8900d4200740c000000d44e104d004580c024411802000317403500360a4603500754000c0500341041038060003a266000c0469540010b498410741c449000c0811162915403c00100c1050307209401d84c00d4600300040c402d0600407071741400118010f079480c0395144d0f180d09094550615002d0414500940000c00490303001d80804010300c1c46007500202c95105403140c1c941800d038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 84183913 1250 84182663 84182713
    0x50a14040b070f0f0b0c0c010b0a03020d080703091a03061e09010603021b010216050f010e03071401020d05010f050a0501050711040209060c060708180c0a03060b030c0310060503 78
    0x1c460601101c00461000c144042c880da04c24440c004070f0b0140c42e51041490181120030401c8544080750080d014403080c001c0011221088070560308107411030f8001071828951420240101001040c1101010300560005014205401c1007602001c0040110543c80e0f0040719030b43e000701c00000003440500c4140c8144094850020078000040c1c0c20840d00302c000b90041c1c9034001944840e0750549034400000e2008100030381c40b80c1302804e40fa03841406c00500d45008102e12420580c034180480c280501e010040e10100c0368821003018610840c0031a45001e4010903034101d0301d0614010002603906050340c444802c0317601c1585c0f1001d6042c1d0303607030064a441c000e00300301074010281d05201003414a410b074001c0803035200080c955401c00712801282850201700321000e402003500c903000d000c0c00c111001032094070141c0e0500104482c100100101c1d01418452000611440c0c60f0302c00c01c0341d207540900c011465540050304803524000e0018034000035010303603c9078078000e0007080c644003000510b07814a0043c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 84185163 1250 84183913 84183929
    0x609010518061b0a050904060b2a0304060807110f060403030f060501140702030703120503040209060a1d0a2012060901030218070306050a0905100501030e151306020307050a1404 78
    0x7050070b003d00302c4440c9074480c0c494401006070030072660704281e4551050402401410014a446130600d414280d40c5d4480b15503d504c90745020104049185070000458040c2c89652420050546424109441c82c0d14444010045070040802e0f603424982e00180140c444c9001c1e5030140086001061508100e0b0141d0091900040c0c40e210044004840c0d00000e00e603561000d401c2702c00003540d9844084007192203014640c002440082488154a04500700e180c100b81c1c00c8075845181761810905080030845a09a030710100703124400100e14042503446078015400714003401100d6492a40b05504960019440b4460b080f42d140c08204941087c0c420b090590b0790180110034424035007040d4500783c0e400140342d00101901c81001003013a807101596100100354802c40418541000d1081840710341568208604052810081071024000098680d0b85440c03040d00c8e15503180c03542e2400c81c0d420b00041001418507400003061062a96029000344003c4580359100c2101090010030030146100754411260 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 84186413 1250 84185163 84185191
    0x60c0109060c05090d1103030c0303070c030306090203011401111518071403211c0c0f0e130b06090616020102060c030103050a14010e0109030203091005030420060705060901051806 79
    0x4001b42030030303171411075900004080380d040002c4001c04524507401110b50200003220000c0c007408044e0503000e07844c060100304c0015070840d8101040741201e11035001d640c40c100300d2211080300c03400400348a034082040103100c0000403880c01031b040c2040c2c940ca25020341042d100f40d40c400142c00b0001820ce41c1d200304000d01600c2242c00b4031816588100c007044d2650107401c000c028a04841414031610454100206004200d51600701c4000c0c21610189640c0c02c2403048590445481d5540c40000c50820707003602a0003c2c40d480c0d840045541406001c104540140d00000c12106070380402a941c0c403140d100760700312440e568503040140c65600080c44001c1c03069000c1c0d104038000964416801c00325168000000402e42070680c0711500351608a60190003503040080c04070f0030f03410030840d10210141d13281002440d605265503280115414496442e1380744103140700500d0703c0c1d030300c142c103d40031a60040c00320b0301c0e20706180791107600901c0d0a641e0702c201e0751508801a8504500801d285e48038200126241d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 84187663 1250 84186413 84186439
    0x150f03080708210910050f0601080403050a0903020307090902040c02190609060902090a090303061a09060304030302040e15100c03080604150801061d330f060c0109060c0509 76
    0x100c580002c00c410111080c03030002002c3d0400243d143c14404d002c00401030403072030043d40703003002110720203040c5006011903001004090f9821518541d0059458582541d85500108040303c8200b1b840c1c200a600d8084c02800250702007023900f0120900d40200c038204251507a4147c1a6039850707940100450121140648030040751072507200d44e8000d4092440032448040740d0b070000b100d800c400c49104000994803540d107418582e040c46044060b10000c107402464298043d13140da810b0180102562040c000040041d04261194054170010240d584003007006041080c4800700400024042c01c0c0504156241041c160703209600340700c00b194060301c5405160300c840040c0005404001103001c0940403099000a43c81401d2243d44010400440c000c14154003444404211202c0a03003001c40e6002503c10101c2c50b0303051710035100d001e419401c442c101d4444090011039950503c504d40340343c1c80b40010401025511064110307641140c0305100400c11000c41c600140c2d40c600440300c0035074000d50103241c45 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 84188913 1250 84187663 84187673
    0x601030f110d030c1421031510050712050f0405120715110609060907170709020708181806060901141602011211030703050606070213150f030807 64
    0x440011070085859090107094840428000403900408400189010303120005000b502c13448200380d80102d0740580382400d040e15030f094044240c0d10240c446405d0000105542c00100c1d144815103402c0070b8002c035a4180181409001a04843c6080d42c0820402041d000302a1084003200c0345034032080391a40c01c0c9410001403080341d40c40c0e40f10300202e600c035030100414200c5c411040340c2c2c2c00b01346547d07981d01114200100c035428440f0151412041e940044184916890049180b40c2500c403001114480c040c0b00420742c903e0404580d0140c88000c0c0700245a0b0203105508000f03041c0411000e0074400405203007000d0080d84444031141000c3c9040c07103804a0107629089008052500e01498811030f0031103010000b003015840940b005009070450843e81045507080301d0550710340207814a00308900040300e150381c1d140d40f00003000ca0080640d61000a00c407a038a11003640e62198000d40381050005c1404800b000030003020301015445168008001030300101015880c054907800110541403494641e50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 84190163 1250 84188913 84188933
    0x21302030108120a02150a051b030402030309010806280e01080a020310020906070605130204050108061003030f0504030b09060f06030c03101503201906020a030807030f0e03040807050105030603060103 88
    0x1854045025403140b11041c46c0c000042180101c1c544200022a4240715605103200300904007880740b0b000c428400c002c090380d000300544002681c00e091030186030792014002880041000803420f40070074156210607442519103c44425079040b00402e04207641c0391514a541e9401d40300009605510150f86420090615005012110000b92170203007000c04690724102038071030444200c4d0440c58070b040517605601c0c0c14021680141030500c00740820b42404e0918070294450341c00082c5c10700c1a8410000314051160045400940c3c0120f280245410700a4601c1e45540080ea52120b01c60000d8021401c0c40c9800709074050001e10090040503040301e00c144400140600414000f100112501c0000200b441101480031440103404001e44c072000f480b04200110100c0010400c4001caa82c03010b020544c0c0018400d40c07515014102011280d494040450140c0398030392001e04100d0411803400c078620701c00009030096822000a13a610b0b80d403500011a4240021aa4543c2c950b2042c8010400300b000b040e1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 84191413 1250 84190163 84190177
    0x702190807121107030311120307120c0c14030a02011505010f11011803020f060c0909010b091f020d0905060f0306011107091e0e0f031804020904090b010302130203010812 75
    0x208807003070714501415a402d04c82c16901c00c0e07020500c403c2c080d601254052202580c0c1c01518071406085042180f8000e211410b049001c880d150740c0d076140101c08500076400c0b410419404001204018206a8466101e801c242210310156080400f018103801d0456100c05c10345106960b2400c00980d118412a259a8184080d5903203541e2245c20410301d48055840c4001140281c00900d10f4084500c0d9062600c0c1000705071288201c02448082d10540e6200d41003030460310354640d80d0780c0b10212500081d51941081c0030303140d0041c1600011240c4680c0101d2042c00d5061541c8951480c0d80c0c2d100b00740301c0c40d17118021450100704401c00000d8880d40c06590184240c80d89801142c0e10756484e001120102c902c09013080340c01f403151128031888013080e030041d66803126800c1d0140210f14440c5046698a0240313081510000903249012120390312140e06031801c0c100010810701003c00da03400c0c0340c02c0240d028041680108076401d0310300e00c0d15950303008880c129900c8400521501081108078401c64000c60 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 84192663 1250 84191413 84191417
    0x10506100f090b0706021312050a12120501030507230a03060e030408160f06050c06040803060f041b030b0306070c0305030c12070e01031d03032706090105070219080712 74
    0x2c002c65482c4442014004052054100583c0c0d0000c1c074055400c0b8010583c0111000500d40c048100095008038101503800c1d03001c5c1300000c01c40b0a02d0000e95100710240e00240b4050304e810000424040006002c6040719003611040700540707a1003840b2494a42002c0c134054001d1076001c030070030019105611404409a5400c1070f81c0c01c203500d602c0c0c0541040041500d03200c0400c036056003802882c009080c0a4002d160904000703151030750401e0706603120784e002807001e4202d9101000264450b01e40195810164200600c1081484031129515222032000e030901c1000914000c010045400d001444a02800e0f29440b210203031062070f942158285c1c801004075020003000d00c0125000e481504905000360f24580302c0b441d105641e00001002c440080c0200d00d4004035040708060400c40c040308403500522141092002038540d080c18000c600a0408900d62a1041804004070800c0651206001d220141d096a42c1a003a0b0340d20480080480724014041e200c0410512000a000007c4070000c80390364 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 84193913 1250 84192663 84192677
    0x1002031611010e060f21040506041212020a03020c01050c270411030a0b0f0102120d02030a060308040f0e060a0605030f0a0b09072d2a0204020a051902010506100f 71
    0x1c80440e441d5001404c1205803a9170111300b0f85004099201c64080b4a915601e40d01e0f860701e403c0d101d5566582002e0005020480c914941c400c2203441415410b419800700c1c0c0c401d65a501203610020000d50003c40070000d25482c250205134000042e00484501d1003503c0207080840d000744250300782d104100c03551603510580d10512130064100c5071004e18402d01031403a000a1030040c41d410710004218a00c4003904640100080d0514480041c042ea410701d029194016220340d5045212001428a50030107401c0300f00100300051300960021071042a42d00302c440300c2560703846080c140180f600b06801054080340050000130080c65004000300d170322040822010031070041e1030b404912601c00544c1c00b00c000030b07194075451039502d901c1d47e164007007502c00110f801034038502c1600c010440802143c1c0b94600083c280d00a034242032030500702c00f140e250010000c5599044601000d82180c1c0502d0500c0d14241050012401701801885024426800a4403030f55500c0410002224044503c00001e4140241 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 84195163 1250 84193913 84193937
    0x6040602071e06020a15091e11010309020a090c090503070e0916050901060509060712020304080d020a02090105060c0718020702100c0308010317160605042a050105030717070e100203161101 83
    0x40c4298011023000fa501603c4200219400e1101d55540c2c01769445047c1414001c000e801070310b80050460445016681c0000c403001c8240089881106507409241c1c10b02c660000415040b05401c001409102c07003004039502510094440201d07031125101e000c0d40b00c054140104030503030080c4000e010f21600140031500c4e110f915554200e44501c89082e100c0107034401314040c05a030b0000c001d1300a0107441d50004001e803820640c001b40d40004140a581d00070080456940300c40c070b000701300f40301c00f4201032603202603441100040a030080d04056410784c410424041d8400445004500340254190540d8420340e04e40e007980c43d025002e900e020708108484004101d00c00c6a00825560240c0140c0724800116640c00c1c2404d001000e40d00301410501111884e0f000121041c03145900042182e10a007845c07501ca64918206544e0411292241c40e40094400c0170000308a51115140c1e01481c82180c812441e0758004000320faaa00aa003400c1c0008040c065020003c43c0844000540b107010502d07100b648184c07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 84196413 1250 84195163 84195173
    0xe0c040312090312090b07060908090303211e180f03070303020909010f0e130c150e011101060b0901140d06060507050f06060603040f0c030206040602071e06020a1509 73
    0x940c000c07039039000680c003007014070030000d016a008040a005190403c4c189013010381c800b00c18810240d0046c0000d503242d10070000c01082d1415229290f80c004c05513503c0d242e0110000c1c0411242c01148900401040c001626003500c00c4030010802e44100e51940042d41c800720100700800d030800c01250603200c1d2015524441c6820402010741c280b1030340c1e026896100e0b0809010b09100d061304010600d601000060241c0b41407000a46e40c090044040324821000c5420003682c4160719800591000f080003c0500155400c0b844000b0003000a036102034002c2d0000304424200c650034090b0900e404010450f90040b98881c03600c0440306510905070f01d00c1c15500c21601011503c0c541d021001203074020a003401070180500034102034038000b00c06410b00d4a40030000a40a210041c0b000f803402800c2014030051202c1441103001950b806800c43e50340355192800a0760f80d45040c420082d140d002c0d60600f40c0000000c0d40850308861041d001401268815900c02c0316414400703201034035890382c2d00405c0300818 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 84197663 1250 84196413 84196433
    0x912040807080606030102070302030a20060c04030b070207030309060e060417062208030109050a020d0c030e07080705060d0c111b040c0302090d0605060a0803030a050f01060f02070e0c0403 83
    0x40014000c24100e8030b030401040c00d20700c004084034031a0b4030500101021940101c211981c1c00e15038030300708103a14454041d003800b03000108048051361040a08029088030080700a000f030780d001c1c0466103001d50710007100300d90340e0800380401000140c07101c40403c00c8a01540070150080c0004000900301600c03039011480c01c100c3c0910404060b803010040c003c0c40c943c01c4011465088a900500d06600026118400d040c4010312400c100c00fa0f88200050070140e40350706441c0c0100c0e5040d070500c00c4c1440c200c0020050441d4190b00822805202c500180c514400645202101d001a00b440d08112030907800c0c4004103007036030a0310305100002c200e42c40882418000c200c0c525400b07004a0018443c0070081c030017140d516046c654145441008550100c2da503c0b400b10400c2c56003c0750100e550340d40d80b4003141000c1059403015009100110034403801c44513541000c1d05c104200402c080850380da480086a16040e000d10400140c0c00542061084008415040d0b07031084a80c01044d1405990350b82d805000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 84198913 1250 84197663 84197669
    0x150306031005041b081209100507060f090c0504090c030206070f02120f060c160f02040b03010204060905150301030b0403080a09080f0307020c01020309030c1e09010e090106121109091204 82
    0x118161348113001d20307800020040010b8080c030401422459420700014049210320405544a01c1c0b020f500316010f1842403040b83d01a961040090141082140d90369000d481010300031150940d1515011070141003520880c0c0310b50344c01c501c0c8180300314516000d00072650712041c025101007503000d01080140c1c461503407041c40d0b01a40740040c840a038407136129a08100c006060700800407410440d000c47c070b00c2218584550035030000c00070000c03043d079440090024000b41c4c0003203405500200d00047c00940000141040b101c0c00e9500807925405030080c14481e20007400300a102010810119000c20301c544031459021018120000e06401180c541c0c0d0959006450b8001d03914200004000d0030550601081e40784e00802e000950800d4140310000380c0702c0004808480c0103940e54400403030104508081c010380034202a04040c00307540c48888009485c0070171180080c19609215002503000c60320f000320204e0941100c548280600204100070440764044d28881851142c003010820b40da100030000c00007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 84200163 1250 84198913 84198923
    0x4080c07060f110d0e060a0210050a062103020a0b0c0409110309010e0f0601050d0602120a0204061704080f0702060d1104090c0c05030703030e030c0a050d080a0b15030603100504 78
    0x524100840040c8480440700200c03103140c011004400c0074603005000c640100001b22115038880c00500c101700d08d85003040b10181c1d9014104800d206041c5180d42c07014007640c1040213103032a411200341c80d41c00c03541c294003c0100113a01c64848903000ca20194043e03900a121f00c2c3c640e5103050344d1a1200340035900380c81c0204000d03080000501034080400d11034180090011406030404a5941c1c1405480311014460140541040d0b201002040616411510a4014441c010704a4100040d10200940240c050030b80031031480e00c09044009200d545d00c03031049600c140c0991406810352041407040c0c010080c12a0001d00501030684007a5141c05149a41302d14950080d441da890000315000356403c3d02c0504007404458a1181c0200750301200302c0e10380c150942000300c8d100b003444003624a1071140031158901c0740641c010754020400042003500b01e0b1080e40d81e0382c00c03254030345111060841c2c0c0f018050030391106003810320000c620040700141d54051001000d56403048101908441512811a41194 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 84201413 1250 84200163 84200177
    0x13020a030512090a0e090706030e03040914040215030f04080a03060803070b0a05011d0411190803070c140d030815060708030406050703020c07062706020d0305070f020304030b04080c0706 82
    0x40e060130140c45010090000760400189400c1a4075115203c031054015001050b8651034503100c0380d82c0c02c03c2111f00602c081c3c0410403006000e2100c404240405a8040f4415418280103008418005041d40e004a03a03c8105003141d4403242c0c0c130300780254030218002c002d140d242c1c9400621043c062010344101d1740214217140d02840c0100300305c400c4507016040ba40c1010b4400400320b074040f00d0395103169405a400741d02090b441c82003078000780c5200c01c2c1040300c1046000403400403c04401c0440600303000b1b4411070843c144241c840c0e1404402062a80e80e290704003800c00907410100e40320704241500312a00101b0128a0b80900340031231001d0780700c00e40a0301e8801e000021300c002c00680303200b042d500a100f46000c40c1008000f1011944484491080d03000b0440c0904c1d8401114189420090341803045e1401c070b800725a903a0b40081e494004600e1140080303446c203000144544c2c0240c03c01c4a00f00c0322036024606c0d10341507950341c4440000c0603200f03580d022000d20840642240410280c805802e00f034480c81 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 84202663 1250 84201413 84201427
    0x3140304150f0c140f0906090d060c0c0506010807031a0712050a1e0501030803040b04170a0309050c090c0a031107060e0606210c0d02130f0b0f03070305030313020a030512 75
    0x1341c859141240c90f415100000c01403021000c400005850343c40c079044460030703034071501180001d000c2c01a000003d0321640c5880b0004441941240d44d10b89041e02c03403800d03200b15030382e41d001d03180d26050780e4400034009c4d0710b107c0e41c3c03403940d103050382807156000145050502d800d4981000074421500115111440c42d41d03243c0354401e03008c2105000003501d0840580074092981540c1e02d1040c2400007401c01010006038002081c1080002800ca400c4640204115030b221990a40f00a001e050034410554480c003d01d4503024240c2019602544100450708000d03150501c04a0120300418000d01d03d00e0300c1301400d01603040000e41a0007400ca800b100400108441d003080b40c01c00a803000c550a2f0780310444400340080341c0162000c540401010300464860817001000e0011900490170018140d64462814440c03400520817175109089503801500c6001035030f480003042c159194040e0002511640c01070000508100e122058101a0341c400740000c200c4590f03c0daa02450a0f503440072203852940085020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 84203913 1250 84202663 84202667
    0x50d05040513020309190f08070308150f1f020f0303010e070e012109030e120706020712050a140f0601030501020307140f03060d02040204152102030403140304150f0c 73
    0x2092110400b624114a14100001d00716611004411500405101c0041304414803090b044002141600105d1080c4d85807032030324008040640880300f400040381e00c54900c40003030818483c801c0402d10007520410341c4941a10b00d81190091007801d8108600c198180d1102040051000c2c600038111101c4007481410449000b410320300e0031400c2c00f0b04010b01000025100c85c00b0310040d0504000501001400340381d24207040f604290b00d480d805070400c00710b511803005000000703184002c6485a500b030324206520b030000346480240030340d406402640300407030803c00310780322003000203039009800100c03031101c8010709085060000036031094440c1e03513001c0704004401307800040782e00035031103101d01c070601e05261003001e1461800094020703406121030807039450864a8641c11100946142c04220f00820400c40001389030740d040c41038021110070141401c20140505000352409a5455120324000c40b01148410350503420040041d40d072008882486a01c120b040d100e1102d519490b00f00210300a4105900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 84205163 1250 84203913 84203929
    0x8090c131b03050403210f18060e06010521010b030d0f0306141f140d150b0c06010302010c03020111040f060206060109030308151f050a1206080a030305090109050d050405 75
    0x10725081c181040108070009a00440c00540d8501daa44c0074440b100c010f0940c113008001e20104110b200780780014081080101207825206107200725014010f20102d10525920750400b881190340090f040c1e09206200108001c1d4641c40c0e580c0759000041c1d011072039000a103401100454000803a4407403614040040e854040c2c80042c150041820440c01000c402040e0090303180c0e003009102e43c0c050458035502d103201d2201035950000804189440e07551604022000385403120300310000340c44100002441c200041c0030780304074000b6140a802260301c0c540040d1080090010101c3c02c6550751958510304c844c048014201810321038402401060824601a00c3d0103005080c0e181405901d20b02000083d03803103500c0c2e41e4001c12010010050401c0c0c0340200b41da040500140a00b244c9801800b07000c1a58010042e0440e0005691852910140111800129441400b03a18540e0b0411715070400424003d03001540c11480c0000005440c0c0320a0712200c3c00d182070380c0004800500700090800251500805c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 84206413 1250 84205163 84205211
    0x1060e070507150c0513060924230a0e0406030503041a04120b040311031305040e0f0102030f150a080a02150f0309010b09073207151b0c0305070308090c13 68
    0x402d051030a040c442030052581d800d00022044020304c40940b001648032b54842044283c028001002ca130550f84030040c4580c2100d0304c6180041d5000b03896080a03e080e00600086035041805189424180041c1c1c110b00040d544540c82e05003004c0ec000584480b10310710700b0024601684080e001c608003440c008000180107a10000144d1092020030004a204040304d402c8a40482c0c0c00030300c0b4014401200e040040ca045000800d500c084100002030760341d002c50328032507a210340b00d44149030035a80411a02c9650b50140b50780c1b5030310141c2c1400c01410641c00d20180c80100510203402d08907690404a05035100f00c8000301d0f50794544c2c130074443c1800e0141b0804c0d0003000700d0034981a20038200b400c4d00341c41545020104c1c5c201c41203000c003401c541e182d0001c0342c044e503801021702c0c00d10034261810740d0040c3c80007601141e84805d011100c1c020480c03142d0800c1409551542d511440d041d0191802c0310006006041c201550140f07902c0c0d01880d60340d0041104800340c4803900420b05014145d08000e00c0c0030415 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 84207663 1250 84206413 84206417
    0x1a0906180a1202130b03190303020c0c0114040b0d060314010e011103060d1509050601270213060e01031b020c010e0d0c06081503060c0702090901060e070507150c051306 74
    0xc1c0140c2e0040c0d40d07803846544144440000001c03103100307000009107007600303101c8a40080c49010704900185075040e002401d080f4410317000c449090070448011100719038490b00d0b800c0454824081070219203144c1e001040f40001d4a08041100c588a4030380009030014460008401ea66464080300c880c88203000350b07191256070540305804c0d8a44400820b078264840711000782401f20b1004a0320300c111040d408030b42c0d82504542121115038603000c51034800f0b0400b81200300205800c1b0101007100c4000c0c000c440141042000110081b45411300c107035941c60005032890305250300c5010190031894002290504840b640e40108030840c1c0600000d041144101021402000e82c2100400850401880781c0200c500c07524000c51145d07209503043c00340c000f44034056a4140100000d01111a1022000e00120b0340210303242c541c16211480c80e10700b241d40610401100001a40001d900d29002d00040d00f0030070700071582c1034407518210300c00f074044074010b140c5403001c6180495511101100340d0b4400e006444c0d58 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 84208913 1250 84207663 84207689
    0x8070c30020c0102120a0c0c0e071d030a0209130f1b0504060e0f0408070b01060509120606090402060d0f0204080717030715021303060507030f0c0207030201091a0906180a 75
    0xa80000b511150130400141e120704000500303030020f520030142108071230707008028403084a481ea807094080c01d400340c82c5040000c0740120411019031a4a90703080940000500900403402d2603801d204109500400300e95405a8400c20705010036221100c44c42035510401a109285084401c05c504942040d00164040d83c40e24905129000b000001c0641040d030452070401641c0d107915104d805845046c100a069903400d1000240d0507802c10302401c03010504954043d040050740e000c040e941d03002142c40e640d0098502000c2409400c00d88001c1c00d14021403c03021490b00300703400c03948040c1c0c3e100340c5c040a01070703002c03c02c10440325228201d4050309418000140d4030b400d0103034a42202d02640c030300c3d6030383e2401d0f0700140359013099070080601001545e0044c4e091040785000c0001600400602070400406402d2544078800342c2e00c081581000d6a0781611040c2003d0705090304040c0104001c1c04201044104108121035aa5030101400d0480d1240c0c51b502d50009020303045c4040c2c55103540c4100c6d0b6122070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 84210163 1250 84208913 84208933
    0x41d010212180703080f03130c030803010e06220e030903070f05090603060c0d05130605010803070b06030102130608090703050601081e16090b0102100f090501140103110108070c3002 80
    0x405c5c086070028a02c690f0050345a45444612861100c200a0002d0421100800000070004140041d504950621003007040507941c54090008120528180707081e0801c0c6805015440411603004992840360003040f282022212000b0900e40502c9401640f22005250000c05c154a4510701c850761240007500580014180320120300d11038000c400d2840807090300d81000032444907000c540303500b519030040014406540e60329003a40d1a507118010587c2c20700c04a800007a1641414000c480b0030306c0f0310040b980f410a01d84002141c400300050035040b0740340030b01d035000808548100f10142c041d108000103072010003840b25244070124800542c00034a80c02c40f00200d10000100184c4100310341a010740442d1014034100100d0511000100800c7d166203811403502ca03602140e4400220284548000c000d152412200c00075021001d00c0014040c2c1303c0410340b189030354407490316070b0b400c001142000f0b9011413041e920f54410020f02104244030b004800400307110318044020f80c42030b00c100c0340050109810303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 84211413 1250 84210163 84210173
    0x13020c0105061c020108150315060103050a1103070c060902190501081503060c0304020103021c15080a0b04020d0f0c0b13090b03100203151215160905041d010212180703 74
    0x506010181c14440c0b06d500007201d014440c1140c4991000007816980448400041030000c4001030300e2484c00a4540000a02450014400c072500382d180d54000c2ea041d0b6403038607412225200c60300d000b01c070040e07202c800d520016150b000c0351100c0442d00c2d0304c1c1e0458241c2003500040803518010410000140e00404441c00394402052840c1c02840f0054015640e90f80c900058010b4803594400d0454403103840101c040b40f0703450b48d2041e68000c5040c0c1c00d005a01d0350b2640c1041e580c4460b40005082c0c40c014501140041ca000620308050a210320703180804008913860f402e000220700c0d4042d442c0c5940001e42d001900c0b245000d8000541141c940400c407024895021a03a00d406405002000c1030340080416904c414907021a1140d140040075070b2425000414616151019a5921500224820049483c020b00c8058104240d02c1e2941c642c5c0815141804100107048188815802c51104401e4a500c43c1c20a00041c00140403c0c842e210807810302da645280f40c1e1800a2151840707820002d81400018 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 84212663 1250 84211413 84211459
    0x403050a050c090118091110030b0907090605090907020f0706020c0114040806040b150d080c10060e130c0308030103030c150506030a0b0603071710050c040605040b0c0c13020c010506 80
    0xf0008800024600d06140350588210114045542c8c2c049280141c0e400c00c2d40e495048001403040903582982952107280b019039050403e8040e41000c154140301c0e442c0c41d400d140390481d900c41240c0c41102d903488840300b146800d00031103400030401a0404a00c1202c596002034114040c010154090f5140900d0708860945032040030b40300504840280300460380c5c044500010500c101030041c000750014400380ba00d4003240d4009039244040340180784440c10402501e00c00c3c2021140401c0d02c2c500d981c1d503010002286420715040464101c0201d8034040b0216100c000070318040e600c03039124003a80c542542490104400340c03041c1d602680e0f08020400001e41ca001c03514022103a802901c032503464560320002420060550030421454054402e40e20740030780e00043c01400c85940311402c200c2c1d03072965102c01140384500e00510000c10340400040142014050003007803000d150009540788680d00d40e00203400f00290107244c00416401180b0503032040d0084c402c00c3c0e007260049450915107041404024009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 84213913 1250 84212663 84212699
    0x6020f16060516050106090902010201050a1418010204091b02010f06030302121b010903030b100f090303050f090a0305010606260105101b051b010e090c1309020403050a050c0901 78
    0x8404105030303241c2100f110390f0011091307004009010740d40c0c4502c4003038000e00070804160f00543c281004034400e00d52502c51440680034001500c0c206075228240d07840c48c41c94020940d0220340d070030040020461540c1c030904061560940400cbd9404103116402404e48094400403c101ca14103403040001a400181e42c00c0240c0074680825100c1c01a920890a403c0003409100119400e00800034205a415803107d05001c42c01c84101c20030743c1c1011000c40e40b00794040f01d41c00100e0007808013031003c00d01030400352200c400b42c080038074580110580894035441041e4030440701c584d141c41041c4802900924070f0030840020708025000b0f21128000d0a55a42d010711031280500e0039002c124000c513104003241c00c02c1d03480e0149842c1042826180461742c1c1d00411201c2d584500001100c0d03101503202d540320140c00b01340100b213170885071034501e200c0c1d43c540d100c490902d203441c800c048000740d03100c0e41e80007038001940985c01800d1007d115080c180d0038101c040d40e016110f108800c0050042000c9400110a2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 84215163 1250 84213913 84213917
    0x1091506020318010e040f0f062606061e030a0f1412070210020307020904080408060105150307030e07170a0c05010f020304170a0b0a0b0117060102030a0305090c1203030106020f1606 80
    0x5c5200d411000c80c0040240200c03400141e4103010700010218284d41051040340c14880d0400989100405490615001c03c07100c2441504200b01203156032822840712042c87c107488442d50041251000082e20345071004a0440f5000120414041800100e9469517140341080f00608001b10304060304442510941ea0001e00ca10001100206118802c00039a805c95601600e491140e04181c2024895074219224118417072058400103d405d082c01d14803840410040c44149085807a141d109038080c000c1c00c10b00c204140b0807444001402c00500400924401c5080040c145c0d07000b041c10540340b42203c603003005042c0030f464400c4801e1694000b0456013182c01e180900c07015640d400f0303001c0f801c000c40240007800d40019001400038120ba154040041310009072a0540b46c0d681c0000c8a40d40300c0e030200c941c03601681050121f0a1018000e40000380c0c003001c03030003d1b140c018a0050008610510000700c402c40c40c0d1001c401803000c01e804020b01c40810030f080008140d81070100c02c25103005040c50003803000f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 84216413 1250 84215163 84215177
    0x61507080d05011e0603020901050f0c1606050903070e040201020a030f0908030f0c0f12031308090d06020703020708060408041a130e07020d08090d050f0f030109150602031801 77
    0x1801480801e4403080900880140041d581d0342c849103288451641c090700740840c80803c001001030083c802c80715010700c10307116070f401c2c1501d440070010103420004604000c1d0203400038040c010300001d45480050100358580c692103c1c0700906062415a41d0341052010580306c00610000d40c0e0001000f01440384e052912443d039844082040350110031940c042481d600c8045070f5020300c0c8035400301401249490f0003c584c8005030514200da42d65260440c01d8a00840800205c2c00c000745c0d032240c407103101d400303501a1482e22844c88041116502e501c4c0098501550224403c0c04140d03061000380c0040c002503005007818180b5485e101040c5c4181d00c50900c2030160f5001d01c038940c000704001d44959000071540172240d81d42d501c11903a261171040750b0000041c010180030a180c50b0146843c2805043c1c68002440c030b84103114000c0c0c509512410f007401c0c1c9054144101a250b500300070055010780356403000410452840c8042e010031094641240096420512149a09201100d0002101d140910b0949 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 84217663 1250 84216413 84216427
    0x50402061b150f01051f0804021e03031809162109050307030903050f030403080d0902010e090103060207170c03030601032c0105011806150819050411090601080615 72
    0x1514003030450b4034040708114103004109075103d0300841c10341242c00030b4800c000600a1b901c0b401440e5060810381a01180100c80890058140f9180d2440560b10400300b8940920480002a15541100070041c000e0841c0704032a070a030741486802030740c00001c03070880c00322135500c0c80002074088805412424042ca100040d0f070229101c203904243c40c40d07a00402a20780d42d10940c200209407100e1800103450394032481e000c1300c2e00000b0010455013129040040076003800b03440502d0102420360418281e040101c41c80100c9200d6881c1081c1500842c421343c40141d864400307150151142620400040b00004c052150320701140e03021003140c2d40981c091a002566001088400f140d01c03407118410450700b0040e49c01381004000544c00241690101519201180620403885e8103890040c01440ea00c9072000466404450180c18059085001c1d03180d04000c610b400300803201280c500320303002d554480d0420440d81a40c20701c000b810341c10520038601064946005004141034982401c8411084000040d8030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 84218913 1250 84217663 84217717
    0x41a0c0307020904061a010f05040303120608240108030f0702221802120a02030304031e0204091212050105060f0706150602010606020f011a0609010c12050301170105040206 76
    0x8a203101d034010f10b0883c45003060b0902e14014114407480c2070545141c805540400e40c09506860103c404540d02c840c503150640d03808540c07091381e941c1e4108007144c490030041110b02083c80304001032140c603074050881e8a0840303003003054150182e02980307450b00100210407003002807104540160342c040e2040800a4000080701a007050392681c03003006d0515102c00c0e81c1e841c02c50700741c0031030213180216001021079950710407040c1c86103543c44000394168410081040007841964903039081006c0050704121844064003c6410340710841021100c181ea540b8000ca07180750000c0740c2d4014040340f00000c00032507040c20301140031391180454010007030b40c1c0070840d00100140c0390060b2905d00c3c1c00d03148003061036503035030b101034060711250041303c0c00340c040e9074444145480144101b9005170000310016070720311110010b126165014030130060401c0703440c04142c4007041c080c00c01840e2003032160f41d41507581c1d0b1400708040341c508200d01061070350703904000500000d030750f50500f903642d8a40f5031051010306031604899 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 84220163 1250 84218913 84218917
    0x20c1e01050403111c1b051e0405060d05062a030727030c03080a080c03040b070c151d010b040e0604170903070608061305010608070c0501110c0604020a060302041a0c03 74
    0x10300c028100c80c1440c2da4041141551b403101001002008504000e61143d041218521000d80c1d06c00c038000c40038108254034038003500490381082c0003402e02031480d0940d80303440d4200001112889403031601c4400320720742801441d038144103848215a03494290f040880e00140245c02c20030054003990704240e0344482130513400b020304005580c801c00c0c401501e5524500120315801031031142c00800c0004001440b5001c1d440110703849903a00c25074002c402d60705c94030203a4404030040420b6450308a804103080c5005003612440d2006403640781103a213610f0308802001d003034030000a04540118240070240103106000240d0980099200910030680c500500903c1807501903100d030a070740351090002c0016840d40050a881c094907080e40d18107140140340501c5000d459083c03003803000141c034540018101e1480b0740c50b04091a03104200108a1400140d456101908070403488039864112800f40300841c07502c0242c0030002c0ac001d080550420b4a0a000752200121030540d1801d0380500140c664080002841 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 84221413 1250 84220163 84220189
    0xf0501020412031d09041a0a0b0d030320040609090e01090515010f0b0301031707020d150b030f011505060a090503011806050604050103050309040f02120403020c1e0105040311 77
    0x2c21280660143c10020009030f8040c40c441c14070800c00800d510581020036005102d2034024101510681030f02c00000c002c030300001c0c4040180d0380c2e25400a845542c4404030250300c44c0c02590301184400a650394000948018411030405240c00c1004004c4540c0003500302d01110440c401c0050951103980d25103014051700000100140142c851150341301105000c02c0303058440441861290580301c8511521a100a0202800148000f8000d8480741100780003441603500c00340114a641e501744c1c0e1900b0024441d0700d04461415100d106040316820308001d09064103030a40000e00c005082e001c070701c0141858074015a40a510009014903149000340c1c2014010600900200503090b8202143e110100c1e29010881784142400c001c141e040c03400703016040c16280c00101651a001d00c01c030810000306030450403c0341d03054003800102d81c03d0400c1180325114078000e07005401d406001400300320900b00c03507509603040501e900c0d0f070b182e030350b66403000540c0c0031b40350300030b109020170110394001980c00600e40f0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 84222663 1250 84221413 84221429
    0xb070c0c030807030807020709020f070609020409020411041a03060a06030b120d0f03051302280b18010e120a030c0201031b0c14120d0b060417010c170708040f05010204 74
    0x43c3c180402d40d001d061203110751059820703181a07075210f08030101a44900c03075a400c00740303109120f5074020070070a40c003080b0580e00c010000035076200d4543c0410151002005181d44042c000300703081058150102142040781c00d85c3c50a6469803810000003a128000790103110704150740e401d141006522044001c110907507000e0f0840b23036400c161010082c0100d01390f104c4980083d0504000c80d040200029406a6142c0d0003404910700180d0380c4076080510040300c0c5084203c100010f0000f41300c007101d000074a801c5400304010300c01c441a6000244c0b040c00c04c480c040f800b9400a05084007913000110304001010342c5480d09601c00845800128081c200c0d01d070281440c02c284007a071140607500442001e500611508a000781d00c8058543c00ea107400d050b03020309800080401141100384000d90290b42580001040103040ca81c90b040645c82440400018201300d039544c0c7c1d0981c0744107420503080c0240c1c42000c3e8880c1d4280c03611a100500100d80030340300802180070f00680c84100b04081d01510050820740d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 84223913 1250 84222663 84222667
    0x509010306231302041d0a0303111303030302070507050d21021501060314010b030c040b070602070b0906072309010810051507020916020c0613180902040c020a0b070c0c0308 76
    0x1c3c80c001804a64040012446580703000c42c844c40802200b0341400881c1c4400001c0e02440f00030342c5054000d8048403034506881e01041000003049800d11b00703c0b2002d9070003981c00580358892860000c0c03502105410441c854022130090f1000240745260741d200e40d07600010729100f2800012010b0745000c810501180311062440000708801d40e03d50711650303540450b070b01001116680c9600010300d91100380d0362045004030402080c8030901d4260010080540300b184c00501d000540d07128070f001d03020291400580350f00054148000d803030313001d059003c604040041d001041125000214014419104458103014040e000900c001e001c1c910303034034014400685010f000c40d5000308410a250b01500e8224810b40c0c187d00440d10324407002005024250407500105148840c2d001080782a41081d10034030003801c0e0110340840c01a4104200c42c07003a824040b00032500c4c40c60b81c030400040d01c01c0c00c0d00400071075101c0d10010021a02c011072080d0060030034104861842d120f0b00f04100030a0607500050301440700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 84225163 1250 84223913 84223921
    0x6150a0c0b0103140d080421020703050709050124090e0c0903010504050607031104080703230f0c04111206012001140609060102070e31060e06060307050901030623 72
    0x100c0b10701d4102400c0014107031141004450416035211070140e501400012a5035481003641d042003945407e2380000c0d004032401c06540707a42d400c0c03621403a904070250380364030740c2d0040180b02103429030700c1c4406ca0305a190340e201c02900315009005510380c0c41141305040e0312101081d95411080100c8042d00d901030000e0100f840d050401a13607030882030b907111000902d0113070021500d011070015202683d400c0da02810485145480d0800c0075035000d00100340c14400c54a04000300070003000298035401c04240903080724a2500208000c5920362060203100c1e000400060003c2100d0030f0200d6402807003400e15881c444a80a02d0382d035800201c1525840325032900c0c02042000059140d510310840f000c540003c5260744860049844074180d2050346a00080e403000324910300b0f0103204000d82c42d0034840032003e0609240403003030356000c40050f0548401350b03208a06105002c050100a074010710a40c010b2020724a0040800c80280e4144009820290f0324502500400d051007500c000340c0022110500b101e0034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 84226413 1250 84225163 84225173
    0x708030c1e070c14060702030c040c0509090907051003020a05031f080f060613020f0703050a1e050309010608010c02030702041a06030414460c0807081506150a0c0b0103 74
    0x5294084c0c0f03140c009441c50318034142d10b02401100c21442d0b01401034010300100f0014000907001c07440e202c6062182c01d00c003407109a292250340e54494a1550018001589000140701160007800124810076004008006c440303604441103d8004111345190503002144500302000000c43d908002000d00800b48088010400050618001d5004454080c5c5820456000740c04030300c100c14584510310814881140807034040e01c06004d508060341051102c4a5100743e0300e81140002d900350030301141000c002d012040a00f4403c020282c590301d002002010a0804007a582e07016a9900a106684a102078402100058140d620b2000f02030805074403820540b43c0030071406543d2008207040e104445030442c9003035280304030400102d60902400764000001c001c201d4000401c00c80a0b00c030002c5040e482e000100c040d005140206007030006494601e0030111418107180c0c1c104120850541007100344540f0347d030b0b0300c0545a40040003086056940d0800e0741e0035100b0f102ca8a10107070200c9014000002400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 84227663 1250 84226413 84226433
    0x3060608030912010204030f0201120f051008190c050f0d050f01290109090506041503050102030901200d02071401051504060b130302060c011424060708030c1e07 71
    0x28400719071000503150b20f485010701701c0c01548400350404c40c6200c0f4040140d40518056102c129080101103001782d8068555002d4400503210f581d121080c4003020810000140008001e22200c890300000341e03c01c54540f4051140305d4010070f07204200b0111b00030b0459990004640c0030592020981d4410403000c0c0c0524000e124241d444650310ba40c001007040148000c010300606810142c41c0c6488440c00c0c5040c0c00014400181840d80060f60341800d940c50700c5a451504000710710800c00542d80740b4240b010789003520081c0e9510403a1041e00b249410408080001740d4180081cac0c042e0060302e4081d1410010800d40c03c905501c0501e500c0c0c0b105114812042c5036040910107016102840401d40d00d041d181080d10a2040d51040c01d000001c060006280070401003d10400820000c1806c0c1c3c1c00d10491894420150707000c14041261220b001498480d125900c805640110360590600445840e89a128800240200f030900d0b40024201c03265640700840b00503000c942079070191904014a801c009070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 84228913 1250 84227663 84227677
    0xa06050a09170d0b1207060e190902070c080a05061518040f020307030f030c0507060806010507030e011107170c01050405180403180305010203090114060109030f020d0204141008060f0f07090306060803 88
    0x40040c0c03044296802c1c00540840001b1014440c9c1e1103e6282c1250754001790010311080700e0280d60444000381104042101d802514052806040305040c48580c4600429840340564041c00300040c81c5040c1c0d42501c50740c0c030780c85500151400031000c038070710000341030902ea9000101464001c03010030091540c080341d00b0602034440d9040354241c545454041e15560021a21503002840c2040b10350006403242000d82c050000c181084850f402400b040030b82000001e8001000024064410340c5204104121005600400382040b07403920703080c10b0104610480a1017514034642c4031901007001c2520800d10203541d60360b01041d07c03441503200d05d420b901035441601c1003207040d03003803845a086009518120501414050f10b404552524660340d6880f6550352090036a444541c0c024842c0150322180500707460300ca80115a0140346c5040d9a801e0320100d0030360003d440940c0604108401c003404400c4442e080f0202c001c114005990700e43d02200c0d203c0d03050f00002d000605000000840301c5002002c0c040c0c1e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 84230163 1250 84228913 84228917
    0xf090f0303050a060f051306080304060f02010f060807170a0503030c22080c040c020111030a02040e090d050906070204020903010c02010f060501111005060604030f03020a06050a09170d0b120706 85
    0x1d07251a0b03909001e80c4c106009600a4141c05e8000304500d00d01900b07038000051b14080040780f041d03624604d050840c0c00907402800401c07070414403080056828403810901c18900342c0d08100c501c0c10a801079558180e6030054503c04100c40c104800e050741c040001440361644401100e0307881c54003044c0e1100341d03007010424201d4040c84520481e00000100c010909841aa2000300b0064000e8403c00c8050301a912688095542e511815492014044021131140400340d00140c3d581d85005540c170603003103009020300c0e800e8101c49103980d801c07a448011200329250482c0c0c4a80c40d4482c40c00001d00030300c1014000380d850740c6490705a81c152501908408691508441c0c20400651345e50015140b41d00900311035401900104401c2c0390444a540c44180c100c88060040f0b8241900ca07071712041c1c80f601c41d0400783c001d44d120310220010400349000d0a540102200c5041c82681455941c4604140303c04075a01850640032511007141c0790705500001d070450000b03011204200c070321440140c907442517000e4140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 84231413 1250 84230163 84230171
    0x4180b010306090207030206060f06160c06020d02060c0a1206051905090711060f07020703050703032a0807031202090402040b0702150f03130503040302090106110610061b060f090f0303 81
    0x260a0030f030361003610407464058002e0701080d600c2c8400c12203131016a45885170301c1081803058030800c258140600004511461501070454109400a03141c141c0910f80300d0219070001e0100706e5203032411000c3c2d51400f80c650500810000740400c3e0007000d05102d03000160855061082d030314406030600c070940100c45064131030035079035294110110fa6802105440080310b03401000460303107036144d4906940e0302003407500c140e5101e2901c036642c250501032554000d40010314022101c0000180ea07000c100c2081100038a08040c081e901d030303101e41b4203020306d160103400d0010b42c101185001050b90112103054500600c01c5546035194001003040341c0000c41d0680c0208402d4665241d4585078100702d90440170b070522003070b00315035442c0690f0f00e101540040445941c00705100010041c0c0303e00040394064202615904510110f4240e81482c2c9034000709070b40221540c00d4001c00820b90844030f0b00503040030049503440100204d0501401074590f20481a214a28120710b50b010f00c0806140041090f119540c140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 84232663 1250 84231413 84231419
    0x3030f18060c080606040e06120d0c1101030507080708040303060e18060108010203070e09070c020d030905090f040210050a0e06040e060108010605040e01060305070e030a0507081005040b0c07050304180b010306 92
    0xf54071900c1210b0031500014204800d0015070506882c140c5d200344010300344072448441e40003c40c20007a920070180d0118a07503120000801c5000d035401450803000780f0301000030303103000351004102d180054200310911464001240515200382c022101078100241c0e101d0300b604200001c080344101c0c1520810403409003400114402c1e00600803240108100e03624424451540c4082106400c0c000c0d06150501411a10480c01a1599442d40c801207000b901e13601c010b58540b1052211030078004000c00d1029520b40c0420005031b4505022100e0034a641c030340f80d921882480426036081906c031044960001c0080380001e020312a60400d144190400c0c5d0718421640d907121010380b001d00641c082da50f801000c500050100620951000703074003038443d1400d405c034540e9640c0482d04000c0c083c1003d8038550003e038010f00901108100c3c1061056080c90200018541901c41c00315801c0c2c003404824080c10000f500c40c05200701042690041c228080c2a107034082c142c01c5c0b10350f0007099034030030342808241051800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 84233913 1250 84232663 84232667
    0x609080105010f05100c0b0a0207150905120a090e010e0709061409130b1903050712020d02090907270b0a0605091003020d0606020f0606030316030c03030f18060c 71
    0x71a0494803012a441901c5003030000b00040030000903440410019036403100d00c00f0509003440d1900800d490f8000507070700c80c01d5041201070304a00381c07600040341c1c0c1820090400101e00107034102e8031418080b0015140d0300141c804948c0c0603442d0f40501c04006140c00040398813030103c01e20303501850b0750752900c0c81405c0d03407030701c0030b60300c1e840780e041d0610243c00240400d039401c0c100440d480c82c48502202c070008c1c5615131040095110540701d049804100140300d8180100201004440090b107901e5507140c002020316400107108203007103840203005230620400319980341000c2000e0f0303000c0d107081301122034200c44280503030039540d030740e002c0b0b070304032541040d82a203039a08001c51040107641d20742e6200b619040c89003080c0080007101c54652420036908010281c000c0d40c5522502018004560291050400240e09036280000140c0741d14071130b40040281101d107030011a44210001d6140c2041190401c15050030ba0042010400721f0b200382d42170500d203014400b0303035000034110709114042c2000010580c00013 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 84235163 1250 84233913 84233921
    0x8190204090b120c0108040f03091a090306101a0903030c0d020303071806121e021303150b03210c071403061b0904181202061014030d0305070309021203030106090801 73
    0x10300c5c08521910049008030761220905a80741e402420441201c540d1210034a2441c0680341c1c203072401c1c030800b00744040340d0314040c440d0035000303000f51400c1030940c1d0405604000303e10148240c20a0f181c0002802141a05e00b0700503103c1005522056075604a41084040c0d240d40c000c0f1400742c000390642ca986043c40c0d4510f4802002e49889590341ca00031001021741000138030840701224159403401d030601c0e0504983e4001007217140c0000090020b01495480c1201d206d129509580700b0050500a804c205a180080d4111100b0f80060205134000e80079015090a4070451080c04694050b8100200d00d5644880c0c4980402c1000c0e02150415500c0050703501490030502c16081140204118241c1c140c602508020882c0b4032100d41200007031950340c1c0786a0500d0030441e0960145e00b00d0f500308001c0713110441c607410040500c2800039030040099070000303031a040d40180840030705980e14041101310307100e98807a189540c2c0c0600040e032400c1104282d0b03a503a030403d101c0c0c000040d00d103040210310b207501805 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 84236413 1250 84235163 84235183
    0xd0503010e0604180b0702160b031909020d15020a0e030c0109060311090a140307080f030703300b1c031407050f03030a020414010e1008190204090b12 66
    0x81d10501520303603004100c054618425001a05004001d039880802c500c0c103505402880c1a4005021210340c1d035900410f01c80469108449007101802040804034600b0301c00d1a2100c040480000c0280003840016007003980701c8405888800400d02c02000358990303a005000c0fa515940318042505044010150350300c4020007880d002a0b00710004000d03050281d00f20990003010600c2c03079402c0040c914046010742516901c005080c82d50391508190505041c000341001d001b01030050f004980d641d1902d65501d20440700f0003020400c60002c0150142d22000349200c00c0c4200000c0001603d822010301c6014000c920b403034600c60002524500c510040c800d500d00d5406e503060b1101180a810300c001c101141d00040701c00c0e1018054001c5031000c1c803034140000d40c8911002c040040c3ca4509014801c1d42d03801b4400041030600c0030342c000c044020340e03d03540800200c80c0c051505034850750320890b6030100c2c8002400a40c422030b0003c0b07408a03221b07000e90040d4020784820303940b00b030030100c5180d45295115034a070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 84237663 1250 84236413 84236429
    0x70509040809130605060703020601051801060c120909020a031a0105130302061c0e0607020d0f051b0708030c030d0506180c0a0203040e010b0304060c02070509130227090d050301 78
    0xe00071560030030035000c001c540f401403400240c00350381d500030032030560203550200e005801520051005181c044810204012020341150f80381d0b041c200d01405c10000c0c2a070241c40d01482500440c502c1f0710a0245001400011a05540f10154130001070301516500d4401181081045141ca040d54441c00c10b481003483c0d450059040d986c030319020302c901c0c1d5210b13011030602d0b40c0039260000d82034021070049902c105c02d01c20040003203207000d860013402e00c44000c25280c1003140301a00040b40702c0d40034080d20b11a0440c07581c94848c807440009500d1401100340d02c01e080600010849800000c1c0c0031001e00034085000005000702d943d110100204034180c2c604038860380c0080c801090303007a4810000703042c512100b8011030b4905619003a545040e407200368001d00c40700780004200010010b1600a100389a042400107144660800002032140340004010340d0203022003012940541d641c28880c6a03911030381b0803c0381c0340c801450600c4100842d0803942c0071240c4c428900f1008d240c520070400c4038102d4002c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 84238913 1250 84237663 84237667
    0x7020a030f050703030f060b03040b0112020d02040b03160b0c0f01020c0a030e1306090b0112050f01050f1801090203180a0308010306021303122a1e0507170109050705090408 76
    0xc0a42e003d4104140580c20155103400e044141000d900c12035016000f200c1c40141c0740d00c0e1078035041e0400c0c001604008032402a1408100060301c5004510049907030454010955980110209242a0040302150210219444005072409408009228005510055481c01c1f0401c50009090303128250600890742e002501080100340320310031022501000a1a080c5441c140c01445019244c01e41c001c01c620315521034411100c0d60b00800d03800040d6560140c188610715100380c00c0c0082100522400340a01c206501c40501659030300800e4144510300c1019142da940c6864403800250000c0f96130700c0114000345106618030310009400c004071603150303076000c003d40c2c21a5a60301c0a034200342504038808680d0303040440040c26401c10755100c2c42c1565980b0814044600c00710041d46101900390b001805000c020b0300118a4a014003410240184401842500c4500e020b920f054007a034440b0302c110240d032145544070041034000207030031030140d02101c00080d1594200501141c054500600803002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 84240163 1250 84238913 84238937
    0x12150406150b071502090a0f181b0e0f0301150e0106050310121e0f061103091209060415020f01050106050307090501260106090e010f0501051606151d07020a03 70
    0x1111095004c1c028840c0c0e005400c080c2500c000c507001c000d03180c02060b841c41c4071a905010140fa40101d001e101d00314010240700365a40c2e1101c100f044c0fa0f00012840800c960808010f806860701d241260701c0c80c102500800031000c2c4051418807550f0640109038128042c8000007450b03510501c00d0341e003c0c141d02030030303240380502d004c07915944805070940c100c4d00d5501501c0c0c85828202200101250304e07024000c1c0000e112a00d2400a0888002c480d0030400f10030103005215204034001034000d000c001c4000380d59a503401c2c1d60000381c010b001c0c990101060300e45983c060321810364042180703001ea00f81c5030020f001e2641c03150310070389140c0005c99074280056020740040040e5841804000005601a6030051041030b1050140b1080f1600b41c10010102e0710344842003140100c0c0d4051180108200800c40240c0d42c10000002c190748145d4050292140078038452000b800340b540c2c0200704a515081c0300c005507035030321410b24401980340c10507410401510000502c81500204840c550a40c0c180d40c0c1110f181c0c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 84241413 1250 84240163 84240173
    0x80f060f040302070506040f090b10020d030b01090801020d0e0f0309030a0305070f0606150207050f0a050609181303090608060109050909012009030106050a030f060b12150406150b07 80
    0xd0000d0064085120708080080d05440d0000100042c0c462a100d08003203e080a0707070a001d40b0520000580203205801c0210100c40d80819585400f0368a840d010942840b00320040f11000c00b140c2198100c0d500c00240d070340100c001540103107160300e0030b0001d44404464103c8072989038090001c0407a0580c015540c440b001a01c074100806804d4426144181840c40c1502c40fa02150495041000580c1002c00382c1c40d104d640422a413402403604444a040c2c142e21034010410f9841d1500c1420301906002c9a40c070070503a2010010b003403072060342003d0181c0d407030140e0710700344a40084c000035400f050406402141c0c040c8583c1d9a5032042106840750216036251009108201800400c0c443d425503845c0110702c01d0322a00803480703044d41c25403603c41d84c0342c0d4030381001c0600312190340d03100c503108116101c0c0400009100c41c03503049005800c81c500041022003000414100c540f51080c00c803040c0105504005030b880900001030080c0d000700d100700413100c82c5c203550152800030307405175a8000c03205020030750000d9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 84242663 1250 84241413 84241441
    0x30f0201031e02070f0209010510091202030102160c14040203011508072a060e010204150c0302032104110a05030a060209040b120601060f02010b18060307030c0f03020a080f06 77
    0x40d8181040760700034000b00e8201003242c005440c2254141c42ca15001c00c00d6107000404c650260a00321000c4c0d038049541e0101400c40d80c3c20303120712038a2030800742c040c0e019950294180c48200c00b03950404640f00c071651410f402c02086034040c00d8100401f405000003582058825681600c10ac2c4d403005111028098064905d814002d0243c410488a0b8406290f01c14010701c2811400f5a2107d10420701003043ca000c000b541c146400b54041c5a20512040080038600c0c52148150038031420988100345042c2401c03806c600c204201c0414020102100e050001245801c40f4071440c01000d2580e00c4244481c00c11180c100e036413050340c1e4181d100100c15004600135034014203009600910018ac40b0096201080b0300f0305900c00c00000c81d40015004000081d00030448a44000c3c1e03510080240440b840c00044108240030038220070302c05190300043c49074808005080c09036802000c600e40c1255119503200340350300d50b404100d010721b2805100082e44840040c03a2071780369a10344080c0c1400d550340d416248000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 84243913 1250 84242663 84242681
    0x403050d060b0d0c110105040201140a020f01023015010e040b090406020c1519050406020d0f0b031b0a0306090c0e0f0a0509030901090b0a050c070b031e01030f020103 73
    0xd40c0d075024001000c0c0b11510040c07420251802020909080c10300d4081d040c615403c20000366a410b100c1013200507a8003110701401c0056111500d91105600c03d0100e1510325150521043c0c2d610004600c42e0b00e011807040319840f00f00444107000043c1c410700c000c421184058540d100404100403840103658040c0d5080700418002a100003003410f00a0001a0f10032070940341696110350018841a0b04002400f1070a41442280822507190038600da484150340d0044800921041e9030700c01003400c12041d9011521724500041c814410380d0390433030040e4028601103d00a00c2442482c440b036500c00058404001e074081c1c014070b960911855511918050301000000300e6821801000101d843c6070307010720003405030358a10100580703407400021500442c0c8003d042c1c0c6099520a0140d86640c0e070344440c084047d40e40c0450000d0312540d01038070503205806a00326504c0c603406001c0e00400da020040003e180304034107480e00000106040c42c2681e000706000c0c0406011080e03008255009540660008a00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 84245163 1250 84243913 84243937
    0xc05070e07030f02030112140a03020316060e0f06250206060f03030903060a0e070f05031b031c03050f06010e0a030602090105160b090106050301020a09170a0516060305070203070b040305 82
    0x1180307500c3c200c00c80480c0d1090b04800c0d041c07003204610009104080000c103807144880001070a8410503520040d599004202600301241e2105544600b00300c007542007a1401c000b10b0048600c280380f010700f0300d03490b45800ca9540141000265005052038808041e5200542003a0060880e60b01d074a41400154542c44061039011320041040102c103403010005244211105403000814586d10100a410a80d83c1d0303021484407810b90205011a40d0702082d1002d591080700503200c484002e1001090901d0030881707498603181403003420000c00e1034054002512810040f00044000d80d2400c0064442c8100c0000d02c9800c00a010420f0000421580c0209a00d604c141446400d100341c4001014035825995001c071b600f420010305014442d1001d008140c045c1c24110005c0d81448203500004010320250300c40e001c1542c54107030522104e01014454080c20b2074219081c4c0d00b15090702511000618107912829000a19180008001f1031011080c3d9050700d5115121144d15150341e142103640350045941251 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 84246413 1250 84245163 84245171
    0x8070218011203030c0806010e09090f01020a020c09130c060804030212031303110604110f040f0e01020901020724050a02030d060311040c110304121502040608010f05010c05070e0703 80
    0x4804440c0c82509000b020680d40035814038809250003001da40e1460400000c0c80703615030900800383c0c1c1000c0e082648840584260b01296201e034860f0b80303442c030000980d114035440020342101d0307954040381c016040d40c816920740030030780c880051003007040401d01405044414184810b108240c03180d0b00c116080382c0a032044135158102e14142c00820b03070065840310480481d0360700d84801c02d50800744241c003540302c00c40540030500d85500c0390006450942c00140c4182081c0100c3c540564440d80201499030320b1450070005010300a4499001758045001c0d98050b02c5140c0300090052200382803039a1441400941c08070042c41d00c41c041d54550444010003080d400180030140e40c0d81d41d2803103030b0401103000381260201c00b680041444212500d0003041c074100300c2c138580fa0034030240000080350304403105581d8640c43d4441170704101c0303000c5410380b40440b4001d00025002801a60100e0b9450580303030001c46c0e40000541d14030040d5007035528070b00c0c002c8c615001b490b010000494080c0038903922078500d08001ca = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 84247663 1250 84246413 84246439
    0x180305060702160902181504230405010b07080a03021e0c061803091f020106030807080d05060627010e1011060c0406140a05040e0708180d0c080702 65
    0xd0411404981110050703104541600001075081050300040844040c11894807015400081c02e900c03007000c80c203020320b80d40303a00d0100950114048800400d01c030140042d503054038074007032440e80c070414480385d05c25810400045982444001142c0a82e5072182c2d840e031400c6005202500690840d40260700c50240366601c1120003d031801c018040c060450340641814034200f910403680042d00040e003401d42d8030602288940303442d1500301071482c140308182080c401d440440100d01410b5103400051a000000c2180002c100c1010040d0a4a24000310288142c0e9600300c2071000501502d1850600d06400d0304003603103020f11040342d0403011101850108501e0880388041612402c05412600011b0300c061074045031900203004d950b4000030b80c02d400c0ea00d8240351541c001c3c15454800c00d10148400001184840e590003081203130001c14507110219a41d00d819a0080c00b461012165400d00d1680142c00007c140c01c04242c00c00241c000d6118034034180f015031507454854119940c1240c000e46964901 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 84248913 1250 84247663 84247673
    0x608010303030f0213260d0e04020f04090207030f090501030506010912061410050906120d120e0a080904050f01051c020d0501020403050c10030501060801050f0402211b040806071803 80
    0xb074210608500e80a546c0241418801084001d015000350014070b02004041c0d03000315201c070300d200100c07400740c2c0b00e181d80f81c011142881560b01500c0301c503100048100c20140c1102d490340700c082564a8071030251380e6900c0154159101240c01c1070005082c00d07024004d8241c040d00c50300e04135016150019251050007850004c010b02035079a17820000c4035200410091038500c1c03015a0000c010343d40d03911050810b206480d640c0b1961050341061284000c8000140302950340941101d040c4a0304407425003000d0f0070100c011b40e01103203409024a08040c0014501c840d00c070361a80c12900090310316944005c10b030b0342d900c00c5400b03407200c01c0364050038104104000c40e8090002e40b003c4c6014101801c00d010b6800100320729840a14404000e05041400400085030810380480c116441951688074024110002500a22401c07540245000010410740014207541680c80d10404000480c410110351401d00980e060081d0304c90103415034042c4c00082e03aa14810b003410403004080500c0341c41040d4a82d941c07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 84250163 1250 84248913 84248947
    0x7140a0c030605011a0f030703020c190309030312020306030703060b010e060c06010e01080f06070c0f02041401080c0612011e051003020c011103090a02010807120606030b190608010303030f02 84
    0x10645826442c0d1005110178010300382c0d8903858424465400d850300e822944c1c3c68006d804010000c10a255001c141212404e50a014101000802c0710b1540040c82551034003900051950000354002240c04a48c092010783c0303842101d01407000100200089851944c030500542100240c2e0b41c1000516903200907503490742005070022581c980060000303913042400000d0304032016403010815134405880d1007105a00812499001095132030700204450b402d08008059a62034a00250003134034141001031601000420303c1d05803a0380506441348940711000300170803800345582d040c407202e01400041101c0c58041e5269000c414880103040459075541c00002c1894108500d1580031980000c0c841c10000700078400c24810b079404480050540c1031220405a40341c0000f0303802814090b050b0301042c440da0041c2503400369809001806d20440703848403030080240007642c40e9907001d0382411003600c00040f142d813024001d880c03059880d56080d03842c64408034090700c400080c1e108050b03420451309680d85007183c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 84251413 1250 84250163 84250169
    0x40c21090203120f030c030709050909100e060108030f0c0703020a0b03070e010507081801030f06080a29060907051c02180a03080406030b040e07140909010b010507140a0c 75
    0xa800601a501401414141880300c0803d001c081c008001c030f2203e4407141800d07031303403c66001000b03030391640d452400a4841c1c41d06134000e030b03a024070078208026020100003040940c6491254044c09a05615840395980314000e01a055283d041032150400840812003d41906242c80e8100d9000382c0e560b802050150b01c07640c00c2040040380000c1006007113900800001c0c00c1d10f00a19100d403a103052511160000e00030201154407092580520b0002c41e80f00760480d1400c280440d10401074203554041c151b554100c0034801729030120440810342e40140240e480e1071580191003a45080c1c0f0f030b5402041110b5280010b080c4014004244948095104070021840d03465a01180042c0e848114980c041d0040b2080003085205242001d4107000144a62086e241260780f103050128002d440240058080c00c40003885207aa84220b800000b02504240d8440100850581c0c080d40c9640360071811313a080c1c50484501e40d010440400c401f40000d0984031000981e00d120000359002c662042d03907020010410380d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 84252663 1250 84251413 84251477
    0x21b030a12050403050d0503010614030a09140709061403060402010806061201030b0106110109020109031e1719080405210c011b030e0102040f3503030a14010602030702040c 76
    0x1003018800c1003c1000706e03155070121400d1035420766240c148000d14000600c10205020600070021409a4080350055402c1c0c0e94400d8040702440820009240d031440207120f07443c60320381030007400a07484134001048500c000c8050060841a522030f00103644208000c0c08854003d03c0401546480140c0c10703010318081c5225400185055260440040c43d407034040c03070101d030581d01d080000c0c00140c2e0041440d034100e139400303030801280c0325454288180b86c408040300a48081541d510541031000600e004003442d030081e10340309130a4105404100c40ca6401100e00802950185030114002e007480504040c4240512002c2071510b031550f43e01a080d6000180d050909103541080381101035014041c1c01c0e6406c0c40310000314209490041004041011403140b5280c200c00c005e4003403050100800f041070007400f5088903200b1030f0810925556243d00c200d40002c0f40d180b8200c0c0750f040540700c03c08000d0481d00b50b0b030f0096040100b1502000f0040104510a40c24403010440ba030407a440c00541c1a01c10700c20f44 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 84253913 1250 84252663 84252667
    0x30e030d030204090605060903030304110411041212080910090f0c09050708060102060702030405010c060b0d05101401030f0209150901060e03010f05100315020706090c081903021b030a1205 83
    0x20702c18130036150039800c0144101028400c18086480000940e0b621540080740088031003c0f000c00314006100c0d060b425407010f1800180420800310640300a04c101744112003510700040c00d1002110040d03401c1c0c0f443d841b65003115428503c0e20038960045481c4030b01855541c1d03050240f9507500d98050b80164815800031392100d04101c051504003c5040d1301542c217001a042d00c2c68060300c02922445240612030510441c0e0361590b0034000c180c1d08c401c04540000d0407101c4850328a0401560300c800e032504241119041c0f4200601c0e4040c4000464126503201800e45860303003847e070804c40300c10401015068550501c01c02d6a0103503803800c1d0761a00030107083c1c640e0050080d400c0103040c01c0d240c40005d605229810311040c020000703041c0319180c08480d00698413004000000f20060043c0c4212303000506400c0c104030f00c07036040c001035440000c1128661400c40341c4c1200d201c88038010150f11480040c025802000d0351400201600c0081d101000300282543c0d1500303442e9440107030114202d1003940c001680 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 84255163 1250 84253913 84253919
    0x318131e0c02251a04030203070e100b0c150c0d090809010212040e0c0a050c0f0105060a050111060402040e070b0313030e0d050309041a03060a0911010e0a0909030e030d030204 77
    0x188180c0342d80240d1240b0344040c1c40c02c411203049003410f40c2d1296072140c0b500c2082d820f040c42d50500c03e90740039680c000d00355060b0790341e1404904c1c80c0c40340030390307001c07001400c81c0344001070f0000f00d1411908100c6002c0041e15a00c90340b5013204550400c0202541d044000030444084120018803a50010302d00c40c80c0725680310702c0c3c10747c002440d02d80300110703042c0041c408200c1030044011030104168488136802059943c0d0010322012510f50040d030f0200b020500c20060051881001074000f90721904068865070042c0d550340004407100d424003000d185080d007110000c00e02604080d04044102085541119807207561080003091580c0b007140d40b0f89200034125001230815501a4031481c11303200440f41500391016944a140e241e00c40d00301d00912440d0307100b41403450304044143e1080b048000406480b0b507480c20001170703c0a4172152400711a0742d6a180c0c008040d40d03004402400c10a0341c040c1c0980001410644101e0050030080f074154240b00401001da103942e83d04100c200c64204061742c0c05070700c40d89 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 84256413 1250 84255163 84255167
    0x60501090501050402070b012c0708010602060a06140409020303040513020d060504021e03130c030f1203060b1e071212060506040509070f09050a06020304170318131e0c 74
    0x43c0c00091003940108020740c08568103441207415542e0401135200e801600115034210140303544000c8803410f01d41010015103541000c2c10604a400b01e03002e581090740e541409408666490044860302c44811050240d0b500f001c2e800f0780740080c806000c8901e8591144006107152140030305d0385000300d40000d0240c02420b8a4000d400003040305680550800800c8030342c140590344e080d8075802c503040000c00055004165110705c542111f0b08150b141100c6512800e024222000000069410f40744040d254220a4820704c40c480440d4156503c990402520a5269103c41c90314420420b42410034002a0046085600c041e200c4201c107031212615130354004900030546456a1101d0700c225030502003000f05d41c4524010075803000180c9031403200c100080320251400c542d650003040d044098460040b4106400200078001d5401a03101150404095003405540784a24410030f240c0441100d4500c2c214204244000302c0d1b40303485400032440403019070340e1048220041c1801b100301900e4801464a041d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 84257663 1250 84256413 84256421
    0x203010e01290f060d14070f0f09080d05090103110307020a050709051306050603010e0715120902030c100210090302030406030c0806010818030903011b0908070609060806120a06050109 81
    0x886014208081401d90b0800180e101c2280100f5030f0140d480001c3c2c01d1544680d82c2e111400035448400c0d045802c5c1080c480041ca6000294000d0000c1500002d42d03804007401284c10004844809005080301c2c0c52598085600d6008042c4040c140341e1210342c0c1004c00c8100c6001b8610880c0302c2c1d40103000a41c1c44c0c0c03d101d4a400856440340c06850b207490140030200300c80c4c0000c0f180060300204003080319103408012070300410410180c0c00d20350043e40d00200c1d081002041500d82c800b01d40d0b481c1080707043c1c0186804200c810b0700c00025403540c046a500f101301d0812828244454201d401950580d8855801800031780e250150214010b81000a003804a5500341c894080b002e20940341428061814600103001a00081c14082403035260351940801d02100304200c03641c840002e8002d001000c00032000c0030204c140801220082149140d0101f00e40800159413011203c0560711032004504c0d242094861080203400190010041d801e0f00f081581d00304030400049228442c0040c00c7d40c54400c0010450f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 84258913 1250 84257663 84257711
    0x614010b070804050105090d02090702010c090b09011205070504030c08030c0d03051612060807121a0606030f131a07080901060506040b310906050105090603070305130203010e01 78
    0x19801071141e0404192140140d805950007801c0041da9200c40c00700003800040c440034020350003130144041284165064001000b050000d1301c51448050702c500c1d85800318011418a540003a1101c5070601e8003000d240c00840d08908913081c41484e0540f00d4a0385215041315811165255200160b40c000a000410000ea00c1c001c485c03408100c035040c091038210f004504600c0050402c02a0100e42c66081d8413075000c040140700038000c0f40c8155070313105420101c1240d0300c44150f0b10341e80b22482c4070044e0b81005291a110794001090185035548030203107c5503018000d010203180ca0511310080d000258429a04400c080e48401c3c0c00301b1070700c1c0c028802050500020b000c0d0215034100241044161603020a540559074806891a00d84440c030003000200c1020b142007034146c11041b0301412001c0401000002504c41101d001d200079034907000191054441c0c24006600f0500c01c00c00190420300c030750712642d00516001f5019400000c1c1350006402e41c2c0041501600d01e9564906a824665054019a0f80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 84260163 1250 84258913 84258929
    0x30b0604090209010521030d0b040605090f071407051207060c0c0503041a0906030703020408060c070308190e15060f010c02090403081008070e011805040c17010905030304061401 78
    0x1c042881d03400306103480c00c1031044a014032000d880d04096074410b80e110207401035114044a85422402e400c65001e4400004400d00507494034a0100d06802c0281e903407445420fa285c148501d58035856003c8800c006070b080383c1490789006205d860700080c0300f8011580024006114584c456481d0304141c03040720300d6150b501060050740d195410001c7e40110680f81126a80d01c00050002a0001e14400d90b00c50f071801541d0061000040080468040e80507000b61054001142e1040e500d9980488444c0b05000000d00498440800507010604006007250300b00100d144c0810074164514050b8a007000b00003860b07442c0c0d03500c2020448141001001505902400d180c03200741c40c00c07070360080b03141c003003028001901708440301c00040d5141100c65207000060002c02c0803038480542d0b0364522001e0810a0043e212031690000f0b5094543c10940296030281d80c001c48070300c80302c038907100e110150880d170400440c005548585121001c282c2c1071019600c10346c000c0b0300c042800f114890080d0480e1a0507000642 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 84261413 1250 84260163 84260171
    0xe070203250b011401020106121406010812040b0a0c050607091701060b03040f020f060304030c03021207081603021204030c030203010e12180f09090c03060c160807021309080301030b0604 82
    0xc04900380102c0039044030a10605400c4440301400100d02508540d08145090558507000c00b080140b0f51152000e24502003050342c0c0c00740d0b00c0300c100300e17140e81301e0494011a04105000c06d1000c80c50000c01440029098180b00a5444140c0d48050800300120380440108100000802c80340d0781200403240301155420081088074107040409003140000b0300094210366240d2a0340045450710100f10815500c001e107840e07144e141600e0300400d00c058070f001c00c50060048100c800c0b08091075a00f910300b22a84962001d040817805803081c0c4054844d081d09400f1032003807075582082888131500400245025030740c03607071a150850040c9429103034508001a003e42c84400c1030185071006005a40d0020301100c040071740d624420f03001500c0071005454161380912510280800d0000c00100d0440c000300079001d8030381e1341e07546001908a500800005c00c041c3c0030302c001c0da000000d0414000303080040c8010700144501c41000904802c0b942030f60f00403550444000700500510248400d01c0c0e0b80804210f80c180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 84262663 1250 84261413 84261487
    0x304050c011407150f020c1f050c042337030206041a0706020307030c030c080103080a0315080d08040203071a07030e03010f0e16050301050405030901050708040e070203 74
    0x41403a214a1101801081c1c0441c1804e00204003a000b510070034011a03000c1d074980044940654860144500f0000fa41103584610f1000141034012907210b5000130b0f100d1810280781103c00003802310385540d40100040d480004040d995240500e0307000d401d80703000c45030344180c4461911800c090b4025134400001c1c06e10440401c016a40c0404903030589240c001400c002c00c411210038132031406007030b01c02000703d400401086512a0715521415803a0041c1c4c4c0d050100099090702950211400e00014140038410420811454080e0b040940300e81780060b109020296100b4030b00c1c3c2000d4400d1801c200040102042c0000d510f0308102107400f418405030450340c6d1118144070442c441c4295031000303041c08054000c8044070380c1c0c2035016581401010340184000d11132000041e444001d000700e81010386441c42d00100c4c041c1014403c2d503200307a0b40640210720700080a401900c1c50f8000040407594104204004180c1140701e10390ce03400b448654005507103d040c420b450301c0c9008541c0d005000c0f0400901203203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 84263913 1250 84262663 84262697
    0xd141008160b1c06090504060b060901080f070207030f1505060a060504050d150e06010801050705120f150612060103050c27062502030d0c020108010b0a0203040e09030304050c01 78
    0x1c0303021200500482a514403003424010340c5000707030114510419207400800903451585810592003180315070820008000c0e88001c0050790b0203980011342c001030f40d4000240d01d040c41c0d04106908040d050044605c001e60b00d1703072070041c100c414000c1210f0400c41d82c00e0b055028071440c000c040d045842100e882d44800d003440c000900d80e0203684203142c0301700300064004090103012100e168140d48400000d011100403003c45ca591010207102750f8002c0d6181c0000221079a21a800b500c400d503488080c00d041a44626440d104040409444c0022000c00680c00782441d50361000103040c0c00c0f4640c41c0000a0f40792020014007200c100600303881102004001c18503044054203a8441c7c00f403400880d182c2110860808605d0500454129031060800c41007007400e00c05544540c01d500500c2101110300f1043d000000300c03119181e6a000070b001c201c0000c018000d6041d1400a05104080b82c4100c0e800d06d541d818155038040f44c00e55a1100c2504004180010f101047c06030301d0b0406800e08005c0d44081c161542 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 84265163 1250 84263913 84263953
    0x71506062709020307261003020906040b0d050d0206010e010e04150b1306050307050f060a0f0c05100b10141801020703050106030b0f1501050d02070302030d141008 72
    0x88091a09008800c0c0030107030101d48001002e0401a4000c5440c4e141149020b04413410102210000d1414801004d800c41084d40c0c1d0548206c0301e142c0b42042c043e01d564240080c080c00070b0106039120b83c981d01c580c0c07065204c449045402034003c42c010061400c81100290a10f001078200c856030380d003c00300521100001030a0203800951042e403070041240800407650050026801f030341e40c01003d4401c00170f8640200d0300a1000c0c2c0b14104d0541c0c0805a490b41000800031040700030a820400a000700704600b8010151403c80c01c4003030402000d00f4555070f403024100b8004191014a0b40c0e500ca80c0101581041100701e4032060003401c00c1903084041081d4185580100c01c0c1920040f0300b05080101e10364400e0007107500840c0d2200080c445a5100d2030100d06000c011540007080b03920041c00980c500e8007045010041071810b0b15128641800a03076200003a610490080d019840100042c6a00c00300da07100e481002648001c4000d000c1c01c102800e91590300c0554030442c96a40884010724030444034443c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 84266413 1250 84265163 84265187
    0x52113020d020f0904051f090f02010305040305160503040f08060f01170a0f110f01051201050f01031d010b100f082a0a050c07091a01211107150606 65
    0x1201404840700303100003015400c1103030601da04600c0910a20040140001e0000300301d110b80201903080c1114045400200e8015003006402020001e1040c1c000d940650320641d0824000c5c5001c0c0d140403110394018039020203030542281c180c0c0c00042c040000d15400c00c1003e000c0c0480101500141c02c000081006114040c01060480000c40540c2e402c0d13040c0400980140583c420301040c01c225071414006904040c44401c10b0003500c05c454141041c0d0b109030226405074400e200b094495034201014032007592102c102c40707814503a07200c24011460501c1b0039804040e141940c00440c60000072000c0c042141d8681d000001172001c243c0b001030314190070000140d0b11041c1040054034000310110841c05a005c80da0061220080020344054260781c4032000b40f00c0c10703204004481d080c0d81d517190784100b00c3d331f0a4441007604d08148118508190321414040b845002803894030100018516640d03000c48060841212280e0400544041000300300308a4907040c581f0340008205880c0b50400180840035284 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 84267663 1250 84266413 84266419
    0x409080d0c0207120501050402030105011223031605010c0e040b0d0314073002060705040b1c1e0b12030906070c030f08030624040b0a0201060b0a05211302 68
    0x81d01c10721252003045401c0c001c151078200c515050140d03041040c02420240c905900950818001080032010140f42522042d4042040ca000600511b0a00f8414541c080750281d80c1c002040801000904413a540c94680e002e07000000e044003915070007034030645594040d503000e241448102e000c5959a030340380e4446150117041035051032000c0030035040140300d41c00d030003841035500022204203010142c2080841c14549090010195005007041e651070b1800ca0b12040010001c010502140c120640503080d810484003c40303c0744110040203a00740d81e060201d1145a4072040d0080300100a10b02130385100b04400d541c880d914000300024951a0322540e524180104000502c4a04000003015810300560308801444030031a840d2804004070b038400e07103495200d2240031303c0198907541c100040c0c42000d100268040d2905140800740c255031303003003010004159541c0e20380c002a0701000700c0062010038200d40d506661000c00ca0680c0345c6242080380502d05104d070400c200816a03040c4030307505084075011 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 84268913 1250 84267663 84267671
    0x312020c0307020a030c0f061106130206090a0e07031a030322090f02090108150a03020f040603060513030311041a030408040b0a03141305071a0f0301060c03030b0409080d 75
    0x800c038580c5140700e401002500712501c00800400e2201c00318500d0181c410156032035224543d100c40c01c545441075141c1c00c2846800903008110103c00040b0880a06480602050704290184000801e21521644103039100b07500c0204000460b5414032500003084450180c1c2d04510a0440200e59603010b90072a0305500101c104940400b0040d25401c80f00800201e5810300c141d240f0140000702030f420070500d0f1408a14403101068016181da840a03c100c4400307400003046914540030003c1601e035903040c164125580c3d040200108400b03014072485081c0c404254005a0744500d4014125604209a102d031b40340180024029051180c02040c0300301146540141c8030f071910f0400b00d01502c520350005191030380001f0303802c034442e8241d04070458400e41d100c0391030802c0e900c905030f01442c12000000100030b500310240c01d01c1070154400038084d950070303240f00c09820810180c0765480c5a500070b820031008652080264070425070315001d0211041c105641c1403024087d10341e03a6154a01a119460840e0b5841d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 84270163 1250 84268913 84268927
    0x150504170f0708010c080f0c191107060e0a060512010b0c0709050a0c1e0507020105180a06112a0f040b040507050c120c0c091308030106090918031202 66
    0xc1000800408080708090324030455441654038001c001c00180300c000b0901d40000212030801c520081440b449100703018600d407060424145402c480410214030601902d40f040e00211401006041d002c0c0001b900d81c081d21030160001c004510750b455000b0700400c50304100e036424003407420310881c1c11600300c112055150150540080e0410341250000c0404a181404100100340990440c030800b120302d0301c51090b03142110314540076000c603020305840400c0c2c0400c46d84c0019440f460040800280f06049464080400b800064045101d6806000000c0c84c101c200145e400d024402050020f0f130905181100341c000f02110780c40040806035440c483e03526039014242d80d803546d411000030244024020003c510380301901070f201d038002003001e00441c031903403484ca0310f0482448221074044030220300400002c0303d44010402c000c9801003a0203441a903050030040003070343d80e002447c007070301e21900c50f0400c250500c0c0f02c1c4400c50316060034400805404680034004290802342c1e030803540048803400f60340c401d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 84271413 1250 84270163 84270209
    0x50c2d040506120604050601140412060605030303010801020403120e031203090102121602010b0d320109060203040204050906040f0209151302220b0301050405060a120507050a150504 80
    0xea41d214a402c4000041c1190b40101101e22081c40344400321402c000c203488a10044030f0011031003803071032400700003000b06003d150703149401d0b0380300d4910900c000701d002501d40001c41e0440c1c00a0b03004d4002603402040600410280001201c1c219042d0b1810032150840600004d82c4c2d0391140421034420710000010410701381c02034040f81c2500e10500140d15060500a80112005011664034401546405410900782c07414a0303034030100c103812540119402480c60340c42c02d8003003030040c040800041c860000108164080c051010b9113800740c140140c03a403a00d40180000e84200030142880340d00720070100400034070250b003804072158051301ca000b042da9503000701c448160b03040046694030845405075044140a207400030501c04900387c2100c6050410302e03040f004065024040c141210b40184018061810b03d9407200f5132054005252042c000d550b01118061401d42c1701d0152604d400107801440241444c0c50100c0c02001d590141c2c0c5103625813040b004145008600416059620a4000d0003842c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 84272663 1250 84271413 84271417
    0xc010f150623030c0d050403020601080d02030423040617010203040b06120303070f05041a0316090b1615022709160804141207060c02010b0a09020a021f0906050c2d 72
    0x2d0305c2c200c002c105508090801030743d01c0b10b0034414028a44900e80314424118408001e40782101c0119100d800d110301c40c1103400c100307105002042c030303000780d69150000303038411050b42c4034a0704607a0207000507900d0420741010014044d00600c01401030090001c5505410720004c102c9522040a1411901e40814810220b030140300c4d50303100c114580c400810088011207030f0001180604086509501251031500381610022030a11522400d21030902c1a6100ea90b0a0b030b5100b04883d00c01e080300700b20010b2070641e510490708070024500e03215072560709500740d15041402e004071030542260810303002c0c034009045450804001d1414000c200c2d0400120b400c0040d40740d2103040c0e00c0e0519065030042c03082c024101007030b0713040300b50140c42e802d0828544a040381d00620a0700705045024000d9031501e420142000c000c0c4d4080d9092000b10b128010040c10041204034004001ca4070800002c10728900d1814601b056813400341c40314444120402403091142c0500741411606100004c3c1a5a41085039000300068 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 84273913 1250 84272663 84272677
    0x306190b0408010b010210060503150a020c070b03070f020609060601050918040b091e0706080415110405100306050604051002120d050601030c05090919020c010f150623030c 76
    0x220380081008a000710040d041600d42d6042a400c5541d1413800c80ca044003511454410a505a0042d0506030386980510344100d1b0f0114090070058034000210621030320b03200c02039114201220010062000303469000301522003c035060300c0184840d0420b0101c4035140c00c000b40a0505200000443c1c180a0b01c880402007aa40084040e500701841c1c58141250560b904888122546c0201c40c80000d02c0ca0807001d00050740c0d0721032001800d54074240705c0e041d1200701c000340059400c0c241d008107080e034011060150405c0c0c03c1040c03803141d8480e450700040c0000030100c0d445501c00d15080c20028080758607100c040d10304868003210b0240c1c18008ac210203030308221501c9914080c5440c0099903250000e03064103c280910020f0383c0820404070741d024100d038180682e1000ea41e20074204d0011965407040c08a0801c4100c02c03000c001441c10501c0402242182c0000b041c240780b02e51129041c801e11a000c5110400400c0ca9080144e26401c2105140725050049080403842140100c0842d5425071100c050b1126 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 84275163 1250 84273913 84273929
    0x30303040f020103050f160e060706090c080f010e03160c05031b03060112120c02031204090608100204061403130807060905070603020a09090b1305040c0e070c08030619 74
    0xa20306050408802440c56810180d0219081c80c4c085445440c3c140d840da071003000030030481489000c0c00785003124001062050030783d001409003d20804036140b03100d1104024441c84030700d0f0318546081d0a04d410400d28010b018416403400c0700340654403402004413108455580c01c410300300b03841450000c1c000c04160304980d03014454400c2d0701140f5083d501c5400c0d98808102d0482e4103030703039036900d07051150036001d9401800c0300403d21110002c20302400318006d0f52840242525903129a8111a6542d0340266000010194440e1000c1100e0003090003581c482e0542188254680350502d1070191006000340b0b0502c051140020000e4500740c0e00c80402d0300c0b1a81e01075006075840c02a41040c0002c0d1041104c00e40d81c0303000300000092124080c1c0300f256010030b10340d102c1240f1549000001030090840d07180c0e00390042d40e81008203107038004510501d4800d901c0b88850f60020b5003408a011030300c582c01044501032100d614805408503a0034402e4a41c0100221424a1500250301400032002e23001d81c00a00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 84276413 1250 84275163 84275167
    0x603011d040c1e0609090c0e0103020705010e0f0d090807080a02060d02090604090219020106060801090905070504020f0403120c020a0e060609030d081906180c0513090903110609100c0e0303 83
    0x4092080c3c959030303c12039200307036038840c44943c81d85800001c4031642c094001c04503039181007449403540680c0103009900d001e507000052003800c841c4018100443c4104000550b00300c074244215080d003103140c52001d41083d0009045450a20018580d5a03e080c180a4410740003c242502c0c8101c00d901110703500c0343d002e8603640d200ca9940b5044006500203030303607543e640d1800c059a621020300c144150011580c50b6981c4151503481c02140c4001810139400c20fa409004004010880352190300080c07408800c00e01d00e00b90750f20301d1410402d00c4017016140e07003410004030003043e90260343d5198034441540c0c0c03406802007094840500050381c1c1e00c1507102850b05030294034090301042e50000002e500c612440d031800c16100c00304c0003801c01110042d0103140c4031161a910600001c900c564441200c0200c1420002e1407c800d01c2107101003290b55601200050f600c03070601100301644600060080c1004600a190780d040403440c5a403079002420000300780e1607441c01011121361180b00d110b04e405c40081e060725 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 84277663 1250 84276413 84276449
    0x30c0f0303041419060209040902090c0705010c110a021309050d0215100f1802210a18080702040c02031b100c110312040204060308040602010b030c0603011d040c 71
    0x2a2a40c008030303400d0b921160060158201e005000c039482c9140c003c0740f1913019064140d9581e00c070003074100c1c10821f030300983d84d0200ca81c0144c441800040c02030030303e4403030140c075655103240050035901e0031001c19040000350a000c0426400c001028102c84d0360484012008002d0755034040001d00010381c0c090481d210f00c0c003c45000a0b008607003141d04903004c003413400175651401c07803103000c03842c0324800d00b41d00030010101000401c140031400e03198401c2c1420094a0440d0034080c00319040e1103001c0109040284505120a86282d031156000480c481317146813407000f145403164107140c0954280a4081da444a020318142c42c030900865428907544800400004000c402450b50f0b590203215507000300d031925401080b90b034050540300c0d56080c880b40045150075120101440d501d000640f040f60030640390900400000c41001c050805845160b000049100341081010700d00345e8010b035202e00408041005006c409442c143c410502d500707900000242d500c7d00c1c60030b408035840b1580b218440c0f584442060b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 84278913 1250 84277663 84277693
    0x40c022404051f0b030705040c0203040605031e010303020f06150f040213050411070c0e0c040b0f0f07030c020f090103020a05120a08030114120105071b2102060106030e1f0e030c 78
    0x3507138800c8158219100b403a2600244400c8802c041138a001603401400200801c91080e4019644214000042050f0302c801c52024a0a0715081c0c004401581012840b0039a4100810046034041c40c200c0c11100050042400710b4101910144850300660300007480e00d0380e40c2d50101003440103040141c010080180c41001c410b01c1038124120803100031108100000700350100aa00e140650980b4030034501e82468900b03100210b5101c9120081e440400b806030700b00841550300031300480e038020346621448156600c1001941e80c2c026074107912078004000140090389400258806030782003913400280c001104207007940f500301a8040200200070000c00401c0e0804c88451451419034282d03008417440c05c1c2c44991600b6140700310707030740d5000a60321601203d4200031900b803035010034010521080c40a1350300d2446040808040030b88405a800036004020181c0d041c440d0280000301c120150001402040e0b01e10301c0c3d10103d1782c0e001040c42c0c49400490301d9040500803948207140400c1203c4003900100d2903 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 84280163 1250 84278913 84278921
    0xc03180314070608240d08070506010f0509041502030c07060603120801051005070b0402010e0622050f01020309040b0609180a050c0702011b0804080d0905040c022404051f 75
    0x60308068019100d0004080e40100341c2c0b14094440c16a811800710031016440c49001e865240b06640712402501e0300001c47d0b1304200078080c440c003690243c800c540c1005c0481c2d1204159520060040c0c591004003c04210311041034840496030f4003001d079580e21010601d415030300030010050b04072441c01cac0d0000100000b0081e15005201c03ea2500c403802c0ea41c950400c541040f41c00721050110700c04020034030000b1004540d984c1c0c828030505040c41591003850125466030081c0c40c0c1c103543e82900c0c110880400f00d5500750700c1c009080850348412030340203c10000703449005484686000310380f514210000d55481d02c2c00c3e02c059640c090701c464a9006c40004e22801036600369440c000071882c10003c210145400d8049640c0740f60103840702a56950206040c6079115066002a90070030000d000c082904942840f43c40380d14001950351070134240c02c00003008125003900d940e0038103541c0940b0020340480e50813946041600700810301101c803540c2e103040c010b0070040404a5140b034013200c1e070700ca445849010b40c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 84281413 1250 84280163 84280193
    0x9070203040519090f0c1407020d0b15030c0f0d06050a09060c090e07090f060e010c140a0c0807060f050c03070609200f06030606090d0203010e0d12020405100c031803 73
    0x1c2c02d01c032005c540840801105c2c54101c5541c0000e1084441039071840842c0010030649101500d5801c580040340c898951946c4140e0319041a401d100043c807805147c10016a40c0c140e0089540050250366440015001c114050000f4001340e11030300041ea00f612180e101180817a00000b050040d1010b944d802802c2000c01e000c3d200da101c4044c40491103003031149681c0c100b075070007911410340b60ba424030360151804c06490f41154100410310020400048010300e06c2c02e01d09000c4001421101c1080c9000d00025005400184050f8070511041000541c00744100b042d10490b4100750703582c2c042c520481c1c0d08500c1020000b0780400c0c01d206020b01080003038400041c6400c81942202d0b44442400d0402415081d465849540460180045016458404000c101c040d40050220106102c0ca40c042400e4540350300141d503040e00101860303200345810480134a28504007110843ca800e040000103250380d445000d44a04000b2202c880c0c01c10940200307140c04813a070a00030095001940c0f40303061402070320455 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 84282663 1250 84281413 84281429
    0x423090f100c0c0f060e0f0715080405011e06180e07030b040516060f0305070507030c0201030f090f0c05100203070c0605031b1b0d0c0f08030402040b100521070503040209070203040519 81
    0x40351018843d42d003ca420380541304027540ea100b00c1801c1060407112024003030002d6516560700d0340e00420392801800b1100c0000700040d0042030840c134008bd40e0340c0004228406c5e00f092424240c0140d00410081780d10001d69a04caa003c50f9140c03281c0c01c182d440d10711603480c80722941c0c2c0315820100740c282e00030300116940500b50f80d092100e9030719508200c0700e6000d665002004117950255201c01580207402442a00300c00002c00203038a07040e62207a4081442c40c50040d182003402c01010300803814840803a441c6500e0314001540350024a590740b0f0600061403180008016001c80460f0340d040c221007030720400803207510000340c80750344051090104d501040c43c44c41c440d20030b481540c42c10501620f100c3c82030f207030041503d8000400ca51104040c59100920803039200d41d8424504001d0f54414054a8042e0f1640e540e036500c41c2c000c940d0b0403020742e1400d0402c40c80091703c0e20420111a60080449900c2641a0b076000000c3e00c41003021f0345580250b400c0591b10001206e0401d11526901c01c2c0c440481c0d60703513 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 84283913 1250 84282663 84282673
    0x30108120909070e0310020d02090405010e040506151302070506100e0115050c0c0612041104050f04110d02032e1107030507030207050423090f100c0c0f060e 69
    0x2000c0501500d10400c0840c0b40c00c1021480000c0c650b9005282c2441d0141003d01035441e0020b00589180813a8400d18801c400103038042040501c0741070912802d4051301180b0a114110b04154888680e038070b10041c5074080c3c8401c10702e580d400b65100c111085a100795050302c00d548800042c40c084ae03d5181c1182d034090010841140003d0f50811483d03c1d41c100c03070030851802c10001800d5070440d4254000c40014a161007114445100c0d505c0c0c00004049a501a05440a003030400b032601c8c095121941a18521850070802031100320012105490b801030352120110f180c000e08600030498a0032807040c082d5050050352407260a000e24060303c045001641c0d0030350300400b00011910411a04402d200c0c0c55507003030038000c1400190107003004045150007801190102c0d65500009070942d41c0d014840881d011800c0002c0941c102c00080c4142c00820020203408240d00808584e607888c00302c19000d156032601e4807614080c1c14080c043c0201015080f003201c084c0c004460038814080c0c4501c900c9150a8450 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 84285163 1250 84283913 84283933
    0xb0f03010b061803070b0a030b10031104210203070e071106040507170a08040f0f05010201140a020d090803041a010e01030305030f04150903090302030607030204140904030201020c0d0302030108 85
    0x1841408403200700104000c0c00c148000b08404020031142440710b030544203203000403030780801a43c054220001256000306005100d0000d21002c10b004140440606050001c290400c0d1054070507030302500d40c0103890900c03100310700d9003c2001c3e0521450194050003911f20120754100424152842200d554071882c80c0c1d41f4003035605070750300c0904890140072908044e106000708107100c40f001c050032041d5421501c0b0310500d92101c84165010b5070182c44c8200307000d0005c20207500041540c10003002e0034002003051214045002140f42e40c01080d407154641d001482000b05940c56000810b00c0750807221941c0c40e49018a488030410f01101e2400007c1455000001003c0c41250340042c180d0b0340c180d48050031625201d940c0403c0300070242040b629000406120420100300348564000c10340240d490b403004500d14014941454406040082014010081880600708100d180840400180ca6141c0d490b138560804034024042d814182002c3e001c0e15001d40f0321a41d00d500910f0603152440f017500c1560385 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 84286413 1250 84285163 84285169
    0x20a11070f050303120402041416020709020705150603100906020d05060406080304060309050102120403180b0c0a140309030106060503090712030f03090c15020a0b01050603040507030b1b0403060b0f 87
    0x7a115032a4140c1c020441901644908104141c10074406040800e400f410040689c140400407148a08014242603000640640c1007200c1d200612400708210b01d081403a0310f41c0da448a152001c6e4401011a070004207c00d500c08004001c0d0030987c101c2c003081303440260720740840a07603c14441c40d031040d818400400c1381c52a040c031400c03007100c0c428030042d46402c0c5004010f50140c0480c54087e20303295828405010b01c0c200180d0120710403442036444030100750501500050b1540160890f0f102c1c4c9509111a1b59101c0d0002409002107401c04070220300c21405010291a5208011034a41c040d42040c00025000d5000750266004011050640e00754544076496406842c06841018000a03096017403191034500030703403021000c24080d41a080429807609907100f680300b101d100d0907005906c10000c2105104445080902400040712100e29506040c0c48043d03031619103001c043d081c07208410215100441410300c2085900d216010951a59038900340382004002c0e0700f00c00703409040344050b601040e103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 84287663 1250 84286413 84286439
    0x11031803010b19031e0203060f071b021011100e0102070c0801020304020a05040519050705031006021c030c09090e03070201110c011709030c01050c0901030b01050f0d0f020706020a1107 81
    0xe1500200c0c1c0c0d0845255031034a59040460021521855003d401c405d030141e02c0c1444004e100d02200300c90070190f4204440010035400c441d409000500a0030071308400141d5034440700d81c0e502d810034503008801c00f03000700c900c90609010741d440d00051482d024086001500c1900640300c158011103c1841c1269603003103c0b403c4c0d1000b03d8000790706c070b10781d98000e101c1858164011900020f03441c50304480c1c2441c060403002282c0065580c040810700c0031042248026001c1d2100001d4155480600703060102075840802c01041041c07134070281512007944003400ca1140c8425001000c00c2f000601c00d40031034841454490b445403009900003080002030710384030913001a1a403540a41a07407007596446440030703582620f10b400b070107081c000d0004020700a8030480074001d01c0e005000c8160722035600d0003030310005800c9030480f9000d1410301c4024041c44c0341460100b41621818004c0c1a03021901e1039265220303d00034414018000d00070303031011840c0c46600d030341701c02d00c031549071421003c0300c000a8860040200003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 84288913 1250 84287663 84287689
    0x14010f08090705130e0102030f0f01080307030903020411090d0b010317040806131509030302030114090f040f021c0f03020d05090618030a0609050607170f0601030c11031803010b 78
    0x16070100400300428201400100482d6507002c2000405000c0c81c400542a81e000b0345560f003404206030248241c0e540d4ac264410300515180c401149044165500a0094025807002910583e903807031061003144a03103021502410002080149000302c10f242c25071040703800380001e842080c82014680544461a411202600e44880c002c0c54583d070b07141100750b1107440c0c80d5000c44a54604055490b00b0724418080e2a4449100e5100940c896040410242c160302110403010310404c03205051000c042c0c00300555940260b009842c81c010300d9464004a59029001c01e0050030010a0807000d5003400515800c10700803a1090307003a1184940945012109809400c100030ba00200c10412022100003064240d8030840d030250a80f101c9140c0b0752600300c101c0724030581c2075501c2c0e00100304111070340703501880b6440301c41d1013175072089070508000018034071042d0b000700910b040c1a6100300000605000d100c0184495401320200c91f542d506400603208032041d40c0c580c290181d800c01e07035031703a0083c50014482450 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 84290163 1250 84288913 84288931
    0x2010806120a0512042405031902040302031903020606010e0f040207170f04051807080f0403050910110c030604050a0b070903080d0203040c24140903060114010f08 72
    0x544910003000032807140306000c06501c0c800c9142800c00a4800d000c200c0000442504050703c81d464405000b2110302000c0d40740d03000018441303040703038615002020789400c622402c20f41140a08a551400001e00c6540c10185d454414000094160014504070014541c071030f509071280c948a100064510359407058005a00c0702d501d10852855051550190088900804204805880d41c1c1000c207080d034454801018407000005003844941800c1d5110222450303444000304003032602c500c00418640e8050b1919031033b800a0740101d410b262041d8240c0c1e0051500400d00c2030a0100d0040240c10b400e402070120f4038602070a03041c0d000d2440c0c0450000d00c941d400601401642c1c1c402d50b01d940c07541d00000e107810300384000784a0110101d20700380041c00c01042d442c3d00059030f03402d00e8200400401c0b207640c80800c40401208400e010b0019404014800e42c4003406c00c20a04450340c41c0883c19400780e000151341512803400009640954051503907030001007070325070003145c01810404507031420301102d403c64 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 84291413 1250 84290163 84290177
    0xf090e0c0f0f0901030c09060b030708010902070201110102130e07050a080613090503030405031804020421060621020a0e07091523120903190318050304120312090201 73
    0x240d2418100420054140000e11950001015a0025004202c00e0f00306452410300c150080c801c4010603c40c42010b08600407115013076180500d00244800c1c414021414003580108185045901620b20f40c1c655100640c02951500c4400c0c101104051091141c0c02c404092800030980d594050340c22a10003c0381070341c44d800641e44000502180b4030b50b500104103e01d41c0e40c00341c40041141400038500132441003002e16654a015844025413032528005184110710400c01003040880307101081301c02c52061645d1540c000c015040110040ca401d900041c3c0c030b09008020241d03d40190040c40c90340d18400c9415030711203030301c50440d003800c8001112030b800400c503240c605010542d0340290365000030700d2505e080301c1149080500350000741c2c50325403100500f4030007048071b002c4000d03101400d0388d01c1040301004604248141188101c0ca0451500c618241641c9200c000e000403c0d103e021101190001e0490fa074a0366950503290b141e000303c20059002a11038a14200c0728107860082400d203c0d01699506 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 84292663 1250 84291413 84291433
    0x60f070602090f03150406060e060f01030f2405010207120c18200706180b01170c0d080a080c030412140d09060506030c060c0709051e0406060f090e 65
    0x4001e42c40a00c0d030759840f0354054010450b95800300501ca015000d40300d05d00b001c0781814a02507040c1d4403550041d40d03004510508000f80c0381c895000d001c400703050900e030200f840c0401020710310007020544034500f61450811070340510460070784107540442d40c0c2a400c0ba40700c9544c441d00d0200c404210040204800512a01000f040907505001003c110405100240e10700209150704500983c022400d907004001190309024003841788039800341c030800030641c4640500283e850740c061940501503a43c480c14014200400804100078000d690344d000b820a1110200c1414403400a404c1500210005511000010b4012020344180c030300856100c2c0d0b40c1400390850340c0e030039900d0040c41c000c005e00c801c00610440c03c1c240f0040c003490740380900403035002075242007440605003030040850105008580030051100d8901c00083c8060403100080d60003d0a40c443c409c40030304840a10a02024000203c028402840a00d40c01841255245001e1074011039940000c1c8058070482d4803960b0450300080004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 84293913 1250 84292663 84292673
    0x90605030610031508150f01082d070b03010b070c0611030901300c02010c0518090c040e010303020c21030703030b0619080a0b030109021c020607080a0f020c060f07 72
    0x440310481004e0b106135546515820194a0242c0e41d400c041032801d03c038010f10403141d1102d40700a02412051010b00040300391b200310f040401e00500c034145855850042c007621011401d1010b00081c10785600600d40c0c2e541d491160502c19008081d05035401840a03000161032401490140071048e500c2c800f07141070007004001542c82d1103105c210701000f08840c0e0084412013400e4a0700300e048401c1004002134807080b41078003d085038820018003087c0a0100104002c8280f00c800d0040714100856007003136603030b0700c0041062050007035500c07006030341005d0342c004010103030081003685821006a0311114030000203c81c07901b0349803001070013003e10382040040c0808a4072139041803071001030103007066290500d14104143d40c5181d1400d00f20026160720300380002c81c59a40a0f40c1d428000c11402403121050580024030300c800c06060301b4013a400b22900403811511a0003c1da1405600450020b4403071a400d1406810004052001702c01800350b015902600c2c548801650300c81110030100a040c05881d54132 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 84295163 1250 84293913 84293921
    0xb030c090f280914070b0d0905010204080312011509030213020c010608071e0b09090601121b0f110d08060d08070c03030509010909060303080601080411040606020303060109060503061003 82
    0xa441c0700c82e0030b0b4900708214200380c407442101464031480001840300e6076080809001c840c00600310265004110204034040071402501d01b1240c10403000221070b1014500f843c020310a55000c0305460001040281000300d01b400310034100e4181c000784141c141c1c00010200c40c80160750000a51101071070304a124810015409400100c3d0303403000000304691642c0080b031501035194401d1104564408030104600401f4400360700902c0801c90380c90410500e9070004526400090580c2c0c1000340241494001c860140c02219161380068056074609044000c020100050304180101080141c50982012940040c806486a296a5a40e001512400e0400c1507020481d4416206e0b040c081c48807401140140e60000000e40c401d407112903a6104020001d49032403450f51114800a00d40f840420111b5080000700e54082d02c24a01106241e40b203107441041003014681980d002403401e4804034003603030004001c501543d026203031140703e0382d0784003001c803003078882250703100e41010081c9a0b02070614000d0704 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 84296413 1250 84295163 84295171
    0x18050601050d021819091a150702010909111905030402010c2a0902090102070807060e0121021801031b140c07031506090b0d02010e011d061803010b030c090f 69
    0x21142403200301d9400001c400d45c0144000c001ca4012441c020000640c00d0b110f4031044c0d002c41405005d200c1c202d200012583c801c240052106a08001641c03401c5a1041d80c1c0e4401070540c03c2d1081020800c003d0040c034198000c00d0032280000b00c103c00e8451014001c2050300c0c45a541650b941d45803c029640701d07001911002102c002e00c5411029035030780c11041c590143c0140c040e02000680b50380d2001c000915107120782c0d0060206402c401c0b020301c9050b07800107505014000030b0070449074031104000c070b158030904542c4d03040401ea0b202107080251303814900442c03510110700340c1e02888481c820800300309030482c00c038007214086403016a44410881c1000090005281c00c0000e0714a80ba40e039441d0020218408200030500a60380c00c0c040c44444814443c0d00c0c2d48090036140912140c61950001c0e00d0384c41403082150500c0b0b41c5041014042c000c00820010040c406010b0741d40317070000c0b01c08125032070010200c4075102c0c3d420f240c6980e0903404c000078940070703035100101420303542c0c0c079060144450b0f0300d0054 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 84297663 1250 84296413 84296437
    0xb0d09060f140f0f04031205060a031a04020f040e030403020d0f080c1e030310050f030c030d0e0f12030a080a02130f08010c0906120b01020106030b010e0118050601050d02 75
    0xc8480701c1050260311800c0307400040340548482d249050700c80c10522a100814100300c6600e0b90b410f110200380d21a003110412007404000207410784803403000504501d410351004001c101000e084000d01070b03d00c21000d02481c429a000d5040e02030807001c2005a60200007038507504d074014842040540b070412000c160489c01150701850180481d2030351400c96201c08100c00031540030401a5203603446d184100b0030114000005107046080031b196003100c0f00958480c2510841072400340319115602071019180e01440101129202081c07040090f121184020703c541c031503d140c818100440c00e2862441684003442c50142d450407400d0304c8241c0e141400940084241942441204841c5407108d204c100a00106100040d50514284a0b14203480100440c2010400f400a04014054010407403103a00c24683e10041500014030004078010443e130741c00a0300c843c503403100000f000082c4074582810b035290883c00b4030740d078401d11382001c040c0c0c0c0d400c0d603025001a1080000001001903540a8600c9121344 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 84298913 1250 84297663 84297671
    0x12021305040207110102060a02131412060a05090d02150a05100b030405060f1806010314010f06090c09080303040827040207120306140d062003040302010c090603060b0d0906 76
    0xd10007260880c2c0210740c00b01e6a1a1812506080940e010020554804e080200c154034024100150b8011881ca0b07125a00c14802000114640c550b41d0341c4007001e0031103c5608490013440e120a410740680000d0b561401d0501400c5005000b241c0301250101c5001c5001a410302c03251038030741481005080c01846007641c00030045000c00c240131134900541c0210b010302c0c0240000d040c08030002c00301000180c4618002148401e0040340d004000c9100c50440750000940e44005280d004500d02404079022080f038164508800441c01e52403a90051007044a542d8405a00d252209205030340c91209881c040c0480005002062901d0150601d107030340d03205c08100d21340074510701c500800c0c02d0740c00c212011070303000c068289040038041d85441464000c090180030124880d8030344000c40e010f03075040000a0701e541d880c0c1c03242002e40700c0308401007020124aa03000959078641410003d000b0b004e03a444980c00241060b00c0004c030544a401868160b070b1014102c03074680b40325080c8140007012601800c40e503940d21 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 84300163 1250 84298913 84298919
    0xa05010c1e14060108010501050108060f040905012c3009040204050a1d0c03010f2d0b0a020609010b0f01031505100c020a0801020a0e210a03050403060f0903120213 72
    0x10300340045074041c0008000f0959541003442c606c3c25a501600068100500c0004102d0207940d1307500d0b103d403001010384000400080d181825405461303840540060251030403642200250180000d81c0340307810303d8083c1e0b0036641d0041e00c902207805040c1c0240501005040202882c0080b142c02000c070b04000410042c40c0036030711008202003151031350103416118828000c4a140c0e40b1240ca0081c0d112144410181c910741c10002081e9001c80381d8041d07400350300206000200340c1103845400c3d581c0e802c030010014601c2070343c070320100030240e00c1882c0702c4c0010f024030400300702040014000e030a00c48030024004402c1e0700c10480118018217100c00d10f0f14524001c0c071000503180d140c3c00040300c80d01e00755544e42d00311140c2c2070041c014990015030100744242e10400c101c20f9100d41c465108032809801711060618103281086403960154a040908030718050780000004140e084001402246d1103800240308030f6100c0e2100c2400c542c1c03001030281c0401e451801c000110645680202000c104005000d5a040d81b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 84301413 1250 84300163 84300173
    0x10509091e04060204091503170706020c06040803090f03161101210c0e01080c0301030f080706050c0a0f02060f06090702030f030c090301060503061003080304020103110c1005060a05010c1e 83
    0x5015038041d0703050f690000d02413101c0c4001380600400c016920081070030180c916511080c282d0004202c1180050000c1062400c10041e501242e01e80d6030300c0402c03100182018100420300e5882512090014400c1c8421416010b4001c01580d002c5040444075420101d003548070b80035510140c0d140b9a04019254808034041c4034409040250403404030000100040340401c0a403c1c0c041d1b41314414140500700c0b0400200110b040f04590640b54800c5004c0f50368507980c9003131041d40c011030f00d00900060505040218096850020f130a0b450010f40e01c0c08000c140c051003d1341c4070101524144400690100000c20b03a050041d40182c21844500c11240740c8980076000e440180c02c25204050082c10002d02180c031490240100009041e044025103118104461441d00100e00e44c40010070164000c0009000d42e0f000340d02401c8075480e0030303401664940c1783c0980d050300c840030548030426540c40c0201240c080e041c07410902050300d0040e180c81d41401c101d51a403103001004800a00018080c001c6001d0003d2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 84302663 1250 84301413 84301471
    0x51308040b030c0913050f0601170a0b030109080307030b0f0a03030e04050907260d020c030607030b010203130e100e01060c02040504060605030a050f25030f0510020c0a1a0601050909 80
    0x110845c10004860501c0752030881c094602421640c1000040c03848885510680781901e5002104404001455492440803c2c09004030000c0580801c2000c010001541c1d0950000744100720103c2d04400080d418404004040c507042c08054001804003402d07032440e0915034403154008550404544e88030303039102c403c800021401c0342031090740652070703045000071041000301d0036080b0140d0000d4001c2d076000780f0110355604c1008003940f041640728003076030240364002d1040341e030084084010040102e071140754a01c4d40840c180e6188005c00c103581c03000514441a11080ca060b520982d80b40ad195941c15000c0002808029100307882041e5581d0000a075642c007007001e004154428405059854104640642043d881c05002c0c034903010342c081c80001401040725145d06a0f6803120741d450301001d10b07082081c42e1515001c804002103100140076106c2030400104402c42500c03c2d48040350354110301ca442d41c105032096404c940032039805e2082e200c103480d00d0301c20b240c2d1114070111304c5120140038160a01401c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 84303913 1250 84302663 84302689
    0x6040f0605031c120b180c0f030703060314010b010207090207080906030109090c09090201050d230108030408121204060c0507080d020301050405090c010f0f0e040e010c03051308040b030c09 83
    0x500d283c0e240d004401c0e904410b010031501c2100d04200950109a8040780c110310000b0320204060111a0015991801d681305440303a0501601314541c4a2501450180051807a400140d404107003550000030041d41c140105000c3c0901030f40504a540e10b00607814000c0e402404044a040409110545041d181c207030145009100d060f41c0482c1d8440f01c0d00b000e294100351500070600240c10200c5110160b600031080f5518140f02074800030308540c0003000314007500ea03540d9400540114440000030380810000140c000d440c02003096480c6184009414021803180c08140c464182c0c810b400200803138025031000e88a110281170042c5031038015074558869610007824140f14990100c0180042d00301071041e15030195201c001010305107043ca0018146944c0c02d000d00d81044003e000003102c0300e01c690441030440c03c01400038494210350140f0140a4204203089100003490080001c0d2803071300f1030303603003c0c00300f42c021411501d020f04198005c021984010100300d0003c1c3d0800c001081c1d52268440d107542 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 84305163 1250 84303913 84303943
    0x1213090e010207060e0f031e19080105130b010206011a04080a031101060e0105030a060c020705060d1d0613030c02030c15030420060904051009020f040e0604090b06040f060503 77
    0x1548000d884e01e030040740c200c03041810043e4050030381c524088200008907000001034848016051140c3c194800c110301c507140d9251240300060015103070f41508440301e40d0690f241110440071090103060030f101210110001d040c01a4010301c010400348020078200f0038020000e400d094500340c1c42e00040c03440c00c803800301d048001600103510100500405e2040501904218a0000c0c265140200190707071458007030b41c0541196500c1c142c0c0c01c5428020441ca100a14018141d06c1d00c0d4001d42129600400d165450404c4900b92541540107990380890302e58401c2c202080326003a41c5074280c07003c460070200810100d805124461070b02401da41d5200c603410b4000d074a054407a9407850036181040240200d41d01303942040e01c4210b4801100d0b55444141c8466a9089e100081e407907907003280b0b0305542d0000da489502c01510010310304805041c100020410307039114900328565034881c40184000c03a0074214001d01607509000100749a454290000020040040c0011442c1c5440702c0003e402c0020188010325 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 84306413 1250 84305163 84305167
    0x71a0405070b07120315080d023403030c0501271104110409020d021b0601030201080702150403050a0c1b0f0501110604020d020d060507020105061305091213090e0102 73
    0x2081210401c03000000e020500344041c1040856078424100240b822001002d1540300c010040707045240d6031003800103110340011250703241e1403030380040d4441d01e501c01003203450200008582c107140100d400c21075503000700d9444ca0317400c00e15645049484100008045555541358940030030f002c01c04020b00c00518054000340070444c00e4078034100103448440d0f11450b008904212820750507481c58010760b0110760b441c45016940c3d80d0305440c00c42c024440c400d0001c03a071280c0d515001800d500005101d40c10303070b407007070301c400c40241c60304582aa544c0161940720f85503552580006000640f00e840542001140c90802c0b08011138242e45035403c24003407010000983d1000f070340030017000000c4401c1c00c0042c00c0a00302080c1120a840202c0d854210041c0007a000d0900490108115120080400b10040d00130000700018100000c00030301824054600c0c0c0c0c0308410810600c8210b00070340c414103010b070f4160340052044c404034801c1081d640c0c01001c900b0801003881000007c07441071602603035080d04a07443c001a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 84307663 1250 84306413 84306421
    0xa060903050d05090c0a0b090d05011e050c0309030a030b0a0503100509010606030c050403020420040902280512060102030409060e090706020705100503061903030206090609010b0a0e0903071a 84
    0x150807114020440e030a103a01c905d1000110b601c600100f2030640d0001c5009690b20304140c00428000601d280d0000c0a0b50300c3c1031390342d60b9920f038000706035505280d01c05010310543d10b48141c500e0050201f5904917a450b04108000c07900f1034003d50142c0d40410004d4402c1c6070803590b4000190400610802069003540c80d1000c01080013801e12400e400781035181810046900e050900030114002c1d0b01009025503a15182041c0406502040b000048504402c0641d11600c072100d8101941040c0601c529481e50004c41800d40c1324180650004071009682d0340d824641d044094601d4078602800c007a043d2f010410020641c50514000c0788081c000641d20142e4a0510080592402c0c009610040031500001d07424041951458800940c0103140d181464a9445080016038082030610f1000f4148810070000402c254021030851301ca084840c0c01e0703401036941d840c6482d00765512030081d15400203a07004184036042040300419001004034040f01e0410019941382c90a6503504bd03090421242a04100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 84308913 1250 84307663 84307687
    0xc0402071505060f090103031e0f050912010b0307121a1e04060912090609050909070b0307110102130302010e010c0209060103110c070e0103140f12090d020312030703060b0903070603050601020a06090305 89
    0x2034aa270b503031481e140c001040c56035001011400303209442849007488c0314600e410781400b50000907102c0001000e5604650361080b05801071511103808441c2c0c0001d41c00c018070700085424113940309603200d00c03804560b041c03e180e6200d81e001000f401107c94a0766410300e200407404001d180740d07039441e403612010019828042e004c0e0115610b0b0340224030850383c000411411401c0404c0c00c104546a45401d607803641ca40c420306640d0b100e0604001c10003907201090013101e0f0503804d051181203034001c1e200d4203801444000116459081b9100194110411801055095109501c04550b24880b8011581845503001c141800d004250b80602d24028503200140305001040850a40c0d07900032500403e010720048280350340392010318120180c1d107200404e00446c59254070300c10406065008080d1182c1c0b4010110501c05908142c80a40010f858828040f8254a40500721121180c004004260300c0d850000c00701e020f044014900350440c00b69003003640000c0e681e030051111040c0700341c48554446040ca559 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 84310163 1250 84308913 84308957
    0x50705091207120b07140a03090308070f020d050a02031e070201020d0503090604020910180f06050102010c050f030601031b030e0c100c0b06030327030c0402071505060f09010303 78
    0x2103152660441d030b800b08410425a045411950b502c0903120364140e480500584280402c05009112a40b00142039441180d050f44004e0040e4030948031240c25480e9424100d07000c1c12501c049002591206401c8100d680c081c00203486008403a10450b807070041c034920442d80c0f003210001507500300b240c045003620840d07806010203096418145411401d510741741c62140c0e6980c0000e80b01034080d404180100304c1c0c0a001c40c1c600c50107000340b401141d152031110060b0b000203041c015000400360340342c140c0101e8658418096441241d0301c40d640c080c10601160f002d000b42d43c0c00503026606060352041074448040741c4d1081c1c0c0d94051401d4800080c407401ca41d0b10075041c00985400948200c1c1103c0980c45940d400041c08480190441841c1e6650366175000443c9c65849290300302c4140700700c501d13405040c0300508034000000040c19015120303207680200c1030000303034080c0110003481400f10340100030300455140d0200b54040c00c02080c058a5401c4800804c020040a030000e60008001100000845104140f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 84311413 1250 84310163 84310189
    0x403021e0f0d11251e050d050c010306051c0312060f060207060201111201030b041112160801091e06020d0906090b0f0402060a0528050702090106090f06140d05070509 73
    0x124841c1014180c0c0c0441040380c54500417018215240c10031050012070007000c0c0d601030708000e066100404403d0030b0090383d0300102c0440c180024103141010516040460914002c51540c18042000e028184d5059907003041920f42500b000c3d45e20f00002815004183c001801048180c001c0c2c11045d081c060001d0a540411181d00036422080100c0c2c0051142600c0060451350081c964420a48451034140c845c500354805851f48110448610100d242010a080c480102009024604140d40f03008046c02e9405c204030203412400507112000480429920b5500d1040c81001e00500c0d01d00c00c1c08692046440111050b18501d903542ca002080145204110b40c02409070580702c40300f45083d600168991182d400820100000440c0c49682e00020b4880321500c60748409407000e43c035048900c0104a074100800c203900ca00a0013000150304d50141d43c814090326041d58221400d84d082100907503140c01078900c1d001c4044400c010310200a001031080502519003603442581d201a58001c00c414805000c07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 84312663 1250 84311413 84311443
    0xc120306030c0907020a0c090e010e06060d020d050a080703030515120c130f061404110703080c0f040306020a0207050f04060501020c0909012703030606080403021e0f0d11 75
    0x3801019600041c0903035448200322000556507907000d100b01e080c0800813000424902a0341000b00d00c0d40c442c1d0300440d01441400c402007006604201070240d95080c10b86402c3e8125242c04503000c05030910a2124000340d009200300d030f075681030710b94440c40350341c0c0102c4081c2d00103961041800b81120303109500d03c00d0403200b224a14540d0f0001d2100c81c1c0c40e4103020a0b4030744545104c540b04503000b2055003100c00b102610340750400c101a99481e00d52003100b40201c041f84a2898028170791141900305050340c03042d40d0141e03503148003992201e2642000e5486083c0c00035188005000000000b1110700040c0410b0303415502800740c5518110521082c104802c001d588181d0400d0b00500050741d0000349840180000c0f1020301454841c014818010700d80351000900d00b4100d8900d0040846c04200705642681c82a40c0070000c141d912181103480410540e402401038103c00480070f441c400810048006d001444c041c2c40d42d41074003a996a161035202820603000c0ba00686000503180c0080c400c1c0ea0510b0f00700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 84313913 1250 84312663 84312667
    0x4050a0e06100327051005060405010b040b1e1801080601080912070c0504050103030503071407030504060c0c05040c0c020a2301180b03040b011e05030303070302090301150306020c12 80
    0x70001800940d80c0d001e0060425644401c05041c41c3d001c04400b03400032020f02c210090b01121418400e86820810020101c0c00382000e0202d5803c3c102480740c14102e80d008200c0034105804c0200c0d13040658001c03e80c250101491301100752002080b80010000280304071a03142035010200009441d03070030002d24043c1840246030400c1800c441c00b083d0703c0242d00343c5c403030f210755501c0980c50a44803c1c01d15402490300240b40c80008420903400200842c010350058417940c22071010803400c030225104044000b00000d00034401000043c1c01880850211803048008848690300d92001c94222821426108005041c02210109500304402003001501080e40d880b150384403034085012040d50003a01c02810485811000314240c900384001401402090b40c40e2644d03414103003002628494280500409450b025400c214049100101032080305c101034051410f5a56401043d002034000d00c06140c2c043d500e0b00860b141d2a516180d078030700075601c60200140c0780d43d0000010f928042e41b0525020f101c0ca01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 84315163 1250 84313913 84313921
    0x1030b0a050907051009030b0708090709091e080c0f01020307030c03090c05150408010e030d0e0606012c12060411180402041508100b0405090309011e022104050a0e 72
    0x400b080420030744205403105c2c500c13003500035800c0719850460f51010b007601081000740803105510404039402207426204880b04a921580824226021828000c140500d045034541070380e2991002545210f0040745041c0c00d0002c1c40d0805030070300101007402c1010343d6001003048212501403141c40c0a0100034503040003035503460b80d1907141c4940c0b40e004180c804d040317000c694404001440115000303030100c040280079060b02c40320b2640c0e4a402405403030f00480d040c03000060080700005031b00c83c4640300580d140d0541004403844d1003200c1209103a220f206d582581c2c5240c0721529040445c0c141e005003103006002030310340f07030900b080556000d0f0151881100302d00b443d1341d1440c0350b00200e250440d8044800041c1c984a020f00c501075071082d58001e201ca4083c4a5a24035003d8503603205880a8006a0b401d10030380d41c4094955880303210351210140844c0b10382c0041c1c0c05007039040f81c2480d40d0002030b00484106c001c81c0700c640581b20349001ca83d44002a030010703090229040c51010742c002040c01811070341e210f00f0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 84316413 1250 84315163 84315181
    0x16050714060702041d1501030c06050708030a0c020f120912010b2206050a080d02011518020708070f0c0305010b06040506030a0e0a080432060702010c0302121201030b0a05 75
    0x200356040640310b56185c004010510001d084038003001401101142c00d0300c9411030445254200c00d02c019200780307d009000044103805401217407401d03907100c500107241d0740e101000c010042c0702010f451000c5100b900e442e13100301401004020100c901c42c040c1503488141a008221013141c1000f80c0243c682d040820860b0340b0f0700c1e1229810b80e00c0c03e1098034807c50b00400c006080c02411700e60300040d030020103200009141d11001c81d00d282c20290350703070082c401a0100b800b4004c80010511600c20918040e41105600d03079a664007820034503100340d605a03e03040840c0c86111400c001c950003a1000380f0131110030010408244901c0c001d400054551a00b0f040c0b80c040025854000107104d400940c0c1c8400c6c82091a01081c00081100355000e1202a180c0b52122110010900c10700d01d840420711028000d040c1031000c00540c06c0c85c482008206a03e02102a401151107080a040880c15885030030700840c0c03240c3c0400058200d210080b0080d490542c55420185582040a443c0101443c40d160030721418030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 84317663 1250 84316413 84316417
    0x50c040f0e0403050903010501060c05010b0108090c01050913050a1509270203100606050d06050301050c0a050a051612030c0509010909050603030409050a050406050702030415231605071406 83
    0x254018100038556482d8181a2010312681e110944d00d540303028008a4030541002042da46607000c1c400070080042c01c40b00654914400391440d9806038040182201c4540c4640e005000742c3c10050903428154910282c240e007511403e4850024840d20f4400210400d00700c0c8a01c00005c19121a045c80408007880038944049020703200744803d0540400a1015500c040211148116a500781049900d5032058010520303000110903005281c00c00c0d0300081d59150500449000d00c43e10b0350b05602c0c010300024183c6080e03102c009000207000c01849100341c1c02072041d00d01501c26000750705141d00c0e410030500040c109c0d404041413038203222060002414599000c1e10941c25901b025a00003466107420b00068550300031580101105800e142c10080407440981040340140e2042c1e2042c0120307154030f2026030b103034013450040107222070480a070704c00c9061207220251110741c141d111204e4107003c9014205010b5001c11000b060480303240000c0c10422070700b04510001406448480d0302040003c40c0044c2040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 84318913 1250 84317663 84317669
    0xa1202190b0a12140f01060818070504021305121c050315121903031b05031308090a05060309010905150c12040204021308150c0306010503040f030c0203070605090301050c040f 77
    0x4030f8101d50500b40c03642164001c8280e200140865405454003240f000350b0f40400f406514009440303000800d082103280140a038408441074058907401e406c080c01d020007500700480746000d602420000081e5034a41014032076041011102401e03658520b4909000741d604440308442c1004820000c0008607007403200810311200302120000e980d112262181e80c9010f41c04403916840088c240880c40c205034141d401410386910071035001c000303041c001c981581c0c940011140e14100e20088079903040000d100703400400785480b006240000086d02c40003c104240c108483c180100d0f99542a01e03030500000700400e1000307240c00070100a940c0f030a81810521070041001c0c2c00051070451010504640d41c40d010707908242181c002c0d0340504e60361048100c0c4e44500342c0144c08544404140412030100001d001c0380d01c00c480c180c4409107143c40d55610b01c6082c20000f00203404100d00c042400c001a6010312070b22004003825035031603460700b1005080608485000d400039407040e0042204110b0074112400c10012 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 84320163 1250 84318913 84318917
    0xa080c04030c1e030c080708150702060408070f080406030f0f060302150a02101505010801060912200306150a0f051e060408150118050613020d09020a1202190b0a 71
    0x10021070b50f0b0b0385001001500024440c99600002003079111000a40401f154a48000c50b50108242c480040c220b940a40f540d00040e0401ca00003400705a004000b4503840b40700b03092a440090740384e02d030506160003a40208000a455000c1c411081c8600d01500e6106e404000c010030095185500003800c030203020b009000003100204005021500a0200c0d42241c40724410621119415a4640804e0000d901410707001c01d000c5400070585603c900008026a00dc410040700480b1060703d4050701c4010404000544a1a00a030302a05440921400f4056032a0b0320340c461165400c6030800803d00059003008043c0294903134108001e584003140b00509400d03191810982080301c2010603003a1013550400506445940404400b44400100da1412241007405400b1500140345042007035600a42c3d1942d40720560300c00c1070031405003540c010400480c1e0748000140010b013a5001c0303240ca0583d54400c40544019002503400d42c140003282c3d800b40b00070039680c0d01c40302e0304080c540d1406014031070740082 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 84321413 1250 84320163 84320189
    0xb0906010f03020d1401080105071103090f0a05060703110c1002100507030902030303090601140402031302090a0b040f02030901050610080a0b01021608011d030a05040311150309030a080c04030c 85
    0x160700c078002e0703044a035810341040c2d050014203008030011301505028803a1004070340c60030f400950b031544a00d000424002c070803005545408000e008100c1d5940702c50f080e0301c2c0d200c01c4006c40024145d6a0340000c050451298480b81e0f50010409012400c0c02021509217008500040081007899404140b50300c0514800b0301c0080c1d01e48a0641c2100240107420000b50144400420312812002c001a054121a01200009440e640e90b105120070b90100ba2265140c00f04d1035906c0d6401031034100502584154038410003e00382c1d40e048009025592108251800701343d0000900035800020b02416511520030b440c43c02c50056001c0c1d004124484c010070b02c010103603440a00940603031081c000d100400c001d01030581d084540750b4912038020840110300d4650082c40d00c0381000e20241c00710540c2c0042c1d405032246810705181d526060b2540303504142c1d860344000950f09014041d5244009103008401100044d40c0340c000c0c070302026240e100007400c008a4403c040c0410400540d2000f100015900a402d04030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 84322663 1250 84321413 84321437
    0x180b040b0c01090b07020303040b07140d0c0210060f060e0301181401020c0d0f020c010908030d1109060a0503010f06030204050a030201110c030a060b01120204180e0307051009060509010b090601 85
    0x140188a41c0f68002e016503584000c3c000300c59800000303140240c3c0503030714421a41d220300809075071020820b008590603070380601001c074152482d40e0040c40c04030081d0068803030500c03079600b0000440f07000b07070081c8140e509039080602200b84d008952041c6414194001c000c2c0501d10300707042615120b1018000e0034078454406841e007900c07080d0141c800100c0c0000c100c0f40c10034072000c0040d16440103a01c20800611592942d04000d40c818640c030022140e0003405545441c0031454000c019000c2403078140d600d60304c2042000e074180c5480005000c50a4903030742e810b841794100070105201000c903a02940805005000500036a6152000101200e40c2420500c091040c00082d0030f0600307134202c40030350740340c003440d0240b20910445402c80300d4000303802d0340c03105652780d52006c0c180c0803801240503044190340c0c035489414460b4083d07070250340c001040f24112418101c1da0754a040ca000c1c0002c40c500d0070700e500c405241041101d02e00441d604070340340c2ca0007482000c81000100c0c0b8100002000170f810414040408 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 84323913 1250 84322663 84322687
    0x14040206090310020a12050a020909071101090b010e0906010f0b040603090c05090906090c18011401091502010204050102010606031a010c030e0d05030306031b18071404080c01180b040b 81
    0x402004030b07520b001951100c41c050340c090142c0006c8000f81d110365041c4000110004074510880380c5114005080c3d036500d89500800300c500941da03c859107643c0d96039028000125110b81192070080102030001c0016140c20b4980a08280069110b1202c031180008140825680c190035201603d00d2858006088041030410074000c0c0e00f241d00158200c90054240000000045078451040044100f00c072100300d444820310618042e01d8640300b446400c2400140a003017111150150016414904903558544941408034035800111046006d81e5000808100d1035070207000b0303000105105d040030005070107854404d240d0040504211070400c4104101c4d941010300a003c03c0110090140100915901d54601950b49a000381d0b4107030310903c19001d28904644540b240074124040281c004c5048100c0c0c8600745005881c00b40600e82032220010010494000e9980030b8401881441d00401445c0c49520015080b0300491a1800c04000400014003211020904490441c1c14100325150345820300448 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 84325163 1250 84323913 84323923
    0x170d02010c0512220f0b0c0f0403110a0801020a2610092c100b06070c05011d1309031707050405060d09050a0501020702090c0a0804110310050c0d0f140402060903 71
    0x514820841c100c413072801480009103001031094440d141d14400c54a441c5903460480c001c00302440f0400c1420081403001400c0724000884662003d40302484080d1500305103030990300210305480c00540300c0c071114028124948414981d00000c0020b4180c0381c28556400c840c140781038040c108485458a1078080e940068018815002c1c5141486c81d000700340205000d52244e00e541795468009080401621061428108440c1b4040d8000c01c1940000c1c0307064015100301c0951030b82d4442401c5e0344104040039842c1c3c004000d42c510324981d8000f86036919440d0203031544880480445603000104100101c031508a0215002d0315400c8840c0f40e21884245100360140c0f460b280014001e009e21034400042240540207014020300c00c96110556907a0345001d5004bc0c0902003100b030004801070040313008070700800022046000003500750b942581e00b001603042659019169400d58550005065085c1c9849104030200c58810007000c0c8102c01300128589030f1050701420180c491400002d1040140e601000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 84326413 1250 84325163 84325201
    0x20f030a0c0e1807020c010201271502030103050307030f030903020c011407050106090c0f02030c0307080a031419110405030c0906031e06010503150c03150402090406170d02010c0512 80
    0x414000301900192076410b41c4001620f20f280580306c0d00d81c03100d50740d60040c020700c80045d03407800b5240030901341c0b8074480880e0300480105888003101c20210801c4203c2e1800250301842c004d000459807800d00b0f1500600080b40c80103030a042520748006103001a5012594007402ca809203400d0f2101c1c41c04c1130480d00c0c14828850000d02d25880e09078005824a0b840c0c210003054105030319080c81c1d200144600703a8592103180e5038172840e5042000a140058507010250206009921f00060300c410303010504951010142c4460328074020400c00c481c24130b01c0074000c00903520300050f1160f084c00d2801011a40c0d0341c0a80382841d02c03c0c99200f0009960f500c08004030364080c5000580c900300f03035880080b20354582c0000e0140c80d009014142e08180f80b031341400820f40c015098801210724564507041c0200e1030340c02e000c0030140c0c0a60204442120340e0748900501c000740c880900c02e203440324001c1c900580f800035030f80740600075a41000e000e54000c075040400e40c0c00c0e000e980b800b6411540e9644d0712000491401517 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 84327663 1250 84326413 84326419
    0x12020405071209230303010f0b13050d05010203040605060604120303020f0f040f030c27090309031202150f0103020d03050309010906110903160b0a18150309050709020f030a0c0e 78
    0x901c0340414007110341c0e5400740440c4140c0030011402075420070700d03449120034041c08001d4455014100203289c0c4c3e0070b00400e01c8440b0454010483c640301e00c0040c4200715180010f40f003507074010040c4001c1c000c00380b007010b0300a0001c482041c5014500b541484140c904514090203040e03012500c80c84038601242120348005075400e6060b5299140c812056255200d401f040d0382e1000c8400000c1880880e04201070b0301c0d01041d0070300b900942076004515000c2d0480d000f048080101c04140040002c010505a07511264260040c1c42881c140c2400302c90700800051200d400840c00e540100b0141e25290700d200141901403412554a41d01c03821014058511204010308651400824462013125480602504a4200c09441c801004440414282c2040c0d005e0800d485d2070400962480341d000d40c00c000341003071a0861303074100c0981d00d549030442c2c2e1419030000408203480c3d42000702002000d004010107804180005c506000100c502c40803117000040007120740a40d40e4130807008160041c0020740b40c0020003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 84328913 1250 84327663 84327671
    0x3150611010f021b061e010e071e08091b060405010804260d0c03020c0c0907140c06090118051906110c0f1006031703040c050d1208060604120204050712 67
    0x1c090501c241480c0c0b030205104a0185902260440300220151b00da0101c54400504050f400c0c080303400745062005c0c0183d410b11034010a8180e001020b02d000b032454600944400c0068508202c540b0b0604080fa140305004100d0300711840419500e40041e60103803030003860841410341c3e480c40d101d90000e80a45110341d209501c640503481c0c41c02180c00800d02403001080a1022100c107400550583c007030244071a032250844844440c0e141413241069a100004d803820300c51004100b000d5002c02d80c00403070f078801d039504000c00700030340c0803824007034540018808541c18468100940b0741c10f4803140d07541015646010b024004500b88455a08503801140b14404415500c800501d441a56001024421034241c0115911249100c68074400c920807a80c010140c03925030b4524011940036548000c10440c3c5a014403800898079840708980c440407544140100c048140b0b40407805071840740000e144074807500303040106014035031200b04001e40c100c3d815140403c00c1d465000f02520321131700c0d165544a916140c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 84330163 1250 84328913 84328927
    0x10e030c100b04020304050a060f020d06030f0210050a1209030306050a12060e030301052407060509060f0a0b101b021513080d1b050114040605011503150611010f02 72
    0x3288503084100301d90010021000301c1014482a0300045901420540081d0f090001054060700952050107644400610f0000b000315144101c880c45c1c0c00681c0c580302103100322801c506041d01c0a41c186c1d140360a00c1d130304100038824001d10001d07080140c600c5d1944c69500ba6400c260107604284c2c05080020f10010341c0304e88950601600000d03002081c1d428606207800380300034400200449040e103c0103481c11004401000001c40f04603107a0204801e25203003048244003154040c4501d50289072008041c145900340340000004081c000341c07085020764505204941282d56840300800b0500d01c0382015402c1c00052000c2884001c98900302a400200341c00c032003410319441a005000c01210003802841d0161900340c40c0c0c2d40c03100709049810101c0d2001310080317010a0100d071099240d03131290b00003190b1001001440b202558080d90300300d4009440e41c005004441c4e1003a4002040800c0b441c0c2045500ca2094030b02d00c582d040d521079402400a12150400807400a4002c01e5003295403440542d13507004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 84331413 1250 84330163 84330187
    0x15050412080a020c040603030f1422080f01050f151f050415090302030303010b130308070b0601091d06040518120c0d0c030e04020f0d0507021e07080303041103010e03 73
    0x101c034140b02d07801809a0a816009440d0074400c0405a03030b01a0703186a0600c44100058601c5101e90404d6038035000d06000e0401040e0448104601c00c1311041c13110a51586450ba18515040d211a008070059041504221889200820840d800740780b030780080d8a48400c0700c0208500d100c0400030762030307003910600c50b0020317194210300100100c400001c1100d4100b058450102da650f1103d00009605800810040002140d28409490005102010740e816540c0d00c0e0348192080d808510200d03002c8004c00c040100c1582c000001c0c0c4000c0a0b6140050480350f0a808400d510610040c5003900c075660703550100305198084440d0001122150048034968035200c0410480e5820100c2031541c80d01c2151900e16040348a030003040e40240c1d040e16440764000c03c05042101a4100d21a0f42080c1c0b0b2090004401000b040d00905010381044d4001d814601242c042c00fa400c3d02c40c507420310140f6806084100131006001089961064200c40d00b0418020f5450000f4090701d00300340790300e02c11310001c110390701d800c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 84332663 1250 84331413 84331417
    0x1602010c050a0b010e0601020a110609031501080a060f05061f020f15040b0a02090d0f0602070804060804050c0f011413050d08030f1510030c03090c0f0503010605060909011505041208 80
    0x105d80e21090304480e0342e110012641c038039030010001c1c0500caa0b80d9441d91641003000183c01102401000d0f903034800ca0113100350910340026032110640e1350003480c0500c140178451090600941004e10140020b1030a200860540000c22240400d07070f620034040c000807544240490710b00504010181c503c000d0044028004e24401640e00b5078808210324081000c04800b482244d000300300240c6048030b00b4900d92202c12030f070b46407144c0235074000f82c003000308600040d800700080000d04803a849107420307801d0034144503140a1451252600504c01049415001da8220885012290107143e003941c3d04d030b506c1c003414080542154403040c0c12078201c800c040c040000103800b640c4200b03403050405000780c0c2c5000d8000808407182410ba42c0000190004c0e0078554481d030402c410452584c04c01084400303465840400410859002403054507800c0c405104514080c09041e004090850b03106040082180000e20641c07410310030b5503505404a4101c41c41c1c5805039058a0041c044c0401e40c07401c122050070989699 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 84333913 1250 84332663 84332669
    0x30706051e071703070c080307030504060c02061b0702040204030b010b09031c050d0509151501030c02010504110f0111060f012d060302090406080717010b090103081602010c050a0b01 80
    0x141d0501161503081155405454070503401c41c0a120400d904030902920940c0003070469000c01501c9402d078004582030200450003040d05540005461500d42031900031100031240d203004540014050205c84068400c40001d01c0d010040c0b0555241c21502c0010300030312407580020406002d0500028000b0884000382c1072003682035080d654800500055900d2a01300e9820413404240203014007a141038140d481a94010540c000b04d401e07200003000a5480d01d0300c00c51301d17054181442c0d24004040e592601031405103902a000900c00c0d410304c1e031b580b21401c1180c0305146010f00c4641c00c41410310382c400c0034400480440282503e20380e0400290300b112000c0700f4000c40c00c3c030601c0c014030720890141d04150402c1000c1c844094103031941c18254214013035408400c52543c03080d120940840e5482c0c003808484000c11001180200b1100101007031030a44000707a0301c4620805460004002290301c0300100d40ca101554152815294224030045c0e40c6804a090050200c2c420060141c3c1000034160145043e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 84335163 1250 84333913 84333937
    0x1409031f050103210f03050703060503010905060603010f0606020613030504030f0b04050613020f041505130504050715090303030b01170a0504020a090b061213021002071a04030812060d0203070605 86
    0x140da03941c0011640041e0380640502e00044024041c101a0b031b10036400310313800000b01d25021840c5a41c03400041d00391950b80e10155280d42020050003441c0c81d09200b0811000c05866091002510703180010b900da8200528180b0032100c5030840d0b404243c4550222400341d6032190041c4001882c5050890005108580c1258a4419000410a082c02001003461055402860600f856402c0301c188000b4003110308900c2c842a03516400450180d031110083c90100701c2a042c00251407510781081480c010171039014400703140080540d000781a82c01040030301030340d030141808203c03100c2c14001214072110320f0038102e04454500c1c06000b100e40c481d40080c1e0255000312403811185440b9131603035080741c002e400f480d035100b41c04110140682c40044540c0f9440341c010303000e59891160980114007410540c8042e0310050700090350500007400040e000c1114805400300c51070503e411a034502580f40704003440c000c1d404e0004000a1030381d50f03c6244402c0c0c515409001d54111380e55544015040303070020322896403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 84336413 1250 84335163 84335183
    0x20309030c0f011b030b0a030605090309090a050103050d05070302100614010e0f0901140d05160e1806150619120605060306060414061306090f050607031409031f050103 74
    0x10b03103207014040c90f541c80303d050303298500481481c2c03815002840e0300c4071042e030449001d04001000c42c085205d200e02c22241000596034481c3d07807108120140800501c1c0c07075505450040140701144001801c0a41c400081c01d240e540c648060400341e103480d4400260399111070501402254448194113070050a040a8a40201d003046000c10080110611500ca540000c0d84400411405200444504e400325010f00b5601d54003010b511420b0500c6044030483d2034608a221041080011241c02c03698000740401d0084580b0f031041d00429100c01c0c0292420b003004500744058480e135625a411502c0ba42140d402c2c403400003d030480e016009951844000140c1d071318000c00081d5a00f0710000b01c03880b9050042101d4a440d050481907070031a001d041055401260511024500c902689011000307844951212040289000360325031609800b5000180070751800c1c801000007a41048407180c00500a0315402c0d2544614000b0030b280489004010388102a01521f581c00301c5165032016060380e000d120450 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 84337663 1250 84336413 84336433
    0x5090f06280e060a0b0a030507090509060709031208100509040501140907060c0206070c0f080115060c02060a03050903190e09060307080a03030203040314030405101401050d15020d020309030c 84
    0x4100c6501e03842d803002c070b5080b01000071070400f5243d02c0326400b140c00414407441c060320b903251503191802940250203030540e01c0301800001c603010004154002010314110218504543e98503140c040c0e20703442c50050022581c0414240703180c14841c840a80340141c21032105150a090080c041c0c01030180f40c2c0d00e246500300106000c54808906101039506645800c180540c040d03092000583c044441030791203c40c41c0d5000305006000303034918402481140c0001c24514078092070401d880c01550300c031109100648049070b0040e00c80005880a103003590400003140d0740d40180150562150304c24420244071114600c014160b0042d0513100c1c103040540d0820350940d940018150360351107600490b1061b41c0900604800684a40c00441d070084c031a190142840c07200c85a00c1d04103820680713089810303800500761805043d40e01c0c8591542c0c2c1d0043c01c20b00030107524103804200c0300e0420440103490040c2602d651808070041d60116030b02083d041100310354a02e0170501203901c980102d001c428190055411007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 84338913 1250 84337663 84337741
    0x1a04080703110601061704062004080606032b0c05101401150c24060f0510090f12050118050a030906020a03020303010501030c20030a11070e070305090f06 68
    0x101c0d05035603c6031510040030292000d00030881b0401003040f105030762a541c440c8900400c00300405d04100800314019121800c1207405420a4030041141d4007a60064a41055500d00c9121241c0c07607481c0d4407440050201c1c050710854000001030000b07441e521403154021280b00c03140c1c1c40380301e0300d0450011054150f602e4031400c0c84aa0031900c14000010b0200160002046264158600503030444680140c140060b03a1070071b080c0d80495018100200281008101c103003801ca1a07400c2014203403500150180c20510303804902c00b018010030007028018101c640400809602009103c103d0511940641880345451542d55801d144110000784800d000003c560f070000480030342140c0d054014604607820400110011324080c503400f403c011141d005100b010841040c2142c0481141000d036030f407040380200103001c03e642c8a004482d103511610041015039202d00155070030030810b1801040c1d5481b1350034014581b0080e05070484c038074010310003030183d005010401541501c5080b41004c080c818029a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 84340163 1250 84338913 84338923
    0x1080108120901020a050607080f01092307020a0f05010c030b01080f0703090309030b101410051608040513140f060f010e01050f0f04090b09070c0605041a0408070311 73
    0x264600c40d80c0040c1c80c00810682100103070608030811301c11a1015a03007900e80528145050741d212005c119044180000100d03a0007246004d004201e01c28461030b10102d40c0307540c512040391941540e460844000c40c02e00c0b4400d2044092041e04000d1091941e01c09003401d81c000c15800056401003480c140c074003182e9501598616100301803500e41c0c40c54a994600c41a80500f1a2450032000c124141c1400f00000301c0306c0e0b400701c0c00342011011140000c3c0c03c040c00c0400a2141a0405204181803400050465440707000c888052400c0101007441900510b094a0680a40d81101c0d5001c103024410b000da45905d41d0042c9a1002c0e95195207816840f0b01c40231844c649000d407181c80d041b40382d000404042e03501032918411030101c189070880c684030402d01d150401d0b8001c4540c0c049a4440002c0812903682c1c04d02505d40c10003000c54000b001d03810005000b4141c8810220010001da403903d001800b48101000d486454000342c10060060348dc05103025411680400e03000ca01040721000420034182000031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 84341413 1250 84340163 84340169
    0x40b210609010302060304060c050405060304080304050c0604080a17040f0608160305150603070e0402190e04140f0403120618140105090a02070807020d03050c0d02010e030906070203010e0109110a05010801 90
    0x4504c1c51501c941d29823034003030246800c0800c1800341c2084001495207a01000398401d60003800b00d00d0301c80c20540742113420f00050f440e0480c41000c5c14407050101e403401080204000c1c1e48488102201c22200c01340b0707031950099a00410420340b0504c07000640540010300a842038140315070b0080c1d0301c0321400d416021100103603080f8910340b80d80c0c40c42400c0d60034610002c503040f01003030401403003020125002406036400018821144441021495826a000203001079a031808890500921512140a125240c8001c00e00b9460401e1800410217250060020b80500d0040110902c406611401c051664899030501c0d0201c0c60b01d07003102c3d441c0481d103078001107050350b60080210805884042404000c2c0d00f00700030603203070305408005138030040c1d07070365900061100c3c4a600c0d07085e250484254841c0c1004410f2080303d095904001e20000000d1000c8229501a1801ca40c0c60341c9503406400808c1c018049011002a95841d0003102814480003107410018680100c80f03400d100d588410045403102800c0c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 84342663 1250 84341413 84341419
    0xf0304050f0d140702180103060236010f140c0102030601110a0b04240911090f130f03050c0105070c02040c09180f090804030305030601020628050a02040b210609010302 74
    0x201001010b03540f0200184856400204a40e094400302d0f0081c1c51009000e80c03080300e00640c00174580d1060305603c0510000102c0c12400d0030340ca5680c00c00c841701688080751071207042060242d401c2c00414041c141401e000400701d1561615009941c0d2464002d60041d1001804515004002c004110000820700441903002000700c1c92600c40f50f94606c20192040801d020520403640d07180032078905446049a00c602420726508604d90305800d001c0c0c1648003824125400c02c10504000b0300016001d40400f00300da105a400000f962030b0305040350140140b40304a0b45650805090100c540d030b2014100c881c89008032001c002c40e4a0319003054883d041e4522548840d180b1252440141c4070895101d000001c24a01d000b00384080c03ea62501607980c8250002c50110342c010042c0b00d01c55a0404c502076119500c446400a1800190900403405c0c40d20316002248544460000d481d00210b03030143c1700201340b19540c00e03403101716140a542000fa203000c05c030b1000404000015034140341c03054205040325006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 84343913 1250 84342663 84342677
    0x215060102150a1d070e0604050f130305070624051f080c090306040b01030611120a020a091509030203060a0c0c23031206040c02010903051602150f0304050f0d 70
    0x11424400d4442005003449001c03541e070341040d07810101c402c44c511856541c45000c4c0a11505001040020242c040c0c800c50040e860101007144440340d220b61035402a061000d543c17503900042c40c1c100ea4520a00310300810603810400e41120504445180c4401465908500b806007515070702407207400c04440301980c000c0410321403550034a602600c50b130b54020f091646054a440c0700c1034040781c0b40840c20344046426020395001017062100310704c04c0003954002c030781c0101d1400305000d0000d400d032003001c0c20b0818520f50000d144204140100c8a14000b040140492041c241c40c038a000340001e4554881a8000d0259000003407070242944580308000141762102905001140c03146814409400c483c10b60141010708000c0f22800c00304090455000c2417180700d0000e00d4190280019500070b0766028065a05220b0040000f0350401c06645141c00d041e01c400244c1c0803070380001204811552040220004001228407480704544010351295024800b103030440103c03809041d6031807450380c0200000038a1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 84345163 1250 84343913 84343933
    0x60203060f03010e1e0a0506270a0c06030c0302090a0e090c0f150a09030b0c130608090606130902060f0a020106061704020d0c1809030906090308120a0207080711010215060102 77
    0xc070780380016802e1408022140e06485a07594180361800943c0d400c68041021681b221032224849c2c0600440912000900340011440d40c80380c00305140c40c0a25030526403200f8034090580e200f41c0c16100da190004001c03003151692580c2c004040c042c10f6900146501564001d00024101000c42106210000e807102c2180e64118401d0080c2e40c02c00c0c1c15000800c042c14000201044400c000103018002002c0140d50395500000d010840b034480394050fa040c05007a404000d614480481d0907684540107481904682065031a800000d01c4a44002940104040b403541012518031000d410f03041d80e1038000b0000191129800d0b00c0070350440d2040c030340b171070f000c2c80004005003807041039801850710603480300300039030340300c1c00c5407220b4048801c03100320b80130b0380c40381000141640032002c0380042455080031005503056403202c035001d1190724159805054903002080e0a0031542c2d04a90040c0d070002d0a0b00e484101d1440c11a0901c00c6164032240103208104040d04290807002c5090701681050b002003484c030030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 84346413 1250 84345163 84345193
    0x6040c18050d0201020f0303180d09080d08040510020d060e010b070b0a23090604020117070f1803080a0815010306120b100e180f010911060c0106050a03060203060f03010e 75
    0x104420302241140507484111b0140c050030070240d80205c0c0c881c0b1141c0844c0c00c9100680d440c0c01c18004500c8104820b0308010840e004000c12000350310500361900300960399640c18014948444003809103500c0b4030024018140780101d41c0008181c07008481c0d902d020b83da0302d254102d25401900700203040391000320082449900c45600c04051503c0e00d80352003202030a0309c0001c00b56118119182d51071908913004000c00c560740000b1490346c0f5200124110200d082203c40100301e242d200c01d00c03505110b00d000d1002030040c0941d510500940d0b000d100c2c15521410018010114081a212400070240804518a82c4c0d0f00030b004a009072080c42150034203030030070398480d1100f690024181141c0e110b20114049000c808000f40c0034841e648941031802000241150301e480c100c000c288020701a4074004030f000000750185001c16070cc1e10104c5443e0f480d400002d0981c2e00400d8541d00455000b25151800020040350b50095481080201d03201c0d84010007035000d150a9450384811146a80c00c181c0c5034008c405 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 84347663 1250 84346413 84346429
    0x1a191806080706200d08060405090d0f11030409050c1e070503090609060c071509170706080717041a0f0f010e1801050406090501110a021218100806040c1805 69
    0x38070752400740b505004030402c9043c1405d1900c0300b4030b400540e2840030402c1d1030074280281d0380c202c0d1601000707104400ca1100c00800d150302d40003003070f800c022003148050000b00c020010303034018200f81d160030010340c104030b855000250f00415107481c511010640344109503480e00c083e02c02854005000c2d61a1039900740800a0660092602035400750027032100002d0762008000e0400903141c0e50516810440c0740d480701800d1101180d2100510144a0144a5035014041800d404840f044e00f08034061b80c580c1c1c1c505a43c5400001c1003594858a81010401400801c0050091100c4101060021030b182d0f0300c40804040703070440d440c65a0b082d42500400403654110b0483d98054403090100ca0b00d0160f000c1030b2401c0d15802d880039152261910503050900800707101d04014480c501c542c403032504d0201440a9203441403000c609044a0001c60f441c0000f0140440000ba43d850090005440c1c004032080900703030704019580c042c0924a84061200d066005503040d2100d021010310b0b00006501d00004c0002070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 84348913 1250 84347663 84347687
    0xc0901180b0409060c080105011b11120304030b0708010312090e190b0301020a030e01060b040e040305090102121c0c03020c15060310110d0506030d0806041a191806080706 75
    0x2c10781c1c0b03c900c00040b03403281c030556881140658842c085940340c500010721002c0d00c1e21540c0e8000d100d0b400300e1800141012205004008280c0d408400c1002d481e0b031301811402281d101404200c0010b003000111030340720708041d060f2072241c0340059004040c0e2100f02e03243d2a0368050441a03401c2180400c1c21605002072100d5450321004001c110380725140701107402e903044500403a01003603c400f24064405828050603024001400c42a8280382c07400c1d16040440d1070141c80601804030002c0c100406074800d102102502c0d00b003d891940d50b05842054503140415071414400d81d0745084024608030313110303000b155400000310005150310b04e8201e2002c41030200140c2001d905106a88034400034101a000300c00c1041c5003128415100c240283c03100c403e684004001034820f40085c1031800ca0580c02000c100d80041d81550009540c0310150138040b100851410440d611100c5180e0150600300810820010b0b80c2010310038120700d015000c0c114041c2d0744140500c1045d90030501c010711100713100b00c12007114 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 84350163 1250 84348913 84348919
    0x60405040905030714031207110a05100c09080105040209040b18030f03070e0301110d0c0215070201090b010605030105151b0111210c0d0b0a0909080304110108090d08090f0712050c0901180b 83
    0x600414bc0c0e80303442c9000f041c0d032815904a40c55119a035251034010071500e000f004010000c4c002c51130a503000070403920700104028500100400440c4441500440e45110381d40c0e40006c0329501c00c607008d80356084be0001c4036113a0000305021051941424180182658003446410190400c110140b180010b0b0041030038030f80440c483c03800000c03020b052a91115000b002281c0000401c803e0a06102a400b01e0503000001440070030001040b01c0d441c4d244080d041507060212450301c850164418070002c0782070001e440c1003903080061003074241d400c680c0146034586400b583c0748d000c1d010380f169054401808a6400311800800d0000700c0d940e6545400034048000020a0808425141c01150040b0703910b19105950031100842000104000b904e8075200c0480b003401c0016080c0390011405a031008040d06040801000c1408500c0403c010000612401500816070b0f0790310f9103403942c403210b8185002d410340d8039102d0700c80c2003421400d00301c0415050b1920350030307800c1d009500c040c2000f01900600f000190 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 84351413 1250 84350163 84350173
    0x2115060d020a0308031b03070807051b1e01050105040e0c0d021c0507090c0c11040906110c060a050105040207030813080702150d150506041406040504090503071403120711 75
    0x50303907803110b910041c5100f03040c0c02e074607800c00c4070803290760084545280612002c104140706986410100e01c50b030080e03003450034541c3d43d40049031810f201182c140c80704400780304040d480e00b41c03142420301e0300c428412040000c01060381d0321400c10003600d44401221840d5005444d110380d103428818003084a160014050884050703120b8089a96090742c200182c1c0c0c40e801040c2c0901050703175680105102e10039207182c1a01061290b807581d0000142c4080000e1150f50b48540e400100000383d0001010014402c9000741c8684407446415100c003000c0f6540312115103040d0011a29141034401d80b0120b0f034065442e01c40540e80e002400030143e0132403205480841080c000c00740180d444145d4102210b40010010351a8100111840c0c03d8680f41c201d1484140301580003403009460348001c0d50100c5d0310102401c2d20310303040d1324089507161103690001c9030040d041640d0b01003841400002091407520a104222001c81c604101c16140d0103007410400c529140f0704041070f24039102d4050320440c1020b40d002e0390 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 84352519 1106 84351413 84351439
    0xa140703120c0606050a0602030403020427121403070906021519020a090308040b070213020301050d080304061e1b1d09040f050304060302030402211506 67
    0x908022012050b03405110f070a030841302c0145006001909042d88030741d0000d460b41d015000c1607018508220010000311303207115200a103a020482007810002599913140841c041c07030b520410412a01d80074503801400d20300b00940c007a00c0282c90b401d07002c6180c14030290506005c83d4112003600300721070400c203071000c850780d001c915403440000c01a071710035110005844088890300054056031020a000c00d01035220300050819078000c035210014590406505410392000f4001c150700441c9841000c00092501000780d0382180c8209804105801c5c000c04480719000c48040800f03d0710348030802d100c00d00c051074070034041400040c603051032681c80d10710983d445806000c0055000380d0f804000203049c851a0219030074410761080603a6510350751000c005003c1d4105803010780c80340d41d1005510706041071039006c06014010440250100d501d6541c2d8804003164007d084a4204900180308 = true := by decide +kernel

theorem cover : BRFrame.Cov 84172663 84352519 := by
  have h0 := BRFrame.cov_init 84172663
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84172663 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 84172663 ≤ n) (h2 : n < 84352519) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
