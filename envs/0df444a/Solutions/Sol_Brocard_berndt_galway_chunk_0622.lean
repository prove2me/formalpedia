-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0622
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:46:46.682025+00:00
-- url     : https://prove2.me/submissions/497621a3-85d8-462c-9a27-a797c2c71461

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 111690647 ≤ n < 111870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 111691897 1250 111690647 111690653
    0xa06020105090c101202133206130e1b030c03070912150f090602180108060a060c03050703050d1d100504020901170307020901081f06060206042904 65
    0x800d07044841c0821842803a18541c914a0b007078040360f250b0754503035489001e135804030780200010f5004000141c3c094442888041805002d45a41103016000c85980142010300c1e80410483d040441c03010318003846041080101c691040c40340b6074192003035940840d540791107480c90b0f8905010603841549612001200380042ea211500040d03000326003581d501d240060311103d0a0000c0d4a9141001b0103640044c000c40c0c403421656000545480e0104030700041c0401552103000c1607a20182121103441044a103100c220b40c0c000394019000300d8203031110107020b41450300251070846401005010b00034049076082c2094800c3c0d049802001100c4010300c40d8482c0071820141010000740c500030b02c0d0040c4076580850542c240b141901c1690000c20840c000d920702000200da8041903400e0002d2400200b18000242c0c803801b0606008100210003403040042d2a8402481c07043c3c0003680c0029a801e103003003005060317400140160400c1e0081104007248078800c90481d0b95403000c00100c80c00104081c204030034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 111693147 1250 111691897 111691901
    0x30917010509070e090307060b0f03011b090f120f02030313030507051206040b18010603061103040c0b070c0311013c17010902070206070b0103060204081207120305060109050a060201 80
    0x2c100b240111203d8503210310710fa001c510400c443e140410b5009100100100d8455000080b00c044081e082410b0041c4203400b1a01f516150714110b50f401c07900b00311165141e40c0c040c3c041d0005042c0b01859031103160422403684106040c01c0806881c418400d40b1100170741da4240100c81c7e1464032002c1504d00e06950303191864032441e584c0705a51141560380040c442a04000c01c00d207101e5039014403812032a40d940c04032854166000014081250f580e03000100000e0040e11400515401e03a0420035160719261400f5400c100c00c0e0f4000140c1d4440a003c0c0000050054603848166603128134a48030010080300121065170100302c1251885041020b51030764400340c02640000915960011291003840381826a031070069400c01c000e00c542060300412481b41036601170000030344001c0244c1d02c1c01c182600e5003184000203810036030b070302540040e0400054004000c0e65214596101d1141d00300403490b01c480a00e00d0030b0461003020b00d0344840000da0940c1c4035240c0d01d40135020080c0440304d00c3e9100d50000380 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 111694397 1250 111693147 111693151
    0x308090414250305040b041202100905010b04050a0b1e240306100f0e09090f010501150e0f06070201030f060f1401080901050f1b12070302120f040803060d0309170105 73
    0x40d404060b1402440140d10030f000c0d0174030176900030540d40300c240c135190b0359031810207141c6d00030300c046000741c140301c001590a6004045006d4012000810212000300070441114000740071207070503a00d0040641103a0b01c07004c4000a0b10f411014882c0500b04c03903070011807922840a40d403000307101e1900c15034568030b0b104c0d0409903004210a544004418041100688101d0350000c030003400f02d460565a8134407850109011684803c1c040156608039410b4010142910000e0f00720f1149a400c0f8041c400b401c0d5400750210140c40d0003150103a905c61903a40c041981c6105400010b41010345031440030104980d00d8100500400310010341c444816a6071b41800c40380101040100e0001e00c5000204c0d5a016050040c54041c81e00403c00040381d0300c43d128600e4034000d8002075a0b8000505104120140c1c600846103032048030147c9026aa4030b500b44030342680d42034006d2040f43c6003d1010203000c085581b4405407980810300740d030940301d9a5613a003030a8846140d01d50001d00303801000060303a6807031001900079034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 111695647 1250 111694397 111694441
    0x30a03030501080c0f09010b070303110c15090304030b010b07052a2701050603100f03030c0b090d09140d060603110306010e01060f26070c05060703020705070308090414 74
    0x1c81c44e5020b101005103858440306000d1344080401d005000002800d4010b000ba2880381c1000600001e03900c0164a03a83c210303542c618203580148524041c1c0d020450896079204103940043e5180c1421542c50342c6400c5810f00844c801004013140341010020704100b81c503280d0000c080b5000c0b80301c80303001a002058500d0039505004038102c0042511884501b08841c404d000100400203461b8200030a00140d604014240320a64510b94400900b0460902d0044060350080e41d403840740d2042410152050725010300b0603801940680c84081500358010604000e0314600c0c0c0e043c3e254800081d0015006107100580a07103450318164000040158402d00364048802c16000c0e01d07403d1f80d80e90302503d807402c02481078001164840070340c078141c01e00c0354a241c44550f20182800350760701103010008031030840403580e4001080d5081202c1e014060b04003e8907a01a40b58034045d458041075589142c0c40e40101e100c0203000341070100c0c081d249a44c468000da920f0042010701540fa070f01d0440102c1c600a190f0074925 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 111696897 1250 111695647 111695653
    0x15030b0a0e011b05160303020412050303070f170411120d0201020d0606030608030d0203100e010311010809010e07090e0120040905060102030915090102010605041505030f16030b07030902030a0303050108 89
    0x102c0705000803c03020101403c1a456050070a070306030032109036000d07040c0d40071020180e00b08004075900f90010b4004101602501c021602c0b80342804001d004213045040c4242800400f8040369031480403450b81c0d5900940c01686202c1e0703441c180c1c0208014088590694031a4028161801c0c055039056000e091a64040007090090f5071703483c0000c2c0c04440e102c1c0540d441c141c02c00c120243c0440c4064000b035411060041c034540d40c1c550344010780d24a848007038000310344000b1443e69441980d81d001b48031f50341014840300200284844156410340d11080341c4145110b140d11911201781403e42907002c840340c11007401041d5008003100c4901441540103009402e0024508408606103501c00420740e0781c56070f00a80040e01e01103098840072440d41242c1c480d20304540d201c11000c10f5603100d500840c403003c410074401e170710100e051004040c24006d0409400c001b039403000c60905003410034080c503030040766001000700b03100c1c0c1c58072502180542842c460194051041c03c00450030194143e0056040354920429 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 111698147 1250 111696897 111696911
    0x501050916170303010501080709050d1208090c010801120606120317010801020903031c090501110912030c3003010807090e01052806051201020706060602030c1015030b0a0e01 77
    0x403150b61020120045401c0768010b0006108950082c4000754010115041c080c1c11642e079480014400440400101c1d6040500b461002800350001101508000d003440a1310600c400600020203c240512545201103020b04500d024007180760701c80c0001c0c00b00191001c0f010070b26414060b1182a42117503418541018000000b03400c4410300c00c1d101c149100501441c03800d1544c1c0c1c0b44c030301111038504030215881d0b030340c600341c100040e42485000c84540801500c151145a11010499200908401c0000680040040070004400420040c00070000d010544107810306c103a90318035815000c150035909040c00080081403079900003c402c0112001c604060000030b0f10750030100e081c0d40d000c2d034440070810490034449800d01d0700c2402012044000c0200000c10340d42e20000200790f020003042140c4983d600083c0c00701807084500442c0042c0215000442c44e000411805503950f074980701c0b0802c20542d543c1140d081c0b603105041ca03000196040700c09602c4c107090042614008010b108044142c640c60400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 111699397 1250 111698147 111698159
    0xc0303040b150a0321030f140702010b0a0e0a180c03140105011203050703082206090b0603030301120809040204090515100f02032b0e070f06030908070204180501050916 74
    0xb00181074035842203a11034003905c25000d804040d0300041540c024561104c00c0451401660310074966040413504112025007423820b40070b803c4440456003140200803d50b400d000a0000f001c02e04d410400d101c600054490707000d08207007202d003440d0070b0041041c0c0c0c480c1c900009101040220b100300c13021b20340007040380d03903600e00340740f01e42441d10701009002c11414480c40002c00c1c042e510441c1e000551801c0628014982d000b415032008441404644031075442c01d14500740509080d10a134410000d0b402180303154103207080a54003d0121000811a003000120f6245076100c40c1c059030000d0508820612543c1002031010030b01c0c40c9020041c03805443d00320208410184107444c910950314940c0c0140d81f030010901e4005070030b6150901c182c000c03c511004446074407a510310428940903901e0b070203084410b0400b06601c0b010034076584803c04140c208503052010419103000c646e10103038121400160605900410504103008540c00303031040d4640030800243ca80041000402e480749244410768103a1681c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 111700647 1250 111699397 111699409
    0x50108071815050609030a0506070504080106090c02030912010906020d0506030c04050c0a0e0d0c090204080601080d0f030507020109020a080c01171e07020703200405070c05100c050c0303040b15 85
    0x140c400c2c602510080802060030b1140041c5200540034044da810745155840e031610340380040c0e0340d010016600007030411200c0c0c001c1c4502d070094003d000040c0140140030000039502c0c0a5004a03500c540f43d0f50081030b0100a00751b100c41c41b4294883d00070341d22807085011010003414105d42060182c0240e1071074021616103482800e2103061b440c2c8a0300c0c1400c1d118902110172800d40384125400820720304000d4003280030b07140400c0c02031030601c8002d681c0d40d01b8103910608090040e400345103290301682c0e0490f0602d8110020800d00c241d645000a0180c0c0d980f40100d015020340c02e03007c2e410407005240400d1600e8041607520a5840a0b200d00c0c81c010500e0b04403000181040780d880040700d0b4a5070f4051070640b1280d0340740350007400c24411648555260b0309c6400103480c8040d03034a130751102c1c1098079071028100390044560044180c00c00102d40300c11900c0c0c41d9114164413002c00e0300d503a0b4a11540500c02d0140d0280e40300d0b40c2810044a44924140c03415a40c4942e09940351001130900743d8a002d0079103000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 111701897 1250 111700647 111700661
    0x8011107150912030e0304080129091b030a0204051e010801080d0516020d0503030a05070e01171b04080d0e0a0b0c030d020706020906031501120c140c0309040501080718 74
    0x4071405843c03005500044004100c4002a800c01e0700013044009403101090180048030a0740110368003000c5286850911a281041840b034015084081044405110055a24a50a901d0b4442540c0341d803820f40e414024410f5070080e903480740c10100920304011a02001480215003a210201c5c1a40c0b00c031005d42c2d4612003034541100107402004a00345170194401c680e0007a5101400c1c500d5600704640d540c03800c41e0000c5680041c0240e5900030404029480b40c11134184d01000c0c03c0140441c40f0280c08075041d20402800061240d4000c025a807441d04400216130040c0a01001d880803044500001401031402c8001079208100310300d40410312001c54003c0b10207030400c0100a601d4102e15841d40c00194100700c200350f80084c3e00b03010400395902e48100552140408031146035007051150009450503008458503004d41380350041140310a50000300340480c4d084c031011201d441c0c00410000520314807808900c20b4009080000000d070040c400204103080d0348000d8125001820000f040f8800c03a409 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 111703147 1250 111701897 111701903
    0x12030519020304121b050409200d0f080a0e130f0b0a050607021201062412050403091a040306060b03010501020f01140402131410052706120304080111071509 69
    0x6100c0b80008178205407003603079001c4d20300042800c644d42e500000d04840744a00d085c3c80c0f0741c512400d50380603151410309022040c60121882c103101e8030b280d01e85018142a6840042c0002c01c0010f107403081c18000d0003012081000100207080c00c06c01103260002801664a2503801d250801c2820061881d040021a041e00c01c00f07441181440380c1c80e000c01a00c040d01c0d030018401c07550f0b03078900401c01c00452042da510302c0c0d03210040b00c416104d030880e005011041c201e00c400041482c1070140800668801d61400881e507282c090a01d00c4914080e140d81648550f44c00101814a083c81c00aa11000c25003d9812100700360255004c1c00a07020840d4242caa05000f80c00c95040103000240052070a80848e110604460800140c401c42901c0f00e02140e6006a50700c88441d0382d1403208001500c1d01c080d44410045103032106404485510010703e085450141c415803241c078a0010f12002100200b00352401040d55100a10a1600c0184404083e901031103040d07500c0303403540e00b10344540f81c02402201495a4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 111704397 1250 111703147 111703169
    0x100309080703210501120212161404020f0c1605060f0415030f090302060604061d0105040902122e050702060703090c0807030b010906090902011b05010612030519020304 74
    0x840750740d0407551241000b403040355448004000ca02805140c0c480c03203001e000003015000781c000311401001401d80c0103440181255210342003001040301111640011213030088e10a454940c0040d001401074040c201d1000201600030401610080300060302001c03160303006140820090700d40083c071041c0d200305c03c00c01034040030800c01082202d00c81180000742c0d082d58070380011b042d86044403500035503860010a4005911540a211680c540303449080300030310f114070311103c031006c045010308191001449104d200d01e0343c8030015070a42d21000c03160380b14003450600750381c042000c0703920ba4020220f1030940b2540c00210240c140060582d2849414044c43c0ca6400800b51552940b00c102c0160407004030449100c603070f030340740020300b01300421201c009548182c41c5519a5030500140104548440d80301984990420f400f010250340c0007901201d0240341c10108450001c203508010f800f600307007036111102010320214800709259200c4040c020449114600012000c0e28020403640d80c0214040e890500c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 111705647 1250 111704397 111704407
    0xc17060403050903070b0403080a020c09090c010e040b150d11090603010306051803040612111e03130b13020306130308061c0602040603061703040f05090c09030706020c10030908 78
    0xa0041020f490102c00007411030f00c2c00d94440c00a080640c100350f004448440020440c00c44054051090303044070f00065030542c15601d82804e02a82c0d800b00800f00e44d041c4495501e41c01c80b9a210380c2c000c402c0495000d480030b40148081030841009900540144904d00d01e40810b110b1240243c40443d820000c1c0206200d00310313420340e150040140000740140c4800b408100c200b5080341c3d03007440540002c0c240d03501c4011105448000d40c2d4181c641460035900c200d9002c008100c1d041d44110741c2c240030a1a4141056140d6450030980c03030b0500c6402c000602409640010440b00c00c54803000c1070701e554402d078207840064448200890000300384070700040100d00c0c6140011030600380003607280300154603004c440a80d4601a1592012a1301c1600030000180c0c503a0340c140059440900340c0541070340001c0040d450545000e00c4c00180407541c2c040d2500c203583c00c07130200300108a4001994095040142a0b40340c2c1079554001075500d5200101050143e02c0309041181050300910810301c0d03c64100c80094a44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 111706897 1250 111705647 111705653
    0x6041502031801051504060509010f030321020c0109031403040507030809060d02040306050108070f0303080a09020103060b0c061503030403030509040b0d0f0302060f2202310501030c170604 83
    0xe0340008280500e4491480902da8514400740540b0f40680c2480d120084200303052414001585e106402040c0504014801042117080303e1f060103080304d406180040700003100100c07a00301d820903000c0c5440c0690000c5030882c007465041d48600c0340988030f03848101007041554140b01080c0000c42d00588150031580c01040818400f400405d02810b0091206207411180415a4100d80140d003065607001d9903100107003d10141045090050614900b81804080c0340d5036000b40031103001021906581d80724171101e01164081e411000c003500311034981d151030b404214941303503075072700100c811040081f54024100d1581c00c01104481c15660140e48140c6032111880030b12015142032203c00d5006800941040041030300302c0d844a080c51310a602501c0141000100d9411019000c0c03c41d5903409111408507103440b240020203000e1641c1905c400b060782c12400020001c9071080e044040300500042800103c0f15660340c001c5050324850303200480389503210f550448515005d83c0005d01c6541c400b0f0082008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 111708147 1250 111706897 111706901
    0x150824101404090e060a0c0e061605031209031801090f0b1803030f030106030b09130f051203090c0114040509010b130305010f0b040b040506010206070f030b030714030d02060415 78
    0x40030071001145180940da69122401ca5038104c9001505804c0f5500303010004044e40211540088a4a032017100741841e40d0001c0c001d0b101c0d068241c0b4000b01d6205109040003002e1003a00c0020750900000e07451850038141d1582c41c1e50001080140d61000e064034101598046c0c200759059075051485d1292250410303145509940c007501c132280c0840100c203114540d690b02080100001d07602424180e80725494510054142e4881050b4213101e01c0342801001988803007801030700d0001c0c1d040903024000b84881c3c00c00c1d50821400c40040801404000b08105a030a0006480c1e2800f500a17aa040d071440324020942c1d80c980035501070b180c2c3c0010700c90010850040004040c0c0b040394184a000d030442e075681c0e41e13410300f1203da550f80f5070340864490b0b6407180340d03240510681e108058286e03420f000300d10304400000d4a0703c0004101c4801c2c000000b02c1c006400c1e01c00d03030010410180103000c0f50a0181c44013044006441d4291100e8420303c211071400e10788910204603e405181e00c42c0c0c800500b41c4800c070041e00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 111709397 1250 111708147 111708167
    0x901081e0c0604031b0605090d120c05100b12010614240a0206040c15080402090702030904050408030108010606020313050d11040504061e020702032515082410 70
    0x910450704001c849641c1c002c01040114800c04c1c079845240c0b850354600c500d10102c1d6112109111050088000c203844225035852040d030321580c2e0804102490605468205d0780b24406440c900c192000302800000c0c1307510018514004403445d0340200041c03c50f0b103090b1240c41c0242021600780021080040c100002d84031007051030a00368426003000052082c8550300021494001a4040d074284000c0c000c3c41080b000141817a4041c0340c0c00350031811005030021071301a00c0240580f02d01400544624401e205503a90080001c100b40200d0074a814210610740080c05a20f9481d41303002400600305000100300c0d00340c5a2540c082c000d000349460b081000c5d030140b0010a0301c01e1680003100c0400e036aa24481c4e944135a104200024103107404a00261b0b11404105401400d10f02c10848540035a40010705103900b006000c030740c24846010b1040e00d403c1003545900c140501c0d461020f002c03a00a402000440c070441c1ca5160f111400b00d5005140da200074010f154064001081040f00c1c0c0740c3c98031405d0111 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 111710647 1250 111709397 111709453
    0x2402071203050f0315010e01030b09062101090c080d0302040305071206020f03011e080f1f02161a0a0504030503010e040302070b180f03010203011a070507050907030606030506090108 80
    0x250a0040300c04100e803656208032044038170642c0010b5115a150303040712040500c42807e00c0c00704030103118500030500b610005000144201406100b10254040300950082c89484000003800140c005240c00512a2058041c82e0818001c00c0c00e022540e5112340b00b40c504880e0020002d041c4289846120700354502c0e007030001d0303680301d0f002c01800e60a485000000c60003011406c49a000d80d0f0402c581002020760305800404085e004013031505c030760800024890007407445000c04508440382c0c50b9409002449203111107600c000b042c0c01c105007486107500c030340e509800c1403155041c01a0345801d00c080440e50708681c0200450424001403044042840c4100d030301c640301780125403940d034583d80c42d074255400681d4003000c0280c0240303008a1a0034031107151010480290020740c11941090324440d00544d05055450001c8404920081800010004c10000305000b51003040b00381042000200540f03405d000b4000440d0030300300820302c03508151806a04a07a0f094002d05481c025030900800054128601c1e1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 111711897 1250 111710647 111710657
    0x308130b190f051305100501140103020d060e04030e09010b07050a0f020303130b0301090e06090309120a151a121b01030605061204140604080a03090f0602132402071203 74
    0x603042c0008148191802030740c0401c049a51014246059440c2c20a0451900d0031141024010044048000f615540b4035600b400c0c050b856900031000c00000304015408460441200d9051006140e0030200783c0309900010740c0d41d580e45a80341e415204942c414400000c100d94844d100d800c8c0807a1038400c803440c0b140e1009042e6840c0c0b010035642d425064001e900640206040040100a000414410048200c04203005081c003858182d036500d84030302602d0551801030a400c0c0440149100901c410300c0d8407580a0031003a80ba44400350503c0050082d0341414a41c40002e4001c0d0304a4030b0400030440e4101e9048004010316008801c2d0f1041005010800c41d05140d1504004110795446801030542184460303040007a034501760134880c0c80f4050100c00c0c8800368010300180f1001c18800002c5a4030300c903050402007400d01e90340c6010a900b114010000d000d003407020130460303413800c00003240e4400c03282150709802405660700400b0503500b144000120150344071140400c050103280c1c96220b0f100e8024242 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 111713147 1250 111711897 111711911
    0x10f0903020d03020f01050604060f0e040503040e16230304020f041509020316080408041a04090c02010902040507032309030d021201080d17071803020a120308130b19 73
    0x200d45030341c02c004021009030304902640302c40103509115107540700104075002e015040c580940e041d000025400b50581450103000010103204040048a0040c50402c1c000035040c07528002c109113148030030a0000010359036100d0300b0441c41c00000c0d03031104601548611b034a542c546500300300c0003100400300b032500f1a845160101d000590041c640c3c0050954980141e0b4a181000c685955817003010350f1300d002c1c0040304080c0400b00703070b8100680d01540c1c0a000904070440c45040b4407070180c05217611600078a42480721521020341d045d00b000d20424400c0d078080c04039846012040d0705540d001146000d05580000005449440082105801c40303038a41c10381e8a40102c010000c2d050340d02591607264400030b0500104000740c01000020141c2c2d40034901320320000885001c01950f0103018100e1400c00c9001c400103002c00c01c04100c00790055500401e08201d0a40d075421680804130311880031303404100e03044001560119281001c2c440160300c4403213186966105020b10841c0030106842603402c0740e40f080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 111714397 1250 111713147 111713149
    0x30a1a0414030c030702042004060f020f1f1b02030d0b040207150b0a060801060e040207051501060306060f0219060207050313081e0c010e0f030c040615030c1706010f090302 76
    0x10650500b40e103029607a51701e401e005200540d40d60040c4503041040050010410040b9074050b6820703a40c00746003507800c0742d022080481c58420481042d03501400341c04c10903c000c9406209820f001c2504240030302440c19110303a0b14100308000e0100a0140c0c0003001904400740c2c150f40304030055100200014201040c90b103c400c2800e030078200c1c1caa80f003540c9144003000c078900004882c00a0003a4a81102d50b981414401082c101c1516400c41c000c4e0307004610003041000500a2032030a0402507002032456941e130000a025207094401c40021a042151200400c0e1003c1342c0c035055040629000500d1010507640c020080d0321461007030f070302400248010040c018401c1c50b258010b1501e0402407603421001b4144200011500c84042907a0344441c10b01d40450760481c2c80301c1c4c1e0301401120340c0d02c0ba91080d100824242000303452074a5110780f901c034001c07468105003460000313a0310380380d9420040391080383c00070765a0071003548107803101d00003143c001103007036101e000d045050307680900d0704a02c1282e90f03038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 111715647 1250 111714397 111714403
    0x10509130b090f01110a0c0209060414041112070f0e0705040b0c0706030b090402090a0b010302040803070f0605070e03100b01090312080a050609010f03020f030f0a0c060806030a1a0414 81
    0x560882c4540d0000580719450701001d000d00d50b401c040c140c1000740f8040006030050305000750b1140003401945101c0c0001c209954503445944141d954102424942c6014a8401d0260581c5c080c0684a1880c486000303190300000181381c401c0c1d900d28105190414181140d180c01c88134010294400c0120800c0081417034501304010380501c170394500007050082d0600501a058840308484907001c1d601d00d508000147c0d64845a4540041e0b4103007002a4109107440100c001c1d20403034024240611000440d10108222000460300c260700500042220b5294000112541c0f02c0d02141d47e40e0503070207441507a8003110350384c0c4a0740c2c5496050402048003952991414003a42020300820046a0000104078400e25140107003940080200e66040c010342c144a074030407044803035020180c01140907514042c1980c900704040610512a00100d034940c060f07625040d0750900740d41c02000002440307000401c3d224100060703190b202c5c0340c0c081d0070245541d95007514400c003108024816101da03944005601c07141c51041c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 111716897 1250 111715647 111715651
    0x60316080a05010e011a0402071110120506041107020108100e04030306080c01020d020304140604090e070303110f03041202010e040c020609160b0316090e09010516020102030f010509130b 82
    0x280034001c0c0300d81c9801c0035401c4940e1120044000c0e410074014904002800e1110b1641c0c0008a0700140c0710585030510030425940c03d1300068205590840c1c0005650700f0100c03414154020001c20f01541d950202071200307981c9803080700c0d503081105004040049d03003c0c450007030f40a44e180e15140d1030745a0343e00c11070f00c140c04251802d0f40840d65440007031082e05404d002204050b0340a0008020040003044020342d81d06c581c0c820002c01c2c0e040301c0a075403181e54a9404135002050621010f108201e141c4504586401b01884114003043d14016030202c4040d0115811149441c50809542424504240c841c880714900000700e040180359401c0003420307603540c0710301410000c85e54001e0034186442c095251800d28141030500d00e070081d45d8000c1007502c00c1082102c0d071100201020001d103640e12042602c560384982c0103140709038184010030120480542c044e0344034072402800c001c40102e20780390a03804c0703200548203020410b0310580103100301d08000180c66006480350b4101089a1441d8584a01610b01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 111718147 1250 111716897 111716909
    0x60d08280c020a0504050712050405160f0b07060507050f271c200607030e0f120309010305070219110f0901080d03090807080301060e190b09010503060316 68
    0x405240304210600689003101140d450400c0d04007000150001a80c0064901c6038502c900d480d9400544264031440a070081c2c040702100500c01070425103000364850440800d1120001d010302000522202d84042d410200c0700e800075590718040268444101606008150704103022040080c1e045d42c2404100404210a04000b02e4148944450707100b01080080ec03001445841c0c076000741d07a0142c491107844000079030f00c45820140380070951444207054030316050b95907000002090304800c0c1a0460048001034904642035150b0b030181e4400c0008680507482c9100d40e40e4028001c00400c0d501a41c0850380203d00b5004a030030b000c00c084507201d11210038810440c0c80c1d2030311030004c131023600349070449104641c0201c3e0340300140c0d81010701259070303441c080f65035004054650385060180100e0100300c5513a15040b410b007036529a107458025100d071864042d100e000d8a480c10001400014180c0b404060300d0300810300a151504a500440719900040c00c0e5a5040c0134143e4182c00c000c600310024801041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 111719397 1250 111718147 111718177
    0xb070602070c0b130602060702120c0c0d0b180712020402070f08181302031e040c050d0b250e0103020904060b030103050c100804030c02010c060e010c02010e0708030403050601030308060d08 83
    0x40c0941301c0d0502129400714080d54481070070300807020340100d102440044181e20040c0c6a0180460041c80d1600361442079400006002030380d020b0003044003030a031040d41070000a80c90030130754626171540c603286032003001410951144640010729141e0000d020300350103001d10b103049042c02d881d018842d50005025090410341d04084c0c01c0d60b0f0130309151030403000c011040b0841c01c600e0840350700685106146c090040224031038000404000c002e0407000040d00f0b0240c11f42c4907609203860903e18041099442440c601a4658a100584001d288a440c608041d541e070f81c071146440c0c0e0056020390058000e00c0d134031948070b80c001b15844644102440c021400785005001c41c90954050044024140e48500300300f0520108100101781c0020941f21525820301c0c2c000b840d181c3c2c03424103000420700b05140720855407d00c2d00f0340d00c00030303815008440b40404c500181c844d40c6030303615440361b41d030f110700c0c40014090b8105100400101c1e004c5c07086a42d11400181c0040c1e49552641ea500c0d055900219014000714 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 111720647 1250 111719397 111719407
    0xe190801140408160201051c1406030327060c010e010902010806010801080307030e1305090d0219050c040b0a030b1014040605061605011d03070b0c0a090b070602070c0b 74
    0x802402038103405610011207085a00782611858410720814000384070b139a503900945000c59124004442c250441c40703440030003240054048801910200d03100d00ca81d5100c07100800d905e442d000c8200c5042040c0c0b03001060720f0a00c4004400c10b0740c04100e29850317100b0010b010500c000d0700c0070700642c42c05d42c0301c6000000c0c2550b880c0c400500070300c60140c50641003010200050001e5000002100c0e051901030501444040c841b400282c40d50180b030702211581410102803000305040001c0c40300e00700380642c0a61f4641705103482242c01000810501500e9039002c02c00d4255a802c2a42c46220058400f4102ea40a01e031a503e44003034141081ea0302c110070700d12072101040a92860814030050030021103060100c5481d00303001030300a000d6440004007034140300b401f1808002c001d40c00000d500f14548514880300325902003271900c0f40c016600541d49074503080005242e1060800444a200000361500d0181c80e040840e0044203400218003201d000c0d90030001daa0106201d502504014084913505ca0355030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 111721897 1250 111720647 111720659
    0x1115040c080a241d0a0209060609100804050313060215010902090612070c02100309030e090708010b0f04030c0e07020f010e0706030b031005070c031d0306060409030e19 74
    0x4100c450744152032070b402054014002071501c404090360000c00c1d0340b03c00d1400a100240e000245024040d640701012a01640a407007500840e1502c901c41c000c070780355007566540006200e510710640b0181d41d40402508034816402e03006900c41500315000307100700e90810340861ba5610804074039400c0740c40580d00c4080803031020b03da0b10709464058030b0310712410b605200781d0001140c106d000f0420b55100100000000880503841200b01070101500206442014030058501500820046800383c1c0000c4006032400091704100d400d1030b0081314240c0c2c52201683c86c16614a15503001036030300b040301c000304000010204840780782c4900907044681e060720041c10408006403925140801020099043c0b907041c00500102040a8084903010704004c6404a10200020b040c40071100081840b1882d03c000e004d920380c1d0188440d40034030301c40e48414080c3c00392003194044550408081c075078140c0c09003000031050300b4150030402101781703e0704000074242c401c1c2c00040d801c0d040c1c0c0a0f1106007600c0b00e40e02003100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 111723147 1250 111721897 111721913
    0x909010609030f030503070509030714130b0315041718011b200a08010f052208030601030f02070209150103050a020f2a0303040b19020c100c111504 65
    0x4000c03905150110600d10f40c0c0d021401040e1a4000d818084003000081c1c00c240100c003182c43c1460010b0658a51030b444002d2001c0042401c2260341c007421300010082902400b5204655284000034024403000c080803011050450008004075240c05050f0080340b540401034024040348030f5180c0c03030710f071005135004001047d0255440c0b00345100782d5481c01d20700c04549c424890b1840100d00b04900340c245240d01c5c001c1151164a9444010590719003080700a000015a10090244910f030366080b407013013500d001d4041e040340c11000c0641344680802c0440c21640c001c0d8000000c001c07a02c6c002505000e0070ba00000c0110100b180c40c1646030b0314441001d911076a00d8403940e076000c0402e81003103082c06103840c50300c0c0280c080c000440540f10b00c5c00300312003281440b414840b096901104200e81da01d240034a000c04001d0300c1075480c62143c800c18203a034900c0c11500c3c020f40e00800800350090036003010014001005d81208081d44050140110310246070368014820b01848245452880c00c950815140010b1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 111724397 1250 111723147 111723149
    0x40b0603060f0907180303020f12120a0b0f04090b0f070813030e120106060203041401020606010c0303020315040f090318060f0f02070801020301030f030f0f12090f060c0302090901 79
    0x1104650410401007559980c0082201420040e20843c0342503444810a80745090f0740c0312296200741c502d00c4000b08050b80010340203200704804068941404d0702e10540401809003502411140c241980050441030a0350301c10300700004001d0082d4101941e407004201111000d00080d00d40005d604104550741c80203c221a4100d03040f85000a03092138240c45a4207840c0a62900404000544802e0102d50340c80111400c4c418000c00001c203d031a0b601c0304065520340c400e200702c841000c0d071848801100d6001040d171a1003002c0c1078440d05618099503034118000c1d8002807540d454140028031800e06600c480c4280c8400d4000f81000140901c1142400780c1300750001007a074003104013040700c00d11005520044046025081e400c1103035180c0308400c400ea00703011154210f04180d610100c0000140090201c011170302074003070348480c103501e20740100480f1054045c46400d008180d1980c0845100c060a5100300c1d1014090f8040144003140b55940700b00342c406040d003078400a034002c5903100842c034005e80c07014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 111725647 1250 111724397 111724399
    0x20d05040318080303010909050307060509010603030807050c1b010527010905040e0703020904051e030a140313140c062a06070c020405061807090f05061608030702011e05010302040b 80
    0x540b02c0c0d03d4451910307500e00c81402100521034850100004012040040d01c62403a070040f814000c0d407a20482282c005d200510041e00040e21700004100b1403800355040701e6901c641c02d03028050040150780081615a00c0e051500d04000040180a140c00b01003501102840c0826818610390700441c40014098101904542e10861403c1c8600d01640000958102142e505407410041035440c0d041c044d05001000503070f000400c1d03080504d41c51801d404401450100034548a041078442030514928a0303000881b02030202c80440c52551021840b109503039413000b0764440844580d10423100104074640c0000210b006140400c207404804040f880199880c6661400d004140ca40740001005001122400d0b0180c061640c510102d0781c1511000444003c81000000010361070400c2c4070700812049091040e07203804c00107004003240c5c600c0e240088800448440d100344803184507684408e40182d00140c2848190340d6900c038014090f1102d840701104458894100161541c5507005101c00d450b0210021 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 111726897 1250 111725647 111725687
    0xb07080601020c0a092a03050402040f0501030201021914151006020312071206090608030a030c02070602030904050c0c010e07210209010e10171608070b0307051c020d050403 76
    0x1000b0544584000c0c4e812a140c07100c02003041075449807104000e41e440b640e441c40200400c1840c10005405401450055109440410400e040035960004480003030100a00503007008004102c0c0d0640803c140b0b48103801071500038140303082c00c85110f2a24040700d0b80d025804602b0001c118160700c401c0b00c104020511400030b1442c1404400d1204141c82c8001d00d12018400c02c0b80740c9031034601050707000b50058003003004200001c0c0d440d203072505d80d40c1d000f100c009000030741001c034001c006920205200040341c945400842c00c0c62401070810001d040c00a140283c400020311100d140380e0400d010346c0d00455010000b4010060a0003c4509242d403400c95601d80c000340c4007a104016100d181c00241116500340418a65488000751004005995800028014840000c001300c3e00b03004180082000081d022240070a681c8d115083c0c0c40e40540c1c4201e401c1c2500900003d54441d01071402820244c0881e46009800b012110104003280c220602e9125125560f83c2004101508004040581180c1d5068 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 111728147 1250 111726897 111726913
    0x4060f020f010e0316050309041e230601050904090b2e06090635010906050a030f0305070507030f0503031803031302040b150c03090405130309031b0905040b0708060102 74
    0xc030f980d42c4c0c031171007080e100c842420600003001e02600f030085c0d4610080051044c0008207c00310445420003c21884d040010702d882c1040090200407100340030240261811512255505801511650401c42200b03400a841d8090400003604826000380700e10114070a00b4181e182c550259001207094035100d210655582105100b196084075078070b012210f240c50489046540c8440c07604100f1030b40f03428800381540404031049c54003281c2c103040f41610b034001c1703040200720350303070010081d83c96210b00c070142c007181040000c0d2012074401e100a10155004408441426036a0350700c0301a4801001803d50305500301000b404050501e11440132605202c5000540c214142503040d000306001c0500300038403440e41c0e0401030000307841d04e400107541542642d048a0300c4103589541e01c0c2d200c0d8885081540300b949410700142c800302148403001d401c2601961054030050035a40c0300c03448103401c0280503a9003500d00200282144ea079004417486144a0031803000682030000e4081c1910b20081c0032181903400201e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 111729397 1250 111728147 111728171
    0x30123100c020906040207050136030e04020d020c030309010507020601052b1104020d06080706031808072f04060e16140c03070b010e061507030806040b03010204060f020f01 76
    0x303800034074240c044610014984442000070028811542c00803d95424a035800180103080140c8011000d06001c10b521801020319a14529041842004010403900800844281020f5000d400030400b482001494842500310321072079030308201d46810b2180e441c0c804220072240c0c140001401804207450205503007102d0074094200315410b10303035071000c0900c0510720018840c0c5c400c0348200a00c00500300b15038442000c40752002070007807402582e840d4420000700199481c40f030321030f8003603420345200b0980e10190990384e900001e501440c01503580b5a030281e48000c0701041032000c80d05c035003000940d0f01001e60300d54080c40251002c1c0c0d40b1260400b1004810440406060302c2c0711780760802c2c5441c0c440700103100030026210500903803162540c40d00c00450300004000340da010940c143c40090b0782c5000742e5600c100811405080d0b0b8400b4480c121828415207001a0080303100c2a0000e00040000c14084811408a400c9801c40e034000c20024181d0000f003034910b074060100040f01c3d60032000a00032002170354 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 111730647 1250 111729397 111729407
    0x1c05030d06080c0603070521131a0c030105010c08040306050a0b090714190c0b160908011505061c0906270209130804090204030303060f0503030a0801052403012310 72
    0xb0086400d2110004410450880c01c8072111100c0088234100a1740303007856842070f00001a4101c1c00c03a141080d03400c012110070404500700e4414111010303190310350307030a210044903075040412040306e003420140000f2001074681d010b401d02c20f90840e44005190012507041081034a8050441070921120944101010744090215407600300090904948488000d0048034942c0310020060803c121040a010102e44c40306d02d0000da1132a29501ca0098a07140c0001314201c50318411051280e40d0018030400050400070080c00c02d8118014040d11904115030080e001d55041c14030032211113540b000c005101c81c0240300510740d000300c0c20380c1c50810155241c1c041340b440d50001d01100d0810b6402250b07001001200700458020340b54110082d502d603a56460003501618045c025002c16001c10b80c2301155a0800005980700b0802607031b03a00071507920703140502400505154040c21203071059810f448200b003906008600a000442225110110035020641c590316410320f010301c2420803c1405a040b5030003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 111731897 1250 111730647 111730651
    0x309051012020c0c0618120d0203040e0a0605060c010b041b09030206090d1205041a03061e01020f2407180603020f0904060608070206060102010608070e061c05030d06080c0603 77
    0xa01005950300c802c3c8203201d14100041140c03991100000400302c01c0d1907200040030003c0801925462092641500303e00d440c5c07007003002c448005034400d000c02c220f59003002d902d268122801e8800001c2403078652010881584c0150410b00c000ea441d1201360443d4200f0f40b00720003c48640b480441409450000000c02d580b1182c40044c0c403c100c049407409060b624248607200f0144e00c4080380003400402040503000fa0800d01c01c4a202c0441004401803036180d01048a02c00c2c5002010300d01c22230b0211305440c000b020740c0d0841720704501c0351800c3c0700c014420070004c4400303640111003c00050031495044034450b40000f4441400c2100d40101208441d214840c3c900c00d8801c80c0c1401742c2c80d107007042c2c80c41055015051070203911604001d4000303041900582c0da03070301460f5180d00752109551000016030036160140704950640e4800c7d602000f9084c8110160341c1c1001009000740c55500340c614804441d442400800d5586c0e8000040c4d40900d905a0700c240c40081138243d001c1c1068000502c0051114000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 111733147 1250 111731897 111731927
    0x2100c0224160501020405030a0b04150603120309030c051603060501050a050102190501020d14190507020304060f021c020c0306091605010f0e090406060501030b031c182103090510 79
    0x801c82042d0400c402074040c3c901402d4050100c0c1d449000364102207514100c26142992404211074402d90b018680b40a00c00585e40c00a01d0400a5550020220010585a241517040280c851300b6100016018407411007200c80703166480d10084c2c1541450400c0b140182d1015101e511110410449640c02284124440c5030061100403001101e04015003e44a9443d50f014903a04d4a8262222844800300700342c001c0c0a165801110314001c10a607100703e03041a507503280943e0092004100107032150b40442000c114901c10381d2008070340d280c045070402410185010141e081600713100c055080411100b039110003214000c0c00700b01d03022140342480082038040c0ca410032035100d80f60b1036010301900506140c020086c000c240c0515280c2810401000b56008890000c5e08041c4041110300d80024424228600000c0c03248030143c010f501594034002075402c851410310300641c0051880d1103200307801410054942010000031891800426821490300440e104002000c0d035400c80550081e200602030324 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 111734397 1250 111733147 111733177
    0x307170613230705040e010b16020402131d041110080a05070c020d0605060a05010e06160302011119090b0708030f100801110912070b07120c02100c0224 67
    0x82c240791552a40b500011036241007042c4005000c41c09a03c10700410448030341c80c40d4001140d0301c400c05860148545800c40405031400c400c0e01001d49003544c01130a490040c100c080640c59922140c00450300703c1c0a403947c0341b09414204110501c850400310306600b0360304441e1401c214030900c00161003200064414104241d40300f0001d04202d015141544215400400940f241c001c0c074a84038024000455074980140070210000419500802c070a03d84004000c040505100340e50035400d0309003440c818254110340d01c4641c1080400001c40003820500b5003080c034400c03050702c54803015000c0c110369070002d04003031010024800402e00c001c083d81d170400030750038911030700303441da16010184031440f60030800b0345520f0100d072608128500c800900a401c0c00b900d01c01c42e005da81c2030384035455420030321842400f900704015480000710109610040c824140c00c0000703004807580c0205200c058010301d0403021480000400c8154034292500040294040d5070010b280110484c400700f590003054a83d00e1442 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 111735647 1250 111734397 111734411
    0x906030c030a1419060b031e09160e04050105090a080405040504021906051e0705070501050304080f0406110c0a060f0c080c010e070f0911092106010602030307170613 73
    0x48030300e4000f095104840400404a42400141d1801c40d0383c075042900d103258a06000015104480300c2503900c2190310361781c400c00c3e514140c40200b402440013401c001c0d00d0300805001440d0b0313445408018000e0a001402060140f0b030928149007100c00c058136103510341d03209050034030000c1e04403002c440c02d036202a038000c962500d0b648040380740d20714140e04c0e1415080c400980030400680c0900030700084c1e9421900211104d01e91071413040716115060001d44076401c0300c0c81c00c0c06039501910085400501c115100382c60308850030300300f081507082500a00700007040502c075406c00e500b0420041e0044d00c4220340c0310210038602400600000f112201d0700342400b004448110a02000600303407012a0001c3c0d00034001c0f04038521440b61201e00900800b1803842c4a01e0005c039091a15114046080c1c11401c5400c1c680180c210802002da241d40d8404a98145900d901940016051240314003c00b215001991a42050840500300c01c0c1d07810300c01602c6800b00c004016142d07940d0324401c1d2407082110b01c00140c2d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 111736897 1250 111735647 111735661
    0x10522020c01111306110d0807020a0f0f02040606030e0a021210090c0e07022a061b100e0a030909050402180403170f010b09040c0203090307030f1401020906030c03 72
    0x6401030341210000d42d443c00128000f03100c6214010034075040002012a056901c03105c055880020741c070400b103c183e0110884e81c409500804000d034106040e07004803a405140313950b81d21729081e1a6401241c00012519010741141001d01846001c1c154a00b01845504e21700e030f1003117654a51640303019104229011004030a00e00a201011051243c404140407800e0203050808404100d8407070b92003a034018034000342507684085030401401c1c0480d503000350969070240604101e50f949001c20b5500240c204004117003c0c00180103200e181c0b0032040a091a512180308200444030310182950b4030b80c100f11a50f90000c0c2e40710501030190b9440071000035054035a400420007441c105019451603c802100b80014035822014a0303008120082c2c81901c0d9980307a6010001e050400c1c45840b5650f40d00740040183d03442e00c0c1e048901803000c2c0b441100c6c04c000501000a03d000011361003038400500f940124810712414407036411003011200000d40c034180c8a0070100b01c05200c000e0100d00d80c6640440442d2030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 111738147 1250 111736897 111736901
    0x305120c091302040e0a0e061b1207020d0806060429040306050106110f0a0b180111030c040503070b0301030c0611010f050c030618040b0c0a0e0901080a05060c03010522 74
    0x2903100c02800d8070820100e15200c01e0004e5016000303900130f8070054000604201c69500511406503010340292040e80c0300d0056007407248124000c0312510103818002c8650001c4240b4026101c0d00c61980101440495218064207030718001c0e1405000300c0040006000c51036408213100b240b1600240c8121501207c070402c3c807142e005a41009000900b000300018100e030744071044091007400340f000c0d01c070704000307646245586441100004201070700030b4000032001c1d0f025203580040411480000308145200900010180c0d008480814201c4000f0500344203d00741084208081c1c410109818a15415600d44111500d800c5c40b13407030200070400301028a1700000b9004858100d40d004d5083c042c0381443c0ca01b002d82c0740c000719501401200d58504100000a1078005a0300072038010244d940705480f90f000d0002c9a502c01e1450405000c2c0c0340f48810a242c0798072a409009182d24000350010f00d1f014682079007010009891003040355024001409240c0d1206030028040b118200c1d100c050042800c05240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 111739397 1250 111738147 111738157
    0xc080a0e0d080f0a08010f081c0507020a0806070e04050411090603070902040b030105010e0316090e151807080601151d0405040c030b0901020a0c060c03150b0a120501030305120c 78
    0x1102d0b002c0420f01c2c204080d0f803140a41003005094603010120303a02c030305080450503110310a2426a91182da07901d8840001c0581c1c0c0c0c1510207031454151300c2c200c85d640101e5030151640d480310100d58070240402c902070394402d40d901c0f548101228140227601740354407034440300001d40b4401441f40d09600c0c0400c002d43c1e001c11032800240b080d0f2005648072656412500d02d550000d00c5140d010501492486145180110703103006812041d007103a2000f90b05010301d4200030218901c10b44020300c00c016108030501c0d241070040c1d129001e824100400501c10b0b00070305041c0b40312540880e80f9980480c00600c5015a00c24180540c0384c454984100d440100914008114641851040d04646400144012b010082221405481c0070340503181140d200d16800900300d20130350028034000b0381c0380b0704c0d8000000c00e550401c070170105036450045406a10a4054041da50940c0d10040c0c80c0c1c000020503d1040c0d800194610b2801d10300101000103616680700501301d8864038000300c0583c5025000581c9004544c0207a072 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 111740647 1250 111739397 111739403
    0x61b050312270d030609092a0521010c0e03070b0a02152a0901020307030804050703021f080f01060e22060603020c100612020d06060302090a0f0c0c080a0e0d 69
    0x6031008120400980b14050f160103400003a05082c408103005606002e80341c00740b03a010000442911180c0d0030381d40d0b50300040200070700c001418400069265110100d4881101540b4004803401790325282c01c81c21248200c55120501076140024501c82e40c020428408499402d1540b5a8816104000300d0030700050b0315034880701c50000ba05020b042810780c28480d10003c0c1020b482d020384244e002040900d40500c940301401a4010407a003070002c1d10030345510f60000e100e2030840324499120760000720480708401c0c2c0c00040250b240070038511154403000403608090341074507023449035040c807070000e0402c013240020901500503040700c0540c2000041d0b101c90080c841203003c0040984861004019510001410003075200c2c1d1100e28404c60054031544c003c0300e0180d41c050302c511640740d09000300c6006004058a129a8442d0300001684075a040f4a105849030680000c8122980c40420100c0703100c0f828036410400f600040c18001151a800c440380c1c10000e0a00d440403a00e001c3c002107401240d00801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 111741897 1250 111740647 111740701
    0xb0f0907110118060c0e010c0b2e09020a080f070206070c020f0d03020c10030e0d031e050709030209070f080a050a0b1504090b09040512070303061d01061b050312 71
    0x40e03000e03c001c030745c4100c0c0c900e4400e40d681340040350f940c00111001d40900c40302404040c4581c001c102c000f14251005c115194615510200d00c0c841641c40c96042103290b07101c400030503000158000c0007580a00074580c045641e400107040e90901c01e00003580c58070001c02c460244244000f8403015580c42c9498001480310040ca01c070307110601c1d450000d44900c1b071750030298000c08904070307100e248074000d004440402c60b400c40104603030502c1c80d004402500062402e01c01e00300304040c2c40da11a01050040d144a600e42c1d0301c0b01c0c0c400b0f905e90f1040c4440e00d880100f024007040543d0f811203860a50207a01d01e500285400e40c0400d940c1c80300c04c0408010b01c0b008021a91160311065104c11401551000c1e2045034640d000801c10740340c80c0c400344031218600310340080c200c1e001444003400c2c5184240107407582c280240b03400114103484440303a5092044040100c135902009800400510b5407180b1038440030001079150030303000c18440c1d0b02c46a6170302603516a46286c00c00580055440074040c0c0d41c100042042c8405 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 111743147 1250 111741897 111741941
    0x306050a0b0d030207080c010c050c190806070c020a06110307061a0607031d040b0a030f0501060f03060902030c01031104030b06060c0a0b07021203010302010903081e0f0c010b0f09071101 82
    0x400707980c41d0810f00c00c188440c02801e030f00c00d09a6000380c0c2c0603440e45130448050b0011620f440f007042a036501400003400331044c14000451503640c1006902d2140d0303c4e0b900d0350350b41482035004110440d40198021000c000c01040001c1c644107001c410b90f1341040d0f0105000c2069801f8901d90444107401c1c51040ba000390b408501c602c1859031142c50b1000d600c96803e480404042c220041c030094500b00e50703070103030454400e60007000020038102081c5c0c80076006800000b0200e4031b40c000340102c894035038000da6003c1e1701d542c13010b000e501e000d00240e094128242400c010400c81b50b04070a2190180b8070000c0c2140c1010000038009482c6c0030202d81410514006a400084040c5006281e118044d030b62100103108203540e0024103441c1004884c1038a40584903c1e1030a40f446d41d5503070030396101d4a0b00c00f001d80c0c2640050004280010041c8c1004003107140111b4560b006001d1250841b25aa44041e2141101d4003110000b900c1c0d48952941003845e5203080d03250710000c00c0c0e4403030140400441d0008a000d000704 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 111744397 1250 111743147 111743153
    0xb090f0a05191701050402031c1e0c030f080910020d060305061003050706080601080f0702011407050408010c05250c0308180103060603020702010f21020c030301080706050c070306050a0b0d 83
    0x1148801e40f00800a00625145000481800c803801124005d41642c040c0c2d94101a10040000700c0640444601c1d101070181da0b46402d4001b10030201a40b5000709403840400c108243d00706001e0401d20703225140c9010b80d071800540d460754404040301c480c00b00690001783c98503030b40500c4d00510041c40d0054100d0701d4604108500c84461042840299103d000d84240030400381e2040c48000d00949059484450903160b009514690b03100250104040d5962754009000c12203080507220b01c03c00c8075484554640345055005801d498507241103c0c10010200280fa50041000020b0340300e018900520301c80b04882490074101c15645608060600c010206481100c5072603d03120b403c80103000c5c0e0f800e1042940e50103007a816130083c0d83c8001c0c003150181c4000e4854612668aa03c020008086118a12007914405c81c0890384409549040d0340c10010040c0001c2e08100108001481c092030801c0c5003e013100280e40d110403103030100511540d00c441c04079030f52601641100319100382c010700780032452000c6c0c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 111745647 1250 111744397 111744439
    0x2060a02120316090b030106050a050d0204170d020d02010603080d0504051e011a01050304030c0f051c0302071202070b030a0e07090606030209190b07031101020d0204080708060c03010b090f0a05 85
    0xf101c01d030010b080d2070700101c1c2c0f45a819050382c2c100c444a4072003e0a00c00003000541e01608100101c40f21507038240800101d04038550b41a002e145d0a44010704451114880e000703050941003100e40c019a03050003c20400501c11000302d42c0581a000380014068550349069801c1c10320040760410340e00500480d20301481410741c88815150640b10b0359520052201c0c0041d41d0032700044401802040c82504014003091031217a040190621800076140e00322051040e095000401c40d05030400240d01061742010841000301603c01920030303000814001e4644070151015120040884e80034070746514001c414844100704032806007012a2040c0802c0d030700c4110040c001d420120086219641100c155889a0503141c0c081c425141c03c81882450054951019101060070510400f032a660030025420110340c02d1020340050301040005c1d10510f46801e03041d07450140050b040300b080020420040081032241800c40351340c8a000c1e900408440b12940009101c18501e40c000380c2c10081200705885289a10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 111746897 1250 111745647 111745681
    0xa0302041e14010b04120c050301050a15120206030c0d150303051c050709060c020105040b030a0504050d08060307030b06031009060c030c02010b100c08190f1d0a0302060a021203 78
    0x101000c0222070b0308003003042040082840303484a84002080b081c0000100e4248a078030481c007501c4111482c42c0d8804c0446c0c00c507407017142c8a440b40c0303649080c640c0d00c08210701c5040d80100303110f012108010ba015000106075120180008003400c40001c0c100341d030011540c11007515020346e80c809000c07203540c0e0b04010304144d015103001c940800d0189007015540c54284500e5018800b40d07038800c20302c00d05003407083ea000041a40300340d050003000c1c0000240040110b000714030600c0c180e000401e003414079241407841e1103c05111003062091a204002e045d84000845500300c0303801034018100c540710400800d0030000c0c0c20074129401802d1854034000e1107415000169444043d580030070a01c0e01c0c01400300d080710b55000080e50f004c54007100c088581841400003c02e094050315003285003ca004c50030300071010410b0b1504012502081401591a41168600c8100c8010380903e0b0141002580029608081ca010003441864003054084001d4402c105003100200d0000c502da560307041400b034281e52070f801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 111748147 1250 111746897 111746951
    0x907081b0907030c080705030709170102040f0b0a0503060d0606030f030806010e0a06080c1e0c0105370903021002120105100f021005040305161a090f0c0f0a030204 72
    0x140c0740100318a0b5110380710f213541142e5035540d6503000303032a60f600440302c9900c068010030401049440104002d22020510b12840f580680010390710341c41c00c408900c5881c8581e0002d201c24034188505480309070020704682d480354003210201101e0216140c1071009082c5500050320524615003150700b0160000ca405009417401d0729103e008420050420031002c102d4000d0500042041002c90900f01d00380f40940320314101c0070480005000c0700000c030312464200c20041c414581d142d10501c000c001e08401203150100428042500502417107518014003007422000c001c9581e0344424030004e061090100304191042c502c0103554903010400c803c0d601c0c0781b0030b0081501c24454a610203001178003c81348031290003050b402070482e11000000100090030000e00c16005c1c003400700603060120b5072103041813020b540324401d41201161610065031002c200104940150750065051140c015000034038085070f03110488141284016802c00300e102180c2543c0700a400ca805d291810040d805070010101103a50 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 111749397 1250 111748147 111748159
    0xc0d05010f0501020a0b090c0907050a080a0603170c0a200a05040e0a1b031502030a05070c02010806040b0d02040905010633050a020115080601050a0603090c0605030907081b 76
    0x103281e80d003210702141248510350140e8000002080011540220145d001001c48183c9014085d044042101407000326000c0c4e000640000d0460012508a03c030b154001c7e8a0240410049013941c0e14154072050705002030145d220041540d031210002000f00300f0f840c90f40540d0440d210307903119501583c0341000d45e10046c4194030a40e4041035500706485403035504400e80008044803611516450108051056503010b03030751100c040800424400c40c2e80d41302d502245100113a90385001e4403404210341010303180004000c0c050025001503a03100e8285500801d04031000200741070400002680040322240080d0840d06280d8141c090103810362014044580c94104c141030002c10490840030f040318070030340045282000200c0c1303108a10a20141080e403034103000015604c2c0b08141d00c03204010042c0e001d0030a940c4081c0c014481420540744000081c141418284450007903030f07552800a4503c4d0142c0703c100100030002030502641004400c0c0106408426128140c10031040c0700440b80700f506c4028040da03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 111750647 1250 111749397 111749399
    0x3041e061e020708040504020a05190c0b01060e0108041209080f0303060a060504030b0403051b0f0705030c150d0b0406050d031d0d020f040b040b0324090304050d17120c0d0501 77
    0x1071154000c80340c030b09911201c801e1919040000304402034004072102070030440140400783c80e9031482520350b19594016203452418010741e14000b080c00e201600890100041240e11050036600200c43d1500181d002c00c1d004100804550100e0b240103c99202040d10b04c114600c0990095011000390f00640302901d83d0300619031543d8003a242841a8400205105458000613010911031030182c0103006000b1072a002082540c40110300e050b10140c105961500070400070013180c501089a85201c0c0030680b141c00b080e03081d8852089080c01503001c00e41c242d607203540c20040c00342d484d42d101c80007400d002415502c0c00c88142c1030080038025404502301d440e44098100101525161031001400740d4000c01000f103030946d05090101620078986d500d900703e610347d820100140e40511110b250100e20032a500380c2815000c4e03621110000141c641c11298104200520240c0c40d00418488081d400c0030f44481c1141055103420090f10921064025684600c1c062007404d00c08100102414403880c54140016 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 111751897 1250 111750647 111750701
    0x3030519020c100c11281e06030e070512030a2309010e01121109010206060405010f050d08040f060809100b031f0204080703030c1b06020d0503041e06 66
    0x41c088180041e83d0000f00300f00c0103204940f040d20700c00c500c184640401080c2d11000e00104020181c402c0e0a42d200c040718482030408649a82040001408080e48500007040700c2d691060001d145401036604064035080440030040007044800c005006c00782c8080d0841280444458a90300812065070020b043c031414140303180e5016129906d581c0c00450528500340d0a40010f444040031220141e05015185503d10000c9034544203d001a00141461036900c09100740028184040144142d102d10320f0180103200000680e019001510026940110071440508241d04540640c0d8000d44000c42c9044007c515642c0c0810f04a0240d01e0f924111405a0b0001c401082a81e03d050810354041d0f00c84d403000e05169040c0c60300c03022000383d5504d0061074251105070160401e01e040d081540031511240c804030402c44800c0c2a005500c0401407040c444c4c909111f0001c6d01c0e4070112401070100040070001c54248549084523507454091014400c3c000c0c8514a480070103445034088548000303086c00d508030f101f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 111753147 1250 111751897 111751903
    0xa080f09030a27060315120b01050d020121060f05040917130f090614060403050303040807080c01140108011a0d08180a0608040b0a090b0426040303051902 68
    0x5035400c0d501450030200c00110482c2c1680c107200c182c0c840144107940c0d4032041c01034201c042c030180041c0d40c1d01080d20404080e2030b031074190b00c071343c003064072242d80138125004540f14400083c107540040325190310100032400100d070f080325a803441c483c0150302c10b803001383d0f44011580001f0403140c03d01400b2020903a21070070041140c21200c401340541400300894400a0201c03801000c41e0411241c1040a10341ca4480712085040f03d604008500c0341c0e180400e0200690389001d4994403c0104c0b0600d25040c210703602c0c60746900001d400204120300226042c004c104944065804450303060340200302603160050500703095107082c820780c031940d4030b08416080e520150740030041011070003030b08000884c2040d5440d8052030340041c10105504480c5e000000050780d80e0420400100a40e555141450529082072a107103030014052081151405240c2c000003038401d01c105078019049100e50003087d440b41c3e10051581e040c0900303e00c8002c03000801008250704017001c2d10040000d000301c0f0100056020b4181c0c0d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 111754397 1250 111753147 111753151
    0x30408060c0f030a0902120109050601090f02090307120201120e0d1101060815060a0305060708180616030518010e0f060105120304030b0a111c0507020109030e270a020a080f 76
    0x1820b94020030014294075410703003180c0e000600c060010705500905084081c212494001c00726803c0d0004c0004209840c1035000b030410300419580304603d07200300a000240d5a611344d10611034001035100550056a01910031401500c81c07880050201c1c002007410b298441407030b42c107248007080c80003c2c01e9001c10014400d000a84402d1401000c0c6410342c3e40c4003081c1d044008122581c09003134184040005282807001c1801810540c0f240d07141403d10706d00c1c00d85042c00e0b00755003040341c0e44840c0800590400b0400603641030205405e000480d500d4000c40c0c90703200d200425200c1c00942c00d088081225020002c0d18070840c1c1c0c1141c040c4c502c1640c0b103a040100c1110481442600d5501c14030087c4086040e601200b600245100b5000400747c8041a0b107080940021a042a06404410b20460034180900130943c1c48074140c8020030444803160717405000805490700c2d1600510604004180c3c1107444aa040d42e0f803c8262200c001e00d00e00302400358044c0d8450510b94000543d10004100441c240b0918030b4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 111755647 1250 111754397 111754417
    0x902010f210e0a0501140601090e0403021207030216030305031b0f0301030204050601120c020c010914150c0a02030102160c0501020a030215150907020706110a17130b0408030408060c 80
    0x403940c440091184030160058580842079405031082d43c0c0b00141d001d101d01e004c4080d110b40d10419614085c0300240c00300342d0552041d1540e40d1100d0400001a0b400301d900380206149089050702e600c100c1c10105c0c500004081c00d0381104048135001f00505402201440c82101c21440d420240c41441001000d5400f4140f2000242d03001480180700515080d04615800401031400041c00400d2072211001d5904241101c400b603009900440c0d029603020303107440e0107031500f2440f091034241180b000ca001000c0c88419500c442e0004903480440c1401480140074842d0010000c2d500c9070b280da0180342540704500c50440710607031400400a050350012944286498254014001d0040450805075050400900640900d0304801811240f5a12010300c14010f0b0f410f58001e040c81030900c1c0014000030819003428a45174440c1020100069500ca003086280800380040e03a16080306611303c0c219603240f6000281900004100450010b1000000d801118915011185c0548601c42544a0740c46000621 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 111756897 1250 111755647 111755687
    0x1020c060d0906020c15011404090f1b0b0406090518010f030b0603120c01150e15060d1506021c0305150405070207090c0323060102031b07030c090902010f 68
    0x105400e00740562006480600980026150194410f07030b650a10010f840c0300800720050000600094146072945c2010290548041000424030b46843c04000203008000304042c582e03980d54251a055144608020700f0001400ca0f1910349440e005071850341c0d58090680196003440c0200b00c44007080310414100d540c081c90810400b030542e00d40e01103409000f081144c06101e5080f501c03020300c400400800c88590940000a14565250451041c02d00b09500c42d6441651903c107011200304400440381c0441d208444103580c0f07028403029000503100703100c01e68803106841c82c00090210b80210382480e410b0584100c1c000c1030803480800394101c45d402d58541000c002881d18035019410b00c2e510a9420038618011152229602c651940543c1c091295140019440707a000c908001c60701d032580c039825110060b0140e02c80c585040001c3d906e0060301c032104000101c40001503c0741d003040c803540c4082d5400c038000c81c00081d22158054007070125403e0890000d500e40a40e0740000d0320030070400029140038284 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 111758147 1250 111756897 111756907
    0x50612030a0201231b0f040e040b060f03011a01030207110306090303040b010602070b0a03020705010b03101a0103090f110a120501090b070201051005101b150b060c06010e0403090b070b01050405010501020c06 91
    0x2c191785500800001d80d551101000041225101e58a00d140301e14403130210001c161800b03100340682041d0440300c49000740e040541032518403422281840b020383e001c3c6030058581d0071501f010416002544c5c0d48503094000c55007440341c1940040b00031449903028ac0c0030213000386d0303a8413002c0343c2d642e0300e81c462110803880c10301010590750312940051000500880004c80c500041d50002400d2901c81c070030205089a0b2098600203803401500a610240300c00d080801406075281c8601900040140d0000c00381034019a2003130542d5514000c84004d051b610503010842d06240c64214000e02c1445ea0070f0300d1040321880010324851050265138414600e65140ca403034649041e09205030f0004035840b210038410304a1121000760940c00700303104428051a000010000503500c108101d81c62504a180101410025400c9249000400b9411030b82e82d00604c8080350764908040303034000b405401c40e0b064400005284014092004103850595400f202d0400c090b907a5400107a81c0c40c00142c603c140c0162046c41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 111759397 1250 111758147 111758191
    0x10b0a030b01060503040807080c070302041815051320010905090405150a020405060a0302070611040f1406040b0307110708030a140d0f110307020706031e050612030a020123 76
    0x951b410600c507214075820040b403607850b0f00365900310f0303043c92003150710410040080d4a000e0280c0c2441466052100342030304803135111a541e000000350701c4a0550781350004508011000c18158450a800915100003180303004c49c004011103811110031b00161101d80085800e180c621100e0340165800740c01007030002521140079007500d0000b8000040681c5c203000000b141d44170b0301c00806801c1250780d00103a9420380781c6080c40840e1451090f0130a4950309200c140321761440f03035501c0420390787c0e41500c94000201c0d150004283d4429508040b00b00c00020040c1b100150b04611913115409210f02520001034449000c150f032406001391810006090070030500c01a943c3e040181038640c8441004075208030422046826180d1141c514003c00c4000800c11400340c0c1e043c0308290180c007140c0b03003e004980544201c1c0c08444102540350801560701c60101e00982c1d01c03e08ca02001e61820000d07607890b0b9008803c00b90080c1005420181c62000d014087c1c0683ca0300c241c0f5062147e100306140c0e9143ca04086 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 111760647 1250 111759397 111759407
    0x14010f080601020a1b030501060b1e07060204150806100206042102010e19120c02030a0212151602010e0307020604150504170106090609021e090f0909010c02010b0a030b0106 76
    0x601040e06601601c081c1c2004074100c55405d021184090a0b0030f007413140303185050ba007101c005600603403c02c001032016030500086104000071080801e125503840c1c1c055418804020700c42e550013010b03114042e0010307550341900482c14a100d203c0480e803440e02c62aa00710107984619042340c006000d00941007119a06482d03400780c40490540038800000c40441c0114414649500c3c207055a458001d5030000200700403000300c2a20801c1c2e002c1c50440c61460103540032907516046100020720a244841e0b003c001a801088000f000030000d070348024150a000c054842003816500c0c1c04001075081503000c88004800004030b0300320f90b03400380c61b0918080c540328030305d11a1311030b503200d90b0100701e800c002c00101940190860401200c043d00000380340e615103180c450403940654030003400741c1d00500c00340c0403420645d82e8211400035100c080c5681c0320392040005468000b0100c209903c07080c80710502c44805415030190070030410a400070000c40800d03130100640001c00b0f1000911003070504005020291080d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 111761897 1250 111760647 111760651
    0x4020d0204031e02040b1008010902030c0f13050f0d0b040b100b1903050708060915040b03030a0c1101031404060c031409060402030606120c0d020a080303010b040f14010f08 76
    0x900504241e2030340c0d03803400c507044541951003081d0b019800c19420351800d44070750b0312501012509016001c03a0081c000d004000d0502c28480540d6010000542038081c2d0411145040e5400e1030b403d0752003081e4075807800b207549280500c0740500842803c03d54242402c0e000e02c40a9034100c1111303041740c1e807260350380400174400074020f41c40c58980c12000501c40f000070000e402c4013450042c0a000202106070001e0854100a185004205601c81032020fa511810000e0b03402c2480d40d0020000c43c600d03040805c0c0039100c1200c01c103415100019507901000c2d8400090313400c661040b0700e8604802c1090300114160b0340d042c00301c0c80400002e900800c0004199031b000c040c89046d43d0402250180d18042440e6906400700c81d4080e46410900801045103014001e643d401036007200c0041004a10401440c0c7c1c4160720044140a10341c0c81d901c440030344da0360303242503001054907030210390356036841e5500a07900c0e810a120341e1241c00d400a4002c2110459401d89640038001a5104001c11410810481d451900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 111763147 1250 111761897 111761917
    0x803070204020f0d2a02150a09050a0c0f0e0a060b12221113050403020c15040b0708120106050702010c0209041401090b0627010605030603100608011d0c0f0402 70
    0x10003005810500b1800380c141031801c00c0400b419030318001c4440d1441000001100c0c07046402c80900c047c0321025010080e41c200e80100000501c0c0320007890500d01d032400600b4058040b07404030400246104030509450142c503c515080031140d12881b111005489090040c10f81c401c00621407108c0c1c1003c54005140e0002c402d641070440b445003101c001840f0043c0850554408469a04014060409003800c41036603031520000c00c440d10380b42d01c009413135401c2c0e040c2c4280304800f507106000c03210f1281020355002c0c1020080302e0340c4d141d541340ba0010040e8000150347c003010300090000516a401001a600440d030103848804039155540c0c20441d00d000010801c5801010400750403001e02c4091050301e4000e0f10810483c1114184442003020b90300403503001c1c40411a1001006400300f1004101d81e04590240c2050b1351a6254038002a080c0909420380166817480c2c4540085c01d280d054105d8a03081c9241102041c040e00d103007150079120800503201c40d41140c0c0c039a060000307a08050340140310040f4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 111764397 1250 111763147 111763177
    0x50f012d030606090c1b140c19060305130506270a060609060b070f0803272b08060d032003030604050a06150302070c21060e01020301080307020402 65
    0x80c45106100e60300015030010384100340e541c0340078006021036100b005d45115250405030100e020340c107a104030503203030144018480500e0345c44400780d0701e03420805404001401007508907840a009020301d480c00407482407000007400e040c041021444400111400c1c203030404041c1c007056441220802c2079400f003018100e8005000ca401c8000d403141401444074203441050007203049854400841d0940d90b0325049a19403203800c1007a480010058858a60141c0c0c0c000d00007500da58501069102001c00058002440c840031160b400d52000085030061510792040301e40900ba419a45110f041d42c0f01c9420300d1000b0800f150003180c1e480c07414060384c03156544245001060002d128a4403400c43d500d00c1e01901ca113610200900045103000d005003540034148000030000c442c0351a0240324403d410140c080c0500d07900041c80001c3c801c00c0500f13000900020700010081c41c2601190351185140b00100761542842c151094230b00d201c060089034100c440d104000c5040441580800c0001d41c041101055025 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 111765647 1250 111764397 111764459
    0x306061418150307020709020301081b060f03040f060e010506060d180c0b09010801090905031917010b070b06030106050901060e0103060305070801021b12030411030312040605070f0201050f01 84
    0x154400c2d451034042c403140140c4940364103149401074609009030700495080c900510041c4030342e020006065201c50507240c01c1c1800104d0324400f180765840754043c0030f14083d00c00401c000c144903e0307401c2140407622a44007000803d907002c0c60030303088401c1a50219402801000b00780d42c4c0411981004a11618201c10007a1a40181c0da41c101c07112015400403a900324085400f8580e5a0028181401003e4200003803010b10059035610740caa1180381d0950a00d6480f05070f801d81d1407031041c0b504030710140d00346242c6503c558540c0ea504545070480c0c10300315001406400015000d04060140c0d4085880c060720b0900280d00b020003da62042c80c4501960400d0350341c2d0000004184200319102c000c01c480e100059903092582d501004011031501e00780c4450f031048051510f006222800c803903016811043c89206050780d100000d003188030300c800e00c0e420740720041c003070200344006075105500848441c5c40c4c9100144c4c19200c140d00362441180c11a0041040b6801045031300b000034084419500702c011540103071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 111766897 1250 111765647 111765649
    0x803070213112703070501050708120c0c0a08040e2202060c010f050f0f01120b010521161e03031b111509090717070e12011d0601060306061418 63
    0x40340070b00c0018114403070400440e030325404c0038481074010300f0702032038074a14002850702c6140040c41003003a000d140486800021750a4030031102078a40b824030200584000c100d40e81003000702d50308580500c00d41c4801c1741002c1910f203240e181c1c070007410000020782c6041102054017040310075001805210030039500c034081104000d0b110f200b158410102c0d21018001810f204c10b00081c1110142c100c4018040708070700c100085001021090704556003199020341e5400c00e80c3c92045041001c180b450350324132840460b0f041244070421103105903800d03120f207031201152189043c052080c40313200143c007242038401e1815181d6140443c10012a0080403050021103c92010900403a4202808520088041140ca40c103240401080d40c0210380c501c0c0c9601666800c030310307480c0d50a00140910382801004c08030443c2544030050a80d83d9a0311210003000080103084544510b8044904278400c0382c05020000705039140603104c1c800558085688070032400c2103400282580c1d900c0200d0002460584420070009 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 111768147 1250 111766897 111766927
    0x30b0102101401140108040f2402071202062a07110307030b04050d0503060108070807110303070903060609020705070501080c04090219110606150703030e0a030203040e01080307021311 81
    0x1840c4034841455600d90f00d010543d41020040311881341c10030070302c603080c00302080c3c0410f03650084c99040308058400a1090380d12070a0139588541000304c146c004600103003440740b00d4a000400d10120703029100103070b5584c2354000303640554001d0200408496803030020800354507005051501e10641c40041c1d012600c0c0b00107460b04940382d104442044400c0b003004100001070107502d15401c0c042c20300d541582402d40003c0c0c068074004180f50204444400010900c0d40310b140400c01c5100b1038000d40e682d0f03040201c001001c3e480a404152080c5051040000d01d0400d24400c4950443d003000103400c001d4103000044078111800b411003a0b0340344042c000810640400e2000384400342468100314126a181040035040044000500d04a42c0141040182588445001d501140d464407103145d030300c1046140c154001e000d45070340055248140042c80c020107030000010310950b0b4014240702c5041c0ea880610380c0e41da02c2540002904910389540c2d0720f5034118141c01082d807440101c000142040404514410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 111769397 1250 111768147 111768161
    0xf01091109130c09120206071104140a05061005041d072309150304111507170a170702030f0703051606090623041b03050304120510021801030b010210 66
    0xb0300c035620b100c0b80c0401900b081d0004002d11150040003a84802600003403907034011010040c1c2000744a05a09000c0e607102d40c01525902244100e000709070901140000041c001245c0103070041441451480c1e4450240b4251000c45003003130584401c00e82d10b40c00d42555240050120018804c40b080d000400c601d06c1c0070011050300021003902d0f1241c3c105c204010600b90b4034860341790096001c00512010440000d20102c0d00c4d0b0080c2c580e90500c0d11034086420b001e218101c07001d4965406003282c101d00711404801480703088611390b00c081111044600444510030140c0e14007016920410015841d200310fa40a0081a4020f0034a40d04010481282501644014008640c03041d5245420300401005104000c640744616620320740401c0788040ea0408000c010300040c140d010b6803003081c149200095400d101655020701035a4807181e031b0380622a1076005400048405000f00500c040c4400c00e40c0c03007503640684502c0841040380d84040015001030034003510140c114000d40707042450ba032031903008102c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 111770647 1250 111769397 111769429
    0xc0306120530071202070909120c020a0b0c0106032117071707030b1002010506031002030c0706021207020c03010b09012601061211100c080a0509041d060f0f01091109 73
    0x30303001c10500ca130024100001707600101030710740c944143c1a004c14020078400d0f01d080468204829500920b0001070940301c4190b03c0765008110004a111514606400c08807c6a114504407040f4010054030301c842c40c1d400c07289100c00521202c880c900e050305150003058001090303003001d004031050340c2000c0d120300000722003c002003912200445080c0c20000300c00d815809591000700130b04d0410900003902e481030b29800c4051242c010000c500002882e0f03040b901c90a921030300455a4490714074004011500032035140c0054000e4060711541824107009410740d0f6800240000e10b16803c1011088400d50641d29014600d0208000d40402d100244184800390a441540c41002074103454044078544408811500682034199100300741074016890881d00d0703602c00e2600c1d841d0021000e048070603000c0c92031426070007401c000103146000e00b9011036a40d0032840c4800e548035a41c5803a1081004901507402c061103c864200400c05600306600450307401130700503001c41c90080c15000107102c424009440d9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 111771897 1250 111770647 111770663
    0xd03030209032d060c0a030902010e060313151103010e04060f09030e03100b06040b091f080604050105010806010c0219031b0603051006140a140d0c030612053007 71
    0xc4001d0503803440004048900000205010b240c04850f0032002e000302d2614501f89929a0110021a801000d10804901c009888680c40f0319050959208010b4a5001550308480500c0c09004068060083e641c0c410202c000c054a507920340a49003000c818010410740d01d407591180d071003801900500468080b54000c6d075031a2460b048190405003402c440c907400c540750f00e24140c407406031915868195000c40b0701d1015401d0311841c410011416903007021108024403d0141c4c50b00c12035a801c140054040d00080d0342c100f10681c0c075000107540c40340094034024082162100c1c000300624140d20f034034010071050626000502d0b501c3c0e86121131050301c10010b203000804004207102d4541c1c103102e115800320301c3c002800000d80c80c0c61006803000c00c43c1d84c81c0d0090001e0003c0c02401a600610082501151503d0820360790302d41d18290710010441e0750385000000f81001000200d548100e02103103d481e0b0010094203c52100c1d010140f861203000c1c418011000703440040341e400b550070401500c1c00e18007844013 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 111773147 1250 111771897 111771943
    0x90e0f0421081b0a020c1002030c0304090c0f03020403021c06150801140901050f0f0709050924010203030c091207080f03030f060108011a0901020c0406090902011803110d0303020903 80
    0x1d0f0034040c1e00c0d081c04042e01802d20a00e2104c6a0005007941054400d442d03c1c240c01140c0d9404078210311030f40c0f105110501c0b000400103011042070b4080c520300480c5998007140d542c03c2c0c13002201684694440654004c9040d41c04001608a8402403091613102d1360000603170341c0c2e00354400c001900243c3c0c4895202e0350340d805541078000c0e160454603400345a00380200614601420000c0d040764000e09804a9401110b000803e820300400c03441d4042c0c00000c28100007460300c1c0d84000c400c0030800408020b1111441e0f510081940000301380c90007003a01080d06030919180e00140403d04881508a15040c0b0400c040004c00100601201c0300410720803001c0e4be540c0c83c2a01d02188507400141c0142d04100c518001080070280c21051065003114020465031f075020f0941c0100e18105821054540c0280303020400a081030b1640d0117020045d100303894880f030480000702c6064a00c2e0f02840040d03d080807121012030380c0e19000c81029a1540300341030044c00d00c1500000f003440d026a1090b4070356082c0c94049 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 111774397 1250 111773147 111773161
    0x7050405010b070203060c07060e070b070203100b010f0315050a09020309070602031207031a03070b1c0204050f040b060f04030b0f060d12110708061510090e0f042108 73
    0x1441d0241c00c800034440d16001040d4082661000b00401c840e40d5094089500c01c00c10040d0340180720031040c00e60456540c0d0f904da0400c1105580820012071203403080b41d822110311502400b81d0408104140c403000e81d9140580780035006400d810201c00003d8030b49110119280c1d0300c160180002d0500c5202c016200e10b0f00801880c60b00e58590050001d5500071300c030950001c208546080d0344a02c8a00c0e01280307501c41200c4801c01e030003000544c994180108800403c41c100038902800020a0500841b041d800e801d0421400301d110b076000b41e94221030303040b000c10b05600f055040a40e801d074029000d40c0c50b08280b0001e1600d150841d81080790700d0070403542801003500d0704110444d08104100c4030002d05290b00d40d551411101e038645240e05001a2800c5001400310a000001c0207081e0780b003d481301c524180e1510508449840400f501c03034912160010206131003419000280c0303140b4150400d00303486052400f09502c6c00140101d815042607202c2032135142c680c000040c44454075841d650700c5030030490303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 111775647 1250 111774397 111774401
    0xb09060610140708091f11010606030c09050d08041a07030f05040b03060d061b1e0207080d1101020702060a08060301050601030b060f07050a020d030f0e03030f270a08070504 76
    0xa1110410030440d403000c040000e1005003216066540306403056175450f41440811003200703440040b4420111042175100c94150019200c00200b03640000811100e511048143e08035901e0340b200d4800900128401c1c49a030a104403958100ca0049124901b015070300c1a9060803c005030000120040000c2103200c101500f22410b00e01240740381c03c0172070501c1d0910400c0c1906000003000349200c4c80000d000903041c01004d900c03582c5078900c8040c495203804042500605540c40b02003103160441310410b0003105483c03010854a060b1038903100940084182e5580844902108444900039558200b00b00320041c0e030394400a10107500291146c00301c038a06a0101401c403600141543e06160400280b0507040e601c0c401100c0512401080c4161206d4071420140d01c0d00c85d02c0e04009400074003800001c4103050300201441112601a0f40302e40c0207101000506450f4062605052a07080051100c007560081804c03010000c1000c81e00c00911611603100060405075080e840a84250404101400f20382424 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 111776897 1250 111775647 111775669
    0xd0206070207140409020109150e031c020307030f031806050a05090a0503040b1e0f1308010e070e1306050f16030605030c0415091118120a0b130b090606 67
    0x81c005055154505818081c4058a182c507480c40340340c0e250034070002c5a01a4600c80050140b0084100c1130308071310100940b0080e00542480d00c04c0c86851400a644290b02024aa14100b20b6002e0350805003199015680340d07050386000d2013459103501c1d0707030360249a19050b5007680c00e02030000420f080c180b4219040c11503038003800d115001c0c0c020038a0314001c5940001104c08445001401a0303440369000500c0c0404612504800514040015100384241c4110080c01c50342c0c01c490103e914840d654040c0130300700c0e1842900700465400c40a010030040b4281c1e00010360204512485c81ca41c80300c80d607112002c5580031182c1101064a03081407007241c0349a0803500a0300c440d83c2c01c0401600d42400b00281d998403c42c3d889030b00c183c1c0c0703440f6404140c100060b012401070403806414001d0600d11001c00b903841c1c11089100c5100940041055100c0c5020b10b2338180d00b0510760007600083c2d459841d40c907100c2c2320080034220400c081b040c5820019203412081407103a403d00014042508090b41003000400c42c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 111778147 1250 111776897 111776911
    0x2040e06090703030f020102040905010f05090105010f09150e040e010f06080304051509060903030a0302180604140108090c030a030e090901060b041811030a0203040303050105041506080a020415020d0206 89
    0x46010070200070030001d40b1000f07032505401c026000b60381080080340039104980002080e02e0905c40002040c041440c4246c0680701c1c225150030150307880303600440d2044002d232030590000300c0c45c000070000802c401e8a020712600c070501e404200000d00002160035aa62045402000da644400f1030700400744030b200c0d000c0900041070245107494074000001e0001e21110f48984222000055058000e90b180411606143e0010301500e848440c0300304050001c0d0855100320703102402c64140c052807442c0c078070121815900c100c40d0300803c01101c40b004542030b1400404480c00d91250b007990518a82d003c00c1040d80d40c51080c0c0c1c3d41b604041c420003d000c0d000c803002d4441f084c280c0c184803060100b840070405540c04ea03581e1f002c0300108000d11011000c080c008100001c2c194031400410b1040b1004903400071f6101d107000392010b004c5640c0e034205103c101e401d0740443c0440182c59401c18004a40318046607a04128501000f40c2856200c203400300a480c0094034103c0035921400d007000c0322940521106900000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 111779397 1250 111778147 111778153
    0x50409080903150112020f211605040203010b04090b040f06080102040f08010c080105010c030c020402030c0406110708190201110105090a0219060c12020115060801051e0303040501050714030a05030402040e 90
    0x450180a41c0c5e45903a1550300a106483d105000f049030348461404140d5030400c40782e210100c01c12440c6050711000d02c0c0c05c800c50400e1f03c140001c039483c105802224101d5514010301031825203020100001490f04489141c0d00c5620741040345002d0115000c0c01c00545680000160b4071480e010901201e03a0f403a074065452a41020030303045083d034100c0021411658207080000210380a807500b11919038001d41e0003540035201006100d1002e0381580580b00307031200713900d84a49a06040c90015645c128501c200020350b0700800103111050101803a4020b607903c10704126000c204010051400d60700b0803203506040e0740c4031000c0e8009601c1c044058025042001c0490039a042c1000001818071240a20242028005500c01314903a0b1007580042e500381e2055001c10282c940760503004081c24002c2c49480e218016a054036900f008035400340d11a600e074000e0003585041c1c5010010b44483d00040381c1a10b00031a26511484545c0c07050000307001d41485603031042e5581c83c081c41004200c4000303145d50ba600c1d038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 111780647 1250 111779397 111779399
    0xa08160501090e18030f0703090323060711010608030403050309030601061404090b060702030f0d120e1c0c020d1a0f0906040f060204090c0206041a0f0c0a090504090809031501 77
    0x640c01d0f44038203030040080b40481010710302c0070707280070715500c42c070700b18020002c1d0001092801d142d40b00e0000c60a59108000214004c1480401c1d103215901200d0900c1040d0000808959a43d00a510044405411a0000c10401d68406100d0306540281d80191010340001800c180d0074601801454050041810000e507503000b0585201c00d10700503400b0303440e400e60707490034200750035500c0001f5200c0300fa600a045405450a44600c04d0310f0303808000340d10700481c10000c0104104030045c016030314180d440c04001c02c8142103e0003504942c0001550f00710501807170100120142c0c48841400340380b2801010203000500e40c04043c0300e1b265100524075941c050b00e210521440c6540031850076046a0808401a48003240b030070042c1c0284501e41c00408034a152441500a403a0086401c0c0c1c801ca00031983c44017500030490109200b00c6045517402ca200940030001003001c0c5c0000090203444819190541070395450f43c0c0031800316446580c00b950803d0380402c00000c2d0745000c0bc013030800f1104800d40c8035029 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 111781897 1250 111780647 111780659
    0x120612070941090c150d060905070c021e0405040b10080a1a0402150a0306060e040506010806120f070605041e0b0f160209040b0405061b07030302070503090a0816050109 74
    0x10011000e082c50300b504034000402c00d030780c3c4108562409004028400c40e0340d8804948203000b180c0c460f0180b44101400c11a0000c1d0401070341c800d8901c502002d407540300300165141d082000d4080180a55000c029100200d03011545640c070076079216600c660a0400076080a0b1a96103d5044591011129078080c00002c400111201d0041003c00100d07810329680361030f64800202a00d01700141082e1920001c00c80d161030703581c16040700c01280c409460340d1030200170460034081510b40449000d0301040c0c4090100e40700d410408102010b10701c6d04800e079454040305109050402d40740385e0013900011404038080c0560503100c40d0058030b20684440c2d483d1500e00d03043c5401498040d81c031070500e0540000c1100580c1440c9032a012000a41c001c0000100b4601340c070f008005d89030300787d405554078410301002440380340b0201807004a02c1255030005050001c1d075034046003c1e5100f100d040740e850009200b01400e40c3c442c014400c004d0841d4030081c1c620a0604105802c0d002d005c1e902290412071192810011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 111783147 1250 111781897 111781991
    0x90807080c01050d020313020d030513090504170306060c031614030a0801060311040806090604031407030516030528020139030902090103030c0203011a01051206120709 74
    0x562503484c4405a2203550b8042c841300900b008a038040d40102d0b40254100800d584403004107200b118079000450042d0302d0765058400c4440454004205002d4401c0c02e0554645100265038010380043c9541d20348448103000f42c0c290340080c592441c5a80807880c203041041500c10405810050b032100450800154a8004014150611440041c155207800c440f060004035400c560241a078203086034441d080000c0c200d03590702002c84003a800656502c603001140010b120803a5240303a0569110741c2011101206180340c0c91150a04400744501049420b1001451401e00d10601d40f20340c9012250751440392020342520100c02406007201c400e085070a0f24034160380843d00403440d8228001004504c2c502c41a4000e0502480c00fa501011010000040650102c13a00558030310a60091004046105800805c420b81120440c0421000c0c060394200010301442103600c07040c020040390b00c000ca607444050a000c059081260b06640700c944070390342c0c14070308a203202040c1c43c0800300300e0001c0c64451240c85 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 111784397 1250 111783147 111783157
    0x30f08070f1d0406060e03011104032a0e04050c030d180308130f080304080106060c0804050d1110050a03060e010605040501050309100f09020f090105091501030e0a03090807080c0105 80
    0x700380403408071002c0d140010009111428480640100321450b2510000b42929108031220ba10940c2014100040f51540c41e0a8404596001c101000e000044001c02c03002410304401c00204011851000201d44080440321805039029902800c9d0201da240309150400715210350000606c1b410f61030114048042807184012207401c800300c0303070b101c65064400c1d040c10141d0740d204444d2007040c00c6003c281d0362004401401110300c940001c02c1307807907990f443c00c1d22081440c20300500328034014001006141440c00d06000224803e050300030a40c3e002e040060b42214a554010000070001720b240000e00350184240000780a1744503002c41c0b00e6150142c01051840b0b00d009481c100000803020802c401003c020184206c600c00000307010600c2c0c0016010001d10f00f06006902c0b5540c207048034030803401c00c129164161100035001603180e644001903c12104122400141050b80e914442c0c3c0c104081070050b011080e02c40c0e6a1001e6052400c01c04500d0700c0101e420070241d40d000701803c0401030381c010003116 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 111785647 1250 111784397 111784427
    0xc190b09030f0303011d0901140601030203180706050a0e09130609050f070e1e0f04120e0a030c0503070819030c030905100201050403032f070804050a0f03030f0807 72
    0xe55a021240200741000903400300b44045200201c0046802040e005410080714420304d660040c699900302510b00317032490100b8404d802440000032403401e502c66002150b1008503031810880c2c4100100c90300e86170444580c040c400003a0049802002c1c1e039844031907c0a011011601c1e00c45070700b0040401d810854030020700900c0f0329529a054000c0003000e01c48910711034145015a08403a540702c580003c0d14204a40e0040000384d04525402301c003001607484c40c007410455005c0004c80d551035503a00a10003003051102c040c0b010b14400c4002c9642c80d039140b40302951060201c3d140b640e25040c149441e1505507084a6910307040320300860010f81e0004081e0a6440e0903291881250381c2505040c2c51981d1280c100d10380181e0a03400c07002c0c0c5503805400032801288290360400280300d6071050702181c612502d0512111414100303041c21400405000b61401d42d0090442524081c1c0d110000f441c8c1c0343c41640001c0040c1c40b5170300208141600040400d842c0c000a0030300c02420b140130070b03006203842c19a510305 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 111786897 1250 111785647 111785669
    0x705060702041103360d08091c1d04020909130206040506030a051501080601050f07060b0913060c02070609120c030203010216060518121602040f0e0c19 67
    0x104203665403600155810300300d007807000760780f4204015000c0001d01c60015043c0d00e2566603c080d082e00c800f80400503003000207003014000c16154040700310b87e0781801400c18400361040d55611040c4481d18004080d400110341c07a22000050003440310744070501242c4406104d140b041c001c01441c0d440c1c018016501c800040914842030700280b00040a9008a4105a40042c0d000c01001b0481d6a641e0105008400e14011a480e20f400301c00116443d0800f1160036001603024802201680012000741c100c50b4480c0304d0110340c40b4142ca006c10543e6108452043c0500b415200000a00040f171003491241e400a00c094500d040c1849000f400204c42449001e070820f99800d82c180520804c0c084c028003461b8001d0080d0341c1c600c06001e01d480c4807060b200007a20603e00d00004501030608050a24200704000c6c800741000c42003400c0340c2c1441e50803401d0220014050b18001030016540c52080c0f032a0f0031480c010000d0001d94803440710745050716000205006c1c0a41800031f2080c50048003140301100c03660044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 111788147 1250 111786897 111786907
    0xb010807140118150f0e150a0509040204030204090506011e0501020a030e06070b04060b03240c0313050a0c03060f0203060109030204020a03090c03050c010201053d05130c020d0e03070506 82
    0x101500b000c00d13a00c001d49a000080c10302c20b50607840384c00001009100d0342e9190540c4000020003102c0c2d00307000c03681d24610074204042d8001c40e01a10280c24900030050006082560301e13000f0034103840316000708840503088400103104641001010940d0081d10303124061700541001d001030342c0c0300400388014040c41440b1101860503070b102d01c1114481940084000c50905061034200301409469041d18403a008940041d00c0b441e909481040012041e07800414440e00e81d90f4131449298009030000000703045880f0b010020440800100900314030810107802081d2850400310120b07410780101402090040003480813507a801200300d0185d940490780140d41d0b44002600341c1c01000540d5005041c2040c030700000050201c0403e072040c00780c0003030300280440d50b503000c42500046141074116140c040c0a28581407805207000300700d035014031030b0780d54498019220400118010040d55068428030f4481e034200e900e0f1941409a000049c15074200340041da20310000098943d00d0310b0003814007404011030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 111789397 1250 111788147 111788177
    0xc020d0501020a030b040e0d0c0b04060e0303090c0906040b010519050405031207020a0b0306060706050a020d02030a09020a0806160509040f0e0a1e0803010509042d0b0108071401 78
    0x440010554010021990b07040c50f00c40c06009002022a198410303441e1001c829880c00300403c0c00b40243c20251390300c485501e00e6070f90f022041007010308165000d0360354030165038000340108015400380240500410504a000041190310940286000e00460818070108131690b0000280d0f00703460b0b100803850800c1c00c1001021540c50096601240c5c4c184902980a41ca100b1448010f209007402a103448c1d44d041d03295441c440700b910040e11000d810100c1041490b02107000341d404603401c103c007140c000d07140649a442c40802d03038100f034901d000b826645802c1e4070110300c3d0050010f0300408500c0f02615861600241548102a080e032107042400b000203111015540c8582c0a0f0030581d80140301040503e049404555641c5c802100032500d0311460303041107500c4051281c0e40750000b540a40907510350303803d240a014a2200191049400303c019105074071500400303c0310302184102c40124004007030450b0400b01204813047e40480900c1d0040c1c44203001c0c500c40c000926007001820b00300410120302c028 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 111790647 1250 111789397 111789409
    0x81b0a020604031e170d0f050105030723040207030815010f050a0302070f1202030304231207030302070606090c03060506090a090c180b0a030c020318011d0301090b010305150f0103030c02 82
    0xd130040400c841003004814001c1d01d5009404448081002000f98034541081d000c21240c081c02403070f6140e442800100401c113110b0082010300000c201c1030b808070082000210302a60440202103005c100f00d50704112000d031129002e0030100000740707000c001c09442d000c070150440c412040704070b04140e0005040409d04c603a09410851559120f07414040705c00403401c000b5180d41003a50100c40040b2105141356841d405410040198007240015110f040c1c5a042d11002540c89900b0440c2407540a00445011840034450303003006160340f000c04900070110910042c115001900102e20420301848844002c1c0c550600b401c00380d80c1803420009410356114015118070548041d16230803103522090105180f540e190141c0002c0d91251002e21170606044820398a038002d501d401c050703900310040a0100c40d0306c00c03180c02c1c40e132421010001071180a07403800f080c00e41d01282c00507501190301c80d00420030481e0802c140c12080041018a0882e1f0900c07207240500da22042c440541000104c5180f10195640d007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 111791897 1250 111790647 111790703
    0x18030206040e1006080708010626040302011e061404020d090f060204030204230703050a06080a03050c061b030109020703030b0a0905090607030e07090203100e04081b0a02060403 78
    0xd20807900c866407000c0c6120060412150082c0c5200111000141d180c00b030300e03c1d540510315079190f94859a0038488100d0f0f00d003980055601844590801c07002a041c1441c00090066020341c0c000700b8810380400701040315000180010044600e400020010301c6040d09095202d404100c60142c4e460b65080f03402c0c0c019114484010b01602c0329a50365100700300180c0c1c01402107034402e071024420000303050003284049400d0b9030300301c92460b400400180070600c40c2d4415039018000c0000010450f4544192078502412005c084000c9600010b0010054400b007104aa1007065200b07550a500303100d00402140340010304c0352285040e00402c1080402d8043c0d0800d0070384610290000640b20b54400c0365001500050707980d4111030141070301080c100d500ca80913043c605040e48005100c101c5c60401104002e500080000071905440300000c1041c1c1000300405020301d00895881d0b4450143c406e080c0108042585d400e40c840d80412104001600c0d120103680880b0b4100c40400c440d80310348021441b40c0e40c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 111793147 1250 111791897 111791899
    0x60b041404060b01020c0f060703180f0e010503060606071b230103051509060114040b030106050c1009030c150b0306010602100b030f1b1203030906071b020d03180302 73
    0x3003000c002511810040260300c40d81c090803007440301c15071007030059849000f646042a00f2821200300880507041c00d1b40101142e81c42440c100307500d003049070340e5a038103000399422200110414031020041c00341d5000781540941381c114040c0082d4202040012024070407044014882c4c40c9005840e8a0151215071020051440d40164500c240d001c3c035000f0007951aa40200f03000c2407038800481c1e1501c0041200c0640f1410183c54a81039403030b550019a100710000000364482d03078041101180b4220b94401442c0203050a807501e0f034079a601c0e084514140900c88a0310b0008070300c0d08511030b0210380d10040c02d030b0610340c0001e9040411070090740c800e0080d10040c803003d601403055030000078210394006401c0c802c0d5002c3e072004200c1080c0d02001c0688446500c25815030300e520204106104240b0500c9041e0710060041242c074020440485007821500b017241d0f15220764010354100100580c1000c107a41c450310707007400e00e003c4885456000450160840b28084e041000240920071182c101c01c1803003000e950 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 111794397 1250 111793147 111793151
    0x10f09170106090e06040222090f1506150203030406020f0c01020c07050316080303010b0a0c02093c0a05060103020c150105130605011407020a0905090a0b070807050405010c060b04 79
    0x15060480e180a8103182c0b007180f820f5843d003502c1900c01840401e45d180142c0c1c1c014062500740d008400c0e00c0c0756000b0300c1d46d13113420500d03a80d01081d000149586080038100e8807a00512705c00c020031003800c5084913101c0d400071510451900481018030b40c040202c0360b00c580d1000c001601d030b04112902100e01e00640846c0e9400d50700c002800c0c0c0e079070070002604100b2504c0c101c0454006098401886980300d8580c07151140f1a441400140000d14840014001d940388030b190044070010302c1d030006207040383c00b51011071401c1603480700c28101e87c1000d503505401600919590040c1401100c40c8840500020301b0001c030b15503940046240b60381b0980440d4000000c010440744418458040c1860b450001c6c41458032030228140269843c4800d0b0054404961058455034901000e210906186074480784049078060b9050601244c28810743c81414080c2c0c11542c01400220042c2c602058031076005000c0400b4090000200418143e00078100c5007a2203007807920f102d68220300e181c40000350005a0a940e8018 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 111795647 1250 111794397 111794429
    0x15070c0b07051803030a0e0103050406200d0b0d0f030c050a050f07051309020102060f130f060506030f0a050c1507080a03151d0103080c0a060e0c040f050c09010f09 72
    0x2e038040040c000d06034a0709841c0007284035010405980340700d02c1c0011004135040c131110a40e5513020b40c1c0403a91050284601003160301d1a24040341640380580c9a4580d0101e0110300c01c443e102413446070592000341500c11550310405601c40c40040540d100d801003c03c50041400410004148641440c20303a00000711402c2c1040b0214450b00d0360554080c4602039001814014015070045c042d4035550b036010780180c680b0307885001c8400550140240754008085000d0f20540003e80401e0000442c02e00440f0002490b0a0000c100f43c107060307505428020b00e0b8495500407002c110007103a49030310142d04844513645600c0d02d8000c1e082c035020b40000a0454400402e010080c160580c20103c14a16050500701007192220310b11028000301901d00941d40d03c84000501c00104108010038903000c0c000d04a41484121355600d405682c10100105425081010002c100e42070500580d524104110424459498490013000070750088200560401c24104680c20840c1e01590085024020f5421100ba0074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 111796897 1250 111795647 111795661
    0xa0f1b050307030c020316060b0607050d0c1104200307021504051608030a090b07030905090a0b040b030d021002030c130f05101407020121060f09061715070c0b 70
    0xa50402c4940d41e000c6810400305040d803510203c201d0302c0e5100f503c08407009a1139645c5404008100c1c00100c5030b0000c40030459100896000c00054544070a10765810b01104014585282c80c64030f000d0701c480c0102d080509a0321400002580e0301020b1100c10b03015500c95480e01c1c5e04a1405440d44e0b214003200150000340010307c500030030034a001e028006c52007203e441d51480c10603600d01c541c031071020000324414414003c4034081d074003c0c1140c50080c0303003c1c2d460948500000d210000190b8111030115a034544c4c54619090030f00030001c14000c01c0380a0f151007003601130041c0d194940c2a00c1c140d0341540c000001042404410181ca007401d81d05080c003481d036516290301003d40802030245610801641280e00c800c5032250703000c070520f40c080c5401e10341003204e180d005648420504032494101c0500000c000c0c81c2e40c80612928000301882c001500540c2d14003200d03401240e1a9401200c5040e2310f041c450100c004e0005199240c1b0b04c421458800c40765150359003140c5210b149000100500000020700080f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 111798147 1250 111796897 111796907
    0x515060705070906060f0503070f0c0602030c0c060705091012090b0c0c01050a02030103110f150c16050604030804060804110301320f0612010b060f1c0b090a0f1b 71
    0x5950000c4020130100d40c4440d000d6400d0850341640340d00080303007000092211446140d4000003295a402c0c900400100d036907421059030405c41c4d1415140c0000b180c0c102080a0070800365821075814100680f60101403804140754600000c00e8905201194041501202d402d510050000342c10543c1d01da0a42030034100c03610700e83d00145021f28135608103404511600d90600c00c8034100c0fa0700400b80001480004140010a1075100d212a804000030403c031a0500d20380c0700502ea000b1144000d0320001008229041c04e5031401d40101317000b4401800300b800058418000ca80c162002410600f00580d5649060110841030349203c40d01542805024000e01c01c59182100178803101030310702c9021034203c049103038140c07104a40c804901055880451240d080c41c0c03126100c0014200c0020070f5000d035100115501d40e0000a641d00c18520004241803409100c40c010b43d194107000e00b041c80308442883c002060b5000241044034a582c1e2803541e1460403000d03600c0114200483e43e040c200c3c5021040000e08 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 111799397 1250 111798147 111798149
    0x7080916050a151214011a03062b0605070e1c0b060f030708030408030d0506090906040602030c12010e01050102010c050a09090b0607021c0203060108010b0d060e0708030301170c1f03051506070507 86
    0x8060f48410100e0b043d4002048240ca200d80d0015180f0024100b144e005640e9164040b0798ac01e0021a582c0040b101241180c02458407078891619096030b41140141032125039400000c900a512000350a4200084d14081c0560340002040300c00c2101c1290301000070b401d14505030f004011603c4000b50001d1105404005044143c00c00202080242e1300c260a02218440c00c8400070880d0304108002400105a0303409075420645280c0103500700580900c065407500380030381080b81481d08040040100b50707824042c4402000c51440c0484c10101c0c080000781c0300d1200d50066001c10b913101c480714540c80c0c82d1402960483d94004010300c80341d14510042005a00017140b00b80d0180c007a94002107003c01c4140100c1029410250034000e8130200d13612040b0060032000c102c2d915070b0254400000707c4500400c0594060301050507200440c001a035240761821007000d002d58011582c990100300c580008816080c910110341c1404190b5035100c11810865021010425501c11004203c41c414003500041c080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 111800647 1250 111799397 111799409
    0x603010906052103030a0906020409060902070501050a020705061302012307060609020405030c0f0301060324230c18031c0e090c040510050403080307080916050a15121401 75
    0x31094201c442c00e150043c0000d03035000c079207592081010170242040d0b0340c481c282080c0103460041c04c0944511000f020340d0b41d258010f14206802143d00800e00c00207205075500951050001c524003a007656609440306402059140340110316514a8156401444150030007000044940c0c2d80c00b02c020404003103604510b005441841c601035011940c092548210350980d58010300601141c1401410001c12503d0303941c1680d01552500c6c40040081c00704401c0008240c515070702002003e1002402c2c0c0100e841501c0d06e04100c2c07402d00e07030101000c0020007a00d500000303410141c0d42d44038035801600c0b442c0700c2010827054051003082d01d83c0000b484c1002407440d05281c66900d01242030050820044008010360f18100c1c4980104401c202d585010940c50b481d80307255050041c1010399980b103418080d08201c0d41300000c03402c11720400490704018040c00d8080e080a218002005050034081108500140905109000043c81c290b940d20701800140428621664003441004003180c00084004828811a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 111801897 1250 111800647 111800659
    0x307150606110f0309040207020402070c03050a0b0a0203040b0a1a090702030a090920091203030114090106020615100c0b270a080a0309081b0604030206092b020309060301090605 78
    0xe4024002c0c045114460465418019800c03c0d00032820040254488142264041e40c20031040f00000d1084032504010340c003e001625428000713040c0b440c0c0d01c800051160020b203104000300700000704d8811102d90003c0c8208400a0350b1110402c04407291842c280b4040d41c85482081005140d5070700100070319000d201c2e0b94611001503542c0c2d200c00d064560b9000501c903140f038243c18121036464248041d2000110080c0000e0310305a48524150031a130081c0c0200c10100010f00c5049100e050010342c076070040c09207100804207841e140c4003651480146030780b11403003503514100d071030111841080c130f103880c0503000640e180d91030608119171098070703145045a698407128108100b48100c1d010800c0b20086030071110091809202032402c4008040b1001304643d150300a10001e5a06e82100145140c02904c8500600d4141083d0038041c0c50481d0046c2030010992110181108107242000b130b0107041c500106454440e16006c01b0140c0c1140603000c072490b0480d001200018070002d907a001441115400e40308 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 111803147 1250 111801897 111801917
    0x609082203051c09030209040204200409110307020604030305042d110d080307080718080d0221041a0c160e060117011404060f080a03080a18140307150606 68
    0x202500f80329800101003c5441d1036010005424049111a0700034401070000862002d0102c00020060070112075580303526010805120003005446032420351080c454400307046240c0403400940ea450300800050801d9241d1000c942041080203000440d05491600e00348904c25940c0030070301d0410040410b40c0c0c3d02c12070b2004d000e140c0c2080801d80311a1504104c40303030b02d19a9441026a010180540340000300405020020000104a0600c1018080341c0380580054054000024513001c942c40900404210030b00300d141110010a08541c11900c5810740860460b1100004104600550301d108085008494500113259401d10703d04042e41c80c0c02c07041d000c154507003500440341c1003106032181d0940303d140c0c001072203407010b6042480c402d20002480400c1e02030b1900b59804640020394003000040d40900b00b070104143c1c00180d2241e00c04001c00c4104081030201001d00021724100c0700c040c004140b480c14104402c041441103d07a042c5d0041503020800d0545000c4c0790060901d80301e100002a0f010031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 111804397 1250 111803147 111803173
    0x140d08100608041202070302030105151905010203041403010212010f1e050d031124090f0a02030d030915050c090411090907030b030c0909010507140f0403060908220305 74
    0x4068141c407426512460305030354035607646280c08824582d07041584079441000005a40034041d00380706640b02003618201c2181003040c41990b01170000060b1b80840010320520807664000300399401c40743c10444a8014042007004280284501a514a4440602c10001c55004e01c10440c5a085420017030494454401100000b0b5050b000d038015594400411003540011034801c0012004d4001d04406840381a0003a000d0070400000140011500b0240da40c03c1044d0101d09000d02d0985004900184c9041c0c0013a0b8002030710b07420603003072240c14940e90360340d1681030140b0749944c0d4206d4940c00a0030406810089100039250700403000840c0300d682098440c541d4840303040c0030340d110500c01a01207840ca846007a815009001394504290305403040c2d001035211640c8186a150140c01d010300005064142080000e201d0b10f4111107040c400041000181c800001c1c1d00102e8041300c0e0031403400a010080361810032401e20a03402c54002061500c680034400e00c115019450449118008441c3e0040e1100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 111805647 1250 111804397 111804421
    0x5070f021902060306040e0a0308040b060406050102030708031b0d020c060106030c08040b04240b040e03032707031703070306090608100f110c07060e180a0207050a140d08 75
    0x109101201000070305281c010b0509001071a00178800410101ea01c2c0104820b6502d0b112000074140c00040c541c400f4002030025544040b81c004c6400d44041c0003503401c0c580081e580f40701d00382d4000c120712000800541618040c041035201c08000c41c1c0407581d0703243c490b80244041d4000300740c02c0300c01e03005140000524902a1003203824803c120b0300e5040f40c960701c5440e9080541c0e8002d0090702e9003012904c1740c1b10300c00f200d54030300f4050650000e000944591b8000c14003046411070038940b0002d034410000d100416100c0c2038010740d41c1018809191001c5022420f0a041c13910700e40c0000c0400c1e100780801110362101001462148005035800c020141e51201c14030140d80c07840c499803429070045055208162119007050208040014002c985000071040c4072210754803066208240d500b01039030034805240c4c0310f000c16810700011645442414085d841c0f0443c1d032400076140000d40c550000302101040000c0c04680c001541003450442a101d0018601c0e40310001c0b0407000c0006500c1000141740e1089031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 111806897 1250 111805647 111805663
    0x601090c08100519030c29030103050a14190807030318020f04020d1514031209100309020118060f020d0302120403030216050604080a0e0d0506060603130c080105070f02 74
    0xb01d205040b460001400400c2c1070365107a441c40285188404008162030f243d078600108244c2241c00300344454580031254001c810805400394110404c010004250006003121742d01340c214150000b4041030f031300c145290400e080c0800c020010400310740020b07c086040075051712800382c1c81c00e10408022212407124500c0d111802540210154101245030030560702400c10818403030000101440c2030001d0304a40d00c0d07107501204c4942400c000c00c41141c03d081c042007108128035901d180c1001351110020700c075921150f05040c00c25549503005415a8401c684003c030502d1460400721541343c1f1354034014035003400d41d298003016200311100500528441d00c21640210052102c00e9241e854540d0304030040e61014400c4102421b079034540102081e001c1c40006d0045100d103803002c1e50b803401e00c04003410480e05154000c0c4500741c1040c0181c003085000c1b5065500c180c04445541d40c1e81e0b141540c0c51481c429100020702030321103e03000030505031030560040c1e01030401034a07074070140e0341400c0040307070707a40f0710 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 111808147 1250 111806897 111806911
    0x504020a080d120c03020909010f06030e0a031707120504050601030308060105070b1501030b06040e070e0901050d060903030f0f0b0316180203070207030b04110406090c090e040c0f03050601090c08 86
    0x82d0204403d40c4814540c8154841e10040c9009807070445094001120f0b000700380c2010580f6081100c003000400d4151294031980380008015140d121002d40b0050005c0c076081800b07a48048801e40081c003010310a403035458124001400c01c01c824242801c0190b980e800902040340854440000b14004d50301902c00c1d60000d41d4440c2c15140c0340e503128880c46400010018246043c961101c0034082156a01c00140002c0d1251030041451823509040080c216100c44a21038000c0070580014001600c40720011601c035a0040b00c00b20b0319084070b00d412401003441002404016143c600c0c1c04460341c02079041109583c1d011000c540c0c045c5a8015401d140d03480a21448020300410641401c00700e0403900915444262070050310f25666a940300d03402c140ca000c0724115101c03a41389195800340d2a181c0f154001030204404104949903017040082e000b580580501503640307601c1d000041c1041910120400135014000040088079a6490035a45e9050701f030188a965904001c4000651840782c00710034490740e4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 111809397 1250 111808147 111808157
    0x6170c04120f02030a2102011b05070201081b0309010b09090c0307170f03040611011a0604091e0c050306100c02030c09040501090c081b01030504081812060a0504020a080d 75
    0x260715940d046815880350000ca030075010710601c1c0404501c050080c955482d800788010311600005600080c01c5524041055600700c9035038802040075a8010155006241c0c20308204400e40c4540301c0400248e403030580790724061000042000880c1c80c044d0042d45e00320a043e121040551a4801c626442d0380c9031550054060348086020884003040102d4000d180726101c0c181c2c0d005082c0420511308641c06074101001003050701c20300c112503050902c07481c0ba07102d4444500048010103080010418480d610409550b1174662403152500200090361000c000a040001c004c40070f01228040c100d900225002803180100342c2d070595050307010b200c1c0e03444003580c000c01610351102c48000b08811750034060320031790380c0d9940c940d040400540090940300151071204c0042c01e000c01c8004c08803a15000065040741014104414000041e810800360b923264021002ca0300b17100980c3c08040703a0040ca21074035540b258031801080c84402143d940c002c9010318001d0701c3c0d408065844103030a03940c940c1e454280e900016 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 111810647 1250 111809397 111809429
    0x90f05030c090c0906040b0307030b010809060405120d060b1204050601061d06180d0b04050601120b0f0601020124090f02040b0306090414010603050c03100612120e0a06170c04 77
    0x903c45400501d031000d8020403941c109910783c3c00c0900a0740085911001088d903882c524529581c000090f2903000d40d0031b02c001c2026117000e44e50035860b440070301d81910340b603140442d00d19402d495682040c0c010b410603900b580e448045005240884c0c1c030003590207403814010100007140715803290000c03002900900a4a080d002c500c07200b0300c0754a034440901400018070307404000c00603540b59040c8200c80c0d030142548003601d0900d0300b0030600301101a4040702c1c4d8a10071007405400206245184e41e80580406006074507a80c0e80f50050b8094003801e11407440032460f0402501c240c801408200d81a160311110420450324030384800d40c01c134410380c0103800c00220300f480050440c1c80c1501000e0791040c450060b580c00c1d80d0781001c00341e0a40c5c440e90800c0703c8940025240e0225420300308a500c0400c8048001802050303e0701c0e41496181c12807107005400d6000d0f0062401c50240141e0180742c20030780c060224202c19580d58002000c9014401140901c98102c02c0410b01100e002d20540d02a258000f120b00c03502c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 111811897 1250 111810647 111810661
    0x32b08071e09030c12030f081608040503091009091505010c020913060203090106050906041802060a0201060b03010b07030e0d150b15071208070207140111011506090f05030c09 77
    0x1204028001c0801000c1c40001c000100d5a0f810740008061444440140d100e180c0303000f80a480c56510310a04100c254410049003842e45003501607103a000e030400307a03004c2d112810403500f14418044c045401121f03d0004c401e145a00241610464103c00000c001502e04400c01900c040722a100d103a0000f44845c030400e015140c80344205d6001465051100c040d8900f56544505a810071030b510820b595440004100a04152840c6030f40301a0480d4200001d803480c82d1483c000841c0c0d480041c0c003440001c0b41302e50b5414000d52200c1c001d0030032500c0d00d540b0b030743c0d5981d91032080d075000704800ca0000325042ca614209080200605800c55030100da030300c3c010000d1108100041c5001450243e02c83e5100c090030f0000c10040c0c0003044e406000d46411020980302c010040c11401e00542048210340c4a10300401c00210034848030001100240b0300149070713008500002d030140004c02c1c4040c403079030400d40c1c00180c1c0c203030800d0a00003118620540054840d030742d1010076841d05241c4030f07402e80001406000443d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 111813147 1250 111811897 111811937
    0x5030106020a12021006060306140406080d08090a0c03111201140a0f0f0e01020307170f0a05060103020909070e040501060504060c0f08040e0109050603070f0303020c0108060a05032b0807 82
    0xc402c0f80c41210061013143c18040b042d148240d000a0109a44070030601020b03180b40700060740d425050314184904ca28125101b580c442040d481d800c10010100c000c140c8401d400c1c81960035654004900d4001940c0360700b090703107603070356a60207440c031030801c181134801740758410f0159200c0c600050800d1136081d41c4012146c8054100b42042c09070165882481014a102900c20480308030b11003400140c0302d01d48400c02400b07042200c040c03414400321400c01c0114006000000c16803001d09018041020345030500181d000c1d000d41d140304c581c021126010884000d0f40001c544010050444050203140d0741d80d0b000341d803035124034000e0200180894005802050020340d08140040c403034020b0914080c2c0d0f403c45403111a4007078001c4d50000f521a001d126083c9020080c01e4040e211451120f130110307141d40e50103940d801e01c0d44802418040100c00103440c3c2c2c0d480b0070030302c4028580135040c0c4030090b1451750a022000a107600401a510408012038503581c4174890303592082949842d4403154060381d01c10320302 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 111814397 1250 111813147 111813173
    0x105240f063903090306150619020109120e030c090402030307051203070f0e010f0c020a090606020102090a24050d02090d0602040e0603010902060412020d05030c0a0201020d05030106020a 82
    0x1d040320003007000070b00d4030741c40344001c0ea620701c007000c903032042e4000321105040041d24603500c003880795105200603242950042003282e000381c0b501054180c0b907240c08010400901418134414414086e1407082c0d03900640641040c24443d21030030500000014101003074601a21141c580d43c2c041d805005000554103220316501d8006000908480c1803001e07603980c041c81d00240d00900000700101100b40b0205542007000070402c5000c0f42040d005a91078807000130902a07014450704104100705030200159102c0c41360210240000120511a00b5103542c0064042c4d4418040580940d10b10070000036800110300c840445100d400b201c0c005600f01840e001c860a400c400c446e0a016130382001105a207994107403404641521800c40940c4451070640008112480100540e000781d0600300c480e80180e55080842d410360740581d00181c82c01c009400418650440640024851710000410409444002401c4003d1034401d0f0b0031108181c4000702d08440c1400300b846944090390001c88803100041d030701c5984070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 111815647 1250 111814397 111814399
    0x819020c040228050406050d022d031014060409050c0408010501180c030c0e12070b07080315060c0c04020706090b0a0e01050106020307020a030605060109050607060e0105240f 77
    0x182404411200007802ca90000501c0300780800b0300500b503500000741e90b8450030003442d60b007022401d0034905107002d403081c4a4a842000b8181c0d00103007100b800900031040099081c034500503455420039a85c101107090f4030540d82a03620342074082000074034440720010444051006000603090529040b0207002400020301b40e900d01c1402030102040c002801d02c04c031170003045903000d4500800d1060528100311079128070350400309400c1c6a694a0186c0d0807054020050b80e0a80d5900d40200c03c01c840c1d01d0604405230426030801c0c400040420500c81c26202071800303040341c0d6448044007016801003100d0361007100c45c0400c540d0403100d42080e2030700d401d90262000a014800c00305441b500f0b40d0714015004011900b000406a4462400180b017000344602405061540002d40c035100c11074001481c14400d503c40102181d0b01ca000045490744165550030042101401082c0c680300329107030090107040c03d104481c0031986000c1c001540594020188a420551041100c018034041014000a07200800d456 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 111816897 1250 111815647 111815653
    0x1a0a0b091003090f06060302011205040b0619091103090c03060103120503040503130b0a02010c0f0207171e0703050c0f01090b031005091003110901030528020a0f061b081902 76
    0x10408034559140484c1410300c81c03003000500c9821032001610080c80d21032000c406501d8801003000040392200c0484d0015011108140358080058003001d041e0500e41000400310b061a40054003502420b001d180214203400544840000460916644110911010300100620310420340b109006500030358004d0301500c1500d14000c8640541401701040307030f0028040645c0000e0b0080b0b0280d0a114000110307c02d4904410b0b0305c500660000c0d664101c5000e07995500d440c203208580d807240c042210301c01c075040740b0344e5205900f0101e01742692240010310098a5034004c20580d0b182924195140d040031110503151040c0d018180700c0e2000c0ca503000100a242d60114082c804036096603201c41d10b500c11011201c81006442c190714010b206407128442843c05006114014400100d02003425584444030342c0c042d00044808001d40380310380e010f50310041e4018110040110300c4180d054081c030150740765525014001c0c0c5101d141c02164151841c005000e8810901c5a04126100403d914207003420910403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 111818147 1250 111816897 111816911
    0x903020301020307090e0901051b0a05040f14010818070605070f150b13050606090907091a0327070b13051302040306050c16020409080706050403031a0a0b091003 71
    0xc00d003264801d03981c0fa00802d403180030812a104000c21000c0e8801d121200a00a0741000c082c13802a81c1c0d9035081e0b0045412010034291000c0d0b102d50241c900030b101100074000c01e940e507498031040907051082601d000403080c0000076184030310f89511101c1d1102c00c3c1c005086c49442d01e801104c072508200300032500624082c0050011402060445c4409002e0110000f012441d0004100b03100f40c031030085403400c0d410001000034680e40c11050b18081c40060721303080d00907034031554129552003c503003040810003481100c41d008a03031160051031052006203c0744d00e81d4885001212403484103900009065880311070184504680c51000e01102448108070380d02540d200c00028526104800301d070f600c410782c007060410a100c0c4e45d01406803c0020642980e240c1032500e4041c1c9942c60f203031100a400b43e61159000d20400c04003408503028180c000302c1c10070040c2000c1c5001006804032a8100842e540100500406850031040110844102c03d04080c603103801300045c0b04501341c091071410140755039070312 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 111819397 1250 111818147 111818149
    0xf0406060b0d0b0a0609030201050f090a030503041d0609010503060412091503150e06090f040f0605041101020f0c01020a1e0203030403080d050a090b190f0c09060801051005120403090302 82
    0x20306080c2c02101004100105241d090090001440d0b01020801060000410250340c01000b2240c0a101040001d503a411610000c19141009070b40014154440014005007071a50309120798a03020804541000741d841c1e140402100300001e000d480e615420805c0440e0010710b0400c80020782d10303840d08111440f81d5a840920000d5a90411160003103500e5104890028000c2c0729440040d01c110902d05603503042c0400440c041303c400911851034540040041800c3c08109500082c0c1283d2100b414041c03498240381140f5040c2c2050103950140c4540001c09420308000314050b4981d00d41079005000200540e119030810400d50000f0802a1001040c44c0015880500003480a1409014000d65070703c0f442e41040122240188070040c9289010762140010300b40b10b085503008041b42004000058643d501a001000404080700c0785030b203814003240c1000d821804403000c50300e980d1900310031070781e0303d10034030001145842e010310003c1e004005908031500300c030380d40c2d54000303000349081c07107075992698 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 111820647 1250 111819397 111819419
    0x90402191404050f0c0304080a03060f0f1508010602061303231c06060507080c010209090a050610050903030301050108071e031d0a030f031a040212011406120f040606 73
    0x1800c49141041200a5070385141001e018264014198100b001c083d880d110000300030f80e0101500042030300360300144081249100c0c2d0460b4025103816600810100e64a0200f401000711501c9a0b00303000a805031504502e5010300c52880c12030b1056009043c040c0e80d095507141c8160520303101101400341001000450001030455004a0070500d01c0d010758541000d510f005082c00c468528001c41424030703200340141c5070b01505440a5680c07041005450354808040c142c0a40682c03d50030342c118445404100400400707070001801890300359005c90140c00c1c14841183d40d8810409030607015442000100850352290070002c0c1d100e15245890015920590748541000105140060010742c4072000f2100c0102e0803040350240140c10001445880a02d42c0d010740000c1d000c640d1035060541d1246921006004030a00194207000204115561003180d111326904d0002030042556900203641c0700c112a041403400c46034810b8010700e0303419003580c440c4032400504000a004860181d1a030381c0024075001d43c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 111821897 1250 111820647 111820649
    0x80613060906120b10080309010818250602070509180a0206161a09100f0e0d09030606090207050303010311010c08040905040b0c1305040f0e06040302070314160509040219 75
    0x100c1160075040703c24101600c42d058054140e03486405600c10801108000000311395901c1400e0030030007815541c208500351450407040700000c440c01000151070030118454160118011258803018045454400480c2c0e5034283e4011260002c449901003003426103c4164414041c880b4800c0322030000d402d42c00320754160031141d02003446540c2c1c545554100000303001c000b2002300251a03402241e1900354549a0703107002a40c4000707106984c0e1101003404021a8000400d114200c0080b20007804110000407e15091480142c0d156454180c0108012815000f120850394002c2d001f541540d0858803241450800804c00b0350600054038841703000144108023030001440000800140303864681480c02440c0c000601440a8503020004003030811801c640440540d00b096500003a542d801544a500078040c403109646144229410070080683c000b8922064920682c07032086d0030401585500c7d41d0303481095151400d803a00101c00d100c1d030309088482e02d500c140028001c0e942200c84900b540700140725 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 111823147 1250 111821897 111821909
    0x8070512030f070e0f0609010e0303040605040e0906040c06050c011503201002071401091d011e03020a0522090804080f0604020f0105160501020f0306130c080613060906 74
    0x1c410440304084420590394801c1403401c100402c3c0390844002942c0310b4880e42140c1c0300d201c020a003017880e40d106034102c3c0c00700c0e4806012243d071180c440c130003c3e266401c2840344d050381084040004120100205405000d1580140008001404c103001a1019041400d01500a6603034a442a060000c178080b000025030040e54a010480b0401c0400102d818024180c2c0f800b420440d01c20002035640040c00d41c0c100ca54545641e407032040075a00480c0d03454072a03801207041c0d100307420050b82c21000e10312400f41201d1301c2c030354403801c50422150520100c68083c80040d42c80b000c0c4003420815420f01d41d250b001e28221241d0240f900c405101c0300d0720200d071083c83d800d9520400c00309003400045010000c02e8582a0040c0091100d4609940060b03848200c05001504000c1c010170910004524258011716490f8094000d5440300501d400030141c82d00b003103070558821801c8404500d4502d0300c0788200d03800034846584003186581e43c40e007400019030b4056041820709a864000094031b4901e403080310043c001c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 111824397 1250 111823147 111823183
    0x120501060f0e03062505090d0605090c091e0a0603060212010303020d1103041208070203060a0e060c03071b050709020406081005030f030d151a070b0a0b0604090207080705 75
    0x5003410020410b400103403050b4083d9100b6024449842c807003000c4003030003010700d0411000c80440703440125424007503030070b43c0358000f00e584006000b0003440f500b00c248070300000320071200c050b1114410402c4206d42a900180c2000d010040c18090400b50322075a5840000c8131030214002c1c0d52076440c0e400300e90000c2d020240300c05ea03610052007015410302c203040c0415118900840c0c0c180020303040703580301e1250f407044681070640d1000c00e00800c00c484058605050f00201940d040e4038100407500702604016500c1803a82c0540000540b0b050300481c1a030303009803600e694024002074a400004d081c1c0ba25080c0c10344061103095400541d480c824001003014044590744c0c240c06007407121074003c4003840f54028038030a41002d01e0368141c0310400400e480a40e00007000c0420943c07140002d10708007040a030004001c2d42c00290b003040321445224010400c281c882c0b8011683c550318040325404a070824010680c0c400d004002c10011490b082c1c02500302c407406026001d150020700c8d03a50f9407034118210305001d9050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 111825647 1250 111824397 111824417
    0xb01031203050a0b0f01050c010917070309060203030c1204050a021f020705030102250611030a0b13144507060305100620060a05060f0301091505040312050106 70
    0x2079250203669001403403264140005100300d800200f43c4010b40700860f040000100e042505902c2c00d40004403402d400030481000003517a420300f10030562090700b00760040303881d8a10001c4c59500c00403c581c4110549103009041c041c0100011031040d0000c1e00c01d031031510a481d800c0c400360303449008001d903000d184951030725907551a0030064101002648054400d910522108900198012400c1d00402108102401450242c501480101081611100c0411012040004000e0345c2d90082129410031034082c1c907400320601200d01504c40075110010400d04000204d1030703032503038207040200d04d450b10b81c42d5690141035900c90780b05514049409400c0010300da071415907070729810700070b070400340541c1d240600c000e01c0c001904080e480303041d00c101010450140d15004103240c000c0401c0d070000300750750181c580741e0510442c414081d0005a6040b4400c000c0381c030310340046240500c6544c0c02c80c2c0d4807400319111280d8190008005000041058080c031844803120020010b951054034060030081e2114a025 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 111826897 1250 111825647 111825683
    0x6030123150a080604030807050705030403030e0a051f050a050702040e0706180e07120e0d020c040e010905070312030e060405060406060b0a0e0409060f0204030c03060b0a05010f08060307030b0103 86
    0x1090304801c40d2801140c008400380141e94001c0381c41640143c06040129194030341d080103c64504c1f5440c00a055808041408400c155001d0100251158110345141c400d9440307e0800402d030f42481c8680c0c2407600e05c410a20402c0c2e00440290802410b01d080041c1080004d8005c141038860004000c061034020310410703c021a00076050341c5010a44e20641c030b84583c1484941245450064010400d1003135000c00c40011080540016840301107582c1520003c031000c0d1006540c941014000500c01c41c28950444103902d014400c00500380d03000380091515a255813030301030645460540300e104040e201c01304242003901c2008500e010f43d00c05c00c010b000c0c41c60a420000d0849409800410142c0700800c01119660340c0000a84110f0104603000101100103142c0a0020700340d03054a4403a26002003000000e00c0800c100810441c2c1c003a43c02400440c010008014081d05140222070101d100d03080300083d00c51281d14926805800541214601600e0741c07201304030342d8800d0b8030071507403102840614400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 111828147 1250 111826897 111826921
    0x19080706030504030c0605061909050603060c0c19020d08040303080103031b0b01030201052b02040503010f020c03032409040f03170103020102060c130f03050a0302120406140306030123 81
    0x4110a1a0402c41c6003420703900100241c1581ca005044961520003049007542e45460080850740d1403000e4503a050750319100301019041c1158541e20901071a00007814002010046800d1201c0c1e04010b800707000c9142091091194100342e00340d80010444c4060000102800c0007000598000c0d00c0e80c1400d9895880c008007428040c806150810800c0742842000944103d48541505c0d82420038907210000081c068803c07042444200c4c00740d100f0707010703101c2d1111556130080040d200b050f00244248100d964019040c0d00c2038049a20060380b0030400950205013440702d6005a441d1051b100011401c00340019407441c2d03046c1d03404d840804ca180213120030076401070a200c003054190144c01d5000d41c51a000170b511018018031226820600045d500c400050040703104c0043d10400403da0605a00c03420400d9903402450012030141c4100040c02640903403e0081e181152210342e13410014a40c00c902c11011504090140c940641d2620b101440c5034022404400510100d403400250624101c0e1303813910 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 111829397 1250 111828147 111828149
    0x10e0f071a0c0d140909010f050a0f0b030117030c060901050a05010518010315090b10060201060e0f2202101710060507061512060e07060305091b060405190807 70
    0xa1040811241101c6200030a0a6941d00d0113803c10951241d8905041c0308248200d03d8001d134043d61501c000306c0c1c1d1203205c105e14002c1d43c0040d10b115020a03100c09401c03110380028021424804414001042000010203080c10704070740312020b07281042d640389141490f110090b10b103076907181d46440400c5640c0c40d40c1d00c1254010141150388050341500c00040f0000c1d288107000c06401e401520602d0403000e4466000319120560101509080385004401503020210074000c200c01035081c8440060f00360840c180f01c90241107064001d4a4035210280c15541d0045140c0b1000d040c05110811a80981e03620301101b0100c3c0840d40302e01c0344400e9490a00c2d00141c074000c0c581c2400c0ea00302c0c0000c0c00050f40c4001a2841941d02900001d010038104842c1c0152903202c0e4400d021000d00101c204d010003c140c1c1042100510070b20496010a40ba140194152982101c1000039544204407584000e2040c040d90821108060103181c0b40c0303503c40b004940e07030000e0302c0b4000c00c65051410781045110400c0050710 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 111830647 1250 111829397 111829439
    0x40b0f031b0f030708071803050106031406160c0201210504020411030c0d050c130308190206130f060b0306011508060301020f09060a05120a09030f1806050c010e0f07 73
    0x9842e06080c80200042800302404050070441048002190a4007840f140b05818560a001c101503981e20700d4031601070302090100701c40c894003000c4104d50303140001034a140644055003045558080d400b10071a500c0c020352004be4104070000481c10b039a107188030700802181d541a800031405103014018442070ba814202028106001082000700050303000f016520924281903010406855240d40b4640740c1c0103491048007005403c8800004001e26240100894000301c0021070350200d0b1640240c0c0c0314441190b0355101d44110b0038a03400060f10f400b1032403240301c0c801c800000c0c841d001000841c1c41c06409030440907a1094030541e080545421084440d4000c02c1140250702d0010610410621801069030081c088d0f4008209218868007400c00e1314030070200207442401d00c0c60301e261510041c0182180a6001c90340c0c2c0142c1088203403099400301540903040c0308602c18a0300c1c0805c100c800d0b40c4043d1070710505558620704000440303020300543c104403020700000c140c2103080c802142c04101d03078541e4075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 111831897 1250 111830647 111830701
    0x20f040303260405030d0c02010204030b0705120c070305070809060c0a050f15060a03020d030212210c19050d18050616090f03060c050405040e150703090c050411040b0f03 75
    0x6000082213a03c001014040826200087d60040e0f004e4080d0b030b000142821180300420415561000240c040d280c040d106d030300c44686441c650705a09111340c1d82d0281c00034804000500114156400503c184503015024915281170f1900341030501c1007005040301e5030380211488580c0c40b081003128540c180d510000a803958248000091034502651000034028049880d409003814000c0c030030303844001d1503600c8071f50b0384403203500b00103207410b041c1e00c4001390b0300d404000822010840141515859106ca001c0380c206400d000005544c5508443d44061207684c9810005260074051490001c502c0c0c032039401000c41d41448444020050b048000d82390410803580c1c020005810441d4401c01120703009000001e40c1d1480c030f082212180314a070401c64201d0304080c1071003e018030006400e8481154501c200c2515120003500f201910340d400c1c0080c02c102c002c580280481d00c1c055002c108140c0d40001a545007658500724a01d04ea013040c806411080c0000c0708100000a294001015903481030043d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 111833147 1250 111831897 111831901
    0x30b030c011b06111303020a0e040b0406090c08070801090c2907050c0a081c0905181504091b0503160b1b0f0f01061a040b0a03020f04030326 62
    0x8100958400c1d03072100c2c82c40364000300300c188100395100f400030b24080135445a079003007990800e403846801444200d01643c0454000a402c401010509010715805a11929280c403941c4840c406070800d20000d40310025140400591514100700c044010302c5180b0000c240e08d1014104000e010480d9400080450031041814007002c003108103405002c0c1d000560207844040c00d040c000c0c54040b17120316540d00080e6100002c29142000950108140d603480201545445852000c54910001e84109a0001304051107040c44541c0030030400d0348601074110407400a01c01c0c5000809842420b42e0641e9081860500b004402c020b154826000d004290002c0c0480c0141085095100740e0520400301003078800b0038801c840d07000d400c07500e4000c0c06503041120480c10b0003403c07181d00e4440c2d0040b103c0140d03107402d90005494180c800c10760381c000203100c2c142703040a24184074443c00b41c0c8094120310415900f0001d0380007a800c0786014002540c0203549402e080340052041000300c034001031020205c1c0c04c030001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 111834397 1250 111833147 111833149
    0x4140106060201091103030406020d11030904060f0305010e010b090a0b06130605030f0a0902010206042307080102040f140612040302030403061407031a0d1101020f01020c010203060108060a06020a0204021605100c030b030c 97
    0x8203000304103102d1034500e813640c000350cc80390f0a6000d2460041c5d0b2040c10180c000501020f40460711050f0b0b0300500081201e0445881d5243c201e0300d466450756040741140c1c000600d0141c06501c208100280508000e1511402d04052001c8082e1500007c02064002c014002102c80c03c0c05420f500500b25442000200100d40020b03540c1c0d080244002c1054403194120716030415102c6841c1c42c00c220a000b200c1c0c4d0a5150f4140c14040d402c03d000391140307210320030000541c0d96040c48001369181000703030859260200c1c000741068146002030007034003548010071001000030b2980c03060000c00c02040d82d1494071400c01e0440282980c2030128090201150140e404103e81ea40d0012030362222361100c09040400da00705c1c0180d0030300302000c0c0690b0319540b01082e0640030300e00640003184520400da0794008190388240c01c00160f00d8241c010100123038000f540000040c2001d07401428400d9808182d5034400000b5a01c141c0350036007141c0000c0c04107498141003900140c1500405024042c120701a01e18004400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 111835647 1250 111834397 111834403
    0x91f020a02280f06020f07030c02010f140403060509120a092111040905010f020708030f07020d021e010908070623060f010309021c0309080c0105070b0f0414010606020109110303040602 81
    0x43d01035004031448004000803a41211805030241178100d441e16207506001c2e052114100069000c180d01c1e0b102240d00c4c901c0350034005940c03212001c40710709140c256101c186c001d1500600d5051244603000c075218007541044041c0c010a20340da6585e4503000e0621804c668010048d02d041080c10000185500004890007440a917041041d100050841485e0510f5030140a6200300039007000c0c4001101024009150019071054a10280c00707082911421000c90740c8854400342e483c0140c110b08880669910345401d180c820040c070034008140c41040c0d0725400460740c801c02c82243e020790b0782c0340c903080c0d001e118007141d010000e01c0c4551402e4610b01358010500014403424194105aa140c413410300b15511125460042111340c500182d45454034a0040d00300b45081c000e0710045d11408204601540c443e100b01e844066010f0204040303626148600910345101400c1210b200140c8050606403000910901c2c0013002c16074004141c54010303041c402003c04090007000d01a4000708424481c1d60f03000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 111836897 1250 111835647 111835723
    0xe060306060d090b0c18030309060a05030a060302090106091503050402061b0a0602040e0709080109080711180c031006050c0a0b07050c060a060608060102030c0c09091f020a02 77
    0x5a50702980d807040d85103090300611203000001c002c01c0c1524240328010034141c002d03009030400c0c05503544115400303a00309a902d01404403110790200e03040110781c4c02244240c1c041c640101402c0c10108207183c41c1d9000484402e4260481c000050030795208014000c0e0742d104880c1340d035000d03080412180c201038012802d40d20803000b4200303000b0b0b6441265036080b00700b00a2011840e40200007191115220340c1c1c0d64a0425055882e040054038807840410b41e02e406215503080c640d07100440519201c15503844a080f04100c00c001c1c1c0d40400300c16104101021190031b603a100e003501260456580c64030800e902c0001c5001d070000381c00c000042c08101c540f07420001d5050f1081d6080001038642d980d039010216094030460314014013a0003620b00b408080b4101d43c02a400b5104103446000003550f07100012a82d0307001315450a202c551100e070980c2000d040ca000042d41000b00c8009a5800700d40b0003111200089201c00e000008982c001041c10202d941804604001d64550041d01d10009803d06100250828 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 111838147 1250 111836897 111836899
    0x60103020a110105010306020d110f040e040807060212060301050c0c0303010e0a06150503040201090608041101030506150403050a0c0905010f0b090a03060603030f030e060606072301051303030c0e060306 89
    0x400504198880d00030742c800180041d02c00020f015a6031645058000b94200b954241c0b100d40c00c150700c4100c1c1d042103c096a500d00743c040001800c061130b00108003000c0310068000c1d14900300030850030b00842c4840c00203215543c1c2e170800c8641c040c10550141421240000d00f01681503409010340081d04d0750120849046071000081c04840f601d03250030210080410b81e008404480c000741c1c0c5040b4564001024511a030f000742c0380e02a2242c2e4580f81a07484060440e1300609007141003410b0300706580070781d1200d504400b001d44224802080505d00c4042684a078006a9070f640c0000704403030400078018011005001d40c3e070000e11043d490819907250b00c094a0051101d1a02d0114500000c0c5d25419000b8008540104080c42000e44d00e04015103015100c070390440c00a810100070080c6590001200340c010140903104e03030700d00b80084d1942040040c0021010440c0340f060400071054800901966016071000705668144441e1842c0c09021a40c440c01d040f014486071010200c0ca0399618400c0c2c96016070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 111839397 1250 111838147 111838151
    0x40506030a02220b0f1305060a090317090127030b0907050406050f0a030f030c05030a09090b040e0c010309080c010525080105090403050901020a06051f050619030b0a080f0a0227060103 81
    0x1b0f1140c0000c00c220703058015a41041000c11500811035121221200300c13802034800045004090030020310301e1003610030450100340c0358140c00c0c3e003420b030803140b144582d050808440603450322603a07480381c15041a03940b1000e69200c100140110f2403d031003818010003003180d4540d003c4046401082c017020310f604c0041c000c089602c4440d02854015161840c02962007415269503000803d0003402000341c034081c1008151411014400c0e5040512490300032a0b021001001aa05003800440150488170412203003c001480340040c2144d09002d45401000c0d0b1628485400944805020a9986006c2400d003040341c500e004001c2611100f000710b40054251500070741d66444500180d20742034101c4002001c3d10b01d801e0400c6881214000d240030201191640c40c0440790350303201000034500a0408444808101c2c3e5410341c02240a940600201c1c40081c0c44058a155142002d905183e83d04d01e09041c0e54100104500441c40d1842c001c1c00c0180d0384012408840c8c5142812400c6584000e00f0300781416 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 111840647 1250 111839397 111839407
    0xb0414060a1101020313030318020306040b060105040506070809100c0b1b07050307050a02030c010302041d0907030206120613020301030b04060c03020d15081b030d030f02040506030a02220b0f 84
    0x1c2e00c110760300d280380c0801e903009664030305142d03072a40c14100490000383d000034940700d600c10b80c00c1d000758078002e04c260300100180b010f0b89503034590325a80000602824140f1008200010702500c3c0d04014141390ba0141d18138030303121004003092101c00c4039664030f40410000102c11031f0000038600c2d00c4040d004001c000360380c0708d4880c92410700402482003640141c940c2c840418011704102c00090218900c1c0c5c8258103903803412074041c0040d02030380200c1c000c00d9030007030131050071005000030781c514a40e02660010450724102c1e50b80d000f045c49a440381103005151046001040b07020304118884481105041404500d5589141c584411051018200a1850f0f8071030352682c0800e88250107a074080c2c03182c40420001040000c2000350500828030030981385014141210b584140035840a000141c0c0141c09400710091110302100245002054400541c0c1d00b4000804c1ca9110311001d90711801d42d0b11030040c0d03075400986108407812180d4030b070444103002c071035000d000744040042540d01c2840c241e640140c0311 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 111841897 1250 111840647 111840667
    0x2403030f03021b030c07051e0904020d0212031902030f03040f020a031202250f061202070c151b050c0d051c05190f021f0b03070303020c03070b041406 66
    0x280c403c61002c0d040c034010349103a28100d128040010100c1080c0703581151903031a0340702d051219404030003801480c00403071500706d0500c2d405d09503c441d910038802030410311807006c140d00158010382510039800e455170000c141c4242111800b2070040145030300b8002581040000d40018805110003040148250300c049030000454551380d0f02940a950b12030840e041f902441880250707140c1810020008000c0d00074042100400f01054a8060b500f990300d002c0d1005003080020f44019449400b40c0714550380c200710380c5020800e003141c688040c3c0754801c400c44260307800c1d1200070b01c0038024281c500100e43c0c10062030000510005070382c2020315815905a41d501c00e0506089092106821048a1506445444202c15170780680104280801400100b201ea1720203a4202c90405d00c0c040101c1c0507902c2a0303a0350100c0540003207003044200301d00318003040c983c0c00d840c00300e410300140784e0007200503a00452001c40035240134002c40001d06174800304241403500c0d00c00068080c40c90710301d06070302803c0c00280704004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 111843147 1250 111841897 111841901
    0x606030a0e0a2f0d02030601260703050c090106020f100c05070213060e011a0304030804021c0b01181104140a080a03050c0c0108070206072d020703062403030f03 71
    0x22682c00803200301206070b500020000f01442962049108418419814214a0590070140000d40c000e00200304507030030224101104418402000d9841c50301000d04001d03080100140000b541c483c1000d8100407002400f8001c0020701a041441590028440860300e075800103000d03020540c4103c000b1a08443c03807001030b921482000c1010b9000007080341c0703400070402170f42c1224045550031004040243e0b61491712204200c0501c0344030421107000c0000c100800e204284541c0c2090004144a0906110340d91500b50f000c1c0c00d2004480360000e440042000180801c100d801d10001410144618114100c2595142c8200e002e0340407100208404079070f180d1a11407500010f092407100321240d001c0c0e80d040c0540280c01c003064000c440e1280c80d149803110b52040b400d03140940710070303001400d03070b900c0d591410b550640c00684943d0f0b040c200c1c2182c01890103590043c000f401000f580260070302c1070440c00c087c01615403022950480c001501e2989102c20305503603141302260740510b05461024491001100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 111844397 1250 111843147 111843163
    0x8040503181f0e0a1203080c03041e030c06052a03130c0e16020a030503070c050109020402161a0106080c0304031101020711010e030d050301120201090302120d02150606030a0e 77
    0x52840c014100c05440740e0f0043c2001103265400c0312a000320076601e03a02e4500841440c500100003c04120101e4a0f15a0360300c051a002807088034040ca00400401070290110340c0e0300c509134002002d0204000920045108068110010001846050901c7c00a1584810b180c8050078804000000000c002c0350344090342e614619030110030001055901e1508420280041e140350501401c0c0d424413207945800000c86040d03140e81038480c241907503a140c0d030594480f01051001e403210f548402c00b150050780e0314030042c110480ea1503104840c400003410300f00c10710340b082044051410052070050110780c5d0804c40300f03640662214491907503039486107400c42d006500f004003501c00358000b0603144200b2004d501d1031061a1400e031703580711041e2012010140d035007c4140c4050007080701000140414911004201c20b010300605190000980e1fa0340401d031a2400d000c2111034641090a12a80155041c81301400051108410340d00382c0c24440006001d81c4009081e0203c1c3e15a030b03420031801303590203000ba10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 111845647 1250 111844397 111844429
    0x60a030b090130150203090a17040f090905070504020705071e030b0f1614160f1202120904020d06030515010807050102011a0402030c07200a05010804050318 69
    0x40610359440803210701040a182a022403a540f6851040c1d181e80b1a401194003107810421561141852080110007940060452103590195250902c04681240d04264403240f800450b50355907480c0c080441c21010781608112045070401c289840860710000325081500c204880041e610750030741c5400c600e0300f0296400200c084079400c45440780d080b44050241c044034020140c2203101e41d90041041d100800803250b400394004000031002403a48500354a41556142d0040c4519203c517a40100d40303800c0300d00340211905c3ca050030820301000301c20642d2110201860000b040315008166144516000d000300640c05a0f9000c0303605c5020907901d40001e00150f400ca0261007488909611011000500b406502d03ea0710a0840c0003615510501c130b01c0c076001d4006400b0103021540401003001952025004c9079010000b0700907800481c1c1e0080c3c024070103600480b84440240043c00a102c00c00e1200e0b4805418002c0150800010450100440750392604c8811100d04107680c801c0050100501c1240b96 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 111846897 1250 111845647 111845659
    0x20901020a15061d0f0a02071e0201090b22050109080604061a0a09020705011d0d050c0f0304080708070b250303060306050c040305070f030c0605181314070e0a05060a030b 75
    0x7009020100d62860301175554040056401e0741c50203001d0059100e0030000403d5428050b80e0b82414440d0015040416441407409400f203a58070a01280c154210740101c10f0300304c070328411841c5013100800c00c4400601e803e0800c0b80722540342020064403810014006070069031506c100c55401301451082042080c8000d00d402800b58880c05184000e402c51041241c0542ca400c1c00d00c044070314441d114401c45000c000042c1040e0301d002c001280d440d004030304007002d41d00c1418000c462009043c409000906034403401405068500035040c1c0c60f14040b58482c0041c1c200402400d04c0d012940f14013207401c4106414505400c00040c50100d0041c4601e60003c0e00041c900411301c02c0100122000300201e0380a00d04075181d441e240d040d08491b040180c8030007446030010110030409503002e080505034041c51414654500190f49010130340f10034912300c0c0026190b40d215448210b4100064004e604100c043c03410000301c1d440400400c16005250042c1c0e8400d00f4017103400c6900600c01c1d00540b10345000a809 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 111848147 1250 111846897 111846929
    0x203010608060405060a0506090105090109030c0324110a0c470c0909061804150e03130b030912070c030c0b121501050706150e010603020901020a1506 66
    0x20050507014151a410711940c18030002c60200e00c1c0041c2a401034540062600f40f4000c50b003401034503140e000744c4066040c40256503000001c00c0907803031000000d50088840c000c803d4412800e50b28207021910078070b050b00d4a8003e1407014106001d080c1d44408096040421401c0802d007440c140d0061405d0142b400400c0c07032844801904000940481c00d40035150228458118061100200860882c0c62a0600d00e0a01a640081c0340078180960854400381c51800310307908200903900c1d8080c0845040d15402140740030108401403d124680528114030040e6041c034201101c4180c58185a00c40d200e070100c00400402d07080c444c00d01400070300062114090740ea9003143c1c41c20501c0d4207000d200594018500c448002186500300c0300b10380001c5015410740b08195a2041c02810031803090441d181001010301c8204005083c030300c550102c1d8522100400689031500151405050058100300c003010b005005120360360b600012400a49588180c0c55503100c0c003084940d20041c01c2e00d80c800c040c58602462 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 111849397 1250 111848147 111848159
    0x703060e0a1a06070b040f06020f1803160e060d03030209030102070302010f15120f08090d030305061519050f210403030b011407020f03010f0e0708060a1407180801020301 75
    0x80310b03030002001420445400c00d0718030100030142c000d000c005031007002420001000a5102c01401100d44c1c8960b800609040039440aa50227410022108a100e1911114840d0074641005440d0401c0d40b1110303600652803c0c141004908800505032900821503000c48104240c0260191403001034054001c54030f640c21402c009000e03042c0b9900340b03500145002780c09117401c805002e0349001d8925a0722040c803a075816030344040e508403030f203813050340e4254007803040c40d142c1d950b01c2b40c07400300007802a43c0100399420000e0420070004074180f011114054104100f40e80e0f030700f03403020f007208420300ca0130540e840d20382034001042035114203021410000252200d5030218056406514001c5000303070380c10800009060b00645e1036040811510081c1c140910228006241c902280c10440b0805000410710400c491200c605460f0010f40001d0103401c060001d04c000c4004000c00781d03114800020a00501910301d40444680e00301074483d0342003142402d12220b804c00100140c0b0010314026000315500c0da9030f04c07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 111850647 1250 111849397 111849401
    0x40e01240f0e01060f02150c07210e1314100f1403030706180b16021002031006030504020612040b061507021503060a050a17060f1b030703060e0a 64
    0x4810911800035080030410000c10341c100001d4845400040c152030742410300595110b030080c2d00c03035021440b03800303001d00e40ea10100c4a010301582d19455a180c5a507643d1a001400e58004030310342108804400386401625030001201803a00d80a0780c5170000c4034521744222000d0b14001e12000c401440f190144050044190440000c41d855220000681c9883c0c01c1d044c0402c507045850aa410741c400c0c844000401c009612090150110200c50800c0c92840c1d41d80c40c3d6103080490784508030b08044840d90a880d60144034201101c03401c0c2c14114510b140040d030b442000d1034507000f01820180d03501c0010f011502c81d0b100301c407880c2208640e019080c1c5001c4c90500c40d0350004403100350098403801c0d00c500304c4020784019990082d500a06445c508101403107200f11300d4200420480e84414400b90009950312421540c1b0301400b811174115100b040b00c001100e28010000c2d20350300c41c141c00601001032020300c690000d003403820350f003203000d40d01e442d00e44003140a0542900108c1d00100c1603c28844000750503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 111851897 1250 111850647 111850691
    0xf130203160807020703030e0405102112050412060b030a02060d021917040b07031d010b030607080108060411041b1115010b090d05030403080a0f081005010f0e040e01 73
    0x42d503280b4105680d008001c0342c44040070b00c00200880c2904005045518081d045980d10041d5083c00380c840d142d66030355503101443c50f6a2241024822400d000c000e100c140002c00c421040c4504084d0b250034548528821640c5c1c22420140950fa41d81c9140c2c44983c0e8180007207800d66030024516070305c85108981110096220002c91190314580110415465000b64544034244541214081c0140d95a4580710a0384000621484c20155105001030100030340e4114080c01984943c000100140031109041c640305028041c030707060001b2000108107074440000d5061303020f40d0280c480f45644080c00f002c44e0103481211090700001d0350341d12110b0081540000c43c2400b0003890b0003150750310158030000201d2500d081c0190200d48100b001010182c2c14200c00d51040d10b84910101c1c1d10703041c1d403522401119040b000074440020010489000d60680c446503030f43d004481c110400e10360518000003c1c05d101d1009540d4400d00003003c1c1344804568130380d402082403007001002405080c3c001c019001515101c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 111853147 1250 111851897 111851941
    0x31b010f05042001020109030c060b040e0f0d031103060a05100c020a0b120a110910050409060f0e010f0e06040c0507020a0b090112021603140712030603020a05010f0e0f130203 77
    0x203050f07103000150b105000c0d403548a83c060315242d80e40012a11a4005000004201a00039460381e07452001c4030810003404242450030b01c040c1501154040e0020306480c4050076400ca290014400c0c0103443c1e0740c0000500455a08440310f10022001e42e01c2601d0107107045001039408407004034000380d9035040380300402c100c002d030041c10700030381e0303a40b04010b01140d50380100485800740500003400d050030048106c008881c2c041c20301e030342846d80d41c900c040196aa00d400074407110b5a10202000180510b07142d050260940c101c0c0f030f01495081000b4a419031030014130039807196482d10b40c2c000c502d9020744201c554a5402515500d41940c4414050883e031388815215800100b0002c48402c81c17a44600c2510b591900c100d00ca5500341500341c40440d186041028103681302d81c02001b4203000600b40050715480081c07662008142d49156004102d46400700d40d1115052281c3c0050091445034880d0660344c05200031150745041c0c0030518045400700819aa510740701030b02c000103000c1c7d543c0c92144c515040d034103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 111854397 1250 111853147 111853193
    0x212030103051f02032404020c010203090c01030e06091b0a210b011403030915160b06090703091a0a020903010c02031c0c05030a02070219031b1403031b010f0504 71
    0x843c6001c102c04a100c2201c4002c4001c00c50905d16010b101c0300842860003410061000d410811a0074500d803c84e803041e1980c40855011000742c112030b50b05400f0300c00c0c1c000000c50142039545444c0d40d087d615114002100c0c036955814060140c501d81d40d10301d140d03000d060b084800480c01142110362000c4040d1002080e20b0014000d00002130001d1080303800502c80c0405005181030200081c14443c01040031405520301040c103001e41d0402412032a01c8504035801094182000d0800d0001c4c40380f081e002421807030402d0306001c1024089403030007107103903400d08400300101d00740d81e50607111b5802400f0350551258036500740524421142c1d1700102914002c01104001d61491010382c840f2422a4205a41c51020503424000107164081680c0548029400a880703400741ca104180c039811643c9080d001201d000600368950410344880c03266840180c0340b40d0300480c4050316004c0000307a603030045081c40b0000e2001958039015900080d00003103540a8240c2c41440282014030b040c8000700811204516843c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 111855647 1250 111854397 111854443
    0x1090f0809220c0305090c0105090105090a1d10050312070f11060a050d0b0d0f1205071a070315030309150315090c1106060a0905060d0b01091b020105060a09020307021203010305 78
    0x1d030010032007c00c004c00c140c5601c0d292900740310040d10150094200f44e94025000c000000d104984011101f01060301403045d0007041c03900798280700c0741101170340055000740d00c103406080020a62000b2101581d0b0059801c5a01304810310b898048050b00b000155002207000c20b03d00102900303d00a004000b40d902400d1004215007024001980c007400b001504c0304250907031400c082548244011000d4449140c00761400d081c1f5210401c403070403c240401d8400c000c0070200034503568503103d800003808800d008126000e00d1510010101b0102d8000c9809003042c508040441500079840b805000e86074604100340c145c1d48444060090200c0f044150100300103c1103822031410105000c1e100d19001000428458108501c45000340b00081001e604507407140c000768046620841914001c1c200e451002c03c00918017010504200c0d150703551041960304110a011560b0f48006482c0d050710402c510050316035172555012450300341101ca02c00c90380540000003005100012484c0c092458001409070844d07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 111856897 1250 111855647 111855661
    0x4020d050f010f0606021c030509030f180103060e060f060306060d14010302090618070f0e090a0510050a1a0904090f0503030906010b0412030f091e03020f0301090f0809220c0305 78
    0x180c10190b2941f00070380703402c00b5081c4414001c1d4030054100741070904a904040d8010103401d6541d01c00c038410240445141104001d40d80c1c1409800f000c0d080c01a10b1b03103002e041c02c80201c5c0b654080180f84a00c0f40c034002c000117040e9103c680c02c2d510002e00741801440180d03070840000e000031200b804164081c510380380004643d420000302030700c0900c110900d4034174035a8450307000300c0f42c1d400781070460000c01c101481d02c000c0030341d00c0c0781503103000b034880300030008060802c0d280c1010700a40903031000307014030005907042103a1140800d2522811426007825036031041400f00140c0101043d030300042004519042550500c540000990301c14170384001141e10b00e90702d40b00640f107180501d124030508407041e0980030340001d10a0712405442081e500301102806c1e1650b00fa400c0c0c0c1901b04041c03070208540e80c2020001d40c03808002500f150307801500200004046a05c2d04440080041006003620200042c0b002c11601c441c41c7d4001d2034011865000244040081c01d64050840d04a4071000242000b0114000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 111858147 1250 111856897 111856903
    0xb0c1005061003050403170114010207080c0d06110405190303110102131401032703030f0203040c030308040f0501020a0e091503030a1d0d08091002070605030f04020d050f010f060602 80
    0x1c1c0d40e004000a0101c03400c85400c03400b4040080c011820804e1002c0d044242d01c11500c001806480010074411040800000080c41e200c0f050744441e403150302c880410b102c692104500020341c582c025101081284d1054108c018074422540120717007214661000d0446110b82402d0030065901c00e0f41c3d01c00b095a840788426080c2c0c0110303160b00d403001080710340803c03600c506c050182c0030107070043c14003003080c0560b40700c04601e515050390254040300c1307000e8034042015031510402022120f030110860941c2004e8482100740021800024140401d090205051003e82d82c1c2002155a0040c020b41da40c4401420042c40d4032007480c140b078010740640780807541420221601d106101c801400a40c18800112001c590740075054214050818500c0516503251703d07003c001c42d00fa2805000000e96078007079030003446480d203140513102c811500130300403d02040e680300c4d04490300203072441056441500d8a000150307540c059110001e20b075108172542086034200c190020100c01810480400c442540c403902662 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 111859397 1250 111858147 111858151
    0xf07051207170f04090f0906090b1b040e0105060c120301030507030b0112050c060d090c080303092b0509060f0714060109060806041e080c06041106040b09130b04060b0c1005 76
    0x601d05220601c904d00c555445103602d82c0038486e000c1620303036040d101c00702111842c0c0000d44441c0f80450820180e0309010280b25070310790f0340120341842c0ca864074050400c03849041c068544150b0300080d03c43c00c4040c017000a004c0240507004115941c0d40d5a140940c0e4a140c5071104980d1500c00000015aa071000100550786e1500f00e000f4103002105c0e501004050b42c0844c51002c41155180c5071100410388100850020340ba4000c01143c0c0d0b4240244054505004182040c82801c6050600602e0075810754006000c06218100992609460030000741c45015000014241c030b4408a0300406200c02c2802216070103040c01d084d5811644c0f160311010995031f0780d001d407044a90142d0081303000215550190780210152030500c0910300c40e140d40319080782c0c0c00391b9220324042e4003840078042446041083d1820469044900320318180c504030080220b07005a17001288249a000c440908100c040d40200440d1030005004224540c3c6916030703501a5040b1800c9462940b1412003c810500c600c3d21440d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 111860647 1250 111859397 111859417
    0x51c050408041e180b1e010908030406020105090c0f030d0c03031b030b01170702070b1305060307020609010e06060a0506030702120408010603210504170c1f08090a0312020f0705120717 81
    0x711b03441040c900c960b045420382144c0c07410041e8805d40060b840344103101074805403e041e070020034641050b03245285070161081006100c2c0904401484d142d99001800c803c141c400e90818132851041c40c1405e4005101c41c004485417100904c0f0418062a45940001307960305007621509501944a030030486c0400080b075403580560700018040c80803a01041c080c04606a0140c81e81e40ca8648560208200d90010b0f0764003400340c1e001c45d040c08034044080c01401425191000185518502500051040c000c54402e8a000d4100040480c600d644284020f40880010100f0107075070759030310b0300914000c1009110581d40c4080c401040030448045040c5132803450342942d203050405090510b040c0340b110502c2480c03500752040d10003a030429180c0b0085059440100440090303004248a40606a0325000300b5641284d0000c0100d400041d0700001d01c46800b0840c1d220050722006580c024041e01d02c9400c5000d8424440c1c04a40500c0f010103074000c01199100b2100d07202840c0c0300d04424500c9000300728880d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 111861897 1250 111860647 111860659
    0x4030206060f0415120c121211030d0c020c03070803030f06100203040f09021803010b0924150703230403060906090b10050a06051c050408041e180b 65
    0x21410600e40b42c072400101070001000080c21a0700401c003050315140c140d0141c1d10a009800540b000d0060b1031560030010302d6003c5007500ca2440998030303004401210204441480418482240d500c1001c009441e4600c5580408000d0f0310103440340a50b0b00c401c020501031191048807808990803c02205032402103090000804403501c0d40710410100304011816141103210178400010300310304a80c80302008103084203005030748440324016413500304449080b80c0d00aa04011079211680c44102016501c4640d08069a0710200d0b00c0d8554019940d01a0b2143c1d070043c211a0b19000f00ad100600a0104d5480303034840030307085080700c40b190700c000e030151048122408080c0401c00c003103100350700180c112a01c80c13900050110180d0b5100030000c070007a100d41c024081c0300e070024801810907002240140a131820101c3c2800d07204007480b1601c85200c4d04a040450b210710208081000136400c0d50b0142449041407030701c42c21b00340450000403000e84544855680b1444420f50400414403c4414850016200e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 111863147 1250 111861897 111861901
    0x1003020403031b02190e010503011a010215091c0e040605030c030a060509030d11091002010510121103060f24090a0209030c101206090203060d0201080411060d1b030504030206 77
    0x9020460300440c08207a070880300d90754620080380f0150b200385c1c0141a5661015150354100003c1c0f600712800004202c103c030314161499203050780c00180850503004400030b4441c003079550b80c03003035410100e1200c186c10002000c0e808400d410380d00300c0080030b0001802d031820000c1d240d440c01055034507080304040c150141c0200c80148045240c41c0c01091340701c0b5a43e0304803403405400300d06400c121038001205d10b24500c8042040031403072400690040ca5008948002e00c1341d07090001000580f02100c0c800c0d41050210000400f08000a101c2222000c400060680b9010703e04030614000b65901101d00b20f84000e10a100f0311aa07040003c0005565072001e4048207699890004020080d8042100320380d0503c11214070105554a0600d03440d545242e507070382c0110448040d00f0f40000e480e9990407010301075005004110586d12400c0c0c4100038503409290000240d2550700340008105807803c0e0050300b100f00041c134002d130a2a1038100c00310f1032107280000207403240c400314201c0c110f400980f8002c0c01a040800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 111864397 1250 111863147 111863177
    0x40809010c210e010809070e070f0e0604090504170703050f0c0c0a06091d060d030309030513090c08010501020a0b01030605150603090606041b0801050603070903060e010b100302040303 81
    0x1940018540700c2c030400c0c030000c0e5200e90040500c03200c445022000502258140b402c950380001c1c8542c01c00c10060061103031a0801c02c2451428400509240c01c000f55a19140c010328030030751401010342409007840b0b0340c0b03503192124007000d44402c03142965007c0c00d03003042d8205800080b049030811500344c0d40c0c0c0340c00e000c0740c8003a680d4183e00c0038040003003074843c54581c9001642c50b94070701c00040c10540c07aa80c1c0a6458011801e83c40d010b2685203144480281082000585628991510a59240c507001030000390710724087e50103009400d401d014403a1040c1c400300300c4414540c0040c07010109034985420b1681c1c2c5000483e0740f80054403000342001c1c06a0010000a00c154201c960010109400301d081444008041040303500220f0f050501c0781d0040051041d0f40c1050304c0f84a10911055400c2507248442c8540030341194010b00c42d940c01010000002198144941070031000b8550084003444003840d4200003134042d2142c0d4400d14070400300c0c0402420b0260107403007260f08030b0354540c07501f0f1942c0510031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 111865647 1250 111864397 111864407
    0x80307030f12140f040203060106030c080402060a05040e090c031005060f0415051c110d020d030f05071401150504050603070b0c0312090f0c270402030709110405090f04080901 77
    0x10921401d403036203e80d0040c46180ea69a00c1074403602d040503043c966840c00d40109490000e040e0303c03090070700d85400b103080310300b940c0414070662042d0140c2c1c00581d1909842400c43e401d00c101c0c2d00000840c000d800500500000100b00b1500048084003101c0c4041100c0f036440d001ca0f001a80c04079803001c0c1c4000307042c03070604003034000e81e042d004804200302c022540d80002c80c04103488005412440f60304180c00034208961021a5085014141c80d01d000c46450b60303002c04c8514110034005428460b509190b500d804e4450421508003070f502c41074011041d80700404044c043e10844452900607032010402040ba81014401c091290700002d0042203070b80d00c1c1240e00150b0342d0209025088502081044881c001c010020301c6024207105001440440030805501d82406144079547d4032607903c4840721541318241c02030344044040300d1444110507840724030000c3d190074103640c8001d248504000d43c50181c0303c2c1e240050300480d00b06a820110721b945890545500d40021200201120001d00c1052640d501c00c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 111866897 1250 111865647 111865667
    0xc030105010e040c120c051c0507080609090a0c03061b0305060a1403120c060117031603200106080105100801110406050f0c0f01050103061404050c061c020f040906080307030f 77
    0x1500b41703200005030400030340043d1a020104074001c6030000903140c484100300b8084c0c80c450188141c013000103052800000b42600e9010b019540301c0c411543c04615030100c1801440b08099000d8260b12810b035881c41d0030800341000e8000d0280321128000705001031802405080d109600090400041904240d1030383d0204c4983c81046805214240b412480840b0150080000d481c5040080c02550314095a0064140480441d60540d81051000c00080400c0348400455540d0500346603c00358814000e40401c86088004840b080d0b0034400f00003040031042d0b11945c0140300c0c800c0c1040c036103a00d8005481c00d0303440c801d04d28074003c83d00b0003007000040e102c0c0010b88240121849c1b1146460500041286091495250145142d56074801001049030a104083c50303003100d031003021030a00d050340b24540c64110410800c1e02800700040e9031720303040d0410b400c20b4a00d0b12840300304549070034541d0030800f25500240180321400d45404004101601c0000c01e0768482503055903800b0380b8810700c1004070740307000d60 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 111868147 1250 111866897 111866921
    0x615310605040e0307060e030f09040b120a0614070e0102060103080a020c060c100b091302040903210501080705012102130b030c030a151203031d01060e07080c030105010e04 76
    0x500e50000c20240d8640c000d048081c01d00200860705e07801030381499000c03a640740008502d03d6008008842000b6506d60644800300030482e80054000c1261b80444c100004800c03180c4103a010b200e584504000b055070045a6102d00300c0d00110895071400c00c103490303c1e0b00800540d070150f40020010000200c0e00300044c140d0507000c1c81556003460508002c05c4458220301e4403a0b60680141c031154044001e00c4c850003140c880200c5450009092080b01000036103e158000790090791201d084034141801a27113041410f03111900502035040c03a04000100411080c000d0346c105003d0301100054640c41341d014100008855901c0e0100c1c0c0f86402e00d40e600a600c01e540d100c90703140842400103060500780024500c40c0201442da40d40d28134280b451501260490807421304007001d0100140841d080c064034580751240c0c5030400040440d007900000d104410390702e00b140c00d01e41c00c0203808144401d4a1004034010359072604c0d0114192148080814940024014140090365504000709540b402d0741101c1e030300c1c100e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 111869397 1250 111868147 111868151
    0x50615060706090204090803070809100203160c050106050a0902070c05152505030d0209040b030703030503011206090f030f081305060c2a010b190e0c071a09061531 72
    0xaa1303076480c1c7c5002e40080b915040821000002c02042c40310510041024074a14a003c51844c5081c1ca03e100251450200803410020221101403c01500354001d03006080010b244c03c40e04c80d40c0780c8040c0d01a50221a044501c412903580016403820520515244d08039140708140c2001c135059001c89021003e8403010100c18042786046e804200c00744018900603030741708070141c1e8a541c41010310064510072416a80031754043d000401c04240d0081c1980d040d540c2c0d400380f0f83c281078004c1c00c0800140c20002c3c0d02800d541d1100003050101604040e98600d240a103480b007000301d40d26040c2c4c1c2404180305e500090074a070840c10010301460000c4006250242192800c401080000001840c261681c0304011003540c3d0740f659102d40604d00381c0c2125070740212046c050010203060240085020001511414501c54041040020072442000721400d130000c400c043d088034980304100a9a8210070b40c0c49858902c0036107810300c19802c1403c03509900303150911642da43e400f125500020200c0e050b80d8a40e01d40e41d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 111870503 1106 111869397 111869411
    0x170c030a0e030a2307051c08010e101a0d0f06180c17040c050607050703060f0b030c090a06170616020d0f0c0201030b09040609050615060706090204 65
    0x180f070300150034861000303000207444c0d14054014000c1c0140108500c0c941c2c0c0d0300200060801080c05541c07091a1641e0f41c8461440d00f410956201401d40b00480e0300b0700200d0100e50340600c0440303105003424034210110000c032007101c40e003000038030301f1640740d100400552502c42109600807051500c00c104580c03a52201070441d06940020310130100041000031b05004002d0050070044c0b102030066035680403140f070100d89400f00c5000c12183c280c81d0100d041c0c15149144140d001110001d030080c910302c0e45a40c20001d9503078005051450b0540c643d4008120b001140001ca014248043e0007409182026103101c0c1d0021100d038412821584030001c0410401d600600b4030301c6400c01c2e810040714810150004801038030b243c0601c183c000d510407050208020407075100b00e03200b602a42c240c030016150481108000402c015080d98820414844000401d0080d8001c906a81c80100009415 = true := by decide +kernel

theorem cover : BRFrame.Cov 111690647 111870503 := by
  have h0 := BRFrame.cov_init 111690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 111690647 ≤ n) (h2 : n < 111870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
