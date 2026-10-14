-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0654
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:57:35.448907+00:00
-- url     : https://prove2.me/submissions/22a3e660-7b73-4a86-9e13-e03f14f88dfd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 117446043 ≤ n < 117625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 117447293 1250 117446043 117446053
    0x41a040312120b030106080706090605090307050d0201050f0409060512010504170307032c0609071508040201210f0c0c0b040f0c120302060a0c09060206060f0a1502030318 75
    0x1003920441c0c2000035446a240005181d10108010300040c00044061a0958680400828501c0d00010654140c4145442d0200203030b0f590102229280708080d400380c1c040d00220030400442c02c1803075402c807520344141400750a05003200da00300001d4001c0e17030001da0415154402041b907401c12442d0010340003802c10091100345040d4a0310b01d6502100030740b428000c0c00000c001601a40709a004038040c0a0f11070203041906048040f40000e840c1c6180303005068080c5001140318104001000c00071103800d51b603031200403e68540240c075480ea00410a0f410702a00e807801d11260500c0309209a00084443c80028a401d400c4840350129103500c8241002d1085c24030681d00865030403040581d02c03039804024403507101c50915082c44411100e03402045150103001d8030740d04142d004945688681810f01d400c002c42c0040a400f100e08000c580b003941c02603003244d0086062414240c6034100e5025000d0400317118550b43d544460707080654080000c00507000403040c003040d01b00c103c13034413960300c814980102 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 117448543 1250 117447293 117447299
    0x210602120c1c0506100810080f01050a05010504060510032c1609050c0403060f09050a05070e0915011e03081305030610150c141005040201020c090c0405060c010209030102040605041a04 81
    0x1d20f60854914040c0180203403d00021020b81035095440090212310040d00c15403914030b811540649810740700c241085052034000b09841c105031044204681006184000710580044142c0040c459114080c00d21000380c806005d502a01a80c55400c1c04110002852070241410a03100c0380d401c03070f4000034401814401440400c0306950152801e403a0012400102c5800034001d40340203111503a00145280601c07100d51081c4a40803600004581400c080f88156176940c1500c99140c07141c9603511409500f1907001449a4000c40004070400d80c070007405030f881a505c0741c42e11003290700031680300b140b1902c0d41d80050102e07040600461b50401b01c1802c540c52900d08140403546c1010a041641c0c040000010882041c04032294011085401b640151180c40c11a40450409041d045400b81e000d032203103154000707a5007813511044d4452100104c00da810036040c001080f0325517001c030040030388540d0280007185183d83c0a2008000a0040d926000d81d9039181945000503028440960b0701c040006010070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 117449793 1250 117448543 117448549
    0x61c090b011e0e06010f12050103031115011a0c0c150d0609050c0a0302030601091d07030c0507020d24020f030601030e070f09090c080f07050316210602120c1c0506 72
    0x10340055090900c444211b10700f0108962000c5130103c4000998148000003007415000901c1c840c01914403020341d010090311103c1540c0190302071191401141c40d0f0008400160f0034880a03003100381c55541070b0341031120707940001382d407500c0281180348415070005102111038003144655030003400349050500161512001016403401252080024540c0010000b140f980c420881500600202c00800003003001224200d088100106d9155010030b180040e03100159000340183c42c461540102034202d0230015640d200382080318000c1c1900d40c0c00f022108007010100500241035001d10b14500181c580c5405000181900d00b1294109990303002681c05116107141642c104040d106003200100300180307103280640d400712043d40690550f000d00d00c90354405100100b0801c2c2100e1003201220001041c000345c5900841300752003200110b0000e05020b0312100740405400c0410381c02100010b0601800d8000124040070840342c0c01c43c1507400140e021009000b001c6424482d004d2540308011600d07100c008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 117451043 1250 117449793 117449819
    0x190b04140402041d0a030905090c030621030c0d020a02040b0a0f140d080c010c17060f09060310090c0e07022d070f06031a030604020f061c090b011e 65
    0x101078011601c60b18142c0e0303188240c0f81380c02c00811240c8112001805a401d00502d1078889002e814401c801d140042800340c20303070314140c0780208802000408132103522000300f0020003107c205082e0038003060150a01d1454103100000340d6000e07075006071159100c540304000071a484107080c80d00c5046425001d100c44000032140e4026030380103009000102c4041c0c8009000782070b03211030040840100040704030800d0019040340c0e01c01c50300d40d15810905060822648250030b000c492290700100600a400c025251620f00c05030403100140c1680d00d80c2d411881400290b07502c400003902c4080380031100300000503a10701c2207540540b1910160022482d8603143c9148011754280d154000380d00490301c908419001c0c070800d001401021101c0085580e01d00000c1c0140c26604050f100043c600c801e410514200400c07140d10440e4010040200f80d8241000c100080e0400c540f10486c0c2d980a04c1c80c1f86480083d8400d64107054002c08480c1031030340c035200d6420105241ca154407440105441410000f01d4000c1a07 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 117452293 1250 117451043 117451051
    0x3020309060c16060906080a05040203120a030b09090a031211090d0311071e0b0903060604180f0501050615120402090702030c061006090506040614030c040b03190b0414 74
    0x803000da691007452651494006a1100c444855103e00300001d0314582244007841101d05c0c548900304181c0d2145d00f11000c032601201c010350540c002204514a56042500511440c111820002490748000d00410424413080750a0303540d81c0d22842541043c1174205041000100707a40c00180101e40c248458000c260281054041c042c8105e91202400c01d40659120f00302080c0c050100c1d80d09942d00e00c0d02404005610b400f001d41220046c1340403905039248000c403101c80a01600804503525031303005020003030945142d6682d030b688400b031415000482244c16140058002c000204290901c0350401540b651154030050600000300700401c0d0f0046188085079000703804842c07102459945c200c0030780c04c52045040d001210b00a8608008205450400301c80603103140b6582d03007500c5522003050014900c01e5010341e50202c2c400303884501c06440800000e540c03003690140c0d40c9051070b5481c1480318141d0010b484005d00440518500d075078000c1d09100b00d4030600c1c0700300c0e400c0c400e10004c0005505881c901070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 117453543 1250 117452293 117452299
    0xf1b100e04020702040b040c020c0a050f03030414010201061e0609060905030d0e01050f07050a11090103080d0209060904060305030307030e03040521010e121309112b051f0902040303020309 83
    0x203c0e514080d0b6640b0340c06580a03802c06082840070114090009450300745a4086d103115002d00e035030204050401c0d6801c040003000140003580303414145401c200f02c88180ca60480d0466480d9400032680f50480d800c0700c0c03d4044c0c2d400c1c10100943c280b120151481849401c0002080780c012030801c46590001103e828481460900400034144600121560303c500207450460401c000340840400c0000104500303081c4c069210000d050740188108142240c0c203110140080b0800d1091a030003c1c0719500408e841134000b4021441d0286000100d42511015403054407143c0006c02085580d40c0c260064a0300c46458a000d58941402c160018020b041ca49461003140c8494601c40c641d24403095001d85c05e002070040c1103804d1050343d440b0600c0203a00140300d1070741944010000081300740c401c0c0258947c14058103603c60400c0100c078028a034502c603140d51005203518800d0100b044060030711a8600601700644000714030520541d1a49010710035901c40004544100410404130b6804801c1e140302840c11 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 117454793 1250 117453543 117453547
    0x703031d1309050c0618150304021f0e09070305060405060301091e060f14160804120503060103140a0204050301150308070809030f0102041202090601080f070f020f0f1b100e0402 78
    0x2c1c0c2080b40c80c1440c40900a42c00c5000000c09100319000c00045c0301e0515400ca96054989000e00300c8000795005c01c0d14029007141901600c1c517080514007025809440b039500c1c14220b012000c0002030340c03505007540c020012980d510203000c4035040c0b078010341d0303407100c000d90082c040340c01d031540c0310201c0c6823a420342c030519101c016a203d005c22461303030441d4100b21944c81d014050241c0030300c07056158480594080c40900d201036181468503001311001c03441190030030b480200c01c60600d44103179400d610040915041660320281e03011070744030b615a018000c0d90017890068445003404241821945828812610b008200030100000780c400804ca54074240c0c4800241e40b24070440c404280751a0704a552070005500201c0c010520186401310202218004c42d445202902c44400540da50b8500b41c403c80141080c42c0002b400c85809001501a0442284102c41c0041d44075901242806203900c9242001d412003110f08a45030450182c0302c03078550007290000f44a07241d07248060624183c92655502035500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 117456043 1250 117454793 117454811
    0x30f07051612091701020306030115030c090c0309020d110306010911030606070809150d0501120b04020f0307050a0608010305070602030306010f0c0804030204020d020c1005090a0f0219080703031d13 87
    0x10610001c40241401c0900e14800e4940f40404d601035001164040c1c042e41c604405600210310100c44130007102d810841ca0480d641c10001140701a101d1720100509240d1a1600b600041c3c403182045000c9a02030700555054011100805080c51030603402036480034108548030038400454412030b900704900310364995980b0300e6880c0940c011b001302802182e01c1075000d05424400c0b80c1c034400600f6451501170b010840741c1e8a070416949941e0041c9006032003408010001801410090610701e4540c60080403504030740c0d6503100082c41010aa040100014080e80041081040401881d0f028103024005075083d40340c4500000c00b80030107065010200403004443d101481000301c102da0103150042c006550710802203130318201a60001051910074441d503409a01d85043c54401d1302d000d40b545401410480d42d40d500c030035489219980040c3d91142d810307907002c80768000c0f6201042c001d054082c090410b06245050203004465140000d200000d0307114002c0c6035580d40c443c140105172803115000076900d0340d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 117457293 1250 117456043 117456047
    0x130207020406081b0f0d0501090c1401032007020a0b0408070608060301060303020c210313060f030603020306070507050312040308100614070602070812010801020903101a240d02030f07051612 84
    0x5035400c060f000354070740b00c412000e100b2b031070f010b803002c2e20856641c18074105842030044003141d0705030800180d07030b01d2440d0200407641c00ca070000702103181c002000580c20a445580800c120350150f0b2102c450390f03110300340820500303411140c415070100d0304400030000d451071910302035181c0e0503c00c0d9a9109840140c1c1c90922101d4588289a015100c0c908072600e07400410a00e40c50840b00707015000102da071705584040d0140c464020842505c2c3e010300a003410791a412401e9403580c218040c110749502051100084000c0c010301581d100b640a40d8400781241442c00603072658048541058082020148480c0440c1101c0c6040354045540010016620500f0b0b00b001c0c280c1380109040d001e4000014000044d010805401038070300e82c40308031b00340c1d4000713607802070908100d684003011200c0710001c4400d45003442c50902d010b035a404104603141141c03170400100f9000103501000803500050b9001c014043c000c020f49040550100090500618150114000c0c2f144c040050100520b00c400c0b0a00144c0c8080c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 117458543 1250 117457293 117457309
    0x4020703120204080a031707140306040207140a030809060f061003060909030e030f0106120204020a1e110d0507050606040903180e01090509071a1602130207020406081b0f 75
    0x8070121108648440e2211001610b40c2e203403203030560006a0000b0746010140d21101c5031030084020751100340503035550107142283c5420003014a0b900517824451079020030901c03489240f6102d5408003030400f0703d003640b03030140c40031502a241101c103501640402c80c002260400f1070b50414021101000c481c8210038040340503007455000700110070b040c0710801003015003210740340c81d045004406490360301c2c01c041d101c1ca00302da80b0b6103d0202d5144607070141c0e00140c20103074000d060104081c0b0380301d41c080031101c180464a6854003035000000c0c00c0c1e420383c020b40e10b81c18884c8410810041c5440344c68040e45441355540c6120183c103c51041d69281d030310108060080e090300e41c040007540381100051342e84400c0c075031080009104241c50b03941428009560080003190b181c1c140d44442c0058480701040380c40c803030410f40100e07040720861a040b802c0880582d41e10000b101110450502c00b42c3c0d174080d144184029140a43d00141465112040400c00c01c1640302c0d002d041d400c1c05440c0c1c1c540046d08000043d04503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 117459793 1250 117458543 117458567
    0x70f060b060408030304021509030712060f1e0b03060408220905161707050a0804060b090109090212010b011209020102011b050a080108030307020a0312020c120d0614030a0204020703 80
    0x1140000780050b003e20080090b51141c4e000b160140c1c41090110640b0b980d43c444c0c0c00206905802c1140180211041403800d81c05050044000103030f188001c2410300100c03024010403503c42588040a005039100a0064100582c425006002d01e0300b003540e50041d81d4060b142e40c40c0342070783c440900503100c0600d0352000c034014101c91000f4071403400c194034113920382c60112170110006040c400d4801c101c1c51141144500400060b600d49151074200842102c3c0440701900c11240c00b6140c2e480840305a5502407064040d080310580001c800101e8410041c0707003c02d090a0250590604060401680e00f01e020604031217810800811081c11901c0100d0040040341c04c10585030808200c6102011782c0700c000b5015001980d2140307921079888040003503030b074041210381d0030051780586990303030005c0d200d08014900c0109440c40582000524822103003450800020902180303004110048489103500802c070090000003c820006403807603003c00c2e1100c81d5103074045d0255800148040c10148260f5201d040303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 117461043 1250 117459793 117459799
    0x1706190303080105010905150313080c010905100f0b090403030b0f0402030a0506030706020f032a030c15240f01170f06040b06030603100903050d090309080607020a0503070f060b 78
    0x50684a00c1c001d00002d8082c020207000410312100850b250628045009a909030030701418150ba5030318251101400c403003041141c410f0400d01000c0c0000409000310b1020510030303400b5101941a54440c0001c540110311000209414960a00c0c460b4443c0c220141d00b164143c5008540c407d00c3c000483c441c1520101026049480042008a03d1400d60f1102c1c0c0203940441c2a0380c0f4155840304126030340e804001400d804ea410401003103802c1e10780302c0400e142c1c0345c6603441c076500f030b9000c00a00700c3e0464000001c41c0b80682c10030040540b9040551414680c801102240e080050182c4044a0152885050b110707005003801008103600c0c0c5c2c0a13901c4a00300d9019003d1078806450040d0321076030a80400e40d44240100d0a1450205070381c40c004003560700c100006001841d00c00203600d010f001801442c0f005400348a8108401c190301c0310b09000d002000c50107501d6003446280341c0341484e0320b00140100080304541001c880b080c00680088115800c6a404c0b410b4132013801d03006d0900400414000e664554 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 117462293 1250 117461043 117461089
    0x302010f0e22020414040213060c050a020d03111005070c03031a0a06021c050a120203060a030b0c070302071502030f03150303131e0e06060c10020a02070e0c04061706 73
    0x1e6404403d070020000c0c1c0f07114802c490044419070041c48242d0003035201c1c40d41c0c0b411504000740021442040c01d8103200f40102c04450502615170080340300e0301c0600d44103a0010b82200400440c541c01044408040307140039004210505d0105002042d40d10020300003001c250b00e51403043c905400140c545825842d0040c03401c0d6400395a0f43c4065a105200c44040301c3e042c143c10808400540104c00765210181c094495103d03480340714000b80c000b0b41c0020b02a56200800301004008542c1740c002c0144500200d140890b9249201c1c28043c0c42e119184e4080c0310901c001541d04503e45030701000350384462480c1c1c4621600ca4588092600c00c00c0c0300264000d0f00f610002c01c6604070550018112001c403011055200c1c401069001031281a0900b80a40d0001000650124046040a074010100c48003060103803034000742c00c0d5100000b40d9009140c8440164051034062044171000038016801c0010030f044c0c0c6160610f4242d0107440c8511011980303103180ca64030001401502e07a08800c40c1e0440b0001003001c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 117463543 1250 117462293 117462349
    0xb07050a1403060a1503091505100803090d26030c18030a0309051215010b090108070c260c03030a0f060501020c0901050f0f0a0603020301080d090302010f0e 69
    0x18025000103000600151000c4504a0810403460031240140ca000d0b204036000d50a010762101840d80b811444000c041d07440007000c0204044030b4448480d07001e00e800100d0581040a200841c501964104082c1d0f40c0040000c0c80550340ca9403170301c40700241d00101541818403c50820840003084030b2211100c0c010000c208810b03581c140c0e0080150750418070540c201603440c0000c1c96620304128000501041c0710f035205012501d040c1c03055079043c101c0e200884098089803480c006994030207900c0345014043c04520917007150381100d0003690114103881c042049884503200c0c83c0e418120203141c168001c400300c024403013481c00c0808540702c07034406e501100c0e644d00f081010b070002480001c1e50390003890f1400034081038941c0301268405415a005241240f96420207040008040b01210226400520b4a440029544a03108042e00421950720016120361401514904002c080c074492805c0142d9180d040c00183e030031074669100d01950307291105a02100351301054035440349031041507c550141c1501 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 117464793 1250 117463543 117463547
    0x20d030e04150302090a0e010b03011802030c04090305030f041104051503010506091303051c1812051e0a14160c080d140a0215100905100b030c0906070b07 68
    0x40400030585042040c124074141091034408640402584000b8500106034038450540107224100c00143c000101104000c0000b400c45800440101140c035103585104103504c2c050103014040d81d0107030380500445c0b03030302d41d0018440e100051400ba18080c110000c1802c2c80150f8084c1c181414000c1d004000034280710761140704010000d22210310944c01c0c02d0016040d801d20700d20f154003e87d02c090400000d010250341c1560b031508030501500101800e08100c80d0119541d002e0748805500cbc0d25070490440020b41400c41c00c030b40c2600500403c2c440100100480b1101040520050a0428802a480d26203503882200c0d0602008500b1600c4070300410080444d140c40c0743e0300e0516034810403020030815580d11219444041050000700410505d50766445000307403c00040c00c4030005d03031040d114865808904100300900a50340344502c15880d030b03014880790342c1910803660048248244943c1180c40d001c418101c602c0020319902c903c9202040c0d1030340b0b035110038007910105607003c41004440d04d460782e00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 117466043 1250 117464793 117464807
    0xd02120a06090c02010c0f1b050d080115020118110d150c020c0306060315040201051b010b0109060315140d08070f031803050a0b101508010501030e03040f12060207020d03 75
    0x20786541514010380103a0440c014418120400226295101841c203001c4040d2246494881610f00000c448800d00001802c04d1101704ae11048940b07611540b941003640c60072111550740c0c01e00c401d5a240104810031080c2c500f514003205540000c0030083c08429501203000b01449060042c101c840003101e524070455503400c00080320b2030740d90803981c040001004060b5100b209499076501a000300d881009070044440c0c40136030150042c10514a40325604440d4512714812518203c4240d6480424805542e03024044030001c00c0e45240c140f1212410101c07a41041c1640d1050200c03107520529220450b8441d002445d1210340c0160009454002d1420700b158503d01d504c004074001901c0d036000c10104c10242c6200000e03603400c00000d2969928035903500c00811009802d074081030b0402d4000241480454885042c113481039614140c0760b514000004d01910f0740b00c0c4020307110b90070600040c403000c1a01c04000c0d0443e445900003c3d80300c0d61344c2c104a0000d200702c90f0069040090008a44103241d04904 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 117467293 1250 117466043 117466049
    0x4060f0b0d050109110414010e06060405030307060c02150103080a0e121005040605011a1e0910020a1101050f090402070c0503030415080a0b090609150901140a0e0106050306060d02120a06 82
    0x1205d031400c061210100401c4039000f0350201035184c984d0f00103100c01c1081501c42540103102070041442c180d02e4400082c55a0010749003151016200d203012158594140030b848801c2030001500c405c6035041d40d0780c41010b03000b5000040b0401242c6103000c4100d5480d0055030329066141c5040e40c40c0d041360032440c50007408045030b0507290749003407800004041c1c0c011003100008448c40208a400d03c0034030b440000d050510a000720003070090038030904800e0343da641c601084c824a40d0b0001d000300016850042744030748c194001c250501030148515020345251030308503411134070100c5006940710040c0c54110341030901a008950103210100740807803490b001d003421b1003003c070450720b4070307121980d4a5007407005540e4150b070116040f040e108003068050804c61002c0760815040032005407000c0081c800302c3c014113004d03070150152201090f106a2181407601100d806842150103000466042101c05809488050f05d09402032000103030420004000342c0c19200407090340f00d0b164210b818039808081c041d1036140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 117468543 1250 117467293 117467303
    0x1a100306051f1203020a0204050c030601120b0108070f02070924080d02100b01110607020606040f020903060105060705030f13030c060f02100b0d060e01050f07020a080304060f0b0d050109 82
    0x500400e500011440c210240e03103004034602500e9508101143c66000c0b1070035001c030194405c10310064016501d03805003a1207542e108034440d480340f5003000010491101d10701080701c5a40340241d11b0300103903072040c05294003040905000011125069049150460746e070701256441c0d181560386094044140e80402000b1608a2001220380e112041c1ea6103800c9000c1e02d0601583c00003043d0000e02c40c0981220680d20014100004510000c2c1c42442c2094000c4501c40c00580100c400c0041d940b40c01c1c403135107010041d0104d0450034101e0b6200480e0761520103008452180c18007040c0e980810404004807902c070804841201d403210160003155058010900046130324070310041000c036442d886100c01155040040d40206124800c002c1d4020080c01007400780d6420a084400300d00c01300e02d0341d000c1c1c0c16a0b00c40c00f20000603103240c1b08100c0c1c500031901400305030841d04502c01c0003000c91084400e4940050300036100203200440d201c10302c0f00600c020820326401100b051440400e000041d44494030305070240e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 117469793 1250 117468543 117468551
    0x12100510090c05040e1b091309060606050708070f1e0b060a05040203091c1112070b06041b0509061213020907080601020a060f020708040b27010f0305041a100306 71
    0x1802e0a44290203940180820800d040c400039003055503040781d02e0b0319a481100d810f4640b0414801181081300b21144020801d5224842c2c1c5c0c003002101d101d6540104054581242000000e40d248081132040c1c144c060454044580d01c2814032681004501d0071002c4240f400c980c10f461450600f8412004655051051f141811b00164074103240c000c5074440d0302c103b4090f04030781c0401c0e800080014488409501041004003c43d01c04250404c141d00c03030f0b0079400c3d400a0300c840c554074040c10b007000001c00d444e00450030300070040b19008020940482001190070039585034810b0b8404240b20703010341d20030240010001003d00a9100110750003035800d038001c0d5500926980c0744401512194000d81b0014016444101c0180104400b58000d484a5000702c40240c07070720507145c0b98181d45030015044104b641e800040c0c104d000002e140094008052000c0d00d1128654030440003824065000140d0230504d901d8200007420002a0000d00002607042202c001850815111080e800d2a990100319003491030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 117471043 1250 117469793 117469811
    0x50f0c030606010e0409050f1605040f0e120d09150b031005101203021f020c0f210706090606030501050702010b030a0c060507051005090a0b241210051009 68
    0x201d4402d00c504010b844500300c0c1904003007884028560203d082c0c0d03c50003003c14292201c0024018101a69519440810f000d41868100000c890f0b81e1901d01894a190200407a002c400128281907015104405280c9074001d180c1400058040c4020080040700c1c64100450348034582c0d44650703029482507040700c4040040000500880e03809031111003600703410103000c1040c411041c4070868450b11030310550f18222900d001034030b440d141d0807420041080d0042079032801070504000c1b4406255080c001840020344802c000c042c03d007503803680300000500c0000d5502c107000e43d0390005820a40d1141c4200b01d06503403810b00c41d0080034203481000065007414000c80d03042c0b0740080c14600c240c1e00800c1c4c00b07114500d4a00159444c4e44092400c030355a0140c0c2c01e55602603003007445040e21410343d4501a048800103494094201400280140300082690f14040c40c411700d1001c3c0100b4200d8144d0303142c0314000002072034600d0000c0800785034828904200412100c07809a426541c00c84036148028051400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 117472293 1250 117471043 117471049
    0x6050406080f04020d110102030c0102041715100506071112060403030f020909010b03181603020a0b0a0816050d11180607080703080618040f0311010b03030a0e03031303050f0c 77
    0x200a4a01070340c0b20740680c03e2172012402c85101e20080d0765050040300c0c03a1a61500419080e42c200d81d001540700f40d00345410050114003031100019082d4507620220113850408489a0f0b82e4085000c4c40340944000b0032900d04100c41c1b6099000c1d0030030020142d10725000f07940c104650302d10088500310002420086183e100c4003c074001e035500d50500a04c2070140da0300700514440150802030000c502032410f02e0103514011000c0c07100f0403121700501140d44242d0700b18014004000c0c1c4a61003446401010400b03083c640e070384a54455007207006000401ca44030300c48142103079035001d205981d035000b615040048018007400401041010007046080c1d44200300c00b010004240201c8a0103448900108810000684a000e80c1c940c045030080c0200a0302d0840040400c0c903400488003160006483d100403014160800c00f48134003030b422880280041825100465207d000c3c00102d041440303c0359008200c0c958042c415604074003507070310305000007980d00c1c10510764550386104070280d01d02070044808005d007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 117473543 1250 117472293 117472321
    0x80f010c020f1f06030209010b0d0c0503060a060e0a0801020c0a1505041e080c06160305090f10090507090207060209130b0d0b071b030801170c03070e1009060605040608 74
    0x30506005015843c940e110ba42030007103c0c8448071168039903141c1d004001a43c031120460302038103a079000c0e00c1e240d00c1c1100036881101d150003d00428003030140100300056884e17038034400030b4138202d1a2026088842401003400e241858010014650010510300030005002410b000c005020304400001c190b256101d00d01250f00a40380544000380d14104045407907248560b02220900ca941e415107024100d036005805e1000c1518400c80800b551010150200c0d454000c0a801c6880340010342420340003942c84035517400400580180c065190010341080c07003802d005640c0140b21644041d50788403043c5c50480c000b507010042c4a4401e20300c01803813022001c0300e4400c0d01c11810003d070034103001e000c01c0e8440065442d0000c00e084100240d12a01c0c04241c2c0161b40c0d84400c1a200e500c81c5106941000c103102058003550000c40840e910407c540c071210f0740d00069600c11121404d500d01c0094580c9501c0d0959202150800001c1c0c90030205c0c0014482d50160061044402a039500141600c50703c046480032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 117474793 1250 117473543 117473563
    0x70f031e03090b0705130b040603150806090706120603060e0303091e0307030e0409021801051201020c12070201030b030304030b0a1503020d111c050a17070803010e0702030405060301080f010c02 85
    0x42e102580000b40d850380141c0007441032000c100c1b090400726940742c810407101d5015030400c100194441031103018820f00c1842c3d00001d00f2004015001c00d00d09003511a50380c2c0c402d0312030070082000e901240034000c50703190b01031390145400a0041c085580c010389100c1c0e1380e0303000781e58148152042d62004181a5400c500840f25241d4000c040c5141805075241114003000720400c1c183e00941d1408404010303500c1009049081a1000000d5910340c5800100100c0c2c1c01d11240800e140d0f401037004150011012440b80100318080b882e89031582191300048008140010303a01d82c144c4070001d004000d211507946c24910030040c0341c0c0700b40070140080820701281045440029000f0700c070b07000b0740700005001d000066a00e00c0c010700202401a103010f01c19940e86001002555150084101c04042c860b141d1241c0901b034001000352480c100d107541e900c1e01c141c441403143e002c018244401240c1501c5c82842100d00500d0f0090400380c481d61200e070344580b207140546c42c50207290320f8101460345090000c18040c8034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 117476043 1250 117474793 117474803
    0x418090210020a0f03050f12130611090a090203100503030301031a091b0607050f0709090201020f19080a020a02040c09080c10052b110a200a060e03070f031e0309 71
    0x4084c55036002d0300d560b0060b050450200354107102e00c1003c09080c4030724504c0b40c2d000c0c6081c1a20101135041c030b00116503400c2048500c48004028040042d25400d090404079100032800580d6a5a80480508201c0f081d4010550600000000006011090712a100e562689150060382c5480e442d0740503030b4481185100d801d0004e005500c03030000346080e03000340c4211401081a2001c9804d42500681821980d80180c140c3c5035503010600e082d540e0402259417041721000040018150301c64031401c0001d500c3e48000d0084100041d6040114400d010750b1180c4d41c1d01600500504201c408043c0ca143e0003800381691610071190920920301e00711000017590042c58913210316182c0302d06040d900044000c0000b015030f444006d60307480600101d01c580904480482e00311611140d240000411144a5524014281e1500d002c44012a0b1000c2082c803180c1d94001d10009803a1000c001031821402580780180c4182c0755014620705150f00031846444400143d00c041d950180b9195090b03048407200180900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 117477293 1250 117476043 117476063
    0x60702030a14041d0a090b1f091a0d02010507081204061a150d061707060e01090303091401030605090f06010e040207080415170c0a0216120f0204020418090210020a 72
    0x1103500213103d07425070004d82e00040030039403500503241c88a20000586080e48030309441c0d402d42040c0c004041a8001425030490140300448110801d001011b80604550340300d050610f80c60011680160100d074280c6900c10016a00c60b02c040a01040710f00b01100c1c16143c542c1000354401e02c00700656100d81134080000c0a044011020f604400080e401440e008080ea80e916100420880c49184041c116030340400d00600c00766040c0500244485942030191b8140442e04000340002138010250b5015030380d201c42041d040d0088080100c014080039481550000e046038148030b941c2c52040f00b2a44a881c0a0700c8207003184810801b80401c80c400c003000038110440a0000744220198160101031000700c0703152603906d4804000802040a0302581c4c2c60044200c00a01c1011454040c8507030158403000312050609e141c60303d20041c07000502e40fa0000c0403201d10076800403c5503110350545020f40300140ca036500d8103842c10110001418601402c1c0e10801d205058011190b20019800400780d911a201caa = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 117478543 1250 117477293 117477329
    0x30204091a061c0f060b0705010605030a080d0c14030717010602072303030903010c021b060a140d1b0e150702060708030a0b04090f0b060d110d030908060702030a1404 73
    0x400304044220010984c480700026051506030040b00f0141450040d656612070080c90f08500311886a4403040c02600b00d03690070303404102081d05588550100c0b8201140e0301d298200c0071181c1d2002e2940da0084204080140014540d225900542400b5502e000b04110790700ca81e07081c0c2e42e680d6140b1980544801030f00c181140100c80c00d039108110080542260304003a0b10400007800c1d5441c504481780141d100b244003081e501030708502907c003007009903292440c04500040007000c1a103a00440c810700140000e01a9007800e01d5401141c529a10109400804460800c000c05000c0c100405d188284900d901510318200c01c4c44c220752000343c0c001d1042c0d207403804030381d80c0385201d410080084209540c0c40d03003003c90780d80b25401440e030880c0c410300c48808900d09510b044d1982e44000b03030082d4024044207540304000f032112608810200400c69110f00964464034080314145030f20341100c45180640001e000c1c002c5e4000026086100e6951245403040501c1402801c0c4d6005910821105102c490561 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 117479793 1250 117478543 117478567
    0xf050f010612060302090f04021507030203090108040f0210120b01030b06070b040c090f0c08070e0a0314031c020d06080307030905090c09030d09050103111614031306030204091a06 79
    0x36842e440700c0720720100d1415030b04d400241c01818200d441100c4a0140c508002c11440e2a0280c45983d445070030107903040c10f485841c000c0d0f03a8000c0e0a05541404030b10000310302400405030081c00d640c0c1e401420981d81a45410004180c0001510791841c202d09140202da0158000c1c020481020b03400b81c00c1c2810007a0689030b20b450b0420141c816a8600954580420030050902502e03441d00e444107000b00394507102410081040d00010a800c0c1000710422140710140c1d582d40b03601c003c0f282c00920192840c500401c001c0d09620403903110b0451507410501e1818106c16a4016004c0c48102c01c60401030141e8680f1819260300c00c4840090006012020912403440d2015000c0d801003100daa84c14201180140442d280450700c440d16008100c01640800c1035680c10300130080280e00366952b82c2d0a1802441e101d44524041c80e00003406202d1030001d26202e008200280c0f107032031850103900c001007039075804040c009600c44d0103004241744c00e0104029060b001c00055000c0944041c1031145080004030b55 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 117481043 1250 117479793 117479807
    0x1080604021b0307050706090504020306011205090c060a0e03070512100c0207090f0516030e121803010212070809150105010c03020f010c02030a12050405030703050304061b090303030f050f0106 85
    0x140034540c424105402c01222010000b90041c0c5210b0f0005090150406401405046050788841d01c258010020054a66404a04003552800d04100401e02c1d842e0f90340304a0070045510083c541000000c40d40212080d0710070649000003e043c1c041d1680c1c59102c01c20b0104010041540045691080c0703040c18204103140e0082e40084042d00c1554a1103842e060362406a904862105c2c05480e16901400480d800d0b0407071081042000b0700f001c02c800c80318000100c0d10350340c11450307502c03442901003021080d01c2c03802d604070300d881d68004000f10340d500890141070440b0748003500d000c00001d010500142c144640024020f2841030f54100c0a0340c10782c604401128400000c7c1003c8045024a44806684a0017401168000c43c204d802440d180c2121842c028101d10468810f03412150400080c000070230404011170300002d40514243e0707500c0c3e81c3c0d810301b217001c0c01440600c0624554500911a0100c1d0300c40b40e5102601e00c030340d605000c1d050b00281c11100382d50040c1c3e0242d0796503100c20300402940b17010b448 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 117482293 1250 117481043 117481057
    0xf15060f1a0304030503040f0b010b0307031d0c01390b1302130b011116140a05090105090c0f0a0503010e15220e0708010b0111060c12060f0402031509150108060402 72
    0x75414540e98a1a528200e01072004c1e8400341446401005015115405008033f103012110096503409004001d140c1d9aa110740031503415040c424096080200d03280103e001c4028650740e0743c83c00c071281d002d00301041242c54100d5000d43e89010940040340d000e0001405040c1d4054009144800b03220000e58140018008003088505200501403a034800300342c240040c000c15051010403080851030084c0101e010103a5184081c424a907050050010740d582c24583ea041d15803d940c00c1c002580c1c2c904104030b00d40306240e050744070a8408905190502d6005004605031a09019050000d0b102d1080c081050380c0302601c100c0c2c0c0401807604c12181010300c541e5842c4001041c140c00b245007a40908514144071481d0010342c802c0e515120740c20441d58201a40031903500c00c09000781503500d00035103048002d0107508141071466200c040460366a40d500500c1c40682d0200400855880c00d1401e03030409071402c05558103019009020005010031411030405000100c180c680071b003207580340ba003040001c1d40088 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 117483543 1250 117482293 117482303
    0x512010b18030d0f020105010816031202010b130b030727050a18031e18090506150c060a060b040812030901150b030403030e03130302010302070f15060f1a030403050304 74
    0x90548a25540c10400100d12220f90745440715940400704000f825203d050700402c0b200d034480307404c1d50304003080150300400301e86d00107001a404c40d08000c8101c0c00b41080d400e885602c04c114032581c00214003d540801ca0b10750049040718030059076000c00d1100c503520b68041e2410f140b0794080031182c2c00180d070020341e40403500b6040003480c0340d0103048821450344000005ea0008808a9404001c1000b0300f810528032a01401d04443c1861080140c000361969800b49251058030742c00450540d8a541e02403440d00f000d4a4016900e401000089035a604021030380140c0480c149175002500340040d80444054500d1000541401603003285940166400a001e0750801d6503a2035680300c0f01848000800047e00c0c119500d1a500c0c00c2506004003514103500414005400030404001e22000c05220034048960a0a001d80c03907140034102040090300d0000b0260413001d84034221402c00d074203940040c041d1440034141991043d1101d2041d40c1c00000451140c494007010004503000c00c0c0103a002d0b690142c420 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 117484793 1250 117483543 117483577
    0x40e011203090b160204020415080a0e2d06010303030b0f0a03030206010b0a0504030b1302120303070c0f081c0c030e0c0a05010e220c17040b0610091707050109060512010b 75
    0xb03640403804a9002d5031052840d0445490001b003410703800602b507600201400018001114016492910748406401c1c180f48104055041594040d000310040c42040703024017603403e41e60f52401c002d80901034900baa103100c0c8980300c888844914086801c041079940540c01031100380e081415103222a444a505a000d2010034800000080d2501a40b81e11441d0000248a1006c5d04ca2043c41222040b82018082580040c01000035650303120183d0896283c000881008401e42410180220700c2a030742244441d03015000c401d0302140c01504070f14460701480d030301006241d0b030301d80caa180c584c601800041c2c0d10492403002046150301c5401d0070841d50784000c041e181d208401580340d10a50f140030010140403070301c841c03100c00060b4110003540c94070100c4810000240c87c26680c0d90000080040ca054401e5030041c180b070b00254440c8044501906039400342d1424001c003884980c1c0c3d42c0c0038a2080900042d03070510045481e51045087c1e94010018094070030301c82e42000c010a034650000e000c50081c034a48 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 117486043 1250 117484793 117484837
    0xe07020120070506012309070e1206060f0604030302030d0203090115061805182809030c02030714010906030b030c060d0203060a0603110703080624040e011203090b 72
    0x22a10511155507500251656128000c1c0342c082d0621505900c4070314009030b00d0a14002010140c0800b0070310039812155040c050740c1d550300c02c3c1c2e80c42c010030785101d4000c41180c40b6443d49540c0050342c580201412034881c0c240d0129003003000800c0c416030000800603081030044032005c61064000c2c0d90444908000422186110508904813815544c071800000e4600407411100b9210151900d0207000c0541d5111070012100c208401076090181c0a40380c1c010303c0e400c50310165001c04414401c0040d10090a115610503030400800301c13400100243d00c00c8c0030364000020700c1280b4200f0042d10450684408940030702d404019002014022038094160003021046141540c0d400000d1541001c280c00068981c2406013312104a2040d0400c000341454800c5029484551030203036a02c042d8185014a00d6681d1000030501054034580828200c0302c001d010200b85120f440041d1040c4c49541003248401d07071382d86c10114040154014080e003c00d441c58424042c40400900a001060100c1034600c81d5001d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 117487293 1250 117486043 117486071
    0x405091005040305190207030b13022805090a02030f13060207051507030c0c0201020c040e0312010311010219080901120212070e03010c0c1e17071a0c070b010e070201 73
    0x404582c11400200001914034100c81d4480240120404610051030f1041c01d540e9101210000913140c4442c00f096011104210760b542c15800c1403108049048503000071721075121648481950081c1840b5844040008540003004e00c03e8070b10030620301c1a0025151210241c030a40c800049006994a5070204800000f142081045140207088541c4100541c641054005d0860300d0740d41d290703010041840007e0000d41e80c0061800e005810850317001401d00345400009246124140c400d02440010754000800e102050700c103030f0411030003a02a40c2e200b01a030051444180c0b042c0703a0044c440b49041c0a401c0a43d40302d0704058a080302d0b02e030b0300145000b00c91080101f419204440760000070f021004480030b40d080038062920b440f1810708003100010404d60303d22003821249202c82c011818090300490900c02005040014001694501940c1d140c0c83e040803050381062585070a4000c04000106202c000e24400b15a040c9400c03455428840c1d080407603000d550400030b80020215900d4030024070b5080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 117488543 1250 117487293 117487301
    0xc0c060c0f0b010e0105090703020a0f1107050a0e04061b0c06020703050c01051f1401080a200a0c050d0c030804110102010e0f070e070302090604060c0c032f1c0204050910 75
    0x130507418814580c80d807400e01008404c070001003810007054014040e44000d01d402c070907211840090782c1007811443d036285441070300c4c000203030344115485200c3c0f40000911181568803103000342e010f54814001411000c4075030b4036403c204204100025a48010900800c00c00d60140140e01d01c20300e4030500d000081c103215825110300307030f0b2018081910500b000c540480e140d080003004010030103484a107400081c001030007007403008001c0c00e220f40c1c4900700c4441ca0070404418006111414a200d502e0b0310141000824082c0a840100c4a61003215946125240100c14103140141d060381e03101c4150740c0e55138581013049a0301c1c45c3c070350556407568030400040c0c40500941512074841c2c8000c004d05860a48203d4074800060507030000d26104111202054444108880942c4e43e5420310324a00c2d5400e162445082102d42d001800c2805815108803003603200560128000c48000400c4901904040401c80c089516504c03152803809500800d90040c1000e4100c2c81d4030078074400640307c842c42d8504054080d2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 117489793 1250 117488543 117488549
    0x6010e0a032a090b0108061e0f0d081308070f030804090209030a0507150314060306040b10050d06020c1b090a0c02030403060e060717040b01211202060a0b010c0c060c0f0b01 76
    0x2980760010003c05590106d00c203035002d01c0440d504036040314110481c40484242c401020301822034081e030301d410341d141c0700b0a40d40050f5000314095510600c9018521a9034001d00036885c46010303801000070a2101005154207817600201000d20342480c00031200300a5001210103138041c0503811a04010890900c0000300030644009c0b400c1a0380c942080040c2140e00cbc2c4429811442c240030705014241e14001065076120b80d0003880c580040d201d841521000c080c0b0383d07104540c1f0031400b1104c0c3c4100503d98002d0604014010304079540590100904200006ca28000e80d81020010700043e0000440b0340202212520b50700550b894607071a134503a40300f504c070503c00c04081ca9000c41c00380304907a0f0b40300403c1c40300300380540005074541c02d00384d07180500c4507010320031020010241d49503400400380800d0180c0751958418200c049812184c6800794039504d0490703800d05900d180c4a2200e040c1c0d401414a400a103920819103056141013250950700c0c00340d590415145880000c0c1d00400003202c500039940a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 117491043 1250 117489793 117489809
    0xa1d01060801060f0e010305100b012007030311030c12220306060302180c0313020a1503050a0b151902071e0e071407020108041e03030e0606010e0a032a 67
    0x1079a0134800c40d207441001d40d9001c1da07a0b4040b190010000310f00c002c01d0046a0001d074050100d0003003108401203810803a23210074094855000b10200c90584030000d02d901c101c0f40b00740c8402c5c2d00f0700da80403840b030348901514800142640048038038145c042d4204005143d0703220900a48491940002c5039414126070a400071226182d031014144254544206800010107080313600c3c00c0300e482c5c4200540c00d10300025000040d00c00080c28208219581c070808a8007600c0342011604168011100040c05000c0a4554291091030203180c070385d082c01c10b03031100203d940070811800e14085440f1265031714054410008000c60080d010085000c0004103050071143c103c0d81c0300d0307400c2c803410811031028114020341a04d051021200f824031301c21458209881e0641d0f02400c107070800ba541c80c14101c800b13000c805411035012000c0501c0c48205505030303004420400c120021541c90f60b49a10054442d040e83c1d059040c0d100f0101c000400c0002d54081002c0e840e807002d02070000800008400303110180100e9001900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 117492293 1250 117491043 117491051
    0xf040b0702130b03100b03030f0a02031918050613080a1505010f030f2301021b07080307020a1502010b1017061509010e01030b06071109010602010501030b0a1d01060801 74
    0xd62a041d20400c040211080080090f0210b83c1c1c002a6a405185814030f00030340c4400319402e4550b42803043d204c0180240388055038401e24124000c2d12a40710300d036840704000500c210f03000a144558203c00c0c5146007000681189410001008031039000040c40442240307641d43c010661309000d0000906d007900c80d818078031404407503901450507250140c03c5010070030070b980d4080000c071b4040100c4000c030310b07008000040e030f80b010301082c50341813000d80b1041c180030f42c0002007041204400c610740c4449104504e095444c840e40781d00d0055100e1080d0b00010f5446005500240702003640700040111095a600001403500d040b40042100301c600900700601043d01030f401d1340760b0b442f441e140c5107a00907812145c00c1078080310107042c0b0400340910a041810412518035441c0c031640a544a8900c443c8014500c0762580a985070031034107040c80350211801081d900000042550050203014140c2c0d910400840150365000201001840c10304000b42c0500c0004050440f80c0200303216a03c041c0224900200e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 117493543 1250 117492293 117492307
    0x6030804080607020c10050702030a021504050a05040612030f200303010609050603162105010e061f020312060d02040c030609060b1204060b0604080709090201120b010f0f02030f040b 80
    0x10b0512000601500654201d00c9101038255a0036242c0764030307a811400d000f6112945400424580031802000030341045c62200b14125601032400079100310b0707104488000c42561140240320540b8458450000c1c2c0c20710751844e01e00001d00a00c1004c10407039240c501800309010715600da2f00c86480740a000c0c0e51a0f0800001405282c0d807280984020742019201e45140d420030b0b0054811380380f80e03007842d0010821b100301900031700c07102c401910443c0c0007000c1040c802c2d540c40381401140c264040e11101d00c50141c0e9917648080360241c00f03040c51b2054054000c3d50904556810244040388000c0440d45d01002c442d0414006a80e603100d8004d000b0743c0341e9800140241001580c008607100c030b8101da0b0454005006070208100c1031044203501a40c0404007168a000440c0458028080d5810511050288034400304606a4a9101c42203140c000d81e943e40c40103030380450002c11200302c04802400580821020120540500a001d107407803079510403203107402954088030519800079004030710b007901e00107010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 117494793 1250 117493543 117493559
    0xc0b04061401031b120206220807080f010510051f03020f0c0a0501151503021c0207030507060f14071b0203070f0503120c070e0c040b04060c1407320406030804 70
    0x36006040d02d151582c601715601d40014905000d20318210440d020411040304040c10000c00c0d0034000e1040c03904640c0015143c0c821a9158120040e96803210343c603190001e2801a24003150104448010700590446903030014029501c41d2000245401d1640801c1079070340c1002050020010f82103a90054003160000c1c0c58420b0940e4030390006005050001c040c1400041c00c0642152282c4250342001a91841c1c200e070310303070740400340311503030445440c404501c203014036030448002c0421a1166008002c60354000160380c048544032503001c1c001340000c50005021a01488104603416190466010b0201c2540d00003441c200d070760b03041001841403080003000315040802c10101c0c1030859600282c1094000f070394407a991510b0707105000750500d2213000320301d810011804031400782941c41c00f07071036840c3c1d10b8801c05028440d0072540ec981e03e29802070a084400300104402c82607030380c01e8101c44ca00c1480c101d010511180e0780004403030401c040d5100400305039154491840154420a01c55494034601248 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 117496043 1250 117494793 117494843
    0xc3a0309031a0c0a0309020109080601080303041e050d0c02180a0e01180506130317040803070e030a030804020609010e030105130215030f0112080d020c0f100b010c0b0406140103 78
    0xa588a560345150030300103c801000c065480c0c0b141d6510700012098520700040b0340f100c00f60341c0190182d000d03c2c000402da138000803005500c291b0040080c08685841d12a25400a8040c008054515040794900c81c025522841c2a840301500007000d0a148200e000000a0f01c5030040d640e192080b42d95a40113215010b0a016882050140000c3d2441a0f0f0a5449040d110400100913a1450440200d118101802542039100b020f90b510b07000d907203503d0b05140c40ca0695005542c20701c00300306045441401d51a0025003906c20075410340c0c0d40085900c030760303090107083e401c03811600c1e0502004100c84c4280fa202403088510030300c8038600c0d8240c2c5400034014005141d41403802d403000640c0400c20810254022000030341114562050300104c2082410244810302400028291a0b80000b42c481124100050309c807020901c040107aa042c1404201100101d030800358545012400e200c4003100880c001c4a030306a80107000354000b042c09550000f80c0107110401360400c682002c81807128408a00340495 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 117497293 1250 117496043 117496073
    0x6050a08120d2f2203051e030d1103060405010f050603010e13080d0b0901051023120c030a050604060317070219060215090c3a030903 59
    0x5421070100909000145200382000c2c0581c55403508040b2050155407003c2d0b034502569912038092079500014003405603480054800d0320300810401c02108080401007a104032a4404014400d0803c3e001c0e51092406041d03003141e04074082070000341c106102c00c0c010003000c3d0020102e015584c3c41c0c405c00700000c0b030340c041c0c01042010240c120207015a4541c0c004490540d5403c0b1034403400c1c2c0e0761f10620360211214214000709200f1011880d84500072894100c40e034613800032030340c14006a881e0018800c2014000a20500140740340104802d50f04510802416414a800c3c00303034a0070061103184403c081094804e00030030400041040230f00c0c000c0703225094000b03400b00d030203100c01031379915225000e0240c4584542052000580c080866441c08a010b500400320708404644544c3d82e000a9110701400c07040080542615000030800003000c101c203100c0400c01408170040d110b10030700b403010303006144903034003000395080c0a840d41c0400401c00c4200c0c46842036a403d035900b030a61a098501a407140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 117498543 1250 117497293 117497309
    0x9121509031b060603150c070204060f0501121109010f0504030b0108060907080706020c011b02043315050a18090c0f02031317070b0409050f01060206070503130c1806050a 75
    0x83c0520100d65004124590400d0a4403100401ca03100c500450800380b04601000794803625004002070090001803045007107074400d8884604100742c034401341c4c0c02d66011103c950401982000840381c19800340000f181e800c8410f01c2d08a003055200e554a180120080e00106141d6001c08100903d500c01004810040c00c000700c064240c079840c0520283da81c8020220340c038107000058581c0327507541c81c2d9055440c0c901c5030010b1044c48040c00e00428684050b1840121845030060080e0099000e005696a44100d909461601c03e1200044000b1526a0000c0050704100940702c503106c411907841d031204a001d021840c0e0b0021700c20700401c0000d0212001c40908400355081402000300d180005502d0130304481200b41c5111217604500480ea0610000c0d80007a1485d810119010544009a50259108401d00703d80d20640d81d0f01c502d8140d80c0c560301200e02c200060000c00005104084555060300080e2141920f010f00399228001c210004c002104003600d1782d83c1d1307088104214030f032034800000280700315 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 117499793 1250 117498543 117498553
    0x4060608030c060705031b0d090201121e09020f13140106080114120304080d08011706010b040b09030a060501030321020309070909021302030c040312030c0509121509031b 75
    0xc00440d40e00e0f8000204400301303010001c400945848080202621500d4840054a9498024520210050a01035801e90000e0351404000541075400d108100f12001011800039500004510600150006a0b0200c1e0400d4040750180c504c1e44400c40c01d012003a4041c0d49c08075150920308015100c00700b05a02120411420200400c00c6c03446a0f1902c1000800681e40341c1488030740b0460f11455842564800e101c0c620850000c16500c035405895241a0395111078898100010340101655490080c060508902c00400c020890b08002000400120002a041c1c801d144900d13120142143c00980c000d07800300e03484007818165001130010a220b03081081e0411811400e00d2010380ea81c401050180c05004c90303840828a00307654403800b0100c1c0343d0002e5441555a858482000c8400d42c22501c8100c94a00031200c0d0300384040c0c064059400d40d68450b42e0f43d036080145030420400fa40004034a04100c9004030410880300c00c3e1490984c510490044000303658500145130303e121080300c0d51020f040a0b03040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 117501043 1250 117499793 117499807
    0x3050604150e1e0c09040605040e0309100306121101031d0d0c020303070605010902090307090612030c0807060905010507260103390306050702060f010b1614060406060803 75
    0xc1d94152000d0311907002c034401c50796503850200608000d4034200482580d10002c2000035072110b00004280320740054030240502a5114144001d03a0801103a0b076a8a40050081e0107003410b204261800001d014980480c00503556401200c5181040d0030580c0d03110404800740c281c6503014082d652156075800b41c0310b00d484094a921580300e41d2004902d00401c2202122041555810401c1e41c80b000e03084035080256582d5255540029842041054000c0c082e01c000044c0c451304d90700c14041100c1d146e0100e48041081c541d4201c45401407003004903900041031011502042092140c0c0360064031603c0002554100201c000c3c04405102d280d07404040d201e00030300204024148501030450f07900c00300a1010780c060300c2140c50744515000381c4040d861040b2041414040300507007a001184d020345820403158480c0c90742240c40d44070403140307502b40c5207010004002e52070001c00241480b041203109411503007082d64403400810f032805010850703540040281310910105204140062078000300a501d4425 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 117502293 1250 117501043 117501071
    0xf0615010504171029010305070212130f050d0b06060a03090501050a060e0603030702130c09030506070c06111213020609060a090e09071203030b01030612140f030901050d020c0a020603040507030303050604 90
    0x2c1c4003d03801b41059100c002190110380200501c4807861031211a4076141d181920708001102000e1003207200b001d42c10100015941480301c000b4541e80d030010704036040c565900c0309002882d8032852105040503508c00e000c401142080c0301d0107000300d40005002c40c0a41c60000c6020140c0000b800c2c25109070410000d00c001640c0b25022000c41c04450000403031030900540041d11010110340c80a800c601030001001102036105109006280c42031500304410301035a8080c10705401140c80602c0425007070804107403401034441911006034401000c41c0c2c0381031010b00c00f2480036007200c134607440420030750301041c4204080007285540c004a2003006080d00d41c54010b00340c2204074807280107014180e03108050125644690000e20180c010a503905110050b1440c01c3c800c100101c8094080d28003035070382840031260000c0121000781070141d4070703541001e484106c00d00081d8000a030394044c2d8030901c4d407140016141e04018610640c095000707400c0b251f1075414083c05032a0003c000038459842c218140107108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 117503543 1250 117502293 117502361
    0x50405121e030f0405150409110c06070c0c03080c012a1b03020303070804080412030c05010c090e0105040f141f12020117040302010e0609010b030c01020f06150105041710 75
    0x1d1003200c6ca808207001e040443c099a104a42042ca403079410043c400c1c02181e516002450b90350740842c1150303180d0740d44540c215607210300301000030000c85d11480100041060b003005800440002c0c4c00020b01030202ca0302140e04542d804000355a80b000031400d851900b0340012070903241c0580c061083d07460080a43d0003d4032032000500001c1803000182c04901802039000c142c1e4040c08040c00614030502c0d040c14040e0a80102c014115100d41c200760680c09542d1240d140e0304e045401c600700700400c86e4285401c100281c004040c111803d01d0b515800951007000721120070b8001c9511035404003510b030a0b6a500d9070000903e8000c40c070b079280807241b0680103036401502c4d0342074905c08c101016050744452804901415821454801c0c0d4800d03a428020405810341c8519032074041201140d000541c03032401640c4410b404c0c0c14050a68200e500011002240d0307481000790a041490712030714081d100c183d408002d070b000d60001c040d40c2d0b116600e42c08600c2c04c548103400c1b500d26407801170140c4010002c8401801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 117504793 1250 117503543 117503549
    0x10020f04091104030c091d010b0a0611031e03010f0611030f0901090e07111603020d0809010e03060f010f090b0607021014040e0402150304030801060e01050405121e030f04 75
    0x101d903031044100510188071098401440d8000608091180d076046004041c141d1030f912210100d084401da1152908148190009400c1c041c1c00e0115181c5040c2d002c0c1c0701d04107030409400030350000b0002c00c107405901c0035590445011051080362294184440810220804d40020b821f1080e085e051298424001084d07c00d281601c1d2070301566242014012508251198040701080551105125809411001212080c003005084650f070765a00410740c88072950342d100c0030b500960f01b410f43c980800c0b180801000c1c40c40d410b0426540c40e0005101103884e190701211810805180c040040c03010031101a64080140201c110522607440d608000a02034450240024031401c5010604408035000d031407a4817403c0c0019403417070384079a601d9814126101c0125030880c8904005400e01c0e203020700f10b400744d0b4003803509030f96010345513800c04c10103641511050b0741580c184142840001155074619191804a040b2035002d03101c4240c2c1c1510b103003d00c4016072400415600305200c0c0c0c081c812202c009482c11 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 117506043 1250 117504793 117504809
    0x1107110a032d0602030106080603010c0806060901120209030303010312080609010501050a11010e01051303110a0c03120c05062707061d1c0c18050903030c0304031e020f10020f04 78
    0xc0b4805004002c8054030010010105400800000b032013680004020b4030409050f0024000310040b64812101c050342103075400d80c0042c0070301c02e0070380c1944101190010b02c0d5074240014030300f00c0d071100042c0c9550001d90003207400403c08111610400c0c0c0c018891900075405442c21011035060800182c00c43c0160031a0b41c0030000c0041c1103045070304094103c0c0c5101c0340204020055800c180c142500f01407040303070b03080d030114821071810178a01000180d4005416041401a44090b0940d43d550b0410309090880304104141080c0c0745021500500c00980a0741030415a1143c1f500920403410140b41100d506007460f0300034540410515030858005901c45051482010466500350000364400e000c9401d075a180c02c0c1900c030030703000300018081c3e5401070b0340d0000780b08091140111401c00584604aa454910b03410902c0480d1200f125203015580091007400c05113071046070750418549030410900070100584c000480302207800003d222505002c001141c0079031400002c1c0b06106894451071082c195 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 117507293 1250 117506043 117506093
    0x2030f160507060603050c01020f070503030912030708041d01050303091023070b0f060901030807020d030e1201050f01320f100206071803050604020d020a05041107110a03 75
    0x80d6041c41071007182d241c0d643c4500c080103615100c1c14040d030b640e140310302a0350140c481c200203108404400510070b0101d5030010011460048040b080c0908082412100c03401d41c403060150380300241a42014101030b09181101d11034041f05081e40540c85401a84028020740081018140784d07264003c3c0010203185508044c070100480083c0400a41e4915003200b0120310b0205140c01004501203100d40a1030180c11740701c0464441008000b9654820b10004280f204200072020040c1000e03001c9050850007803d09881c140c0311400807e000502c5020000d5050359078900b0402c0841c07411101e1800743c00002541d0203244984201c00100c00714010007504000018424141d50750390345013001e007002d40e0203006108a9140c1e01b001a503108810750300c0501041154210808031090900c0700390070cc070380050092045840d186c0038010741ca1b84c000c034144d03084268201c000c20b15450307501440b8680c10390600900e54401c810704207802000e0f01d0b020814818104070504001040c09104071380d22000e50404401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 117508543 1250 117507293 117507331
    0x9350c1b030c04060603090203010b040b013504050a030909050c18120d05070507060f0f0e0f0a1811070b0c0a020313090c020f121c020903010f02130902030f 69
    0x1c0d00c0d1004030070301c080d40141031941c007144866168025004c01072082c2e00900030800450300300410f48a0600c9a180001c2125524101a40c40d080880721442c1c0450201e09095002e5500c00108401c11501035409a100884c01c07001c00d680105240010280000200310794200300441c0040c40c4601040e100302104501c0301d50f40d66079601c03076001801c0030312017040741d15459143c0c0d40500720b80c00c802003c0c0c0d0385c0c0c0030304400020b207a4001e114070340803480316550704001c0ba418a00d003507a006940004580d00103a80c1c0c0d50303a5035940c42c1e00100d01c0c0980100034141400d0700174604103a050300c0000b0b4118201d01418010704001030007a04d0000e03081900d07101312541303e0344901e5040349103004d080360718007038004990f0001441c0742c1180e0096880c5a00c40c5e0a0320740d02c8000c03502d00c0d41d480503545806c442490080014034041000c0b0780103901107030186c0101600d002103000020342500d07044815a1480e030b90000310a43c1c00d090100c03207240185900030065003107151004a1014041005104203458506a8051 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 117509793 1250 117508543 117508549
    0xf051201060b03040f140a0b0604050406090203070b190c17070813030813080f0d031d0f06070306060c0305041203030f0c0f0311070c1809350c1b 64
    0x11002034184080c0c00b685a00d01400d280301075a28240c81038881220a03c03442000741008035030b0a00351604028290302c140c44240c240300040074000c100340c40709940d07055520010b940030707c0400000c2040454aa4a400980c60b0480b154001040c0d80c8040c41906100c0b00005016851104000307a02c80780c40315191203050500910a00c14056940464034a00d9004003c200401004d4580d084124412041c1541c0392040750741da034030b807451b120001c0340d0043c0d5444150318400c0d040001c0f00c0c021854640b8428801340741151800c01580c6868001da041340c0200000c0075070600ca00c82c001c00c2685801404144540c6004d85544906d0080b05484030f40c040c1c100301814040e0308503000c09c8042c0c560801250700185001803400310065645000642860202d01301020f0610030b40e50784542000403002c0321850003032191004c5e10100f81e480ba0850710780315403501042010130118520610b1100f074045400303030610064810383ea60600424900d20a00c000d140760071000a003240050386c0041021000d064503800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 117511043 1250 117509793 117509801
    0x6060d03141b030705030406021908030a0b12011e11090108011a090a0b1218071404090501020a0f020705031b060a0324090b0916080709080a110907090f051201 70
    0x30210b16803000203580010004000014804c031041682a2100085c842ca607484001d596404040c085990600205442140c00d520040d26010300408210362075900d40f164a081d201e2440010000210381c51300820031061601503108401d01141e034081c42e00300c6441c00a0000079042c000d040b8614502d66819061000d107904541500388002c001c0245146d81d83ca140c00a5401040227581042150300402d0460b054100411040c0080c031004c0c0070035a003803400c40002101240c40d5140d10503211841070000c00e00a1006080c06510b62b80e880032030700080500030340b9242a40c3d02550095005954a01c0301709040c1841102d40301080340c013035a5030724240c80120040c0200d034944510440038545980c0e4403002005800040341c0b4580414040c050704c02080100c90b81044441602080c0300a9890800c0c1d4429400240e1010150401000e025100d44405140250403c4100c8450040000c181040d1400c440c44543c82161440c0c1001d1150a00b00c5400b20035080f031103550300801440829014820003908 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 117512293 1250 117511043 117511087
    0x3140a0606050703080711030f07110a050f040b031006080a140d091202010c051c0311070c0509070504080a08030f15031209040227010e0a030b0402010e13020309010506010206060d0314 81
    0x101da0b11480d004240390027991015604a0382507d40d410b4131042c40c01c2880c40c01c002c4a03001002030225000c0c1101303200181110010141d0325000b0183c406525003050310484000c0d001c21402030103240461320708005680740000420a00e44e200c4858144021340c466030101c25550940e80d41d0100d01c46a10050700c200300347d246e004001c0e0140c250b900c40d04401034100d00781d82d030856a5041c80860b170f00c6040840f06100c0d802c409480402c121100388914203001203180d401c100e07180380c110715007541d03500b000e400c0107144041220740c0c046c0001071204481401c003003203410141201280410450301c2c2c000903a15987c0d0045010700850100b0041080da03225816203000b200d40f12131040c0d2200c0b920310000a6014180100c2d4045681c0200c110328034141b01c05d01001780c03540310722840102e803501e0b001561203210203826903a10a0448081c408a00c85a0000d0f500803070951300041001d041650019082245c000d15050050741c0e28402e0102181d0712800c060341080241c1e4989580b000c046000c200c0c00c22041c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 117513543 1250 117512293 117512327
    0x5060d060b031f140d141e1f0204080c0904060b04020c0105040c09060e07030f0204030f03050a09050303030601050d0203041509080d06060519111c03140a06060507030807 75
    0xb104101412640040b000700891850050340c41e41501d584007003c0c0060f5414805821110040d10400040c0d6a1110140d1248069088039042c5500007645d0352561201c04e010085500001c4005159070580b488000385660301c0e00c03095081906010044c0d944001c140407580c41002050045030610001d50b00c884070008002c3c2042d59600c0328000c40e60701811090704d0484034002050300004415000c1c0c4949000c0e04c0d43e8036a0700c0b40a0b241c0b150210042c016100b112940d8a508010000010b5005400110031a2080c0c80305522110101c01c0540803240692000340a80c00130820410280c0c1e12000312a50008801401601da440d0b6080050320000803201c8070001c503241030007074010301a002d0040c0610500c444014003855803038400c1100c031409422100040e04e241e901d1641c080a000300b503481400c001603011a400403031891716440f4524071040b2074001090b0345000c40001002c441854643c80b4291010901141e80360010040c6503105017900a410001075001040546100d001c480d59546004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 117514793 1250 117513543 117513547
    0x9020402030a020715090b01061808070f06030e01060b0a050f13060e0306070c020108180a0b071e020a050303010b09150706290112050a0f02070c08061b030105060d060b 74
    0x181e00800000e612000e4161807000b480c014a10300021580900005030790307c15940d1b42140d1070510141d41c031580d100c1038410440c2d1403003004202c00d582008480000c04070b4825400b0300902d000409402c44800c04480790f010b904201040c050440f880d0102c3d10f622019180941e80c601c0d81041c080518010401d035551480d00001d40004c1d101c3d40700580c6201001d01310207540d00b58030b482600b6195181d012600901180012002444000741c42c0c41e041c1680048200365440002030703540d4400040000c035010400b08802d0810605c5003000042201c2d40e250281c00200071820341070700d505d0ba4038001481400c0b0706d1a4002402c2c82c10742c8400204000300000d004040c2e44500c0d062520402500424000010010382c61089609600d000e5402028000e010303180c14081800c0d0340e4803840640002000190720301d841c1c0f418103480d0b450b18401000751a0044c82088500b500b412030440c28070502400b45010712a0501040090b9006082202e0444200303c40055442c2801c0c282d42024080c41e51200c080d01d600 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 117516043 1250 117514793 117514801
    0x6070f1104060f080d03050c03090c01030b0402120703090510140a090812091015051c140d12050702010b060d090203070504020a030902090106050301060c0f02040b0a1d0c0414040507030902040203 86
    0x2c0040c0d44417020100d034400744140c0c0d5a001140e4818003048403114401d07441300071441c100c0c0d4000d40c000281d0320405003001d444d0900380801203445402c25280c1e40d0000f980d8486450a01805002e100b1480080c003100348454103600c2315a00b144c0344040c10100c12141e6505004081203003032006c4034503124908a1305065450320780e403115100c0b03002d0258001c40038200540100d6230021106020156440140580d40607940c0910420b482d1070020811980551a00139160030f100c010000e0103604080f41e0380c0c0c4640007030000e150a00365030010702400c0c01d6a040c02c0501c843c0d03a6410040c0d600c11002e11400169401503400021b10348200c0e503112503000f03440020b042d400180d0541107154001c0c02aa40d0a005981e100750445a92009110715070020314004490381c0010306c2c0404c3d05011500080000c110164020002800b5001c0341d131103086070011002c0e428403046907071416907502c00b41041c0c819007000c0c6040d00e07840d090300307a010304944200d039034000241d00c141c040d50005003001d0b000f800454607494 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 117517293 1250 117516043 117516059
    0xc0301090302030c2e3914090901030311010f06060e040c02060402010206060f15191707080105010f02010e0d050a020c0a030f0803090307050a05030702040b06070f1104060f 76
    0x120207103148405011746000810004211040064444400c44222420303403130310300004006141340e2808681c003582c180202d00e00a0403000407408500a2000d080d030b50949940006480b260606c001b0f880e00040a100c1c1c4403043e40c1d000541811203803d800e00c0208884004210f42c0105004014144401d10b04600854100d900c009400d001201c2550100700308156040c00780da40d0142158002c0c0140d2214000400300d003012404007445c05000751082000318088c2c4e006900d150080204c1030803200703100c00e2001f025030340714844e95400580303d40c86003000e04284000510200c0140074070390501001c499003000a510075400010690311000030344240300d5000e00000c10b240d00c0030400c1f20043c880c8101c10881031401500b00012203502c200a2034030741c3c03607e64415440d9040103107000d050313020600540c0040b490074080c034140f0512800c0a956204140d01c100000c0311504a091070241d20240080d40001c4c8500000d9601e06401000b031600c040c2d0302c40005400f40a5540080d0004e10f101440050106 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 117518543 1250 117517293 117517297
    0xa0e011121130602150c0705061b130b090405010e1902250c0807060516110a05030d0804120305070c0201110c0a06030e010506120a0803060d0c030b070f020d02030d0e0c030109030203 80
    0x400c05d1115070682e00d42000910325030042e0040a0701c00c1d0003080204409060892000c00e10038243c640f0700341442401c000c118030650b4194040c1c00b4030745001403034035441d203000d2050a01400c2d070341c65610320360308012179007180302c80020614641d4158002041440b1304800d880341020440310646400c0300f19081d181c81501c6004c54850340809120b400c0c40495664054020f072403a84e00d07107141d03c0032800b84c0d5480d1407003400f0300207802070f40080b007410010440752414425000d5521042d2107861403400c080c81d14010501075100c404040615010900c64169800300f08c15020320303024640540c10b04160b0900b030342004d20326034515502c10b503004000240315805030000c681c425903800003041583c2d80c003400d0102400d084101e00149401102007000040e10b0000615044107000d00b214a0b5012540c1da15801682540c0040e03d0000300b000c100b0111319805049a42c3d41000c0e8406002340346040000603543e40956403d800395540c907401410110102000700e032600e0000200240307e44403050a010751a6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 117519793 1250 117518543 117518563
    0x402220c080907050d0f0212010203090a03020d03020702011d030127060501080106050a1205120f070203060930070213060515070803070e0609030a080a0e011121130602 74
    0x4120044001501480080f4140c400c903407014003c010311000c0e0303030303078061001c54000700c00c9a00101600703042c22044000d201461181210074020a00c1d001c8504000e4909000e69103c07e0030503004210110040c0d0f444030740300b420280c4180f410061891000002409003424440e0241ea104207011031706034451030f81170907010160003000c080240340d80b500d001601b40c50b0355001d802d81000e0001000c01440903c006001000c03806035069501060101c2c440a0700d680c000d404200c2a85004503050055103018080d45800a40400c000c0a11600000d942192010308130040040701c0444800400385e8074420b0f04940d02564018007140c2840c0d011240000141020701945005180c200041e03018103142d202242c9045070050308050842d1759440701118901400fa040365003020382031000c1202071b1402c00000071172521a1030059103030703114030300300901e8040c648420604002c0c510a01500020011442c403221901c4811050f46c602c50383c0c548051740c0d00c101000d001d81003031104000140503501064800708 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 117521043 1250 117519793 117519797
    0x70201091403090a1712030402060c0111190f080612030c12130807060212030a0b030616020f030a141614030c100507121509090b010503010b04090803040b0402220c 72
    0x105944070035042c0c03217110103010000340603030191403000b010406a401966011307100424040c548241d502d5483d09580030042500c540d00004541e40141c0705c0c0311040b0841d0346402e4540301e4000d8100c1d460040030040080d00050040c0025502aa480f540600444001c00342d4001140d0013407543e09004032035a070001d00d40102c12040ba500111b10346c0c0010800b00200c2d1201e900900000c031200100c218590310180031091a00d42d03403192035980713840510000b482032800402958030700801000280c140145031080410759001005248101c0e078008407000800c0c8913084031143c544420400e50700c945141080080d2000f1901c1c0d06400030040000f008004101c42c44040e1076000502141e81d4066940075990303440802c11008141c1700341c0e03c00b40c0c0f01581102160680c048000d580714101c9084800074407080d02d840d0720b107500502c0741d41024004d0900142041e10100141c208540300c40301c0b0303801701420040100f05c004001c5020355696071400080e2000b54202080f510b566a29503100030a1140d400d400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 117522293 1250 117521043 117521059
    0x114390f0d1b05152a091201090f030806040605090405030309070509070f0804061808070510050114040b01020129030f0303070c03051c11040806150307050d1514090f03190807020109140309 83
    0x461000c0c1805092019039000c1d00600340cac181c3e0381d40c041d107529038014909600540d0b110800103160b42d900081d02c0c010341c040d0014550300d0825160203803c00300550001e500800596090140c4903030302c009884140383e59440c10f0400c0d070302d8134030301000034002e00386204030042842d40340c803000c4c0208000106101486802103c0c542e0000503818420f0f50300901c50182098020319818010b03042c240c001c0c00c0c50381c20500c00003810b22149000031245520350b114200003103040541d090024103080010419400c650300c001c50039854403510042901c90318660007402c01c00c0100b103100002004100700205568100c00500c01c03800401c40e01101a0824400c82c1120b224110210b0289040070001004114000d0045c15240d4102414880b40d507401501c00c848600441e044260f500e0380d24441d111035aa201c1304641854245402d03028601a030444c4d0410305508100003145001c072030510184c6840320f00f41014100f07903813030070816401007440450160020124094070071240101000604406c6c1013161303091 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 117523543 1250 117522293 117522319
    0x90a0801061a0702060c0a0b0a060801060e060d050a05070801020a1418041a061305030105070503090705210303150114390f0d1b05152a09 61
    0x6420785031144030300580c158841c541c440900c15560b00905038103001502a5150020422003940b800e403007148195080210507050200e180340d140140d1009241c020b0080c04054241904d07070f41e407640c001e449944a86043c01031078080100c240a0401203079002415211120b030382d1202d0358040d52010072400700060702416400511504001a40d2541da0448070081c680b21005041c40018140b003001290305045004094034181d0347d040080284040034141d01d0f501a10b05001d00d420764001401c1385050200130710070000340c010001114001c5510880d103040982d010710903001e100c2c0640020b0b090b00c3d40400130810200d4200040c0700d40707044030281d8400c41d004445011100141c0502e0703c403d81508050007210b208015000302d6841c8085d011440c031440c44442401c418038002c8000c02e03c44907a00020048805030742c0152802101c40c0301200542c14403800f0366501c644402800c4070b04441c0c0188140403842c0b00781401c2e601501111030300b800c064418040142201c045d08180081c500c2240850405 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 117524793 1250 117523543 117523559
    0x507090806061002030c03040305031b150c0703051608190503060303070b09070906030308070305010902040f03200909011a04150b1804020708030103150501030503190201020705070b090a 82
    0x2041211a1000581032944a6030104980320032020030707000440c4420702c03049079212824002403008601c50130003503507240075100560000310900f103400d40054011a08402801910b071092581c04081c1e10316080c2d1380c1500c1c1c43c0c00e580350b0158401014860000b802c0440401c0980310081c000810b81101c81c200d038102003102250584011200d154041c3c0013400034000140410099540020303013441a119030300e4595a2680c2141ca4661040c2c1c0090543c800b8080750703c0d05403203060b000d001d0a2406505c0c2500304800702e50100040d200061502d81c0c0500c040d55014649007825500c200c0c010850b04460801e200864060000301d1840344403084004180752603483c0c11711400310000204070310342c00300760b107072640303103662a04515030300e5006403291840780103140e4592000b004243d00c40ea540d15203c0d4110300300090070302c1503005071088541c41c000040c40880c8000007640e202d00b0350150b40311226016204e08a01902030420028840c1c03140390408503641000320301604c0d500701c081d55043d4031a0380c2d030052 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 117526043 1250 117524793 117524807
    0x305040b0a0c02030f1605030f031014010207050f04020904090c05010e09040c12020d0c061205150f060307180b03060102011410030b071e09030201030c1706090a15060f030507 77
    0x82c015900401c0210081c10241d00642492980040c426101d040143c8500303003540e010f0b9402142c801c03c0081000f0038401020f03c03003030180090480e8080d20421000010f0340c0c2e500c56014092096006030030700a226991601102c4c40194040c0007402041c508c0c6c5000c280b4038409001b814040794000303140303100ca42010030005200319080018010514900801068904044101a6003100b0b080034070328040b4001c0034600c402060982c0c0c80b41043c02502d5000000c80344044c220200d298054a40c0c0d10059450038585010540c0c1211030320f0392901c80d03040503222088000f18441d034100c50007000040c003110700405140314101c00c1c0c00920411800b80d024080c03100702265180a80c4104103030a0001c20340c40d10841e6803000c03690400e0209083d20f00c1c924442c1805e4400c4c202c0010b64400c0d000e0085580c98050403211890358280300f1b2904003084071003200a540100100c1c06080c1300300004084800c190002008001c48003800501e01d5100c1c10024001c030110a051004641014045031942c1d2103250 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 117527293 1250 117526043 117526061
    0x5010201020708090405100503060c030610090b030403030b280f0f0b190c210e090c09011101020702150d0b06180d150507020a05060a0606050a0522060305040b0a 71
    0x480f46140001e00c00030440140130140c40283d00fa0002400440d00e51010818940030704a00ea1502d901c03460b203130041220081c0030740303004020010600c8040013404101420389400030b615007004200d000e00440840c10101c02090581003a071050740d00424002d4030080c500c403d0703e505071049041580c4030361041219001522500408040820415551070160180518202c4451420100941080c1c0b02c14202811508901491f407a4008050020a40203ca000c26a038003d840c0b60b00b640c5031000c1441c52501a40850714188069814084c2e01d5000030b5041304c0784503a00400401c0716040f2020291199007054807252842c61030100c00609031b02c0d106d4241c03401c2c100c0040c51305040815000900a8503c0040f00484400100f1501e440004045005d4544185201e9000300803001b102d05005107844070107080f0301d04a5160140a01050758030104540210015080132171755803000001032050460070054890465036210740c08034055a043d0081c07030145010342003180d881d450f00e0710081d044905d60a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 117528543 1250 117527293 117527303
    0xd030e1f110c010f08190203040c15020c060d0b0118030b0121050303010302010332161b0308060d080309160806060a1710051302030106120b0f04060f0c020c0a050102010207 76
    0x140040251442991003a031700106d5452000054811200c001e42aa0030564048520304407814042c80b24400c1130000000e00f944510040086103485004583c2c503200e00c080900760790340c41c0c030b410042d140d0240369018030304943c004444803115901c1c2030400400c402802081c20300000c500c90f43c00b14040c054424002c46402c50003651450b442c6034015402854000502d4400000131080d8002c0701c035049a55018818504280c498141351216084107540c04085410040c000d405d03071501c008202c80c0701c45403034082c0d241c2462030281c0c4903000010702403591858010f01c00d032000030400c00c6680000c98401d400041c00092900c8041d00d8034500f070b440d00400c9605035007000807240100000400580b1041c020403c200039600d081000a54400941d44101c410142e9280341c0000c4100310b06007440754400400390070030381d02415449540d51054001000c0d000030807075420840401e06002c015031043e02c00c2d204000e410002801111000382d25005128400361094204e4480080c2c20f50040c002c40301819406 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 117529793 1250 117528543 117528557
    0x9050a0f0b0601140a0813080c010605040f09050a020d0503070503041e120302030910120f020301031103030c1009050c1c1a0105010e0103021c1d0c01030603110d030e1f110c01 77
    0xc503504031b03000344006000100c0c42055110340004104d58000a0070441c903c900045182ca0405c01031005403038540d10b4000b8068900fa285201080010814042d02e942c1100d00f411100c0c501c1c101145107014280c1c0241807400700017000100382c005400c422050030003131a400c50085a031110405170620030f811001c3e001d80c100b0130603007400d85884040200c40f01c000713080c2130780c11028148075001203d000078113503080c0d1540000180180004400003610b0304100302c5c000c520b8001d80b240b88c2030b141c104001c50030144689a9000c2401c200041c030070700c800c441c400340003402e0100602044404000001005407254801c3c1940d44110700c80340c0302e0f014180c68041c1c403100a00c0020000460080d848000407030070a80101c184041640c055020305092014004907401034040c81c80080c03828030110b042c2640c181841c1010400000d064020000c5081000321a0602445007a090a03a05070290f00007090303100028449001041035210800d54083d0340750f0f07035084560f680c040401950f070000000380501080003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 117531043 1250 117529793 117529807
    0xc1b0e04170307090e0402150c03090109080c06041503090803070503070f030614060c0f030d1e0203090604060e030c15070f020606030a020415090f060603050903031b0d09050a0f0b060114 82
    0x804c4417035900207101802070fa0f00ca4910005245c2d240e0080081c020442d0400a005541503034480d480c000649801c001400d0300349448000a04544244c0c41802c3c001c0ca8110001102e080c06544181556508041040d07035902d4284002003465008666000200d8031041c00c50340789902c2072141401b602c40041010300c095880d10104046500036010100d00c501c100c40103108455418800f5201e0325110368030105105009020034074000d40303404c08140c1428030600401080c810700107010358200707420080000307001d4038108c0c0850030751041c8985902c0e640b103186481d50b010b000e41001740740300c1c101980c0c0300301140b00c411f10f040380c0b50042034031031951540c02070101e4405842d083e80107000700740b40d9103a00394600f035541e280b0300b00369103541404510595481f03a04210054040c024203a000030044003461035813038402e1030309079491040c44005a9804021400b00c3c0c1d500620342c0321083d0180c0200807110245035528084d841600c0050040301c12007030340808207280754000c00d60725400c1d00d2111202420415 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 117532293 1250 117531043 117531059
    0x50f010b0f1b011a060a1b06060504021305010e040b011d04020c0d0507121e030b03030904021602030d03020c030f09010e090901050f0c03060a05010c1b0e0417030709 73
    0x1c680707040d41d8000c001c062281c540b00001e600328150a01d0001c0b9030903000810350400c000f00820b01ca40200c00c100f01c503c08084c1d02002c9104221001044249030504074107207840140000c0d000150810b01c00100400003403214012481200c10903030300d40791003048100501040e2001c01201502265984044100c0c40000841a2183c00c1010340018140221010082e01d890f240d4000388022407000941c0f8400d101030042c5144a0090905011541c2d00206d80c1c0e44100a0400440707200705941c9514541540d0f03000e0088409408005005640301c00364070faa090032008034484224400c0c4074101d08400410b002e8000d450b0101c40100c041d40c100f000380320b21400d4582c00303520440c2c1084684050011182e03504624a0b0042044000000303241c0350407050075903c0384001d0301b034030006d031001d00070400703107954888220090f61800e10380800340010f246000181e01421519000321154098004590360440140c250b00c201e0046d10650030040200c2c0081149100640c1d90100040c0500d5060080107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 117533543 1250 117532293 117532297
    0x70305030c090d080408010e0c010f2708010b010917061305010902060d0902040b0915040c030f02030c211003020d051905030c0f07050a06110f120703030f050f010b 72
    0x1c00c00c29510301d4490b152000924014180f20111030354407020800340100842440340000c035410403002080742d0454000060000303800d64440c141042a210030071412100a01d07945a08800c4030410710342d64a07103d09100740a80317483c518550004100240c0007070b20003801cbe01915204024480901043e0f11190210000006444010f81e001d43d22122000300503128080141072094151301b001038030300800e10402c01a903c2044000e0300c10014042840b032344c454549160300c82c3c400c003200c002071040d4070000c1c190080e0040101c861031b054804010002c4140f401002082c0030b5040317400400788141850b0100c41c080505030342144021040c4041800107041c02205c0140c1740b4020b10803551a5940c1d00580043d811101404442642002c40c015003040020403040b0601501003001c1d2200b2800c0c10081044080e003071088500b0840c4c000000c91341001c05001113800c114601081c0e684141d0181e040407081d60041d103081f00024079100380640324034040c3c810301e0b015841001c1d01014603441c1c61a024055 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 117534793 1250 117533543 117533551
    0x501030b01170f030304030503070801050306040b0604051f1401020f070e16052703070503070302030a021905060d02072d20180a050705130306111603030509010e011107030503 77
    0x644a002002c003c0c008003000030310310a41c070a5413856500e180a001c000d04030403041e400940203900c07405c140f000182d05001e001d64003910580e800251656004940300c0610381d40c80442130488039001d00403801030191980914101d4080e0210740505140c40075140d903518143c4100f20a201c850404902090101901c101078400c041c90410b0174000c40340300c2a0080030310140c44408038462040701c0e28180c241442179000a00b0110050000c50385142c0110b41c0f40c6140070402445013100c54065890908a1504407014000183c0300c10f07103ca52032040e0308020f40c007850042e1905426100c0d41c0d00c85036110001044040710803081d011961605030b4400c600306501c40e20142d041c074080344201a060302c4d0300300b1503240d00c080c020300844241800346040c4121100603241c00c04101d400c0001c0000080c3d0403000408480d801840003d000c803003141c00001c18011407110070084501c82407410185645070308500d0281c0c034544020451050a441030900b21031441840c680500000c0c0911004240600c2c061640 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 117536043 1250 117534793 117534839
    0xb09061c030519021c03050903070206130e010e040605100609090e01140a02040512071d180d03020a080601020a020a09020a0203090d030809060c03241810180501030b01 74
    0x4050441c103080c05000c0a4005400050780b2030f6026101c0c10000504a20215032242002c11023800c101b210280c0302d204048020f070240750f000805081580c0c00f0000350b00241b070307080006504c0c1e5844000401c00148240c8058440d241407102090071b683c9042c45c03410881d461503ca0303000b00392070926104040c3c5503e101440d01d0755030390700c1c00441d951850322641d40714041507180180c0d40c9081c0400c001843d070401c101110985d00018061145a40700d4100042da802585403055056440c2d2581c100302c080107050142c00390203025011020203801d40c0140030528559107604d0400c1e55103400480c2c0d5180280400396200000100403c0b00300003540c000d051050f4107106491134092004d000c40c5490410100480000312018200b00e8900c0781801600d40001c108445a8030b10f0504001d00d0618281661040002c10300c4051100d45030342d100320320401c640c9800390040420745406c0c200b28810303180a104280b8075520143d00445070b00d00c20301c1400d041c0c175884428102c9030390908280220b410b55010782c100d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 117537293 1250 117536043 117536047
    0x90103090f06140a060902090609060714011802150a020a03030b03010e06101706070903060c051c060e0106030209031b01020304080601140f0619080c090402040b030603010b09061c0305 81
    0xc041295802500000c0030600c01200311401c000c2683c00c01c45890303070b10503c0807c1c814401800c56507181d0303003111950030f1b08440c03560301c0d50784d1800c048003000109020221990700c0e00b403003108400b005c801007040440c000c0314900e4200d4240e2805100c2032041868600040c0c000388503110000b1700030fa01200441c90040c000140107080440703c03500c0c00c1c40680d0701c5901c120208000700011625060710759040c0c1e414070003800c250304200e1400783c000c881a000c001c20094850401c00681381c030690948000100c940c0307200c801c00c070501079544021700d4580a59211560b040c400400d0381402070007115044480076009181180c0404c00c440c41c420b50b080c1c840350444c0010000000c0240081201e1b50103400c5800c4803c5004250600b0800e181c041149403a0207010240800b00119a00428a410b030980c1420000650741e100b240d62081440f4805003c0e03401480880c001c80c900c020132010310700c40d1030250b008015004400c0c0400c90b0500c01110803d62010b40d080d8102e02c9454583e9800c3d040318401d080c00341c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 117538543 1250 117537293 117537323
    0x4020111030c0d03020c07090608030712030b0901180f050118090809090c0a02010c0c030503071d030d2309060a0f021609050435130306060803040314030f09010309 72
    0x41d083c11003842c038820000e6000706062550075402d00400000b0441032804200d074500e001c1d0203940307902611101070072007180000d0450761980a80c105072007041e0014409550b944c0c60780710002c582c0c410b80800c500642e28240d44621411460703c9400d060b02d003d603186402e1044174110b4400945507030541210150801d0102040585528000d1402801c1d0890341c0ca403944010032000307084406040c0100c0400c40d80035602c0011031340120489801881e2407908a03010420300107400d240300085101c198040c410900080c9145600c914640521b20202940b00040702c402c85c81d80010703014030103419512800c100b010140150080c3c40d5141c811805005851660b0f02c0b140345407503140600e078080081c85403940b00300420003401c02d900b00d065882c01c4904800480112401d550b101c5170710008900d010000081f11000034602200701c00c0103552051062050a0b210310b185512600584412102c82081e5045c0c40c03c00e880c04000d4411806804207080e00f40722030440114080c0404e040103541d240d14400d48a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 117539793 1250 117538543 117538567
    0x3209060c0111091302040506030411010c021503090f0708030a030203040c090e010506010f0c03090306050907030b01030507172a060d020a0903030216050306060d0302152401170402011103 82
    0x150182c4156203003500d44901000c0103000300c507600300c24404c85a51040005000325034420081e2030300240c010300b600c0000d059400050301c1464041e1806541300100001e05801d041d0280010342c49082300000b6101d88600b00b4040c0d640c2d445260150707441a410034020780d5800d600c42c0d40a968080c0c004d4058030006580c4515640454440300f0402040341d4452040003910750b003001e00700349000700d1440d15400c100f0444e10010684262404002c0a40b0386a0000ca00d10410030806140650340000c246149540d407441d16943d038481302e200d40a025005e0b40010441c04178045486070003002c0f12a55613148105030590552144086c1048030361002e000d008005039880c0600c003818400c805070b222000700c503055050103842c2c00d400c80f04458041c18a120b007400a82c0340400c0705504403e0584650088040d14541a4100710b00040500802c0c00d19100700710342014120865802c542e43c1503614440040030704c004403200d1003103140e50f44100444502160042d48100c03490310071101c1d03100a072402c0c1980b2000c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 117541043 1250 117539793 117539801
    0x6071109070c110a03020f0904020307081f05060909060f0901110d02130905090a0305090411070b010e0105010201090c0e040c03060203010618050a1406130801090b073209060c01 78
    0xc070001a04004000782000701e11560204000301c12603994132080c0ca107034001040c10344502c440601405002d00420304540301009240090700440040da61000c0810410814480c50888220049404e0034041001d80c14503d80f40d80c05500c2c03140c081e1100da5682d4518050194018100300c245640c0c411100f09003603042000b901c0101d0600d0400350b5200c48101510071582da040e000144414a06000d110b030031240007841d00d0410381d150509684840c0c0250010300140071991030981d580d0000a912403c010360314101605860011034441950f9072928012800ca4601c2000103000e490400030030b001c40801c81c0c01c00d82c1d225102d41a8005804d40381d6880d102660401e0b4002c1001c2242c40508004100c10640482c0150000743d401c1035186140800c0203650001c4c05c09031034000c0c207001030114030030b040f556030000142030b4000c000d00014942c0e00e015541d03c00101c9455002803444817501d00781275140c0c1040044200804000d1103440004d80c0302c1c0509600440b03030b0030f0f4845003c20843c18214030a000b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 117542293 1250 117541043 117541051
    0xf0803250c0e01181a0f010207030206041511010c02070e060d0f060f0c020c0a1e03080a020c0f040b030606060c0f061f1d04170405030604060f06170a0206071109 71
    0x10040c8115454000219180b01642032503000590811074102c0c001c0c07400716040c0d0103205c01212080d41418203180180e0410515800c042e4120000046c00720341c04040c409940e000003001d507520a46c141d03003100114201d8001c100c5400c01600007020400000d12210050380d04a00c0c0140620100496561100b028554645003160115107520084112a100b8400c0401100392170024151114030361000604e42d200318000c0160658a8040c4190142d86170603141005e180d104c000559114494440a59104021a03415110302003c1d00303079103c83c0c1030a02900c0b03210b4101074024405529040104552504055001c0c900d9105100c007107c0e148600300403060044000c40415a000c0351b0b8401c503280e01d18401e0308141c24501c80200360055200d080041198410340001e800e10030f07480e880076000c955102d42e5000e10713490b00c42c1030180420b100c0b20398014200001103040401043c1c1d0b407881d11181b5110b480d074400040c0c0e0404d0002c0000f500f0300c0301c01010624410034107419942501000180c074220155 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 117543543 1250 117542293 117542309
    0x20f04091a011202030709020a1b0f0b1311040504110414040b060a031208040206090d11010806030d020a061a040606090e090102040b1c091205090a0f0803250c 70
    0x79011000710602038041405040301c0c8414104480c501c0d00031903a030f078010f440f40b100d8156001030407508283c130070000502481c94403945456804414105095140c101d01403e5070078020b102c000c00d0070504007075140212140e00080d550101c02c41081007000920380208240c0d120900c180740c60038169160f10070451081d100c8036000c4000d0405007014101c4000081019004810304001880801c401c0200c282e4590030615000015982e20320120b0352f5070207420440c580000c40c24558100f00b00b04841d051805400a980b40c1000380e030b91004140d0366164408204016820a81241c4007182507508040d07840041a0440d240d000071850104080b01e01b258481000560a141c09100c0784231b9448255400c030008100079410103092005082003440f55a108035961400351862100716001c0c0c1c1c1100e0700c1e0b030b60000882c405038202c0d540013425070b078081c1001c075128001e00301d00800e050001c80f480d4015a01c800b0011810071a0402404040c030082403181c0700c41c04444a5110b0000c0c188075440c1010349446 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 117544793 1250 117543543 117543563
    0x1403040306050a0c05220305010c0f0e04140610030204030203100204081603051b030a050105010b18060309030307030207170a0e010e03012a050f04120203070b03040305040b07020f0409 81
    0x506100382203620291070451000c3c00e02004d810403c0c0d101c801c1c1e40d5215001d000c040000504030190b464600901c1d88028215420400541304241d00008141070656145d104c107a21030180c50100012209184500c40b2901000c10120f081c904040300c28000309080c0d420014902501ca8000034900307540c3c0000810307581c0e0001424403403607200f4000c1e1419502c0307100d00c2000441c21503840640340c6082c8840740301d001564802144656030104603280910790001d000700207950310741c41003114940c0300c03031056603070220384450700d0031281004c2040343c0c0318003041e5028600750348640c2011000f96019000c10740b08010384100c28880c1241d52402480240495164001c0d025000c60001d0b0401180c898024801e904d810340178541c00c0c061040001210b2100d6103490801982581c044c2c51a00039440c07503405000f00410040355609200d840356044a0003202220030145c0e680b0040b04070780c88110707402400130360700703004c20401e201c01d05029001031480104020034021141003c80c04407a95218250394103181 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 117546043 1250 117544793 117544799
    0x308070203070f0e131703040b01050f010f0e0415050a14010315050f0f03012c250306020d140f04110901080c06070c030813060206102301020109140304 67
    0x41000b0300c400425002102c030812904c0e00c80c503403020300001000340d0007051000209404200e0700b101e1045810104002158880c1881e003801000400b0034000d0707500401105140700e881c2d42c000d81811ba03419102d03981301c0b00c14284020500000e0300240c6c1204c41a0794400002144560720702500f20040d0452500002609444000040c01e54210408442c0c03261003004040c010303500e135a80048007100c420348200034401da010000c280101040100e421020000c0058000c2c00c0c2030040c00705211384546411a00340d00054009414481c841000101c02d02d0303546a010000610190007800001500007000251480b0404d51004074007400c9074500d08a2880f4010442004034004105850010507200384005604202d00d4503a500011948644a030b24045100c404210140f644400515800020f16444000040d00941010360a029280c0940039100005070407908034040001294010010945c12019004000342020b8400d4032290455403900c2252002c10b02c007080c03828001441800659803989 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 117547293 1250 117546043 117546049
    0x708070312090b04050d060203060f1005041409011d0a11041203030f0b010914120102040b13080d020a022b0305040503010c0e0d0b1e0901020403020f10080403030f060f03080702 78
    0x503203801101c43e5140900003840f09031078091203a091980c0c40a801666070b145c010016007040d0261032016404440d0700e003820040c0741d001001d801140e10300701081070004c42c91400c0150b038500900a00c482c4a0100420a40d100740100489810010310440058080501d114110685d44150000460030a00490440c10940d1511500c0103082107a44e04100d000382000008101080034071440842e80c041c01c1c040240c1ea601d180c0456003514160000b10343d03030361740d0f0701c1010f042d50041d10071034840b11054000010398100214a074144903ea0741d001d4154595035608110360b04a00302280d000d40a2000b4940381362600020f0403170100d0303009403180c2c3c2d1250303d003404150a54080450b40410050000307083c00f02038440381081d186c1160f201d403180c0802d650310f01c00c030a50074080e902d11003900402c0d101407084010040d40100143e900998020720b03920802002c3c8a155400d0003407040c002040c04000401182c440d40c04141c619844200c01b0560036558044590011000c2c0c105032040040003c03220704501e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 117548543 1250 117547293 117547307
    0x106090501030c0806120c030105041208180a0602070807050f060406051b0d090302010209030604150605060306031f0e070b0c06150121090b010801090203010507051305040b030708070312 82
    0x4024a403d1203801860f01e030041a182019003100c2c0603e180c2d130b8800c504070600303001d02d0a40309000340081240c2d190504140011032050403c010115000002090783e00300d030358401810b540c3c0c0d100d000340708000031580c5010080d4803195081d2041c8105000900001c5c10620860002950203001800e240c203290405501700c5001400c1000032a990035030710400791403280c0039600e03000380c0c1745c0e400905400f00c2e0509a006e803050141e81a4503008010400081200b00f5030400b4001700c80b05000c005590300d60043c45014030069039030f6503065010b0030004150503200c07201650341501400000c50307224003400740c5515003000380c0c0250300150b4010441000c40101000300300ea0012240799000b1208000100103440090401e0882002024040c800c1140c120385412900303084d6804100f1880c035694611010f8000c214450341284294246404504003c1c4590152007a42e1030140e10151000c2c540401c00004010740350720140c2500800d440000c800c4804d1040030002d500809005101482284c0020411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 117549793 1250 117548543 117548549
    0xa06050901020903070e10030602030906070e0904111c0804080a05060f01050a030209040602040f0603020d0c020106050109230907080714030906430f0503010b12040314040608010609 80
    0x3507032050020100640e000540107040310510344488086464440704c0100051281c0c00c00303440301d400001403000140001034014800c902c0c90b44d070b40105040110810011102c1510094041c200101d0000264501008140c0c40c08240c0d40d01c0c640c680c00c40341c1e10f48929802a030b00030311954101540d07081c02d000040c4103160b80140c125801940700d60400c1d0001e440c0e24a2400007131700820760b0200050402029904440141c0307000f01c03160301c0050b9203410040182d0310243c1114402030400b144031000d1801402160242e0310b0503103c800c2c4207828071a0446503a0041105103d806182ca40d41960303d03200d034040c1c580552840d03a0350414074034110130301070a90801e051145440200800410042600200d805600019001a52403a10603504001c010080b0400a00480406042040400503140b4401144818510340f100e00c034011100005940501091042058581041006403590310004000d1a07000740b19061469503040e1210440031550040e41000c004280b102005101c01c41d00a4104002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 117551043 1250 117549793 117549811
    0x7020307081e010207050a03050309160f06030f0203070e01030c02210301050907020f0a06050a09080a0207030605010506040b0711030a0c0902090406050d080d09080d0e07052e18090507020a0605 85
    0x5015603566030b80b60748647d8408003408005000c00030400f101018010000520f502c480000b0200740c0f44c84002c03644103058401c050100c0d00d070609020002003070b40240e07407040c142602d410601c05000d80055005d0a130031b4660208500682a56980c034404002500102c2d00c010090130b5101d604280a11041800c00b404200c25903002524401c03020780b0005803140700941c4250045000e44030340c2e1058019044a03100100700c46d20105070400c01750790000d5500200c034007680d01809503036070713031814804a03204d1030041c040d850004000c43c0d000724200c00c0200e007465602404903044011241c40d4944001119040b078450f0130340005580045107068010400130380720480c1c6046400c166a0342d00c01c218070440404c5010151100c0710242030000f0074060703849041c04d552050200500aa14150b2110701c0c0307000e801c0c4110786403129401c4a081d00c0b0a0542d94603805000d400c101d8410741804c1d0380d40342aa400c506aa4803080002240f80c18a600600d40100700710b4000b00011622850f03c00e081c1c407001006c80f45 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 117552293 1250 117551043 117551047
    0x9091416021204170c04020c060f160c0215040e10060905010807121e020c010608070803040e2701150303031d030306130b0423090106270207020307081e0102 69
    0xca0b00b40c91404460450300440021440c00d04410042070a0031065503820780e0181c404900b03075804140101d680e901c5a00112802d00c0c0356920752140c0001c2481c03100d0030900050080c005240142040910103414982d0180040e0030316076503800c002c424100848104012b9103608904006482d0083d40400280109090020581c504600001d000148000400c2c0c0c00e6070b105d2080e40d50041801c1e001907000b1031303214415940d4070342610026019000750320401406119007070000510f108048140c4003610640d615912003629807001c3e2400301b0810070b02003680040d045a8036404000700f4800e40c0e0600c0c48810510845501d141406030444100c001e4440c1451460044c149030030384080116070b48048101d40d896180343c00d440c44100103010540303000c3d030400d00d80100e103d17100070481c0e001083c02141c425242c03565510608804d081c0c03880c80c461400c8044c807644004240030b0642017494002d03005400018102500d40c2c0019140625a070b00140443c0c111a030000780302c103042003205400e024000000d41c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 117553543 1250 117552293 117552313
    0xa050405030f0d120e060a0b0d02040f150621230108070f17101e0509010204090b01050c0a060c120c0e03010e2107020109050307090209090f090a120909141602 70
    0x7031b12107200038901e4409030b954084010b4103a840c0c8040c005082c1c3c014108010000314120950000c044001e4004142d8404c07402c0042c0d1544105181241041060420324100c018402800d01404e20381e26043e40f040d909c44100c02902c2075000c02c0d94000d011490040c9480340c13030500940741840703564002d13600c01000c016155107030b0306000400b0600c44480d8100020b24004550003803060004003c0c8802e001800c00702844a5480150050300580d10082820840c6c4246003005694610072058007013400e4020581c4e020200c0c10590080d844480207047c0941c50310485460b4008031030301e081501c00452800c428036100f505092040101400d126401004100c00340901400c1440095000084007040061000d0869111740b55203001890040c0881310040e1311003a644003c3d4001040b41801401040c0c0015040d103c000703501070084040401074641c40d1b5883c0c50320142c00100c02e03520000d200b01d2080020f81401c03a8810407042c0c80c4841801d0f00c203070a061440109000301d03035000e00c0c210f40c801001c071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 117554793 1250 117553543 117553571
    0xb13060b01110316061107061d060601080f0403030b0d0b04050c03060c0403060209030c0613150c0b0402010309020117070903030e04020a090b180d0b060405060a06020c01050a050405030f0d12 84
    0x842070500c0c0d0310040c070035002407031074004003805400c10940c1c10786c040842c13084100410350b0131504540c0d240e07003c0e00800002c40f1641c0c60380d03124121303201c1d800601014041003080c0801085103801501915000c502065250089810240d240c070040380d45682000411052001c107120f9140a80801c80c003401c2e26050100c0c0380915030245010181c10b8030344c00510300703540755002c000c1c80c20101d0028105607215400303071229607001d0307a4a04ca40c141d000741d05c816800d8403511400348150003d034005100c905903201c2ea0011001403038103034030407810321540500001100400c12070300c81c410384065032040d08a0741140f9006180d5658503220300e00960042c03050018441d04560f00400303036104842100d8440080c080071030441a181c1b419660400740505800c410b01c010510344d60f218150940b0140a00d40703505c0c007401508500c52284c20010307040090456007a42c0300e0002000103200500e8100e040c15280c100180c24210196a590901d80c0031a044042983c3c01c000701c05140c8219a8040203900748030000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 117556043 1250 117554793 117554797
    0x6030b06061b0d030e101506050319090c0510020c06300103080910050c071e0302040f0f0b060a0801030b07050c030a0206090c040603110f0d0b13060b011103 69
    0xc1911031003001c00c07041c5a01015804603948203030040100c6540d0860300d10098010b0100c0c915008584c0903104180e810710302caa025004400907070000280e2040e1030554212070f66000906001240d803403802d000303080c5007070f81d0040f6814030380030f69003a20343c4503d400b0400160740400740c805419034201c04102c06641c2c0d84c43c1c0c2035421581c502c2e070814148004829140500072580501500d0409220001100384074030b00d800b802e2401415180c810024103010801d66580c080d100c0451610340c4001014848025240c2116482d005465180716146d0346a50004099030540522604d070181c2e00c403c0c05495142c0e034021413884010039a0702900c0d06041c0c201c010402a01404003030886c1a04401040301507101e40c0031544101c9244040d41d45802008800a44924040e02c0410302071144c404406e00030710300380c1700b40c0045030f50012151541003042401c1c4a01d0a1010010036403084200c61048081131500c08210b12499000b5220041c0c40c14519002d4200d42c80320306240d0400c4240f00f074041d031a141c0001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 117557293 1250 117556043 117556051
    0xb210f0a081204020604030b070804021503190f110f0d060504110316021e0d0207080d05090d0f06141b03071d0a05190f0902030c070813030506070e040b0406030b 71
    0xb0321019a40ea2400031642ca88581e62009203180c0d5084100300702d4a9002005501840c03080760a01440c1c0c146491072100c80c001910414078100e1032200d00000f081150b480f000b02080404e0000c9030903102e00445141340c1d0005420340403030341000125202407030b02a200d0600600710440c0c00301b019070a001d0126203180001003400b041000c98140c688600c6008100d224402144e8400050040700c080300c0179900d492a0a00c110094400c0c0c480c080f540c080c0c0418019480545070350303014207040d2210100b00380b80c2c02a00c019143e440d8465040f2020952500800202441c640c107540c4950904002d0340395280884000100c02141c14418070004980c040309003024030480c00c0f0301840d040f55400014880b8441c59000644c0130a12074450404440720f07500800441b840903e030098641c1d40c2d10408016131104a40b44010b2243c00c104200006075800058024140b0004c0e54002281c4c41b580c070709241002c180c840350007240c400b44002072103150030b00801981003c16134090100b640b8541e5200d0143c0d02c090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 117558543 1250 117557293 117557317
    0x50603040807023f1b100e0f0a0816090c05030c0f1201060e030d0305160f020f07090203060a0501020c010906050c01092003010b0312070305030a0b210f0a08 69
    0x90180c114585010151040322042e1406502205490000701c02512050400145060181d0780f4425103104003201d507004041d002030062a4031b01e01d1507100b01c5444005905440d448145000510384540f6503000080144c084c08004059102c205041e000b881211a8008800c482c10003003444106079008c001d99400c000301058264980307840600c1154180a104051041042c41400005440d40e006500030007481017501510000201c1040403410344104a03883c610400c010b407001c54205101d880d052095240a20680c3c010500c5d02c1e40c1c05003000030591049405039004001d010711407a14010090040800740002c000810f80710300040c1625100f4412034080c04408603180754000000e4010445090340719035800c0c5000c8403110054050000707030785032034041d41c40c0130800300c0c171400e000580030b013414418a4001d0429000c2d50b01140c00b07510040ca4030190300e84900d541201900c42602e90840310b103030345a00b0350700f2001c0030b20f80c1c601c1c1046010107034850781e1100c132212011031040e07412194280400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 117559793 1250 117558543 117558559
    0x111c050702192d0819091d0408070303020f070f02011803031209050f01090302030d0f11120a1512260403030e0d0b011707050105090f040c020a021002030409050105060304080702 78
    0x40100c03000400c021560241501600081c00008100c25072043c4416180f56200d10414035155007040700c186400c0e40e40080c15140707c03030101d07022030005c00240c51414404e2901526050350f1403c401e003103401c4800215910420009540b0456801c8010701c40810007800b4035000d03d9186490041605041030035120b0fa050340c030303040442441018054401070740c001100034880c118483c503000b942c1e9800b80ca05c0043c91464802601c030b40d045180280000c00032074200c0e0320704101c00e240b9a030b088118060280c0c1c000f90390385c003000000e07000010340072401400d0220403055501850704240d0b022454039a00c61207040c0c0d00c9440034030600002000c2d44c040c0e07609490400c003c494650301080480c000071102410302e841450000494030710f804248a0b45042c40c42c19140e10540d00c000540b800d0080c0b040c2158402c00340e014102513414940d10020501102e0b03c12600c44100580228100d0502d441e0590016000040c043c0000c09141c02010700408040d02d24034034518280d290144075001d00c2304028803034011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 117561043 1250 117559793 117559853
    0xb010f0f0903051c0e0a0e1b12040c090c02070608010b09130e06180307170918010303031b210504080c0d030b090109020a090306111c05070219 63
    0x10075a0288007450b032200460309000c2044010800c9240220001c0d0b0000d08128540005400c0081e054070844401c0b40407503901d500c500141414000c9004c10f6101c440c0b2051120541e60f80d01440550700607401258a0300a0a0405035403909503440c103101c0809541c0041020003949070304c052201c0c11244006140c0e901c580c3c00e04001510031450741301100c1c185041460300c8000010101c4c0450184804002c051605918541055224040c1c0c520140561910a10039010000e1039801401d03e2003004180b011040c15132010800202000c2e007081d000170780d46900303a804000c5507044204612980341072910110454990b0811a040c50f050a10300880d02d60001c5001c0102c030790250788141103118181c134403030805410300070300800c03030841c9051090f80a032000046a004500c2250b00307414155480c2c0c0355883c1540c5454001c0c1182406400030b29104000070480b0707100c0c5030f40d4102c200309820004201400c01004c000c1c500ba02040b49403491030660082c6000240300c1440301801c003c0001c0b21403904c040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 117562293 1250 117561043 117561047
    0xa1103041d060924270106020d0206160302030402010e06030a0f0506031203011e210c140d0212160906030203010c02010203011512180812071d04020306031603050d020c040b010f0f 79
    0x4420a100d10400c400d840120382e4644405e125141030750001d50860f0300c40001004100d0f60343c582030751440c021021003905103074810300c25001547c0c01401814812080d141c44404280507a00c111604410165202c0c030001a8005c54050160860800c0780180070135041d030030445865110603c02d00514500840e60420722000040b464001400000342d100c4402c0010f642c484008080100c0c1192900398801002c510130b0f00c62000d1141490b40604000700789042c40e800d000e80404e0090f24216244221001c0c1c100d01c61452220304054100c1850100318140381d0301c149429903c10303042c0c02c41564014030043c009064101d8039040d180c2010f1601c8401e4034032a09058008002641c41000041c0603100454288056200202208200742c0680c18441d5074299088038034252291180600f20380381d808580981c80c080e00176540102c40181940c001021900c21820300101c0303580210b91680195050900642d010300080303524600a0710140650440b900000b031400d207004681c8030500510102074100a8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 117563543 1250 117562293 117562309
    0xa0608040204060e040c090e03070b0612151501020f0304060c080d02090402030c0a0e0a080d0311040510020a020901090b0d15021605031b03070b040303020a1103041d060924 76
    0x4920081c44c1c030418101818154180301d102d020350100070703040440e01808110f002040382d0000750401402c503145e480300000c00c1041c0800704030110301072052019040107200c0d03000e006800f41013880040b8241c02d180780000382c1004c2c840885030b2070700d400c244410007641c1d0302f040000c1c2007145d0091903c0e90350800c07403600000134003d008100740c00034804020032914400100040c50392072a41c8e160031511003204c0041050600c001d000784102600700c000340d8038905000750050f0204c191101d40040c20b1640b07840104248454652402005070b2040a02401b58100418007502500d211202844690440004188c00c00b50654008041c0310461240503a190b2841e03054550035030711409102e00141040c240180e503500100601a4514100344e4155a96000041152007083d80300da01c12005a07945c0d00e041c0c2c02908800c004506200d210010b102a40230700b40000c10150602c0d0700826807003901c003000d240030108001d0405000f00c4000c003d02588495103c42920725060100944e503145c850500410000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 117564793 1250 117563543 117563549
    0xa0203090f01020703020a02040e0105070e09060d0609050d14130317040e0a05090d0e0108040b041a07030204030507051507060c021f1406030a0b07030c0c080408010f060605090a060804020406 84
    0x382d44089800010103502240500001d4002c95040c802111907603445801c0301e0080c5c1d031503000300e50041c501c00080d0900950312940040c00800c096407040a03611f0740c1041c0c80b1010402c88403900a400801400d5412201007c8250398946010b0300344006c103180c0000120349030201800c0b5910383c0c08810540c8d01c000080350081c001c0201d40d9400350070404505005400160341c5104240580003241205604c211003054486105a441d004180c40311384480303003d02c4018006840a40f06140c425100c18006500b1a0040000d6030300140c0d650300c7e5041c501d0500c10640c005a1003400c4454400c2040c2100b80d040d03440064212030002040f006070b440591a21440395060101410a04214101c8111590244030400c40740d0000c00641c1d66120101500c0742003040c0001c11545e01040400c0441c1d00ca548259040704413810206c80c0304500d0388035200d03c0d41007603100c110269101c9004070f020f031440d401120002c010f036040450511b0001c100060b048890f0303004100030071028000203425940c4541001c001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 117566043 1250 117564793 117564823
    0x90f010524041701020304050705030f030a0813080c060411040b0f040e010f050a0b01030506040b0a170102040b16052407030b01030b0a0902220812090f030d021605090f0a020309 78
    0x20083c198501a4040c1d0070494050341e182c0030760f000003d064117012900100820b0114055071520300701502c15545520080c1c00207e81005190031040011000401400762040d40c030000c01d4035250500d0f00d120740903c082030f020300490600e500c1d209113880320711140d02c80400072900440e02484000804d801008288103040d00765003410140000c40501d42d00c68800702c0000e90342800340356a00018041aa00c400368104c0e0041c0c2c07070960412099902c40440c443c5080048005460181c0d00c03c000909a000002c04003087c20b01900e41508000003001004089800d514030401c501075400002c104c3c1400003000182030607140c1c819000c05030320035482014282c10080204801035255200c2d08001d4010320300e50111003680034410500c00241d1511402168110401070240b44c422803d42023140e000485081e800000140b021007603550b050180a00021f240c3d0f00900b038015061a640303111072800d0340312030f0145104800307000380c04010f00d150540c0b0040187c0003681c0c03610b911034014500f650031101402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 117567293 1250 117566043 117566069
    0xc010207020a0611070605030609060f0112090305030117060717130f051b1507021003020906030901090201030f0e07090e0705030607180603140a1121010302090f01052404 75
    0x19415042558600c44421321004c6032896a212982030302d00740f00079500258000040e60004240e840c00e03216280000c41c040c5031240380d614001800c0c8003540c4100d84120301190380480148140300c0008a51170100400000401c503e051001003c0c0110320680400c64043c80010006100d03000d0104002e010343d80c0c00380f07420100a0f51420f1594844a86480031142c000301c0303602480c118540b4105981701c41c420b02e1304403850001c050f403c100c035098603030242109040c0c0a010b460115602e0402840c0308460b903400100c0d150078180b0005048407401945e1503040351400118a140e05400110a402da40802100240d11480040c03503d01e00308190b4807081d4584642410000416448215035110030080000c00b02d4003615002c096090b1144201c88047d20100980015080e85503500803c402c1000700200f180742000c0700c11180400c1c228510b42c1c0c42511400ca004008506020040640c8941d661082c0d4540c0d50400c000511910300d50300181303643e0544000c0381000c1c07805d10401c5074028490780380104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 117568543 1250 117567293 117567299
    0x504061803020303090f0a0b160201110f071403160602070c05030d02074b1503061802090319150f05010303021c121d01020d091e05030d020c010207020a 67
    0x1c1d030301e134412070300050340e40603000505000301400140000380c180d00940c0c50141e41ea860151081c02148100c00f0403c40d920b5101a41061030810002d181c44102041c1c0c050fa0fa4600e81048800456182c1900c0c202e1380c42048180040c00b0000d061410300c640c00940583d6424090404c50003982080d00002c1e41030040b604501e00a0350002032500803039038548440c584c01c4030814660710140c0d400c0c1040c0441400304100101c0c412061800038007082280300300340062243c42d0440c4400d20074072a0fa039403001ca80d6841c400e100d180008550a03682208a490a516040d840380101f621084280b091007440c01802000500f00609600d82e2841c1c82c07130842007041100f00200e000c401030704080c40150054080c2d00d20241503034208050041c028040c0b034480700c0341d900c1624601802072000f041d607800f55807241750404070703200000e00041801d240740032008100d02241d4180b911801c00581c425400d080420510a00020b4000c415200d00048100006844415030958580a8814444001d40c0300142d16804 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 117569793 1250 117568543 117568547
    0xf0f1710050a06050405010507080c0a1a09010f060b04030210021e030301030605010602060609010320031c1e0206010902070f05060403030e0105070315050d020607050d080105010e04060b0d0504061803 88
    0x40c030101c40045a2825100d0360f1402c055540d80f007680180e50010760b04000d2400441e510302c000b82015929074040b10280e00700742c0c489a01848204441e80ca00701d1801c001d0080d9504240107441510070740681c10414245465a010b00601c038620000740103241ba011918003480c02481040202281c11a140816a140d00703016502c95100740070844c4c0b02c0d0319000001c80c11500c00aaa1481210044c140c0081c40e429501d03a00a00700c01e407882425510420107c100c4942c81c00d01c91b0002e1710b103d01d14400c443c40000746c1e0280400032581c4002c1290310b40c0a41112400d0f03400520141100e104090060f40d84449041001c8000d42d00c11001e4414800c00041c0410164903900018440d0401c1000300100d07100d141c011025100015070400061f19600d000348214036003e076180d802103200410aa00d810502d80d2080d09000c1d1080100f4089061140100510358104144c0311203c0400c640410902d41041682c1e42580104060840984e540324000344c10010300c3e90120181d04000050b1107070105081c900 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 117571043 1250 117569793 117569821
    0x40902070302061b030609090f0d0203070b01050d1a0601020307060207030e0a060302090f0112090b01170f010915020306010908010f0b180105010206061e0a0303050706050f070f0f17 80
    0x30890040c861000014101d5500c0540e800801803100c40f00e03803558540f4001c000040b4000781c032082c4c26024800c843c1a540000304242d0100c0005a00a5900d590301c508120b110807405910450141d020f0104a00002d0034400c050514a2000e0f00c0c41c95480e00c0e0000103e186024031380005040520010b03a11007496088039110002410450b250401030f620386008406030b008407d125504615010000c00c01c07903000c0c40a1000e4054290030001d48408280c8806141c0741d42a40701111181c103078888070240500a100d03042034051000000e000d00030440d511482c080ca0007101080701d10798080045015a803140c6002c00c02420044000e00480b81008440001400c1d0b90240c140b107503803c510035020550b404075029040303c030140c0140c011583ca0209003c192500c2c00030114011802d100102055619200c180c80a54060780c0c0c0c60391500128540712040311006001d960018407600c041040c0158000c1102c0307180c41d030318502942c2c079040d140c0301520080140386c08008501144020400ba4141c1659 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 117572293 1250 117571043 117571057
    0x80d0b0907030518010e03040b07110d060506030f06060307050d050c150301050a2106090c09060801020403060c030905280618030f1d010302031504090302010504060b04060f17070803040902 83
    0x7207400c4a813981c0d0105907080b503044801302650b50300140001c0041609103009442c6140c010f40f12020081080c01c002182c0000421044840541c0c80040c0001c906007084007030a02000c0d24001c1606040000c0000d03074444031841a5442500501c1002040003401d00c41c0b9020000b02910b05000c0e00c6030704120145903002400342c075008a45042d00001c6060200a0301040d9804090b03402e880b01449860303071409807081d5a801e80304849c5010000411500a02c40d410041000c0030006803114114504507050b541941543d40401d030400300f4007000300781c02240c107503090303070140d840004602600303110249461440381c00540a603242040b5400e200ea200002e041059219645071114003504e4442a500801d41403003003550784040072140d201c554000d500540d04110748031a0023001142100001301074400c003407412030050b51113406000070020207001c0d024100c1422142400224140072950300d101d201d500c980d00010307400c410351400014007031000501400e00c003801d6030794540d1506034520103940040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 117573543 1250 117572293 117572311
    0x409031106090706200325030305010605030405061302011e08010f0902130e04020a0b160b010b03060f09060d0c03050a0b10050604140a0b0423120a080d0b09070305 72
    0x2500140000d42d002c5240000c1d0792607038070f58841515215003289860a414034440c122841704102d60303501945010403074410302c441032030610402c42c800e1600038242c0b14181d00510034020b051003400b0008801058581d13010045000314821280e450004031106101d9036a44005c0c20101103969400d95849140035040c3d4501544485040b0382d5110110100e1003000c120031596201030001744020300040201c02d42090000f4034500901c0d84134059a0502d07031100c4044001d0b008646089003c10600201013801045d00909540c11444c01c400400c0d060440082814030072000e440c001140707643d40c0c1071020300f4146c00c03400e504034180d100d00d0456070b01d4036100c0c0261b0326541ca1100003809903000d40203e0007035a038050b0000d41014038207803001059948506460b58045980c500204080da046130190008142c2c1e5001400c038144241d508400c0000002a07003030151000040d65041c4420000c0e0384a8003c0d413150509940b0803000d1540c80c020300300b091306568410106001c0c0002961325403c2940921122 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 117574793 1250 117573543 117573553
    0xc030601120f0b0702030f04060504240206010b1b030d0203010810090f02090403020a060c030b100201050103020612060d080307030903030b01020a0f0206031b0708130e0106050f0307030204030204090311 89
    0x30005000041e41c4180020701110640c5072440014900800864004030107004690411008039038800054019403c03850005034042020049152009003001119404503554281c0c09500c24001b0344a200c140980707000180300241c000b01940802c0070414036920410140c988810000c10000c019500c217201d804500c0c0308450911034801840d03c500d8080562040040185915030307401c1c0164084c000b0030540550080300c4c82440850300c20b004a80407c0220303500002e13007586204c2080500c0080003800402c5a15047c01480140c40e500c0446400004024115081e9540c03000000c001c800c4d6030784010200e0102000303010000340c064225071000e84c881e45081c07000c004004012aa039005000001d41184089140c00300541013480003143c1040e0407040406405400001002ca90b80c00007a048580520001e0051041041d004500c006000304100c00e81c055450f0504c02041da0154400e148001c0c0b00c0080440d8440340680d04480095501510034400c1168905002d00071000450f1121418042c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 117576043 1250 117574793 117574799
    0xb04020307170c10030f140105030607020307031b23060406140f06010e0102010b04060e06041a01080c0904092f061e0c07050a0803041805071b06060b04080c030601 72
    0x104201c4010b4200c2c0d4500108202d504440400580c122214000c0c814550740d1b1a0302d41640c5564040c088200800061041d042d514100501d0701e040c000a1124045400c00c0c8810300019500c401906002d91070300ba50b01da4170000505111107101c0e003542c211000d45140400c80c5298600201e03115216070300800c000c010450010000d000c00000480d20b0310070b200c160200051040d0301544201010004c10701c0005118030700c05000ca011103000c2c1c0c210803e020300c00c1040203010707c0c2030f000340e00360108500480b80410b81d9000028084090180001d402c030314000c100c41c50151a030ba404900140d400130070030000c00700441812461340010707600042161110541082d024141141202c0d80d801d0071030f0008440410400c0c58005a0300200041c820601545500003000d9850254200107000c2c0680a10b9455150802d2030f25407202c584003880100d428001042155a000107018420300c84041511b88520b2103480e2030401081ca6401105403540c01180100301d00500007500d5882440590840b41240d80b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 117577293 1250 117576043 117576059
    0x27041d0d180501121103010f0504110a0e12012406120506010206150a03140f100b0d0204050403030e0a050c030d0305041e02150d020703141c0b010e0303070b04020307 73
    0x500c144292a0301c4841c0d10007001954810605848850b1000c400007602a54840e204c2c2c1c002d40c03080c0e0103a04141c0907800e0030b01192400b8450380c0208003240712000d1a050800f00b000e80060310f000c80940c0b150900e000104000c450030340010400c018114030b5151008155030b0400d149264034021100084c0c08000361503d01042d6110302070203500140c00600d07070b60740c0d0403400000721b1405100c0c1da40c021101c0340300000081d02d01c156080d2501d1400c7d0150402d42c4aa5600520708040307003082000c0a810009074800d0350f118145003030b031075a8059401184a5071142403c2e00688000015070b00b0758070850040100b40000450780040d02c200032000c0d10008204e1a10450650b0001d603409040c00880707071644d0880d08210341282d50f140784003030300303404800c0d060b06181061a0414100d0200440d00018854100743c1c0c07008840c400641e149050505041c544d46420b4032040301d15202041c42a0380c1e03485c2d0391583c3c0c0206000300d22650010110303541e86000d40340500c55004146d6049000340708454000c0303a004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 117578543 1250 117577293 117577307
    0x360703200409050717011509020304021504120602090a150c0309060906080a020703020a0b0f010f150816020f070605040806010e13030503061c142127041d0d 69
    0x298110f4000c1c0300b4207082c40050750f00c841c408404040c0c20365071039411701e0001010300f154000130500c07020010f0312442d06005000c81078680314010b10f15018200710500c101345c08428042802c0b6002000180c98a1415000c119030342440c3c2c02100c84110a0301e400f98886911804400006100c5da8419007042d80d90103098540c0755007030156101185140c8000b0b000e5841030781c0600b02540c003e1040b254000d100f80c5070086c150f80160b90380490040c400006124003210f40c1d030414020035070554030740e0301070982580040440e50301030a101d030f042c0000100020250b2080010032800c1c04400c0c15548c2017691514050030131f034800d03c07813039580f40a043d000240e124110030480d40706040c004805c0d2090714441d070b411100c1d80e1004100e290f011041014503d0f403c00c21a6410301103030321031400d040300074281c00d100f10b2600c0760782c800306000d03840c01032424030f08050594140c5902510702c0140c0300700e0241f114000089640d0450304650000d2400d8004280005000c01a0042c00d510b03c00307070344400109400440e000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 117579793 1250 117578543 117578561
    0x60911120a030e06120117070803090604030f15020d020a0908010b0604060c080c0d050703030b0d020a05040b01140a0206100e0f180c03010f0209010e06033607032004 73
    0x540c01c03011428001c6800342c480900020fa0003400c0034500032034081c074480c0205007a0440444080024a0840092020881c905c0941a000d0046080214110024901e4450341c00700404d40d071100d1046004001885500b14440022040c055440313546144021000390040c0c07040754002024208001106401071048810811001d001c6c035103481c1c240b140541d0644200c441c111400742041020480c2d0980500184001c000e00c2d503202ca686890b1810020160340c505135a0611030480c6000b0745005a860011002c101e400a0714049074070003000300180c420b9481c00d45e121101d01d40000b030301c104c0c07140d000c02d4591042e100103140301600d03034890b80180d1500e502219059420b42000001c200000305200710381010b4002e00084840200307480b808a829508040d80300740c000f40c3c0204454101e0340c5c00c56440a5603101c10341e41c542c25440c00c044c030b070010300e41000c002070144105684140300c00144050344901d20000c240c101c50b08240c2e649070070818026001040c3c0d00300c0e40c00d03031004191032130306002e69244 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 117581043 1250 117579793 117579829
    0xe060903120304020109090509030423011e0903060203010e1b0301030305030a090606050d0b1501020c030a060e070e010e0108010605010507020108040b0c04090e0c0901080102040302060403060f02040504020304060911 95
    0xd00c182003500c034990b510142041e4188031046900140304065406424429103a150282d42c9442c94642404103010303102c85a1418001000c54060259030300c8078a0070480c002000d411810403489610555003100e49030009010316000100205942c04024452170040d60320441c8649509507101c4111441d01081c040180092005c102060005050b50400f01c4001e00500001903142e0391140000c0001c840390508640384100842080070b450004851100030b41000c0c0003803e01c00000300700083e140c0d5649000100f00980d07412171807905400400402d4040d2000d101c40c1c2d482961900740300744181e102440368001560900c02e0205495119600351071540340e06841d01e00302078450b036032240051100141844550f10043c00001185810341c0683d10703030f980c05c01010f0445120074009106640d40140c1144115038010001040180c5400044400f143d070052000aa049480d0060318084e2145da07004950103030010041c00700348006a131127400000c0c0f00b5154035081403036010520513412425010303201 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 117582293 1250 117581043 117581053
    0x120a0c0b030606040f0909060509010c0f0c05120403150b0102191101021f0e0f0a0c06050a0c0203010f140604051009020d0b062a03072f1002010203070e060903 70
    0xe00310198001d960030100090030b490405403030352030b03210300c460255000300907240e05c4824110a02c100c40c494140c000141c54004d1207046200f55014100d50104040f00302000500e0502c3c00602c8024481c2e0101d031800e55401c1c664655032414070002c48546001d60500e128503100d403070001580002102d00302c0c0030580d89800034440d4141c1720b04900c0407a002c1e01134158010018804940c0080c0d0100400040342d07681d0014502d95404152440d141407410354424560184a003000425020a04a01256900d2600982d10701542504a030007049100009405600307007030600c00381c006076800580380d0361002d042540d1181d0301d6000b00810340d1801d640b100d05404120368184030840702c40e001080700c1c040301c0c00b020030158040c0006c51800e40c0b0800d010810700c080044d07140d01504030202c0c031400c9503410500550405200c3d46900c14100203402c0c110045042c0901c000008803142c00300000303100030041c00c0c40078420304c0c1840079010394001c40301c1c00000703610004901460302e01b070b4003a40c00009028000700 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 117583543 1250 117582293 117582299
    0xc0315050f0103030c031701030c09060515030c03100e01030f120e010c020f0607020d11150703020309010c0c090507091e14040b0103090b04050304030209341404090209120a0c 77
    0x5a044d005e001429400c100c0c0458103005281c8500744000d0080d03110710165280031b4030300302c48181100c486400541c415803001d51380f690b540754040140c0e070300010b610320660303a43d84400c5034001055070603074420026030720031900000a001629112070022405001c0c19030411a07880c2d8102e44c1018142c001a01042e50407a1b080d01505140c0d0170020352f080007500651418105400140b14010090012108031403900340700c0d240c905000c40c0401c145200100c2250600b84aa94003940304d000d40903450341045114031002042c49607042c0c0103801050981d0b010445404d20b56402803072501a8010a560b02c8851071440911202000d5503204461039201c1149480002504100203404281c0c0c0c454101502c1d10a5440803038003103040540a00d04c01c0300196500c41c503602c14020390a60007002d0078162a07140c001000c01410040800c40c500007003640c0642c2003880350006030340d5071190052041f40c0541c00304010481e0310041c0d004040b841030440c0c1c0b014002c0c0318101466690002d00760002c1044442c4d2100b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 117584793 1250 117583543 117583547
    0x501050a08090f0f0a060c08010e010b1303150c11030406120e0708070b03010e010623210a06030312020703050406110309040f020d050a0b0109060e060403020d0c0315050f010303 78
    0x190303800104200c281c07242c00f005216000d14044000f0f92007107994201e0941d00082000c20f110703144502403141040d4541c3d624003e5070108442c0e051040c1084c8070b5000620030451105404020040c0d94070000c0303c24100d0348903610900800005000ca00450440840245404000000c0c1d6084400700e66550b42c5c2c01090f03d1640e4050801c00000000620031003801081082080c4215005003940c5001d10b84c42c0d6140a032070904011043c2c0c400000d01158210044140340440780001c0402071000120b592145c00700001c035940001100300301c200d4a031110911050000d65007050007102c1c00382d66100080180003411104910542c08006e0105508010401c90140034044003c7c9183c1c242c02620305044a41000c581074070100903140404a074005544d19801281e84103030b039000ba00012040054403aa000080c0610015001d814188207144d19a4030181d0340340c008a81c040c660241110180ea0503525180c0301e00c10050104079003070b895041021409074401e11440d03100b41d200706103140c80d9910799201 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 117586043 1250 117584793 117584807
    0x10030f0606090315061503091b03030203070c09020301120b0903070b09030315040e0d0e0a0b0409050132040b1203121806070804020d020409060203070804150e060612010b12060712060501050a 84
    0x129030300404150160440c07841c09c80100d0040d40a40c000e1b541d1407100381f50000d52080079802207a42c0510500052005108051146441d01da0126800943d038a84103046482c502440d030009001d510941c0c104905810040081c0d8001c0c074081292141d91581c950401040c5d032480000c216080e03000e85d040d45000c40c0b040f16150081c050140c11180071544801c4040a41d0380180c00c0950451f481d0801000070b48449409407074801581c42c00742161040b15a00601c110321800d06491190b07442d02030340394aa5940309006000385800341c084035681d50030f4450b0895402411921a08101c01a5030360035100c2c0b1010981a110344520799900c24540c1ea41c0e0308010214800c0c00080e80c05c69a00d8407181c00182c007a00c0150300401082c3c8a2181038913052a1010b6800f10321015000c0c101d090080000510b000001d103260011000c41e919000703072803031000303080c0108684410107a0003038110001c03416030100850401c2c020039180d0359200033050006800d03810360705644141400100c0800000c400c4c5031080d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 117587293 1250 117586043 117586061
    0x902011d01030209090c090102210a030b01180611060a05060a060c050a0804060e0a1a04060c08071208040303060f050a060503040c080601080c011d0a0510030f0606090315061503 78
    0x60040c10004e910020540301c94007143e6008900340300181d104450b6070100400d801001550107024416802d898041d030701c0340501185c1005140d2200001d044c16800b4880c1c100484541c1c22007520760990380e110003002800c00f0314050f03020740180c0713021440814060103060302c01c04024090340e110034175041c000c50310245c0d000c10565007401031443c81d500040c0f82400910003010503590f05604151420104808491a035000260228488022120b0006480d0607502101d201c1e00f4108102d4015042c011030500c14030724001c2c1071071504090323003d038184c0080030a809103010343d908001c00c9032101013404d045402030041e0790703008010003001c0160501c01c0b4021503105100c1c81034041d140341da84070311070b1504000380c000030800d8115095640301560300a03200b4184c0c5503d004120354034000400800e10400c40303805006e005180701221003590074002c0c0c0001103000d1040c0010060541c0d9500300602d40f01d9036000844240c22043e98155091840b402448241d07280c0382c414204181c19070303105030020480c0721 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 117588543 1250 117587293 117587297
    0x10f050904030905040204140102010e060402030601120c030204060e09060c040602070e1e040501020a0e0f15071b0807150221090d020315070908070608070f03020c160f05040902011d01 81
    0x1c00c001c1100c0e1146d0000d070000344004003450810404c900c0002e800d5404c2000442610341c0f1030000c00015960000b0441d04580d00307034154811802c4a402c1030300c07a000c3c840d000690014104200001c55440390942035104030758074800d450140e01d403210078905e20b105900c22100141c0c4003242c14407c0500c188001c540107189800c0400e0030b0003d541c070740314040004030307003d41e010b9601140c40902d0b590400c1a03015020800c5444c04a0254800c000076a49400d03062400b040c200e0108149081048020100e02c00303803d6031640302c4c011565095a1399451001d8040d4031601540c034480f6103001c03400001c62401104143e49617090080c0d44040c0801c1c250040d03510664001d841c619108050384090201a13031030b10313401c2487d81081c0342c80413019001101d158414030b0755500c000300402460380e00c440c485410040901d0060444000004124060f0041e45050b8807240100041900594542d80300701085402007400e030502669a0b400f008112040d07808040d0220703001121348181a800040c20820902e014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 117589793 1250 117588543 117588557
    0x9060a081b120115030215041811220305100504081b030409090515060604180203040807120503090708070f030201030e2d060f040f02040207020102070824010b03010f05090403 77
    0x1000c901404c2d2003012441c207154050085040c402e42c02d10307602e00e05184000e41102d0b468640340000c0301402c200702000c01c8000740c1c1c0c0ea44401c4200c500100c12541c019150103600411020240b0707034844030308081c0c401240c45100e02620700f0100312050013030078440c507004070320300c0e0074132020002c02c0c86188103c403034001440c081000040f40ca0350441c40750042d4240a04001d082000104a92140c0b018002c1d11441c45800180700411042d60018072076071000120010140e03c80e1268a00745586001e00b21000b0481000c1c4144401840d034040050f503c100704c5001281c3c1e0b401d64070301d41a91175a4103801600c5032807010490510140d4020340041d600304c5811030807210100d56034420040c81c420201000710203040501c2d940220304904121442d000f03d07035403201c0d18040c01c1950300c8410102c0b0f400002405250040782d14404d5a00a02c1148014110842942c44070901501d1700707046005a07080039400340a10000200d000408001900e06865074030a807215214280010401d000200810843c108210 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 117591043 1250 117589793 117589819
    0x320030303070f200309010c080f0307030c08060409051b0316090606140301080703150219020c010906020c0a09020c07081902040b01020d0c06020903190f0209060a081b 74
    0x4104011440380380e1541d2840c3d406250240300804820354603c2c494040c80021500d1a028a004030440310401401d00b0500300480480c9001e007464040d09601c0c5c0d40b00e2201004000724190550000e14402c0d07000e42c0c4444207540e0b1001004110342d00b0a0300900107501040c2c0c010002c1c45884a12040c40c031004044422800581d80b003521f02d140282c0059031001c0e121b040c10481c113a00700999400c162455000307141550b0405507159540e00c110300c03000c1c042104644075140c10443d207034112218a14100d04400f411282e000d00655940302c01a1441e00085a910002031494400314050b101c2c203000800e140c4c0300529007107020300650442c00328a8141d0142060001d0481c03810011b00c0f07400501c0783c4080001c079100340100011548010041d6044d50801d0b12502d0809030b00001c4640310f664070140060301d0b4001400032914000b50b90151040001c0a0410001880f2445024403000782c800c649410940e42c0b4403041c0112030305913101e40d0245510080742840c1462001030700f01c00320800505100d1075a50 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 117592293 1250 117591043 117591049
    0x50a020c0904060e0606011403070302130302060d0b15040305060408070302010b090411090c121f050303070309080118020310050403020a0c031b050102030c03090d0c17060a1407090320 81
    0x441500d00f100c1d00c44da248010751090300c00b0300c00141e0098003400c124180045008001c40035201c000d02110030540e00242c51071a5901c0803a0748800755070003914040d1225143c4006400401e480c0203042c0c480c050903040b103a03480242c0300c21601600c3c3d121004c0c1500761280e50300c02d0b0b001e4010500c110300395500c070200001c0648510b001c491046004110203540d5629540c1445905400a0100c55a120007044a6001100540070064002c405403141d12019a40e08149a00ca103000f038000e00d0f85800b00046950916030b01001c0f5405581c0050002c204580c051041102e00101140b00250140c000081040040345244e0089500138040e005071056601e0300c0d51840b10001d45504200c915013005489161f20400e41945180a0f120a00045140a40051506540c0d00540138814880d114621000e42000180e0390100018241003042c1c504047c288845261030703002c01c6600c54401e9181c0154013031950650104180074905588600340300e40c2c1182c9070010800541d0344000e810064030303004051261 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 117593543 1250 117592293 117592309
    0x9120a0e0f0619030b030601120201050a18060903050c06030f0105090a0b1804050c0306090616170703140c040e010504230c030601030b120304150c0501020414181303050a020c 77
    0xb41110202204a050f0407030180c100d40480502c180207030300c500b005018014022604101050702401c05580300c01300342204450800c0100080003c3e00c442400001c0c8007034000403510181d0788180c003a251001c50b080706220050104075140902d42d80140d0040005051401da040e4204203010804111500b80e540401c00183d4076070b040c10382d03031921102044280402032080c5096188100c01524850411580d1650356a0010b0802d40c03446044800031180c0c00e000d03041c3c15102c6060820044031700c0c80c045a015001780b44150703040c4441c42514001030810b112403012a030540c0c665502c0003c0c1c0c0d034241000e20009060400310f01c0382411f00314030a900c44900c401c6416101b182e1201e1255503d1400c2c04c00141560004031038540110310f880100000400d0200036281034491080c0341070207206140e5400c072035044045901410315440014041010000180c1c07240581ca01900c4d90603420000d0000c0c08805881291640700d18500c0c0c03c525030000f0303c104010701c3e54281520440d41185440000030301e0385 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 117594793 1250 117593543 117593557
    0x40b0d060216031d030607111e0303010f0e010e0a0924060302040b0f0303160f1401060801140105010c060c0509060d060311010201110304031407060204090b030609120a0e0f06 77
    0x80890910038a00301640b04c5409200c804500145030301401c0f211010035503501300a004d08007801080105000d40c5002081800c4070b000e0b0404900b14012801902162260700c03c1c0901ea0040050b0300c00030845040f03004525048402545808209a44102d0704c0c00040c6050002252490f1f14036419501c1722074146a141110034240ca80003a04510f90710420040b60a5036000c94062045080b0340f030919036020007900d0041002961064454142d89031042c6100c0703800d41b000303002c10782a0b0030f00406903605521410540e14440000c0018030307000c01e10b0321a1460244200c5d40011489100580060210b401107490320680d410f0190409101c0c00004029400c48a03226001c556111810424004814007540c0c40c00004e00080001e510704c0c4082409900c030051000c0c09015000e02413019002c4400100c1e400b05801401c210344807170300c078a4000045c02d0700c00c2c281c900c64071410004c200c0038a00480c05003250420004200d1421807110019298400403a0403503601c400c40b45c0002d0520b4a801c0018139031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 117596043 1250 117594793 117594817
    0x30903021b2709100e0a171303033b010c060e060711060109020301030206030c030702070b0316030507090e160516030302250b0a0905031308071404090809040b0d0602 73
    0x142d450400038052a04010640c0c000344039040c02c0001a8544001c9500d81c039403038101072180c4201c070400b41c1099003403183c0d00b000c1e6140d020b840c2d4002706141d0f00c03090145100183c48010000364580302a0040400030f01e4101441710b078510100301d00d2940c050400c0340c00d428403070f8401162110507a10a0f40c10144104c80c030310302007060341d160349040703040910455000d4060b00781c0c11400c0d94195004113030a400001d00108480c0310000c00f180ea2503000700a500004c10250a4299a071f10b001d00d00303d822101813468a102290800c4003065607e402a14071209840d15200680b54a58132500d110b002849031203115400d20100700401c00c481c1d81d0354186a004523009840250780e40301e80303940d4002c04174065039601b44117001103015040001c100042080d00900500800705500340e103801d00f142148101000400c0c0780c00300e9100002c00d810003003149401c0781d4181c00c01c00203541c585020f0205940040078003c09508082003075000034034259200001c648005000c2c002420f00598401c0120b1380108400e8003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 117597293 1250 117596043 117596119
    0x714060403090602010e061005060c0f0601060c020411090102330414070e010b0403030f050f16120c08040e04110d08090405070306030201020606040b1c030e0907030903021b 76
    0x404e40901171162102e40b000c004056502c2c04c00251081068103008492003a100010040001d140400409982940450039035900d56554100036000c0e01200d4001c900407802c0c048440d524550407001e032082141d040c3c000d00412156400b8088003c000c0041e03d03950740b800090041a00c680c4502c40c144118400d180c000c3c10442074100003450030500b0742c0081000701c00306005210828200059604070b980c1400c11101e00103224006681034080e0b80000e03484220045402c03041e5440da1a031549400e4040c00c0e808002250151088440c0050440080e00c02401000200f001c24842903540d0340c01130240780d2181c410400000040d80c0f600703083d0310540b44541c002ca000d0301d05140500c202604141c6500301000310710704e140d001035107600000301a42e201d2a581c40b21000641c8904150351a820324000750020106454540640141c282c1074080340030f8041c0030002400c09002e403146050311034058000b02078030788402e07141200394160407244503008041a07801480520f254109580c803002c2e1307054245 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 117598543 1250 117597293 117597299
    0xa0e030403031d0d020102031603050435030f041701090209090f0f0c09150112020a020d021603080306130e030406030b030d021606030c0c0803040308040209090102090105040902071406040309 84
    0xf540d04601c20016441440c0801c444001070380c00204036000c2c0301e500c0c0f1039024402214203050f910b40c007070b42c2d000900d5010100d16a42810303405545446502c4418881408004040500103a0300d010360106202c4a880070803040c80f40041c4046411001c6941d90008140d401c1301c0e9000c200c2c1b1384000c2e40c83e0f0300650700c12141d00c618440284140112a144d02c0c1c010a503950b69800040c201a00103401410045440342100041d40d00c21400711992090880301550340e6602000029500c00f0050300000050191509030340340e02d0101c43c82407080300d80003c07840382581c884208000c3c4810601d002c640c0310740d990b4168a01d524130b061028200030100d540707000a0b030008080516040070307035040c1a80d086402c82d551001c580300c64141e880d4142c80251900082d10030400c0d01c00da690ba841018003900d00400032042000301680002890703c188e200f500d9808480c0c8407440000d0907070141c130345601d0100f0401d01003441110460b5004d040480d00a0b800b8044c0c0300507030a0003600f001d0098074190009007943c0c0c414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 117599793 1250 117598543 117598577
    0x2031c17011202030a08090d0b070f18080a03080c0d1410090b130c050706050a05060102070f15050706140f07021c0e0603060604080303100303020106050103060302090f0a0e03040303 80
    0x1190040c040c0b0014010203029503400262602c845240c000e1822001040076059500e0b440c21341b80d4011307401208122181450900a0984100c0368140000150001d4521010504a402c100101c41c005401400f070302c0c015a800707660300f4070000d0681c3c407488400c0c80006090b0501d401340c2210302072050080c0685090010380c04542c0c0340960400d00d03009017460701c000001c0d00c400f402603c070306180b50390005040d01c15000880b242d106810010304010704003400c0c4007205c0429407025004031000d800b202e1445036681a1038a50003800d12800300714005400d2540d0440f40a2402046024820403000402c2c81d0354500356407440304140ca902e10828801c0003044211601040304a81e0b00340496024009100c0d030070030041202000c4c2011074050b40c0e0100104040b9120101036501900e001c01c15a07403607180401000200300c01d6444158015802c00c8800038055000c0d10840382a03036009072103040d8039611480080304540740640004013096684603581100318080c400f90014510903624024921003204207 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 117601043 1250 117599793 117599837
    0x1030f0318140a0605120f0403020106050315091603050d0e1516020102060f090a080c0102070602040314060604020a080f0403120c0c02040e16060807020709090b011712090d02031c 79
    0x2c50a0000402c0324800e224800c001b0107030f101c100060310202a645030b260880c05000b81e5400a0380504c02c09081f11900070300103000c2441506284115100e035541140e0807212440d05220103881500010203d450f624420109040148000340c000502e601110200d01e00540c0022040321048504081000456a0501103150440410b080890150038403e110700d49500042c0c1c0f0040440b440003c510921040a4040d40c5d4090f8203c0000c64507140d4034103189900e02d150980c0341040d80201e80002c0d00925080c0b09580c0c100b0b6459072604001d1395103509072000c20b003001d4001e0b01403003200e04160050644600841c20741c1a4a81c0d20b000c207541d81d601c180415900c00c1000d0121542140c04100c08144e035011034030b0100c0340310f860701c1d5040e51516401030342020030ba0b40101e18005d040c900d45506001d1034414660496002400b80818603440d24a09501d940043d21240c00701d000400007240a86800000c0c84c0880d07000400f0344041c03c070100c0844d00c140107080c2e49903002ca82c2189079000202c860841c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 117602293 1250 117601043 117601049
    0xa060603060e16050409050c06040b0712030e0c010f020c19050109120803060d020604030c060201060e15030c0118080609010c0f0801031106030a0204170a05010506120601030f0318140a 81
    0x200102440c2d0070b40200f400400d405454040d0f40d0b100a02c07414014108040308491102070180e6560b036032100c040083e00e901c03006069403014038409010014901c0f0340b080001445c48003000d000280f1051004460003004490650114411081c4514865844d40484203500036402a481c0400d460000090000031480d40000d0703440d0004010603000c02c0c8103408803940300c10100da501e46080490710009059014580016103200800071011642a405501c20406d94110b501c424031280d44900e011030103180401c17196901900181c01140c2e0315409078100301000004603c030703881c6050702c030019a803518500b100c20034016911a015200480d400024209071924645007601c00c0350304685800d4010214400006e009000c0080020302c0303020306505460280808030f13036540110040c0103e60355076400c080402d4606510b4100840c10034900360040180e0782e40d240b000342191340c0c40c5072035802110010f202c09400707101c4010000c044280b82c5a0a100280c18114008a02d42c1d041e8000d0185560441e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 117603543 1250 117602293 117602321
    0x12010f1b1404171f050f102403020c0a2003120f03040204020904020301060e090a0513030302030603071512060602060105090103020f0f0301020a05070b0a020307080f0403030e0a06060306 82
    0x182003039426039a9001c40d001c1c1d44140201011810004061928200c0c024405940352881c4035048113014100e900710324003c105c4808005410780350008841e50034a000c0c8200d449601130380c1508006a1000985121041072a0500500740841d10b130080b401c003e26003604450480100c50200f100d000c610f001e01800c0700055004000b00c000940184486100b020075024540c0404000101190b4841c0c04031401c900d00035105640b40d59503910090442c800401025106442010000f42118450b11850780300d05001019036104240c1c6450a9000358406408103030103000b03019011686402c0300b0301c80f501b90200b540c0c900c00241c1c58102000700300e5a60b6005081190400d90040020f6031b02c0c030040340e054a4049603071861038429a000600708035000e1850b5a01540082070500c2c202d90014043c0c142140608440c0c2241c0d40c1e2500000100d100850301d2402103040300c00481c6600740740d41840c0c0c0d070003072080c02c0014010711300a2186143c6007084408568054490f83c2c20310411545005945024040c1d03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 117604793 1250 117603543 117603557
    0x3070e060603070809071d0117010903050306100e062802010504020a030b0702010e0706050a0201111306050f0c0f030901031b080a020c010f020f0c12031302090612010f1b 75
    0x2120024407a440050a0f5004000410010402e2040144030b403a009000f11034402d1301c2c1c2000034849642c1c92609100707900c84444d006407032512904040c010054a90b9040c0d0780d50740780d940c402080192070500029880c0810411030031098041c0c607564000c1c0306036001030a4110b0303549050f2007114504824541030710708590400b002d210060320b50f000c803481901c0d03210300604110399496070102d004040ea100801d20703d114242000170130700e41040082250460302c1c1c0c000d0201211604210304c9900c40c480080b4815a81860200020782c41100600200c07890306640910b0803c108030010700d01091144e031005640c1000441c01c02d151380520501841411008001d2283c840042014001e850004c0800341c4d01074001611b0134013a1300c00e41c44611044005007046444284c051007422042c2c11404050490b442414800ea464800c150241ca120f0300070f041200c48500b80640c24009602c0000d8041600503a200c500b1003107000083c007943c403c950505000145051003c40000c21109100002000344092 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 117606043 1250 117604793 117604801
    0x60c030709180f151202061804050f06150f090d030212040f1e0501020a0303050c040801140615031003110607080f2701053004051b03010219180509130203070e 70
    0x40249091100381e01120740944440068600b0b10723000f030114a00590181c0b604c0c041048034151094600d0141c0c0040e10070046c2c05a1490314600540308085000c900b603030040c4441503ca14109803488071040c07180c810342d00d1442d4111000589170300305800904481001352418844c095401c51a0462000501d003c0b0200e60319290010b500c80d1040040541050b40362130010b103441344010119401044500020808144d043d419844682c205690a910401e449010405100d0070002500c1c01000c118070b045802500c5c43d1780f50030302c140d10000c403c1d070051030501840d001315882030050308203600c01110b0300e60b461a031215412a079414910ba580b07560003584020401e40d907400420f507021600b03a000f00354007003242c41040c101280c031803411186190f074504041000b0000301095448400450312240c1d0b6007840d4940805083c0e000c0d2031140d0b0344440c807407004000c41754858250300440c014240403001059403901c0101d20400c00c01c513a44100c03505040c41400450404014403402171240516840403814 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 117607293 1250 117606043 117606059
    0x4030803010e072a0b100608010b0d111315090612020c01060b0301091b030605061e0d060303020115120803010b03071e23030405060c030709180f15 65
    0xc10700940342014481c8000400c07a600401180320b0700c6140302c200c200034040c04044520302c40e82000c0201e440c040c443c4c0118281e0f0003401d0041055600c151a1141103030300b0007095070016000281d034010b06503103030302000094402d044010000e200d022141d44004505120340000b1203000c080661301000a808400c10410354000d02c3d030000304043c2d4201580d2402c0810150780509090b8003d8000c1c410000b000046c0340c18a64448603460815150f20182c044038a18181c3c12500300b84a00703508103c007000f05c0f142c480040c554081c680c03040d5188007400d1048103000340080b1801a00100c0c0980e654144150120200764642c000800c1080500b5912501e07654415026000c10303c50030000001c0400840d8105019049103003100301c05064402d851014035900600e104030ba10100b10300b0030f110700c40031060501e0301c804407442103400070000d240b540c5036070b0088032460780700404100c2041700302203011803488404210500c02401000e03010904440703201e0028111181243c0c458030910230f244041004035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 117608543 1250 117607293 117607297
    0xf070f11061e0327030904050115020a060903091212032706021e070c030204060b0403050309010c030e030a0606081b01020d0f0c0804080d08150d0f08040902040b030a0c0302040308 79
    0x81d0304100e0b4242c50b901d85612103041382e03030b0700ca02d0720042c907900040c82c1e82c00311800400b0306100102200c041c402d03a6640c00607111400c04258a10700103810200074000800c3c0e854014206041c480e1405030b51155554404400311010344408403404061100c013400c140b80d05000e10002e00380000140f14000030080c1c180052403035008001040d883e0007143c50780494504601e4054801d403040801c660750b0b02e26103020181b03030005000481c41240790a50120741c2c007101307009640950ba8014011484d010b513150064a040c0c54801d004c900f0408003080c6200c450b14107118040c0c02c3c030311628011031a030342000e031041d081c40ca045203501d00714101e901a6800c02c0ea8000b0309008545c20508143c0b4080c407424404a6a01c00b0162020b04081400900001c060600180024460b580d03940c4140094a813145280e00e1101e40304003059100300c46c00e0182000c503410441d40c000c040d200d00d9115103442c0c1e8500598007660044d0f0f0110310012400b00401a80800c6809005200c0001d4034003146017504580c0c1d615858 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 117609793 1250 117608543 117608587
    0x70c0308090a06020f07060609150b03100305031602010e0f06030106050708040b0307050414030a210c020d050607090e090a03120e10060603060b030105100e060f070f1106 75
    0x10100007181000c00180018110903411040555640f59105408403a90703101410441d2000e282c01c02c0010110a28410440b131007010500710070b40c25107440c90340480e980000d41400e1501044000c004001001000244042c3c0c07001502c405124110b80000750442416241c86401040102c2110348995070340b00c1141d040d1030742030401030307100e004600700803405000787e4000182e100c2c00007050180f0b882d0450003800485980e003641c0408481013100389600d41103003140c0141800c2880c4440709c40050800d04e0004c491000c1e14044a0080458001540d1001001d00035030b0160444004d111741140d10920010107450300b00c071404001d080c281169692180b0000d00134041040010308040d50038040e4125041c80b44480d801c44000d440e90245000040a45129510100c1e20b8010000744032440380013a00c1c1290341c0103000900011000c0c4054400044440d0806d902510130050018100900070191103c40c0c0100426074408000e03140c80007000742c0c3c1d0000c0390702c225024090725001d02446c101024070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 117611043 1250 117609793 117609797
    0x140a060e0103150e07171e0d0f27180b03190f060b06070507140307050307090c03020f0c1b040515010c02030309030f0609190525030605090607021203070c03 69
    0x4403d07074090713050410629070000140500d01c001c403001c48200004642c05c407101002484440c159041c3d00c00c542c0c62030100b083d00081404542542d074554050031105944110030b900c43e401c0d00c26402d5240c41007021b80e8002200b03002500b89111b07001c2c50148524900001c00360028204880c44205c00c000d070b01d07a03204c0010103c44852814104101d41ca8001c1186c141002c1d0403241c4526032441c01545480481c064920140c940241038841854000340410403180041e0103000070a04050900c0003400e60f040d40581455001c01c1682d040c0c1d11928010a100c1c0e841c180908501464503445666003000410900d10407030804040c850700c1320038100c080e880c2d02c0302400c0c0110b103034205101090442c003403c1203569040c003c80b882c14400440c00b080302d500c21862407003641d5420400c504c0428048a04101c0034241340e01c504465440141c2a080c0038903290000c8000000f1603540f80d81d620141c074012105170290750400010b215804e03404100c80d2410102c4103003d2803c5262180d4024031710340e0180b1014003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 117612293 1250 117611043 117611051
    0x30d36020f150316140706050405120c0708070504020a1b4134090609091209080c04020d140a0504020102060108070e0112080c01140a060e010315 64
    0x21035842104807051514064a15412111003a01c0c1d40a5a001120780081c803141140d102c1c039980d4802d02040800c107000104680c100842c83c1c4403100104001402101c5520841142e4528801031030301405280407074030000c0400070309241d081c074146191359005600070340c01440042103c0742c105020200501c08449100354000c428200400c0703010300064281502c1481c0d20b41000c070200c090f81101d0300404502c0043c202c41c619030000d541e0b26240500074501c1d5800e400e09914003240c0103002e440014a50b8101142c0c6252503400d88412103105030b10024240d076031041d44c581003140c0d003560200440414107000000c0d078500005542c032101e246d110342d40314590001e01d00c040b46c0710b241e014402c0388103200100c1c1c84502e0300021b101c0042000340c4082c3d001d80b042100000320000d00040c045c064a07210f81d20700b40c0e182d203003107100c2c40362158180c0100c909410500c51032101135424802e00100001800c441841070428142001c01c841d00ba800015054a0040040c8042550021262640b0000244c00a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 117613543 1250 117612293 117612401
    0xe0a0204180b01060306080d0c0b0f1003140d0806010e0a05090c0d020f0c01240501350a06050604050609211203010e0708010621060b0a02030d 63
    0x100700d140d0320a0000c1c046890314002140307250f03140d4485410342e04e610040f9007003602078020982d659054018010210b244910014000b0701540e0a9035030091420083d22651903120364071a11010220a4855820781c0306c942d100e94269408113100383c22041c02e0a20442244401020503040c1c1e20a01a050040a508001c1040064090708481000000000c11900c44680c410b01c50820b40c4103441031a203e40c04e03d1043c2203c0c19103801d580c05041e10122a882c1080d14107001900d125520811562002803140e460104040300020709800c2842d811554a029244c1049210704841064103c079004043c00d00091013a52910303c1220221081181e503100c075020b000103002041c96407442840c1c0ba43c0240041c1e110402030301c00241d4142c601c0721a9200c859922076104030f50000c02442a100045c000d40d102c0c035018181071490645c5549030400100d60240c039402200d030360390321040c503040040e88002002039089419100340610001d02030b2254511190015030a01c4506519406020045c5060310300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 117614793 1250 117613543 117613571
    0x3030206060424090b0901050303090a0e040204180f170a0c080c03091009150c0209010302010c0215030907210819050d090b0126070b090301090b010b030108100e0a0204 74
    0xf80c040009000304003122503214140080030780001c80c403540c0680d13450030000c6600c0c42c0100546c0d4425201502c07250017189441e01042d00c0e060041e000b80e801c0340c0d0342ca01301c48007104883c510300311090049103c41da960074949465461501500007051280f8010b110450754070307a00c0108040e80d0b6070030000290700c80000d0b401613070940c8954112140c0c005205040ca01509802940c480110b540c41082150760594006040e110400111002581320038440014401980030348030622080d40080d1044c044101119030090781c80d401a1000c2200ba8007951b410882a40d6001e40c0390594180c5580c0b0120134591a41c40f40105c1c0501c80040c03402d80b140310300540816203d1009e960307016110780800e00401d090390500554102e070a000c4d10722410035030307035400d420303811181c03880380f10010700000030070459280520100f0560408403015030325541702d090f1400070601c07100510b400380012030fa901c1d9403545041d0003145841000e061451b146410700c62010080a40450000c1d000c540568010070030550040d48 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 117616043 1250 117614793 117614831
    0x105030a150b0409090b0108010504030203040302041e050f0105030c0607050c090717071809140403030b0406030c030b060306060d0309060807210e2a04150807080102031e01030302060604 82
    0x100780da0341c0b408180002c0c80c41c4103810404070346015501038203039640c0314040e45007610000c440c0a4050781c01003708000504180d0f0281000c499244121010235008011500581c0c0c1c00340d8000e0f00040b1004018021454240300c004c002801c100c81561401140341c1d54a520b0301980c1c800c4070b00c03445003400052100c9000c1d4482c11400001e00030b03c0d10092421200107004202020030f943c00303801c402c40d80414070311024450940d080340100300a501c0d507926540c045001c2d00c0e10364002900076860307110002c0040e24034040b04020754402c503a0702c000c500d440d205162920000030103452088508600c0d80d0702080d00300600310182c4900389004207240d901c0c0502039560400d1250a003c030b010191303101b03146001056100000c688000015502c2030f01001d010407440051000e0b134a843d804813840401e0903441e2980c801140c40302c41c407628420300355031522210701381600b590001040e0394001040250584c40d048640e0345414125004444550440d24000c0d640c0c440101032500880e5550304002040e010b2203c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 117617293 1250 117616043 117616049
    0x30a02060c030d0c050405060304151803020c240307080702010b0607030e010801051e0603100f03050a150908091915050406180503060c0a051c14060409020105030a15 73
    0x4160355850300c41c6260703039658041d075140503020f4039000e200c9040398031540490f000c5681c020900750440c0c40725101d116020f400540c031640102d40d940e0740303840d001340d155443c0c0d00c20b280613402034810040e4840a0106002e03040d12802c0022014007103a64443c101401503c0d040005450310300c1e0190f079090b1040c2d0050881307085030742d0b0101c00403c0d503508060b03000c148004142030030303603c4202b1079a0b10801c2c0003005040b18004080348200420a20301c0b42082000b460b8486803070f14840d122250f503031051320704002a5801c181c4940c1c00c40214481844041c9101c0c001440b40c00300200308800c00743d16841c0d03085c010089220300c03980e5001c1c01c0007011b44683c00341d1001340039071401001c0208401c00d40640554002c1c86000c011501b0200c20781d0403031040540001c00c840303024014080a0b542d807400100603a01080441c400c0c024203210f401680b206048082c3c080c5032360707048009030492001401e052075200045c506480390f414601c5100050364010156074002da00c0c120f01050840a07001000c0540d00030b90 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 117618543 1250 117617293 117617299
    0x31110060b030403030b010c030e01030c14030403030e191a040204090516080c0315060111100509010603020f040218060903010204051309020a12030203040303120f0e07051e010801090b030a02 84
    0x18049161641c107001180164481e403000c11070603800c0030041d110815402d4024010401c0001c5008655009402128440700d841c41e016a04042c05011f49413035800582d0168002584c07100d0307110043e6001c02c002450314100d1203002101c1ca9217507842c1c449040420ba801c1c0014201c610100d070031510745030403250555500201751030f070f808024200081c10743c02d14070400640d4031420f80c8030003c0b8280407541400c0011340c00300180450f92040019070300032207a80c0d6103070901d10a40c1c14a4821142600c2058000e580c41c60000c50043d140d8010001d906441c056868402c510400403c8069041c003d04000304400598569840342500741c00240203004a038000b5401003060300b08004e8011080c0c2c044552180308039080d110241d01c500c100550110016802000741e0b004010030b2021034010030013624660203049c400702e0320301d890064104c1a0341a89200b2a01640442424411403400c00c00c28101041c0c20700f0308004c001141d0380024100c0c007040c0324150915a2710020400d045e2070034850341c00301c180c000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 117619793 1250 117618543 117618551
    0x904020c0a120305010501170a18020a1d0f01080607120612060209151c051906150306091107110a0807030317070f05070221070b0a0905060301060903031110 69
    0x600b00340400e115882c001c000080e143c200041aa036008000c402c91b203c2e002065850b60795124083c40004001c00c0c0004c042c081d912a003040c0050343c07480301c0780028114111403c0710441d51110f0b210191400940b03082102e0002c40300601c10200c3c001074055001d84145450400c03000f00d4032094000b04030903001094090010f406503028000140c0080c14810303415600700c50041c01c6145400d91500801c4086031080101282e05000c10781365400158100b0f2001c00345031442c80120790503008aa145a00c000b0100d0189911480389941610540c00240510035062180c2c50610041d11940e20841100408514100440780c0d001c3d295030403064060a65482103840d441d03120f0074080c1c552204121801c03139541c145000981c905100713400c02c041c40085900e0b81410009280e0030083c03103008480d080c5180d1402e850a42a04010401144d4014111611042e80d2199002e02c0140501800e40001d0b0103004200b004004050b800703d40b180803a500b62425880a5405040c12410701d040c0c1001c155004e410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 117621043 1250 117619793 117619813
    0x51207140301140a090b15071e0b1603091101050714060c090a0b0a022e06090203070e0a0317031b0a09090606080402131505031c020609030408060703020904020c 71
    0x24451a43c0b900a0440d0b980c10000d030b030380244c40705582c560749009800050403412000035510060192040d54850501c00410700304403c098802d001200000340c6100c03035030000780075280f0380f11241c030f82481e102c0d46400d0140c107469891785100911000200c9040004c00034440d000d1220f5201240d20050780e40701601c5190607c0790364124160041a0500c0c801e2410f0480050b8941d030b424204d803144600d40d00505038030b18100281108001103800c0b08480b00d0b40c506840c0600d141030b441208083c2010110041c5c4a00700440002c10382000d5001d40d50084100b803200740082509801d0f08500d110100079007681c0d039a100e102e4010400c02e955403192652030080703503414039a90030040c4107058030200701c0c0810600380d036820119100340080e81c0c060742058002540b990180d0060b0807403038410880780200043c01c2d940d02c001c80d240100f03081442c44500a0011480c2e60a50b05100e03064201d12520000d6080c1070400c1c10180d222030300a0300701d10a0580c0015200301540300c07034050701d034403203010030560b21000c0c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 117622293 1250 117621043 117621059
    0x50a05070b040b0405060c2104020604050301050708101d060d02010e151c0204060c141c05040f08011e0b01021f0504050f070b09060c010f05010807150c03051207140301 74
    0x10003a2005c581d140a801e0001d500c0071411030039a1751342d0201000c5040803442c1c05c40341d202e014801801c140c1e040402000003082c151030034044c003801200703d0380d1005210301c3c0042c186041940b0682100305410030074071404c000f4141034000c8a8004204443e0707041198140c2c8010380c1c00700e031107101960300b082d200c0c08410a5508002c0103414000d0a091107401d13a04c1651545404901ca02c0c002e45000c02d048442030b402113000c1c0c1c1ca440c40703488082e804a48a11900401e028494450800c655001550000c1c0910040440b400390f08001c001608c024003006079961400310400038130852200403140d941031100856031080101c021074184025111611014148440000c0c25084805840038803554880141c003107000211103044520b4010010300305034540e001c000007684820325460781903403941d000340e00e01c04e0984103041c020b043c0d002c0241f104518080381031f054001411203541c24410f0540d000c0c4040794105041b01c015400c2d80319100d10555403030009031400030808240c11096040031001181d450 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 117623543 1250 117622293 117622313
    0x22505100801090f0203130f020a0e091f0905060105010c21031b080403050301060f030b091302010f1404050904150e070503070e090307140307050f0a0b0a0912050a05070b04 76
    0x2425450f020b03c8001c44450801080e480280c03210745c1d04d000140b060501252480c03140d400001d00c01014161010350b20806d8048036001034440d0785c82c1d60488120b4104021000440e402d504091010034061441291112a2159814826107040c0711644990f0000c001e41c2c20690348400180c00e0341c00c4aa0740038528014001c12401c0369905140d450074140c503412500500785035100e01d516070350b170031310716801c01904a507500808201c10b8285501c40c03810613a56640c14001902c5400c20001401c584001030000608030720300d6648480034440141030390500c000010007100e0950301c05079200c82d07003611a8a0940c01c01c01425140d101070924100e80d8032400c0b5000301d21081151800c40c12208001c4d00c40100f00b02200c4140c0703243c0c540345c0c4100419800a0007110f155190040b03c4001c0c2d0341052040e40302c01e0300b003000f030410008a90708181444020400010700d2617820500340c00040029442c1a922040581c085100d00c1080c0080420f020100d00d208008461382954020000f8100341410b10f0904115 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 117624793 1250 117623543 117623549
    0x30602070c09180f0305090301290117010602061302060f0d0b09010b0a02100b0a180203010f090902100c11060f120c09060313260903011b022505100801 67
    0xb5052003548030040d900403100c0c0705050b070040e004040c22542907800341c44a42c0b014828541554880c101040e0042140d11502c0c103100a40540c0c5400f8005207000502421011087d000030340106401030003010790004e9450391240d05880015215400c3d800002e419002d4180350000132040000c10785d800d8980760304040715004003501c0e900c9007640c84071403050503406200b02a0b40103a0103c01e10340e010110740e4218694007803015200807803031900d66007100402088140b010a0840d000001001180c140442110090071005010009800c0f160300048001c4280588401040b55050a5200340040312006a81c8001c004049541e513020442d110811500100c6c445140343d80f0610008005840d81030494594240041c0941c0c595a5080c5450f2200b1094103000d4a20b45034411a4284201c864512044048010f5403110b4580c80a00109405d5800c0c41c00c02c074600441410200c03020a400086c9294400b010030b9012402e00b2030740c0d103000d40e0a1034039803160f40d0042c1003900d40b07416076070424510743c1a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 117625899 1106 117624793 117624809
    0xb040e0d1d0a0b0a17010617071709010e07050f18130614180a031d04150b03010303021510060c0320061f230a030602070c 54
    0x11031400b03400000d690880040c001c42065003010fa801c5c50300700715240313985aa41c1402402481030305005241d180c6651104040b80c03585000d00801c0d031080344420302c141c00514160100c90301070b20440aa0700100c0c0580c0e103000c911410052000c10b00301310f000c0d041402070b0400491030303401e00308000c0600d051030a40400c0c24001401a0160360b01d501c40f402543e5000b07082902c20242e41d5400c07038104e0000d0b07900241c0440000380e0400740b13601482c2c044c54030410501c0040d00110f00503014400460304e040084240101b12140c01d0310145040c6ca020364215503408007240c89002c002c0c0b50986511840f100c0228040040074030400201114611900d031040390f103683c10030600b081c03240100c0d101c0e03201d030860b40801c1401d0f40b030341c500c00380680d00d0342140741e1480789070000380c54810110054250380e45441d131070030480342d45444007000020b5074032980841d0303030721420f0411309030003407041c0900b0203 = true := by decide +kernel

theorem cover : BRFrame.Cov 117446043 117625899 := by
  have h0 := BRFrame.cov_init 117446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 117446043 ≤ n) (h2 : n < 117625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
