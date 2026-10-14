-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0084
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:44:58.689722+00:00
-- url     : https://prove2.me/submissions/b6aa9de5-b217-43b5-8d4b-bb7305f7c306

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 14928064 ≤ n < 15107920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 14929314 1250 14928064 14928071
    0x30e03070803030709050d020904080703140403060f0f020901020601052206080303010503210304030804060207060e01140a1109191701020705010c0804030c02040b0102010b040908040305060601020c0603010611070f0303050904 99
    0x6c030320400801035407811000c4c1d84008403401290024003000d001b00140d501c20b04148020346e0f401c200545072600190700590f0000c0d00c82c1d100304800e41c080e2084148070910600118180024000000d40d20b200501855020707944549140600800703110610f801c88030b0140e000c3c00080d444503009501c0790030a1207071318040d2140326810b580041510305401c0144181142c541e095958580f0112400c500140060390187d50800034100490028010b941410011100220b60001d0401140c45007840c0103118141c02841c04a6607003100d0191411140101d004a81e12900d103200c1c0e885a15601c44241d0005101c10700f110280050210103401520049021b4802000328a122500540380010300721002800a0079a648010051030702d9404802d1100046c4000030b0724052000105007112410300c0151510301c0041810070070040c0800c074407a4444c0b000c0c805010440c060314007207452400103014083c20701c104d9100d403d00c088d01c20000d44d0010894008030401080d0b80741400340095108024880c095402d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 14930564 1250 14929314 14929319
    0xa030c0305061806070804020d0204050a0903170105060403060b0301060e13060f02090603060111010f0507111603020d1202010e03040308030915040c0510090509010306060609090b010f0c030e03070803030709 91
    0xb18075010b50100303c4040c043c3c60359150b4007141c94801c014812039000524180078000b507201c0d03218882c80b485588000143e18910f505000c0c1550300028282242d4824030001442039855280c00d940c100e0f98001008100084414006405420b45401c41e00c00c03200e107807042055181c031601407840c9040c0991003c00c41400d000400c001640720381d5880a800100030800305210b9480340c1140c5000044200000541c1e03025030424038140c80007640d40c58002550b0303003c140344502c0107003d50542c0260752064103451600d03583c00705181c2c000030341000d800030000c08000150345000b03410000f0300141034000e980e85d80d900d80c03500303035500d400a490305122442900040c51070b2800152100d0301a54011190301da059107090200210203400501ca00100101d2160001c2d058a03245411341c00303544258030200c0c00ca4100400201148415404540540d003003540380001a42c00508008041d80f0314035102004040c2800c00359202030000f0b5140b80c0512841a0000306680040060340c014205c994900c01c030303540d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 14931814 1250 14930564 14930581
    0x40602030f0f011412010e100b0109080705130e070f060f030b03010c080a051905010b0c06070203040605041406040806040f050705060901140a02010e07060206070305060604030b060d060b0a030c030506 88
    0x9000e292074940d80a940c80a4921748100309050384030040e00045032001c80f65100d1030400d411056000300081e00e0346d40c03141d05903820001e8900a850040010801c89103054006054101c0300365413405260f0743c82e84000700e225400d1003240040d010714140ca004440c2e1301c85008100f082c4c010003400000c2e01d070141500b007a01d018010709299803070769542e107080d0b900c07807011120060070090202e040d5000340c1c0c50350a142c5041c171300460340240594188140c407019002001401c02400030898001c5410030401841015080410340b800d44401201d010300d82011400403c2e0382d072040d0340140b040d5200d80800c00041044104061006620680a44400e29a21400c0c00b509018005140d1302003100503880b5401c074070107100500340407140d510001c01e042d00410040c504241171900080c005805c1101008121601401165000312041e11103c3c03500346192030721070003180090891031285900300042018481150482500d0600c0200220310942d0380b0301d841e2681a820340f0080300e141c01100000384002c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 14933064 1250 14931814 14931841
    0x60a0806090a051302090a0e010c050309010614010903060b0a03080d0504060c0f05090607050c120a0c0602060415020a0e090a140f0c041208040b04060504080c0415060c110405040602030f 82
    0x7050128070b84030410507168204040d0340002003da0b80900d03904e80321504410024050b00301034090b581c42f090360340c0c01d200031900d00351451500301030b03100050000c01c1d20003643d024204d003040781d0708070704c1c0060400290800150001d070250306c0074000c000701141c1d048890709a0f82c8020b0165100300010010103000701c8040d00c150400d0f06072400450400d11465540b070811130010011f952159095505818210f4001520020741c01c0701200325500502002003007000503080d08010b40200e0008001c1c5251503a18501609e1200300f010100c20b80200c0d407080158081e0b0034103102100001c240e42040d2030581038040c0206202d503030b404004c1819601040b55103044401281c0210700d0310009038940b82c2001c3d00b85140c401089003c4810700400c0100090880d0094040c0c4082c01803030b501c1d01d035101d1600103043c0c03070714844030960b82c825490404c031801c43c010b1011248041728082e00b05054110043c1c2008480314030745085454126007410f0821040041641c015403180f0902d8411b40c01ea41c44040404c03004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 14934314 1250 14933064 14933071
    0xb011806140702040b040c03090b10030b060103020f0d05010303020d031406060706090c03080c1501080c010804030e0301020706320103050307110d050f0c0a050d030518010905060a0806090a05 84
    0x100d8100680207640302010002400306900150000c520303210400c1c04207007103c5010910301c000a036203003014010000c0c4242d980d600408464940a2542e0458582c902c8101c00500b0003418140c1c00a80001b5410201c015a4650544007108200c00d607582c1c00c001e512803680042410000e850041468000405003442900488029080d1800c0c410240c0d118402000b07a90401e852280141c000000001c2c00d06000700040280721001d0300b1041e4202541980d29601070b008082e154003c08001303113150f40e000c00d8180d4459018a00340340c5009028000c240248501071002e0007460511541b0380644c00640c2030b100c0d080502410110720040000c8030780e444402d00703000c0100703207400402400e40444c3c0030140404001c10000d142c1007400415940745032034504613080402e03aa8100031041e400e240340c20031400000701800d55450351440c0030303550000c01600c41d0b89004250108000c00060b0315921542500010708400f0313040d0369640c0e050210152110104aa2142c81880d0120005404442a0050900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 14935564 1250 14934314 14934317
    0x6010605160f06060e0c090a090603020306040209070e060a090f0503010606140903010605120105090f030c1027032d0509010c02010e10050406111501060c06020d020a030b011806 78
    0x6101210303a5665041400842d02036424548840d80498440040350807a40124040e003c1d1580d40d9141c2d501f4484551060380c001105285000001c0002d603c021030341c1540654101c0c1c90700000d5a510400791107038010b1000b00381d0040d1000c2071003484590019000000d444d0720005c032038801070380ea104150036a510303801110005400043c0100d49100404040c0a00080c000c00101c0e07c1c0da140c00c080b620700d141942d000400d82c1c0d1900107100b90034100303001c00b00c0ca42c00c0780c00c051454103100034003550341c80220241410240b0b41e20010110300304241003450364014080c1401c01c804125904008010010340011262814604008810000b00030030382040f21103207680f079160900300810019145c0510000c42603040c4003c1c0415018240c0c1e07080f403050b03010440b81e25000c3e00c680c20550010408007000ca0410312552007039880442a41c1c000c0c007581c0c1191000d14104030740ca041450004042e0080c40000c14005001140b02400c442d05030304044010102a6107112500c000825480403102e0f0724800c000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 14936814 1250 14935564 14935597
    0x21e0d03120e0619180209060d020301090213020307110712110d0204090b0709050405011a1b0d0c0209060d110405070c080f03010609080a110103023001060206010605 73
    0x80019005161040c003071102100000380d114a2090001c0c1060400c0300c0318030541c1d1401c104110458242c2c031519090505101030400f644d107050340810340c9440060082031092901240340d0003195425000080850303805400c1e0b4940e00018102030010b504256080c0e00480c180c0341c0d0301d0301602c200007240c4d401c54802c580524400c40883d25850300072030a030341445400c005043d09400150700c4a0003100c00755031007011140e1082c07810303001c0182140302a030003003441241003800400203254050224051602286030840d5102810020340c45680c89a500004076070007200d5050b850240c1022550804500954140c4243e13910314041200c80c0c41b01010052a050b0062090942c50600303a120f25441995070400e02c1080c2c00a13200c5080f6500b00241d441c04115002006004141d403150440300180308410080152004070f6407030001e0000d4002000341003640c081000007014150750844031900c4115a201001d202400d041b40d480400240034060140c07041c9000003901500c03e00c21180c1c4a440002c209 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 14938064 1250 14936814 14936839
    0x8070501050c0a0f030c1a0702100b010e060306010201090f120305070309050d0f05040f0308030114040e030a0309020f060d0507030e0304050a0501050904061e0303020f0604020a060e0a090507020307021e 89
    0x568130040e5160741901005a00d0500c00005000001a420300112901c940c0c1e80034601490300a00d04880c1300c03250719550b800c00d04002c119903040201103110b20070445801e5141d5440d071004034014502040007500c1e1512510b921414043c051a84100340740c8196014001d07603540c03190540c00e491203d400200320fa0f001c540340b030031458440c0881d520016114034245151030794814081c500174034550000e80e04607100000410842c0c0ca0000605c1e028007080d01d01344500d000f006d00481c0c8038000c2214a0051544034210001107540760391b845201034000074051501c581c01e13291801b005100840d912000310740f60002c49414a81c001045e24111640140040f05c5142000c004607070982201d0b41d250b407c20307100c00020840c90902405809104514595503206038a113041c000d00d0810305c0c5900e04c82a400120074880540c0752404130380d0a0f1026801d120b8820161003006c203080d28655401110305500d46428440e0b0190301000411103580219210a007442007004080b44050103990708a40c00600d07082075 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 14939314 1250 14938064 14938073
    0x6190501050103060b03040206090414070f020115081f020903011a0405060109031101030b120102030403020f0d030c090b09011808010c030b06030606040302040902011707080115030509070306021e0d020408070501050c0a 96
    0x500402c500074bc00032034100950000f03669041015129107011810204009000e580e092003a030a00c2c0c0c2403040d102c071001d0310b00749965454650141c50f01403103a041c48005d21005149404585002030050300800c244172034444500d13201d803040e0009a200341c2c14980810010b40c403e503000d0003600e800c81e2102c030785814a40d005500401c000c21005400162880b0503240d0034000b803010718400c0c2d01940241218a00120555007881c5080c0c0c880000d16140c28003480c0d1107036100d03950409850717504403032540d58964000180c0d1203200000ca10a44030107100c502017801c41064000403854000c2e03071005d010129104e0104a20380c081210a560481010b010400251400303400a50b0098010306115401c6250402c0f44404000115440c1010500103001000040d214091030000143d8074035017041a8140150303501d0711050248000760035070750003149113054a40100c0d50039200c2208030308200e40d50259420080c019422500c40c41000340110007000070a54081d03002c80d55000301d80801b805900d4086e07030341d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 14940564 1250 14939314 14939317
    0x14010e07050907181202030106050105030f010909020f1003060f0f05010c020906040e030d02071707020334080601050f0f0307060c06020f0708031501030605030d0c05030c06190501050103060b03040206 88
    0x618400c1107040035420000c820703400b00c950003170074400c18140e200c402103005040c03c1d40c0b0755600c410b040000030400c12000540540d0940e0554034034107404221243c9034000690b150b6507480100b036100b08410000c0f0705040d00b561040d801c550808003100c6003607643d14440340700910306100d95804107a030b86928500500c2c01e0169a40d00400040c80000c0c5240f103040744c5495900300d600c2d601c042581c0080e00301c3c00d00c20b00100116405158040c0186401c0c09580401d07101d50290100c0c95100402c0844102021001c0030b0001c150716a2444c000109940e4288583d036815080c8215030041703801030300b111083d060a060fa2400a0f00140040070868505203084503a1284024151030940d0301f0f201201010740c1c0580202213840c081c0301055203d050403210b400c03906074850a480d0500d403818030100b1240d02d0210303103600c5002d984c0c2080e4685241038240035056101d5200c42001500a50b001c001c480b03000d400c1e24500561312a003080100342c0e00e6000650031207850740203101e0a494240000740042c40c0c602c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 14941814 1250 14940564 14940571
    0x60c161502040b071b0b040f03020f010e0907030b0a080a0c06050a050c100204030b0a061503090201020f01050103030206090f0d080103060b130501060e0301150b030c030907080304080a14010e070509 87
    0x200189000d0740c40384910003076013005800300c1c0c0c03074614948031003021174a41c1e00d9500500b8820003a00d2501d0b107001c2082150300141d1000a000b002100c0030b05180b40e00516020801241c01b408200c528a040c0b00028004d002450312103210b40140300000c624000001612503203594429010280103080c0380c0b058945030840c0000320100102040074a940140a11081090240310312016864608519008130910402482c2040c503a24204042021040d40021250b084402e410002004039081c00100c0c10b000d41150703180215030810b4000401c140e40000d12502c0707000c02c403040d142030000c02c080907602e602c150f800e0140014100070052000c44d03160391104000c40300042c41c07e81114420420b6000f5030324264000000f00c1c256a2003034007035007000e000e003da191303d0010400844c0750608648807218080075110034260704000c80003c40124003041b039a0007601d181d404070f07a2203e0b43c81d01c00e941c7e1024080b41c111000078002a9007000080140a210728848064014089190408091024903100103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 14943064 1250 14941814 14941853
    0x50c070f05030c07080709050105100903060b010e0603091506010f0f08180d0206010602070501020a08040902030a021213030215090d030509010b060c07050406050f090109090203030403170309060c16 87
    0x2040700140b00b80d4200135180c0240801000b80400c40e192260788011a00168000c1d409014066404031030141d01040d03541c02d40e075020000040041e0700100403902da00f80c464003260054400001d00160703020008136144100010312411400780d40b08070046511603410a46900450307080485504e06600451070030303502000104034004020302e545c070792514207038400340c032800560400d00060115a03418031000c00030700000c0c001401580b8181ea5540002d2155100700290720381d001c8080b0312164415011642e070741000000382d5407141003454040da80b401c0500c1c4124050311079505000b006c80d00c0a414644034646007000741200b45850705080d809800001e040449035581c1c0c03282d1040c036989110141c914a1118030003001203a0810051000322616504002d100394891040030240b43d4541c03115506441440750302044800940c4003191039030180b500018214989500b9003a000c8000c200a18400d2941400302c0d0403940380c104240900307215018031030300080650f1450501241048c5104440b05208 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 14944314 1250 14943064 14943067
    0x1201050415091e0516020606040c0e01050304050102040302090c1c0501031101200706050d05010e09070302010c0501090503120402090601080c0d0911031006060908060c1b01020d05090d0f0201050c070f0503 90
    0x2005040780455a0445d0300103c03149640c240340b007001d6410400d0035404102541c003000328142680010303192820640d0f101d410042c001000900b001002c0d0140d400035503028003c881c3c9410401082c000300d070002c48403415502c030014801c0d4420011400344c54101d0750090560400080b801c001110760050301c403641d01d00e08500b11101071840000b0032250008090a903541c6441d034800b142e80b241683d1040e80304a10400749403080c000d0310304000c20300d00112907090900410045140c5844c502600545002030201e0001003601004e800d02281e03414031503442120803101d60350b43c050055074100001c0d40d030802d0411003070083e5991a0301359400048c005018160b1900e8400080000904d0310b07030602d420380c85082e00c0301001c10905070050040d0b005400504041d2940f0310303101d802c8102500034580a084001c2c20350781e5008000200717504890180d4070401c014011460498102ca44d111034500741c4100207542058080c032030074810320500b801858040065460720b000c0e0303240d40007081a20141602c49000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 14945564 1250 14944314 14944361
    0x203040305070203060a0615030605150705070f06020703061103040c0303110102090307090b030c1005160c080102070302010b1201060e01030807050304051306051e0303030f220602120105041509 85
    0xe00b006540c1c441ea11001010408a05105c10721524520f01c1007230500b4182889000e01969613100e1000c4100388841c11425113551080c01c00c0c5d46440b20b10382c0450403d400030000841c2d519800718049046da40982002e208901c1500c0e00346001c1d110031240a001c03c0b11502043c070029109218202c4c204080390005400c100343e400029003440c3c000d03030042c0d02817540c4003000941c81c00c003031000000e660003c9498000706441c0d007001411502c44e0f03c200c4d40c050040c10003d102000640c102d81800b40070303608021904d50407a860081d000341560035026100f082030030030120401d0414022001600e240710f903416103903441c650318103030030382c000020451301e0323000a100c00f04403601c45007204910450310400200d50146450305016007070850f030b50010803403e00e0864104082d02c00004803504a00e84038001c140540e2103038200c010886041020100d5490002c40020a00140da00a01200140410f0000c81b99a03284108003c641c520324101c0401c0000c22000c2217254021790160140b00002c100c0c265180300c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 14946814 1250 14945564 14945569
    0x2030a0f030615020a110406050303071515031b0e09030406030207060f1503060b04060b09010e0406030210020d0909050405190501152c0f01090c020307021009061e080a02030403050702 81
    0x140480d43c1c0740160b2003110441c007844292101c102e039441c001d407010840581000086a00c0380704541025105214228880306146015805480240c0c124680e01ca51140c4078074042e450f154904401c0c1d40304110b9840082074040006490301d018180300b000071454280341c268260080d40040e102035800b0750f034448441d000ca0245010766046040e4025903020030601314074101c0300700c1d041c0ca500b140c05145443e105110380007401c81160a29202400d00106240c1d00000042c050089030300002e4200051010f0460380d280c0024051920010700e40303450b40786a8548600c032045400403600a00386602c0382100600311880003000169550007400040703106a0b00d0040e90007080619031100c09501e140c82441320720242080e8090382d42d0100400141e00605000c1c445e18240e06041c000c1140c05980c40f141040841e008004a42c6050303170142c880041d05500783c80c081d2414007180b05850200305148010381c041841a0009259001c05480d141c040380c0343d6030b0f0f0300f0009410041c0200c083c40700403c10100981e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 14948064 1250 14946814 14946839
    0x9070e030715020c0a06020c0105030105010311070f060209100212090103020c0304081204090c030203100b0904020c100b01030c080103050307030f091710060506040b04030f0807020a0f03050705010c0302030a0f0306 94
    0x204943c009000b0403500d0810300450b0b00b110340c000303411034000c0d41160f001e580e03100301202e044171024600410f1550078640c240006109c0c0c400000e080301140381c01141000202d402800038110129801400c0340368844090f130701c540103d041088226420003074100c03550300a601500750185004116800c05480d10510340c0b0341030b0071b030500300d100c040040780400c403090080c00390031610002d0b4075040d41141415a21858044601d00400d840c072800450210b0042e02c07150705489819599508032481c50030244c000b03000510503028400d0001c0c0c10001550a01030080109904999204008600d804515242290300e05108a04041040074107440050b409046020005805600300e000d070048a062142c60000c030b48607540001e004600501080128404240070394080720781110a4002104c0c282c500424148038503080254882480343c004100c1c49400300c941002d0701e12580071190781e5910340b0010364030301519182c028010b038810094542014850001710bc110360312030030f02003120394561110031b906 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 14949314 1250 14948064 14948099
    0x70c051e06011401050702040b0112090602070c05040506010f030213050603041527020d02030102090405040503040f0915050415030203010e010209030c10050708030c16080301030201170609070e0307 87
    0xc0c010140c0e404041008280711290043c14000c0844441200410000e4498010f0f0803020348504c0d0798810a2075682d0040c08400801c0c072244100b00b00b80d030024600030f0002c1d0403004040d5116054001c011426040c14856240103180503121602c0340c004c05c1d0400c0f0007a5001191600398210300d440c000425868900c0a036008511071200c1e294104403c80f90070b42200c040c140380900903121404c9210ba10b00340341843d410304039015254510102214004603001e031040310800c607040703072601d41000140714002c03000e401601c1c0050b0060186d2903a0744644c0003a12002d040b41c0c4150f40c41c0c00000c00c4285020b83c00070540420700d42d901c03601c0c40e969400180c00c690346040703104402d03500007650801030311b018803489420140441d4007a400c5440c1e00b4005016000b0804003c0002c4400000f10b00c5500603241540d0b4100e0b0344009000700d0b803105140101c5107800c00c0c4000c07408103403030340700e84510a41c0c112819803040c60301802c94503566a030511300b1541e41d22003d8800d5054010008003180560310100b07508130 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 14950564 1250 14949314 14949343
    0xf03040f060903030c020d080c04120305040b030106050403030210050c03060402070609020d06061406040f09020c03040906080304030c12150b012001051e0f010902030a060503190201030e030a050d0203070c05 91
    0x17901541e01c1d001908240040e484001009100b50400c9002e811040a4a060741c06150001d00d503c4001e150036a290310598208030070054002c000095900d602c0002070003660310903402c5d114034002507602d020a80b2002e481c100040070f0284001607160130654003030041c1b039014107008941e0b00300741d0300420400c45900c141501e00d581c590b038041c410300c43c400300c04140b0110180c900c01c1c80c10b86003001076490040300b0b0090011079900020305501e01c000400c10b807400303400002c40401c00c0e03542d5102c100741c4d00da001c0e00c411140c80e480e00e003000403c5182090541c9140b500701890f5411032000d02260300061107200c0c1124140300d144100c1e030b00384840020614510415242c0001050b041c4505a01038080e4046c1c100d10a40055a08004100030400c1e00503045402074040542c07241c88074218000909180c0c1c2190b601481041030405c07401d01c214016101c41c5000ba00c0410042046680e6241c50b8401c51441001040f0b08001d071140c0e08074158000c40d400b40d0f540c0340070240050b196440d03604110683c100e004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 14951814 1250 14950564 14950571
    0x15010507062f0405010206040213110d050106120e0a0b060301110c0f101b08090a0213020315190302010c020402070b09060a0e0102070c0608071106090a03020c0f01050f03040f06090303 81
    0x5070707039403000303000982d01c10615101d0509041c0740c200002d5480c840100300a0242c0d4900000004040d843c0e000f4810803030464242580381d9000d6601c0c0d00040c20709100d0200017660031948032002c1c05103445513000709403600300541003010320f54813841040800601200e403d59601c50701e0305103101d10324001d0b0441c0031368500503001400011615902e0010b089001c40501d1340742215100c0d000000950303840440d11301341080703161507449407610790501c3c0a080c1c029400c00040c0991030112141640110300c00c04110307080300610301001052004400c1c01c50388a4a0600c822241403002d98001d49910707410520091016180400c181e44064441c001610307120700960201c3c06000c000c4541c1d01a01d02520041402142003804c241c03140503c1d05002c1c07164000b032120002c04101124401c50302141e00090b2942110340c54140545103e60b04c0a40100a500500400e05503854510f8058602c420002c030589d41d171401e1151841c1c541001c0d81c000b0300200c60349044100c115001412501810350b0381d034041e40313001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 14953064 1250 14951814 14951861
    0x90603050606030d0504030b0a09050319030c080601020607030b0d0602040b0c0706031a0907030e010e160b03010311040209120105010602030403031b02090406020913060b04050114030f1501050706 86
    0x5a2601c0c1e80a0061440303504500e0450f5015503000054400700c0b82c012900003110340380e1a10160044c1500c00c806003560100190904402c031800c180d202070804a507038204400548c510044a003000140d59007801600b01c2d0f0086807885109c0e41140d07044c030200401c80610000a591408101c0e40940d000d03400c55840441c20015080e428081c00c001420142018443c0901000c0c071803c960444920240c071a40120340460300b540c1c0f117075000300308410f4404000c001c422844005c1e0340d501c900080c0706014410001002103503484c89003040c1e034101d07544628071140900344001040084d400804005820100700944070041c808240074080c0203111a402469990707046040c01407140451803050010501018403680060711402e100e50350040d008000140c551084100107140004807800c0505c04506000700070901c130541e0001001115001d1700c0f040140c503450b5011140900040b146500700109290010b4000f44441e014400c405405140c494a042c0c129070340da5080b03031400103e0000003000070015 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 14954314 1250 14953064 14953073
    0x4020f01111e0d05040b070b1009020c0106051c1a0c070b0c0901020607030207030c0b1801020403060b0f010e030706050a02070306020a050a020c03010b0604270504050307050c0d020f01030905120301090603 90
    0x14081d00101c84d1030403520b81420440300341064442c183e0014400071b1a8030006140122640622010b403080400035076a414444200703038040e0240d0701400b84581c0d11303101061000c120010a505059500400030112503480544003190843e00400d00781d04980100304804c00200403c540c80d205004603c1c0054440240c10002840c00800600d5401858810820035000c2a000356404025a900c0f6480880035aa04801d9860301d10311744d400c841c225030000c1004000c2001942002c200c0900980c0d03c002030b889000011078800028001454054000003800d0000038400d50042600c20007500460700250303942e6503108203c1e0300c00e4a1103c006000442c0c0213051036410b0009401d50a0100c0080c03001400000000f5914170940c860003420940344100c10f059036000c13100d807090014000d8010005480c180c1081c81d1a036101c0e540441d040d02171a413540c503c41c41d01101603100c46401500f111654000840154020195020141d039984914a101d00e82c3c1e5918400441c083c150302000810724a14500d007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 14955564 1250 14954314 14954323
    0x80c0a050d23041509051504180902060a050d0209060403030903050f010c090512070902120402130c1d01020a02101e081b090a09060b03180604020904020f01111e 71
    0x140d031200d00000120b400c1c1003096a00075102982e440c080d511901c004450000c0c2c4040e2520f40c4801d410035054000503000c000007070b020f03008035550511104200341d18481e00f030040b10361010b0025441101031148450340c0340301d10043c0c01d80d200074502c01031410b010342001840c940c01c03a51086002401c1d0803010b204200c030600440d00310b41c1994009001441d05100050060b07401401400c3c0038400f0214201074491082045034024a000701003103544c0c400d40a949440310600f2203003603000d408003c41e0007170801d2003442615440201399403052020ba416084050b084654008114111712440d554138001d40c0d140c0c24004d4441a04d500c80e003014410101106c40d5510703000340700000380040601000f124100d501191307480380202e00b80069507000307444005200200b4079080b10784614684940414443e100a000b035000755105a081454a4003030188155103000486000303400c10320001c0818010700b000e0034000284041414181d260031124000b03586040404201600c0101070900030150340e900511 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 14956814 1250 14955564 14955587
    0x90506070908010e0d0e010210050103080c010c02030a12050406020403050d0c02030105090d1409010c05070603020c0c0901050d020103050603010b03030d0209090906040203070320090109090606050604140904080c0a050d 96
    0x2440220803a41d107541d103034215410b0750001c1c4070000079006d006a2003400490020f101c0900c0410403541c50b401c183c44075411030b14541c2040d40c03900032080041400002030301d149600651303071440003107400c50b0140c2c068003000e48100c1e0025028800400099010300200841c0c4520340d44e61000c0d28070900405081d01c0c07029105c550607400c144c5040c030b07604e58851040b60076102080d038900d91b10380c485001202c004014000c00f5145008144003c605207906400910104050004440c4c0c3c0503d408108083c02c6802e1150640c010b581c1b038080001540a600081d0b4040c2000300000342c50100500480d0a41d0701c10340055030840d50010311410149401c44200f500031060070000c201a250503070110303581c0c41d103901010380794820320314849001c402242040792500704084d00001080d65903810703d8000d000219000c4034a02e0a029000c50241090341c05e5600301e4201d15170900e14a0b022405000d00e600020f0800e495440302001415001001040a8043c481c41400105495480410000c01180010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 14958064 1250 14956814 14956829
    0x20c030a0215010503030405012319020f070e06131104180e0a1e1b120201080702010e10020c07050402032a0c0d050d0e0601090c02010b0f060415120905060709 70
    0x2c00140400e88001082d134040d07960a0a000008940b2041c1c05602c25149600d03030090703c84005141701c0207030416805100d580d4400d0302142c20300c403902440c150700e51901d0b000724810840304034000f07002c5182c8005000b1742d550000030009100c418004c0081c1d80350380b082e04140594003141c1148291802076100d502441100b2a028068101081e5902c08036181c10f203006009015040306a1014001000d040780105032010042c10b112558807a11100b605040740750036030104488000150b04603006000e001c10280c00d040242500003172a1440800039008480d403070490b44030303142021800c1e440f5880154020705504503101c44250b25505040c02c0c041d003000130210804418095400c001e000060b9159941c2d40c0390610340d841d19404035079200100740e945002a551f2150000008621138035034803507422500c050f8002d001c00c8000005111003859500107140d0020f100b000b042004500c2c0e51b03101c007143c107030781e01c1e000318030100c10761411041d9034442c0710075a1144c11540c1800700280d04200014020302d80c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 14959314 1250 14958064 14958103
    0x1a03010c08091b100c0c120501091103011505060c0a051501080d090f0302010e0f060d090204050907060903080d02131518050603040b06040608010f150f08030301060e03010b04020c030a02 82
    0x4030080f8000c4c0c0e4100c02144140030181c914002086018040340003e13049908229442d00da044c00e0260107005400d000352120701ca040211481400d060241d030000307605400010207003916103000d11005a120710198a1a40a00705190b00040d00c00d110756080d851100c0688591541800d8001c0e05004a506440c01409002c42c02001b024450301001412a902402c102c049581c2c00d4005c00c50781d8040207402540404c0000703001c0200075641c0e1200b000a40281e8082180380e0310980d5559640d0b0040c0510004904684010000180110300402d04c04100f110054180343d10a10142408030254010510010440710b565602a61280d0049114200b40b5100d411892400010816074880030304068148030f1100c00044103526035401c030100401e2000000c002c1e5158585965000f000d429000d50f0074009880c4002424204002c46541500d0002000c0c51460346092029582c8203265503070f007500355480e4421140c65503a244050000d20b1413507405940d4030300d65440c0003818010b501c5403110a8014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 14960564 1250 14959314 14959363
    0x615050a1b02030705040c05180a0b070212010b09010617070302030f130f2a120305090111010b031501090c020105040c060309061503061d0307050a061a03010c0809 72
    0x10710803401c400c141e030964240c01c00c00c1d501d03001003410b000d41a04550b422500307184c6102045c507440002031880080d401c0c0c4405410515400300701018045106881c0715000c10b00030103000d407074a09400c00c10030051000005001d045070000c0782250b54240d01c0f030000b00b07036000d00d502070300c610800354294030401c1454118550700d00b407892400b403004040c121a000b0440031121400304104400e200b0102d9400c103102000e01a000305801c01410680964441c4c1001c031200002000c3c00d1240350141c590307605450321414a0040d00044440300344842c00b0300c69a64994040302441e480a0200000011026960108940c14070001c0f030b040d00c43c0700c5040c0045a26100400c40442c590f89222001c1d55803c4c41c01050b50b0300e49003403645c054408100c01445142100000000304599a031000190800c2d28255104940544100c19180e024281015013203800c016030301400a00307590f2040b0304188009070300302c41c90044440407908484134051840c011500503021b1200c803038010010551180d4508a61480d00345 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 14961814 1250 14960564 14960567
    0x40302060408030405030c070e01080d02030306030d0c1b0308030601170f0406020a0509040204291e071406390d0c0c080c06040605010f08060402010e220615050a 71
    0x820040010b04075100100c042020030009004075150480403070100c8032460784810b414040d0300004c1c46041007074130030342546c40300407400030046d20302c50300000f80581400c222004043d210f138a483c0100321019201545201c1000d80901400304c00313180100003250b140d01c0e0180000d4552985502c000d18440e1010040291b02c0340c0144559a00c84d602400c00760326030240c010142c446010300c1480030317402400030801184410b03100b004030f40304044c0390080740c0d0134160500a903031103031103880c41d9034611064005134086180c107280f005022003445003002c10448203400c2ea145090078000d0b5280c0a1880340000c40e20070034002c450800388210341d0055503030144015188051064421301491a013000c0e180c2d100122210300400f07004403029000004075584043c142c3c141a01d8060032101140d40c1f52074000081540e412032181c6505440c038400c02080d2980715500150b6100f6408404158091825801a44070401050392100080a11800407e145081050750f04139103101d100c00108000c005c0c80b1008006 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 14963064 1250 14961814 14961823
    0x9050a060f08060417090a031b09020301050d1101090918060c02030322050f12030106030c0f17060a05060d0905010b030c01090e09070b0a0816030c0210230103210305040302 76
    0x980c44016170700c850703201c05c414494a0068200b0302e503000342c1c004400414041002c2400d210180110101070200c0c0d00c17880703c0e104900003130140e941c000140c0b20b40300740066005c0541d405ea5102c1410005009640d4559900658480742d1700c102c6104400034110040040d40d001d01a496181d138000b80d8110301d0100441c400700201c034180120260206105401482028080c0c0d02d8051541015140c0340c411131000414194001e00c1880d0001c0d1800120540305481100f07810003024060b580c1a0340c0040c0c0100d0140c0b41040600400c0c7c0c040c591010000b400d54a40c40100600d10400d040880c8140b0142061400c68004041c2c95001e0303080340c0c25600e107136a8401c2070070041d900704400d0242551103d40240e4607101c01e64220381803003c1c000603004041d81d0041c40a030702c41c0b003c0340d040602250784410110280d0300c0500c042e0340964040680030320442c00b9030300040704403900d0308556440842921140c4203124003c0c0d00503503040d02581c070010f4528021070149000c0814030700701030080f0f04096800a544 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 14964314 1250 14963064 14963071
    0xf0b01170118020d0e060108060f070c03020304030201121b020f0f0105010302130518011503020f030d0c03050307020a0c0e0604060501140a0305070c02030d0801060e0a0b0d020705030906030109050a060f0806 91
    0x2c02e03800200c1c40d109030000ea105a06000d0160202d80444d0b07101c070b5100c0d60319401580d841408403e1540020a5288550b244010351907240c0d0186080529660042da50324401c0d40040840340d840712000b5022010b6501203000f1f101990f40102241e18109045038249031140c5c000030456410b000060000d40c44048500001c00208040001d243c2e468a0524001c2502941c40c0704040d401c002445812034182d05a2505880c000c40d030b0803040b05440003c140c1e40d41d0b071400700000441c5004450b540868044d00141d9030041c800e005036040341410b90384c0c07080d0020307080d0402800d08080c80203205030703420103200e00b40c050002070800412111400142c4541030191062140402d0344440c0003c50701303889803108109650f8050210b801d00400000050490b60090141c0070004800b01c24030a403924162080348100c0d8000720200749040b1800c00e00303d01135404a10261101c2c80104402403031074903a10300941c020718461100062034180b2100082c256010740d803000c00f4000c5800d0003407200d1540415103070340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 14965564 1250 14964314 14964359
    0x907110a080c0f0307080309120c151008030408070914011a0d0b0603010e0402040509060705160807120908070f030c060f0905040e030a030b0d030e010c06020d0f0b011701 75
    0x440b4070751040c400340b51410040041606020214001c000c0050f10f00185014100c05400d88400188140032081140241d044d42d03200d5030b00c0a4000c0c40e010514043e607a41101c2034841003541c0c680c580c0f0704036280d80c0c000d03400b4071000d074000381081240c0429441641d03204180301c0c04020155140200b40240074040c0c1541d000b600500142c810a500050360009014403400b40c01c2039180e47e540c0e00c010108c12000c07103042e8050b41c10080024913030350000c106c507071003200e603503c0c0c0c0e600745407141c1d401c0c0718204041d031403c80301210208949030100d80c05c000744903403036482e40ea00d422001d82407440645c01c14036240d002101d0f100000d2410b0000a6648039034600340c03140d62604105030094640d00b2900101264020b40d0854034007115600c0f51032022008018800040e102409180c1c021424070400164107100903000420f5a0f04c0000990b104a000e203080301e01a00c0e0140c1040d903c8118101241c1c04041c0c14207003207990b40c030018100c1d600490040d0b1400081d4504c00e00540c500b0142919126007118082c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 14966814 1250 14965564 14965567
    0x10903030f05040504050a0b03010c080105010816021009061d06070504030b090109020d03020304060f081303030b01020a05060a0501051302032404020d020301030525060c0204110412110907110a08 86
    0x4041c10701c030310151401042c0c010001d200c1c03400c080c6080401410b078545024002c1d403c02c09040000c0b030150f90014100c80c81a92044c403290b845030002860414500701c00d600b103002d0384d040c0c90318924403405400800ea01a000c001001181240e582c4486100701140c1c40c002e40001c4c04021040d50008141c0301180d03000420a80282c3ea03085125004140084c00203502283c0384100c80e060641c004081c00995040c2e0b100c040020749290810b40b0504400c5520403041d41b00741e0190000a8460b410507840010180100d034903400c00340d0b40720750030904119440d000040e5120300403c41c926081c0e8901200038644078003103255050480c020b520072507142214403900c0c0380541205040d9101c550480d1000f10010000319125612840e009442d04101118414000d03403072202c00c440c4929503c0e80c4821201c254a66a403004102d80c02d00001d850f006d180446d04000a00c8001500c100c4e00c944444500e03c981c844084c1e100d840390410800360005424482080720100c42c40186070000203202d030195400c02e0009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 14968064 1250 14966814 14966837
    0xa2907020a0806090d120908041404140a05041707050303060d05070803180f0301020f0a030c051b03091008011a0306030715020f010b0402071106030a060305030f0705061501090303 79
    0x2480c054480d030b0005450b40300f010b0401140c410085051505080740c0c0e9118482003a1049448040d80c40c9540090302c07903081044208452882602040c0141002a00204002c00010000e06070258102d0f80d030030906440c0e2003000100a45031911000d000704104050b070411079a80c4507265a03000082c01d6074000c0c10740000250512808000701c40041c95138508503540c070964087c00130861b449010086015144075506c030100741c5018025075142841143d06036080c0103851030220042c0050281d4581406030402c914482c00151100100c094201c0400540c0d0302e5464005020402c182000369004010384000144025145c89151640300d00c040e055181d242d445080003c1d08014440d0f00000384174030701c07070416103145030007042010a404c8140c0003000b1681803003051205a01c94100000d066401c4882510790ba17140000c007860f0401c14401002404a840b69202d91075540190810b22a410300843d0050400c03804000081d44110303500d42c14a2119544400640700c000b15000c01018843d054008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 14969314 1250 14968064 14968069
    0x90b03070905091b0a030203032b0f020301030203061803030a0902060904091110090308041203020a0614150307050312090d0b0106051e03060f010f0203070503040e060a290702 77
    0x620094041030004120900b8000f10f681d40d101002446035803184100c42e1282085d1a00a0b00d00d01220b40141c05140381805c036084003d80854800500701d220050010b415501c0200e82c4110010744840340e00040c0e681d4107500426241c244000c0a01d40303e80150005081c0503480401903d801000b404404251403601d803001076858000d502509400078500448072091015000101c0090001652914106031049074100caa0b0300b06404050649182040300b04a03603034001840c2c103000c0380079205951200d04280d481c441030711480901c42070100340b030300c050002e0000c01244444510808800a1241516203000f003910350042c5006a1111940030501c10a5a2241007410700d40e250701c201c17020260b41e161080600385800c90385900318a61a003082150200504008980c02000c009044210644401c030044400f81101c40c00c20045010601c0703d0000224200042c1c0081d1400802d0200c4034a4400140803008100d540b0040780c1449605481004034610040c0324513007032000c080ca0303076034801da0f002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 14970564 1250 14969314 14969323
    0x3110105040e0c040608060613120c050301020304050f010c170f1302030a050102030712050105090f0702070906060c060b0103090b0f040804030f06020c010e0f10020706060509010308040602010605011701090b03 92
    0x2110b01c84004070420402107007040c800910595060b44c42e030010300e4582e07200703010290140d003a0f1840700e400b9075001400301000c5086800f004c1ca100e000100511a2101c0129003681c2054404941039408440e90490514003030045510120305854403440046010b0401c250f2210040c080c2264405690081a0580001d101c2190b0480e009402c0740c09a102510b0700c41e00039401142e03d20000388100102080305201c40c041e040c100c4200074080c02580e124107401008162010300010254400c0f080e002640200f207004602c002c20007900c40991880f800d003000400d42e50007411445c101407510381c400c40041c54111041d1b0300405d200326200d00c240d565240c4450031348504c1c0c1014000e4030741280c0c80000c00406800500194007164003e1000e8030006242da982ca0040c4800a6000c1e0047e06545200c101164050180305008080120384155500d001c0742c041304080c1c00030b9440b04000181444040c0d024052100100300a10f07280320500c0000e030402e203000b103040c001c44040c8d0b0740722044000150750400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 14971814 1250 14970564 14970569
    0xd09060813050304060906080a050408030f1509100e010b0322050307050106090603140109030806040b03031909031209140d060e060a0204050a0905160f0c150f0e0102090102070311010504 82
    0x281140d959544504001e81b0340b60032840f9080004080100113407081c4941d0013202d01880e48000000d04680300c00610540e10f100080285001c0d0018031036042081c0e0720b00c0e14030750081040107070087d4440d04001c5044100c00d0143c000460811741041800040c641000740000e01504104c18403040e10f03c24500141035110380d22000c2c00643c208000401c00110a610610840c2c1c03240b031489503a8103d00004500340d50003600c1c0600410008000940141000d030040b220142c5c0050649280c594980200c0b840035002da000c803070025160810600420403524078201c004d010301c1c203050b09030130301d000117403201c02001d00342140c010bc1b282c541801c104601604410102c5542e20b05540441c646503021074000e4126120301481141c9080c070005148003d07204840c0510b02c00601c4018909982005407100046102c20608012410f000240440c4500302c500d01e2004010308042085100c901d513450a0f2012034880c2001c691040040c003a06a030002040c808803944111101400b060301401030783d0364090380c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 14973064 1250 14971814 14971823
    0x21302040801020d0e0a11010302030703020f040806070f08010e15060409050a051014010203030f0c040e09031306030b0d03080a0e100e0d020c01090b180d050307050f0d09060813 78
    0x1040c04501d500040d000380912450600e401c000c03880400c40959510b80f00e242c005800640b28121f07001e8554070030b80003107078000345600700949007120201c0142d0b80c3c0e60003a07008801e250095401c0c040744552040c84040450346c2072030480c1143d414a048020460340141c90a0307000b00440c4455992900c074602964004c140b8894100050701e84103141c54080c00382220280781245424102140c2482c4904c141250b010040e401542195a000d811580c2c07000090014907a0720820301000035100365a0303071310602c03400440c0c0c051900c90f1440081007a03007814640060081c1030900d000e010041c0c80c0c12001d00045500f40c600b10304252141240030300100b014071000c88246c0115400c04a5040880d0888139030341310345400729000901000340c1240c030f80d200c15007003600103070150740c0030041c4241c20400340c56013a1102031060b08400242e0001502c002d006134007203c464002184201c00e0147c18420600003020803c090a82441541001000041c40d401507000380007400000c640101405540e194055500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 14974314 1250 14973064 14973067
    0x5120324150c01090510050c040608040c08030f121b0a0c06061a040608010b030105010905060a0e060a030501080606040912110c100305160c0302120901020a020a031410020309030304030c021302 85
    0x580b050b018001d149030075034552003400c03005102603945104103031140506070851410182007840c00c58050318090004d4400000c2a6800f040000b000d0009228050b0543c1c1c10391354554100c41d07042c1c5a41001405040010b600c0ba101c0b5403200314420803113500c2800d074500700270740350b81d11320b040c1c0300400707968228680c54444840c240301060784ca54010802e88009845c2c000070f42c0c4e80c8480c1c030070862009000d40da00007040c4010400250030140c002d402c2c40c40c03036820078450071126800410119000401e800c400a41c031a130040158980921110f5003107078040d20144a9008941c0300c5000108492007440d04010b0180807040c1340d4141403000c0c200c07000004040c40c00b0552011001005080240e80300041d48400000003801d031800781842903c0154990041c0c9034101184071003404603001249018150b0181e0420030380142e44140842000d14800e4180188018082d44c805107840094000300c0c100034810424410b404070b0000583c0c0d4419414030305241d54050502c00300d0840c0c800000c001c4603d500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 14975564 1250 14974314 14974327
    0x207020a030605130506101424070f05010c0206071e080402060f0d020d0f05060108100303140418060305010c03020a05090907020106080a030c02030d0509060d0b01020106120503070512032415 84
    0xc885004000708c3d062090b4a0345125040800c01c4030b00c000c88032007865000c4409266003d1240d40001070415240074488600607140c19445003425900501c14400050b0000780030802d0058000400a00c00c004101110310010280600134008800c003500280c40f511000c1034400880211508036605800c4d00320065440c1c60314110300d580a0411542c07000c00d540d0800d000540554410b0054521030502050600f0340503240d6101030301d4502c040d0100e48045c071410072001c2555051382ea520303c1300d060403030000036001c1d156003002c9003140c0340d4490040c10580100500c0e01601d83c0728090720401d80044442e6034080c1c440794000da006040319480346030359004a4a100c03090640203244901003c1c0250b0a80b259803004140854203445103c1e14a94040030500c01002000c0b11640854034125040c000050080e859056020555843c04d00845041d0310014118003003103418018801e60b60300b200c07a10350031418030106040d03c541101158840100202c680c01c40300d5910b00c007140c00b0640c0390a0b006075a558 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 14976814 1250 14975564 14975581
    0x5030709060302041a0306010303050906120103050a02090901110a2d05031f0e0a0b01090b030a020c071502070506031e040c081b01020309010c050a020402030f16030207020a030605130506 82
    0x4035102c16442185000200c811210019107100061440203019244580c219601510140c000002450300304034240102a811403071421110b0107075000f030004000d07000e5144100210b8100040110311070303904082d04d8501c070b20f6611003941d0981c00b403800e001c14011443d001960340b5501141c02c00e4030107200d00d00744040e180e4000d0029030180c0d0441307180301d031803811424407503a0254192003200c0c0300c1d009080011b000c1c49441e50001030300340030514040782c0e150395407400c00b0411380003038407094411035000400e605955410800c007002884000c003003000e01900f5440103910f400c081d20406005410020001d040110618040302e440e02c81c000e40000c45007081d0074020f02004441c042c10449211304041d480c280c00c085500c082c4810070503402140307032a401200440d1116000801201c02e842050041c030016074a50018500c078000709642c400183c900700c1417100d110b540c850300d07034814984104030440150f202e44035143c064035003201011034162540310149088001c0284040c1140c01507100b880641e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 14978064 1250 14976814 14976821
    0x6150e311a1008010b07062703020f07060c0f0b0403020708010f020909090307020a0302040b01030609050408030f011508040b07050702030f0601030203010609060509011203050c1e120316081005030709 88
    0x107050a40c0c0c080c6000304580c900b80c645802c02c0c0a0000201000c0c40a00001202a084100139001d400c03460145000b0b00d45100280b0340b59158201c0240c1c0018601c0790b540c100410400c001081c1d203281c50075207a42142c91385240c404036102e000c3c0c440d007088400501410700810012008211880c000c101411f03103000442c00940110500c58410305001c404188400400011380303126640040400d851503245608210090503541092414185c07503d0380025403610504c1800c1c0b1413802180340503501d280080100400c2d000503004840b1a01018041110b031a50103e841d507401584008030700241c1e218040142c0300340c051141c000354544030340d01d03003840da4290100d8428100ca1095009020007915890b860045e1b1b0030600955402102140c0104982c0218201510b001030207414428641501c482c0020300f403000714004003800001c07440da229602c1801f00030601801000107090307421414584034a056107150800c014040054010104401446640c0030000420380242100c00281d0350703c0c9000080c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 14979314 1250 14978064 14978111
    0xe01030606030e0316020112020706020304050d030203010617070c0221010501050102030306060d0f0f0608280201050a0309050c03060108150c07030c1214030a06150e31 74
    0xa0800000054442c0a4040c018448203004003071401d1176540e0148a001c5566541d059040041c06003000c00e814115100905e6001c0c051400503990385000d00700a07103061040c0990a08040c41080100b00041d4402c3c20388051030f6043c0384070710158a84490440e000302140801139400311001803455542c00c075403422186140c800d4402480b07182e0f0391303c0059072280030484000360000002c001c02c00302050b41e07501000b80850b075810009411048011240c080b00c4c40c58100a149034468801c040b4000c0004c032124070121601400b015420342c403580020110701803141500b06050700d50320600304103c0107011907601c024000d01101c91660b500c1800c00d40d40c000c1c000e111407105c0444804905030040510480e51003136010b031154008001c81da510380c4101c0038556070b15000c004a40000d5900e81204078001c2d40107451510303010070010f040c038114821b121054079a51040c0024401441203546404940858030050480f01005581c1094069601e41082e11001c150583ca044201802c0c2c07502c026042c1d10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 14980564 1250 14979314 14979317
    0x70b0d1407030c090504020c07170a020306090c0d060b04021209010203100b040812030903040f1410030b0a05100201020904020c060f160509040f0207020306040c090f150e06010207030c060e01 84
    0x1515180ca01c016412188000909000a02d141c0760910031400c2c20b400030400c0700c58810456040d10342c0c804404a189005102c0b81c412500220031240039441d0801030301d50401c00c10000383c4040303540e44000030342c00315032107074028012034403000440200d0f9107507419540816254100b00c40203140c00d1800e02c2c001e50044403441c0f04600e101501140300505403055a09494074800100010768000320764002d1900001c100d903100d88820000410b4032503180d0030b0440148135007002c4101c00401d10040203141d18142c24104109854404d0008060b5a001c840004440c0d05a9042c580c0100700c3c8002ca001e803241c44885034101d800000c81c0c030348901c40060024800c15003811903c403079031595580b8034848002001d031a1b00094007407122921030310342a4080c4182c000740c07010041c1f4015841d40840c0c2000c4e1700319010b03210084c00a80410214003580140d0388800b0340c00804200c1040c0e22404c40101c00498082c1d0507941c440b400008949034000c0020901440c2c0110b40e9500007a51104c00174030081d14a83c1e03060 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 14981814 1250 14980564 14980601
    0x5160f020910181a0607060f0501060f0c03030b0109051c050c0111030d05060d0c09020a080610020307060902060903070e01080c0607020d020603040314310b04050105030405070b0d 79
    0x5400010868030760082e03c003e40b9008010f29004080680501070f4850a001941001c280341d0000e0707a6a00000c3c40c91520880c8042441005000c03103404403941613200f4001d1101600d01024000e9010096a000607810704000503030162000048440051503046180c00c503001400d494048900701c049490300900c6202241c0341c1011920044420685129003070110783e200388a0301e01d442686400190780644054030000f031400c1140c0300c603800002183c0c00105607d900040401510790b01040d807907405071060327406ca0102540124003e650b0b11900002602c0d00d9614507030581150743c3d003811a000c0c1c92005080303a08040d140c0044101c0701c03d013841644150300c50442c0b0013113039041c940f05031054142c0050140015400540a022560744000c20442c00c0000d546c00c0c0c3e011000185001d01642c01e00c10700040b0002100f800644412066000140d44102d1100b100300000341c003400450b41518020310700b02d5100e031218548145860708580250f80c3d000c0000c2800340c4081450391240c01c1c0307540c034814000e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 14983064 1250 14981814 14981821
    0xb04060603020c010e12192303040b0601080103020a1a13030b06013e0102090a030308070207050102060f0c0a0c0501020706090201030b090f060402090f04150806010b040b0a0f05160f0209 82
    0x41d903038105080c1b200360710710050100c410800c280c240061104503290810f100f103440ba002c0b040c420b03000c0358011142d2081c0040144401d00c40b1030a1f50350751020b800c1c2410072107035045800095414a9030320809164440d81011088201008001ea0306a60400e03010440090b46030b04c5c02004005084501e1030000350140034510485220b03504140104502103001e4a4440c5250f41d005904074291014418643d0200f24004807502e50000400c01140682d6545c1c00c58141400000e08003400d95100f90704560144080c0f20005400072149900840c2e4444855034a1284602c1601e00c1c54281c2e201904952000c500c4100340512074000e410301c14400d80c3c040018a82600030002110000e80d41c00c4075413001c400c0054810f062a42c01000381744002002c4001940703c0d040010f042e6001d860010044005401c0c0800004100708011400351a0301802641050300300441030032507008542d1242c2c01c104031155503c02c400c0c041d0046802483c080c68075800607215504254032a016107050407801003543c0b0001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 14984314 1250 14983064 14983091
    0xf0105090703080406030f02041d0103050c040903020c0409020d020d0503040503011b0e091b0d0204030204051303020a03080703021207030b0a2304090204060806010611071d040f05010b04060603020c01 88
    0x1e4042d2544a40b1040c105400d0440440003040151964001140d0030003001c145240d18041c4c0420701d4402c074070881c6541d81507182c441d0910f820144020b024904040c440d00001e074000c212004c1c800800e03030700020394500340d00009010010308000650000c10030782010040c0030003c4003d00070781c0c80c180c0c002c0c030103240c070032150610b8407402c41001030002c2d00d120104011440c140100907005101e030761068650103504640e5450552004100480d215070010b4200110b0a06018055104030710b0720b00d900180c0c59580300079441d41302c2d0850007002c00c081d83c00024100383c0079605980841c06181c2c0101414503044c1405001444440003040c8552008d81c40040c807000c892045900f00c0980c1d42c0e6810390065048103010190601140880e44191141d4001c80e00c0c1e2400c200c941e0003440c00d0b035113441104030094602414000c2d00c3c3c02c01183c0451101400c42c5c250010100182c12507401054103a402d0711906180b4010403500c0c05660780203080c5280000d81030ba2640142c070b40354525100802ca5142441007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 14985564 1250 14984314 14984323
    0x3120c040612050604060812090316030804030308090a05030a0908060603070b0409020d140403090501110a081903090b0103030806010201060e0112170c070e10050105070201210902120f010509 84
    0x81c00c00142c88501280d607080340360f800003a00000b004c1d0001c11015211010303181810448400c0303640e110004900c40c5110301d0108411a11100c400c2800c0c4201070542d2640c842911440c003000d000d2020360008583c034450704200b22001c4503000000d603611102e4034800284111028802c0010520030708005c142d61389030114554040301c44407180300c1d192510b03020700e18010f0b4000b541c10003499503031100308075214a0210441351143d0302c255101c04006040800242519520181c48105070380000d407207100103a50b40d001c945040c850720025198143d680c0c0300440141ca520180106525014070000082541000d441401076000340c000317103c90760321080710004400342440340c04000c5007900c0c0d014000c01c501c0d480404420158020b010b2419600384c412914080043d8040001800640c0030020448040506030014000900c0c140d4980000754000030302c01d080ca4180034149265000100140d40302c6584041900d0b98007616010b480010520b2164850141d4100d05c5603a508050000304150300128 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 14986814 1250 14985564 14985569
    0x5030d06051f210207051c0c0c21050102270111150402040e06070c020a09060501080f1032040902061b010f090809010e0301051003021c080c03120c04 66
    0x1c02d804000350500b0111200d180d407103680241a4a840c40f0207500d40c0142c00101000d9010302e004081500c0d000e0128540100c0c0004e0800c00c01800d0140348000038800000c2e030045030380d07000c143c4003c00d0480fa619103a403441d4401c0107015601c006106a02194806280740c02103c0700d481c0072503040841001075070012012030a604850704030352031918480355681141500640060030004801002c1004146480e80030344110001c1510010b203a011860680440c47c05402000828880507183c2800a401ca400103001e21044515040000c0c14240805180000802400010130444819031300d010500c4150617100b60202d411406920710070341014020720480da40d028102c0b07490445c032030350110101d42103001981543e5407601502507400080c3c0c000c941c24113019070b01075580c4001c000005084088031071801c5000b13905250800046540c41519003003180c1c0c060355196200c10441d488a81c0201804100804046010541141402c8004090f186e451b01c90021003d01da161164034002601642c0f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 14988064 1250 14986814 14986849
    0xd03030b0306010f0524090604120c08070b031305100204090603140102030106140f070f03050a021006050f01120f0203010e01050306070306080a020103180b0103030305150406080c1203070602030405030d0605 91
    0x1c0c0103032100c0f680f6003a05041c2806c4880e464070305117102c82e00040c41e558029802061400c1004c2041400d002d00b60036280024407240004291261801c00090000e000080410741000701c041204d2041c4101480000b5641c07201f071b2801c55880c0c0d25842e00900510307041c0030564501200c3d4548055400c8140300b00c038141c1f0460b0f1650500609040f410f102580e010203103407922070100b4443d00300001d400d1407002d48828070a40340c1544645007120024a0500340c107001200a50a01c5400c10183d00c0c1d100640380049020310b0050307182d07944481580e001e00705030844083c0c0c481c800000042e00a00340d0350b40300c0c103a4904a013074480c5601c1f0300404805407011805410095009010410f00540c020350066003080c0404881000c02e04041d200c5841c1d03043d0991064000c20740303035010040004188242104404c908a030104585810031501a50740e48105c0d129a0095001440034803510b5010001e03192788651007802036650785054030b4129100d400284842030044d04001022405161a000c04080442c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 14989314 1250 14988064 14988079
    0xc090501090503070b07020d080a0302040e0c07020a0611010212090706030e0303090601180902030a03020c0102011506050d09060e03040f0603050703020f160303020c150402100e060a14090d03030b0306010f05 91
    0xc02c903135400320380d100382007ca1f4410400c030030003c00100020007410080019071001a1903900c2c011074514104401070000440f8641000754100580e1202081020b907a028601710a0341d1003240e00841c02482481c003081c241e00c02c03c104125110308d001944d0425105a40d50070f000c420f1110100580d2808165003414a80c1c10860043c041c0c641c0350441d01500707010a610100f0840303480d80110381441f090107010b50060704964541401035809004a028650400410110071131034504004d00c0c034050b840108110070f4850400301d06020789a00b020011502c400f003500c3d40d40356206441380440403648075150200f81003100041d0745030301a2080d104843d071403007062031800222030400480e01da8004021800d05509014403038544004001c04890494950003105490616004114001c80e00c0e800701c40803c95503c403480751a480d5002a203c4005082c20240401400d206407410140240011141c105035130002c20014154140c000261000003a403c0c4ca0050340c035030788000b4203200e490090681080b40d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 14990564 1250 14989314 14989319
    0x1090e010b09061201031b0b030603030403030804080405030708030301090c05090603070c020a030512070203060604050403020a020d060e030304153e040b0408030c0d020303040506060108040f0203010f0c09050109050307 96
    0x9903070003040742c40d9008004610303014200b0386101080b507007070704240d071003560403900c42c501c1c4d58402603240c002e002c02401030f90862400f00c0000f5520312840c0001402c1200350030200b41080040401c0c1c40140070000c0079240050344428840c0d6880e0070900c00c5800c41030a200107441014000c604a490000000c0c0c081032039a51115820b0780c4da01380c003c0c0d0480e082101240004080340d000d000f12035840100e0011a03607100164010549801c5002c1c0c43e07184520f28010038080004c0e00020050f07801c03541900c0107891881c4c5414410000d0040e18000ca0030b90100104100403c000054034040c0c007101480d04204640c8846a400c0d0300c3e01124001d0003c414050080d05400c0664403002d00a2500c0b80e04001d1420362180d0f403c075543d030044e42c01610180d0000c549a584050140310056101c00c007840114210318041e210169180805400c0b5414856407002040038000c25201e08041c15401600070712407007108040786002490b0903440000003030000c59001c5003940c40349550904491006005000da42e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 14991814 1250 14990564 14990579
    0x10e010e01020f07060f03060501020304140108180601080d031a0a030201050c030912010c080f040312050606040905070804140a0512091c0b0a0b0d0f0308270109050c01090e01 77
    0x510003030026040d8824956003550009041020300b000d00866500c6200021171003a000e010f4641d20340000d41503400c10b12091000400d000d0b06403600304400d01e42410603496450b030b07190180f0002010310207d40120390000c22010700014051807414030a0b6410424401060f03040004403e1030320b00386601003403010703041001d58072582c0503040300081c0d04141d074646084200001d1400403691039812950b5150003500c00d8054110303c2d01503020340e102541400504d803981c0c00800030030070710018005659a510102d0302c9a1105025103014181703910301002103080070b800140c0801812541103884544150200300070bc000814a140c010342e20000074a05540136008954594010010b240d4100003d440c9442c803c02543d410072b86194042c1c0d0340c0c0002400c0c1682800c086d151951482405042130815110000709001400081681c05150007000d507200d000700079441042008a07103100d4400b9030300001910906610207408070b8481c0007201c0c4c69100c10001551002028404d03140c000088400402051 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 14993064 1250 14991814 14991827
    0x3060d05071d01030b011505030103080a050706050703021c020a050d09050109050a0f050613020a09020307090f0b0d0605040b01050301032901060e09070c020906010509060c0307030f02060f06010e01 87
    0x861055054071055a1110718140c2d85440d081e140301090842c1100400a11410501c40380c05031428450352008080b4080e0007420034801880000d0008a00141018034288500c5c191208a41c3c0810b0620a40c00c1100008000e50002200c2a4000001e8031180c070303440c201c920072034810b1600f50f2034441c200602d100360100201000d020588040d5203950f00700c40006e60a2114680d80e51040c040140d80000c10b090451404030010045040e1004d40b032901c4c1e002d41e0b640c828860894081203005a50395490b170000f2510100c4a506c1042110220007001c6001d01c0000301418034048022410444190340700100401d035201180d0340c9000c59402c00042c0041181c00c0c0903984080104d0302c0e090354040b52100d500202820036445200002c000c0f03c4020214a4076001480e000b4050b454070110324101500061402103018100034180007000803114030075150b8000352180c001540090301c2e242c07005802c010b8030b605402102e01005010300e000140c00341c44040407040c0140d0381030f950366011010003401510704 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 14994314 1250 14993064 14993089
    0x20a150e010216030201051006080105011b03020c0907030608010b0f0603010302040c0c120503010609060e03060c0a0201090609110102070b1206040903030e01020d09050c0301020c060a0207031106040c0f17030306 93
    0x555001c100c80c43c003c54002100360701c802c3c8250b00009803840c2000103903180c1101a0801420480c1c840010482a039005c002c842d00c40c03245444800c900000c6103016840c0486e0554150741003001c9404108011f9007640c0305404542c42440203100b9040710204006410000e015a10f40c0480284010310140c02d242d170203800714101500b004030009045480341e02c000052002c1d00f10001c3d0700040107000d11644200c81c2001854141441388040d0b500303100007034485a006000490000c008520600054400d4101200e8180c0010007084125101d003045140801090314840c094480c41c0070020380c1031185800c0301c2c0b40c0303041c42124500030780b50b000401001d000f0611b410740400d5158050154107420a10080001c20b0a55500084002807480c0c0343e0300304410800d046200f41d02c14400c0c0c034142e10703021500300e41c0408e0144006071748a8a80c60141c5403030764071220801c000d01c03a88042208001950101c03200352449244401e4400d59a10301d03001240b0035004859015800a0010403814103041c045c2192 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 14995564 1250 14994314 14994341
    0x40f0503070209010b13090b030309120c150705070e13030c0204021201080d0e030d0f080615040b030108010b030d0c12090302100f0e0f010906110102070605070306031101020a15 78
    0x1505089800051000900382c11516404000051070400007501b401200028406200b003480555008400280c507801890312083c041c020644000354100340034405040700c0b000c0280301059001c065030480c4d400750410b0104841500c0f4200001c100c0581b0300342070a01c1414182400101ca400580d0111051100281c01b02c0e08181c007401101c882c0800b02049038042d140003002020300c1c003910003004000c40345440019000303400807481c14101540c02003512001500c5030400030950380740d00c40400e010f0032444024014144003c9030114640340d01c20000d5041b41c15650007440300359946001c15032074801e480079030004150311081740c80004000800300301d44031410b405c0c140c0126981e1340101f102444103106080c0000c1d500711301509910380080c51640c0c40c0e0f0090b41e09050565210300040e146044038040c000c140001c0500c002000d01007501101c40c03240d400304c420300030b90034190809406404507000444030703503046c030082c025694400a10484a00d03009200031000103419814000103102c1207a2148 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 14996814 1250 14995564 14995567
    0x9130606093908060607020d020607050c0108011401022d0106080303090106090908030105010804020312070b010e070512011415030903040306140906070f1e0c0b090d0206040f0503 79
    0x1803203898621402c202c40c5440c200c1030b0844042c910002c4010507410444036007400030351014240b401d510224450b8081c40558143d5035660346400001e100c2401690001e500031b000042c1c2c40d04008010480c0c04031000203803124140399884102891401c02010443d5005078081403902c030007504180490703130a00545403001c0c110030480010440c00e46080b070b04002560340c40002030246061003403084500600b11040b08001004039139032014514030041c81401e0402000c00007080035541d01f8400c0545032081e5036500c940c0c450440c84c0c1a60b0f5044e00348160840c141024001540c0940258111500c130035502002c4282c6a0901c10929a1428181c05482d00034088224071541464044d00550140780048010f640f2180785190001c20b9450780c01c40b5484009900c0103219404100180542d004406814144191440520100c0c0c01c4010031003241c10b00401000e07040175076074214aa2400090003144c0d00d00343d0f5580e8446507542c6050003801003006030b01442c001004100c0c1d41e0390052034184114143d0b03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 14998064 1250 14996814 14996819
    0xc0503070e042a0906080105040b060418020f070f0c090903020c040e0304090e03030105090a060305070317070b070807020f0105060a0303081305010212070e09010605071529010e03010b09130606 85
    0x3c0c20710701c4060400000f04480c0c070410701c038958011141034010001141c060000080304408264180503504c218211103244e6400801c2d240043c0c1c0589036a0070500203116162400ca00380000a404056002d644014110902250080e00e60250304c0ea041c1d0544c004042c050000f4007404000d100c100d60700140d80c0001d000c0852003812034042d20400d8040e0380020354480d4100701c10001028406071150369418603083c1c08000041e0081240300c2202c1e00a68100410210441ca142940c410524024800040202000600c0d1b0b0080085401003505900b242c1c4401003c820940c00c8500c10740c0d00c954407500c0c041c0d0800000340304004841c0c1c0b0500030300110542203200c4e51141e003a60001c1c2d00a004104101081000305503010401d000b6005c130464240d107003545000805006841400400b030312403452a0003e00749000281c015000c16a0380c44403c2e1158003240e0000d042c4002d101440b6400500380041203c041e142c14024030380f516100a001c00d2468442004030350310b40c4401c1c0c1044803130310f4850500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 14999314 1250 14998064 14998121
    0x18030a02091008070806040209040803070207030f03050d0b0103051017010f0501090e0d05070c0b0c010e0d0909141905130c030503070303050106171503070503060114040c0503070e04 80
    0x5034010361401030b10104071030500941c24100000c0760080c5c003040d40040c3c1044050381e9401c10158100c3d0f04104d0507a0f0341d44800c3c10403414258160030241c951054500d6840070544c1c840000c00300d0400b031400410030700c0c44c4500110140e60b800d03681000c0f20a000d900c10711942800210000c02d10f40018000a500c025101020701a54026171040340d80039501c100c070400034541400202d11001c1d0700c0c94070302e14040f441e0303890f44e600360481d0066082c3d060010a90000002c0f00354040015002c00d46e0403500350380d0485400400d0600d441c0540b10035103041c00c042100240c44120284d014031141c651001060042c1400d14004190007004c110007601280340b41c10100c1e40c1c050703185004d18010380c00703142c1d03912160402a0584c0c3d4180e003c881084000400400c6420007030030b6090f0405a001110a002c00380b80000034030b0001780350441989401100c00002d4905400000311013800c0e000e1f07030705008248003c1c0003130b0303454041290954080b6086803c03802140c40c0640c80035008052900c2c0e407081d0507107201032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 15000564 1250 14999314 14999329
    0x50907050d180302010605060f031303090e04050d09060f0c0b040c030206030a021806070b0712020408030d0207120302210a0f020d0207030e03070b0409021822050106080c18030a02 79
    0x303a0381c2a9a020b81000028144e0a029403000340c0b0742500d15601d0801d0924140c1890711004242c0c2c0103400302c5c1c4000104151044102c06c00801040b00803205030b090606001d5161a10b403030307120011514241d8001215030040c402d00c03252010b140c9a10313600e040c158071134221445004000701c403901071201e4040010b96400010714001ca082150041c1c032441550f141148565040070801d00c40c5506102580000e01c0840c0b0300c035800720192a20324005c801003079444000e805030390403000c2c09000226040d51f00310030584c0548a403d0240307142001c0300541c04402d03000c80c8943c2400440d203400550000b01c805220540395030300103c100400150301d40307030f103c0140b0032600a03101100d025a00040c020b0700f411343c04a2504031420084015042d0300c2c1c03410360f40100c00e2045106078004030350081070701e0764958110742101c00f9240d000f8210324070800038a03544200c003803010803420b00701501d000b00106119205100c00c91007514801132aa02e8902c3d40700b007580c120110101d5503941482140000e0b401600c0d1000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 15001814 1250 15000564 15000581
    0x309030d06080307060b09042f060406020c0109051906080c0d02040308070b06090f01140d0203010507020c09010e0c030c0706020d0c03021308010506060f0918010e180d09050907050d 80
    0x4010b5600c400030345c5008415580c560b0517084c0700781003030b1081c8404200c41d005800710342446980801881e00d050f091035010358100c00745444d40304901142c0000c41c5500401d030028005c1090740c0301d40e500c03600caa0030803506058014044000107901e6000703000182c016124a03821104840740d4608004002540703c040e607200740c00031500321102044101c100b10001c42059000001141e18203424030b404d2104a20b060030510405514a01070820360b40c40d074842c00414010a500a0000c1c80076140801c006513907030f100e19070303030328010748402c4d0000803038040440c03c140c0540305000e5002d203952166460b07844142c012030001d680715503080080390710a4149101d070f4171034124951000746e100d4040400d180c0e014802c6078030050181c2d0602080010359642c000464850603504184180ca43e03044002281c01c1007052480c81555002c2180040345c00c0006401c154440d2880c4100c2c0c640381006007403015244c2d200000707400b001c201d041d041070220b4030b0110841e641c46078240ca040c504103540408540c007039a80760ba = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 15003064 1250 15001814 15001829
    0x30c0405010305090d0c030815090103050601080d020d0c0b1b13030302010f0218041104080a050109111f030c0201020c07090902040608190f020a03020d03050d0501060807020d03020309030d06 84
    0x94100503558050040c140e00100400240c0070802c1c1c0000007910200d0402c40017400c108103100020040420014078010514024220030010341e103e1a0040d0765502c203000d417546501c6280d50300f4040c2d44c4009108401150b0a03075950418090355660500410381c0945400380340140184040590070000d0054045840401100c0b44144c1c0340d42806421986c981c140c00c504a40104154601d4141c00f035050301840c6800e4900054130305014900303902c54001c40d00304a2082c0510704840040c020150480c85080303018107070503421404d01b201040707908180c4130303131014640003051100c4c4c8075207001c0d03405601c42c140d103400007614040d40046030500f0810250000008141d8644101042d81403520480014007041002450b241034142c414a400d180180c00041030402d5084010b011034807440032003401158081c11090620401d440c001d00175420425000b8070044c60003000188041c0314a099600400498016101602064030110040e42c0020444266444200700c80128480188990303002800203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 15004314 1250 15003064 15003067
    0x40608130210031d031806090a03080703020d0e03060403080601030e0a0b1306050f012106020c030403080904140105060a0f03150609060807080103020f040e0c1504090b010309051b0114030c 83
    0x9480c03030500c46a40700240384d42c56402840164124080c0c001080c1da0f00d00101c1e41661240211400180c40c07001c10f400003002c48030042401c0e410940c00240c800105259900c0f00b00d8070005031400c0c9542c4103012200900000c180d900484d04035400b0703030700009102d8041c1e07068410104068486081314070741600c0404070300542d00000c0c0c007808254800d40d0703000b0308481041e07045e552500000a03074006480b400c0c09012080b0b00000c50401840d0350407180d900003214103803520b903a0790341405034003500406081c9001c0ca0401d6408500c103030074680c0c9107041e908010310721414414080c2045030340b03040c640511400d00d035980d040001c2441c461181100201520794070401842d0034120010800079014050b0b00c18000c00c0170040c0b00580d50b90a0051502c40d0a80f0005401812148030794a00308120700340b15042004180740103107405504009006071600c054081c820b190070407004600310b40022001510b20b4102124407500060301d424094503080052619510400c41d001c20341c001d50780140c400e100000c20 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 15005564 1250 15004314 15004331
    0xe070602010f020705060402010e06070b0f04030f0e090109050903040e040b04020a1502060406021309090c080606030c0109051c1401050103050601060c05102c0102030604110f04060813021003 84
    0xd09002d040720b044030040041d41000141c0c1d40b456034500000d03000a0500414403e12840d039114002a580e8480d004080c10700075044c2000711001000040e101a00001e40140901ca4061b005107109100b1000240a0150316841c0010b61001403078080e0040300240000c100c00a2004412100d0070301481c040c2c00d8115042c1407500c10070400340550740c00b2151040100b49409513581d00400c031154001e03080307078015954200071119121802c466400481b20140f818a80005002425085005840d54a02100c88035101d1008140d034801c10342ca030850015070000703010302440c100703031031404032036424220318245540c0e07282d5a07840c03102251074003500c4681d035a60041040c8401003051500504c046d0070100380e01c06980d02c036147c84071070030080108401d03252902ca5a000e030008240000000c4c140c044e010380c940201c160a80070354410303a40d0038400c0c0d09120516000c418000b040380c01d4088010903440c60030340b03820002e0711918001415070032411191103034140961544283c8540c019015600061240c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 15006814 1250 15005564 15005567
    0x605010e010e060307060305100e04030f030c050c1b040b100804050706080f06120c0603010603060609050604081f1103150102010c080f01060e060c031207021b06030103020d02040b03010e0706 84
    0x900503481010000e0a54040c0660340d10b0114411003031ba0031030314020806540d1003244903000182c5500401000d50541e04120906da07019036000c202044c6030780d080c02800d40d90082140c6a01070000c07003114542000240500b1034044c40c41c559052040500f000c10003c51510000b500c69600d4000a00403482020400081101c28005080949000d0800070a1814141d0084140f0742000b8002d5009a0001c012603c903d01c00300418414a01c00800b155078a6854900090107088640304032800318080300c101141c145064001d40341500c203c1c200a08682c5c04c640b441c66254a003854880218507520a50310305070248640c011441403010400d4020580412000282103a0321854003404004200c001d1003103528248081c10f04603086d42c40c10382c10728440d080001d079061203082c00000c0340744400294040ca101c1499200c5100b83c0564098032904500c813424803040d002100c01080e4006002c1005000518028000e07000c40b40c0040c0c00004c011070300d403003c04e00b181c08030315800d1116800003600f0055603 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 15008064 1250 15006814 15006839
    0x12020102040f080f0a080c0a0606060315050102060408030a1d011802010906020a0b060603070203090603040c0602071d0406050726061011030313030c080406170f1e0703020405040207060501 83
    0x40c01c00701c0042082e400c1804205817548850071000b0001c940000c0c0e600780d500020040c08040c5a003000c2c04002d0a940c60401800502c0709103030703078090070006032000611980003242c242d100325004101c49140da5110407a09000301000302940307040c0101d40c2040c01400d0001d04c11011030040d4825507038403104450001424521503076114078110751000289100181f0032003103503030700f104099485503101d884503d4141d04601a151035107812586c040100800c0c00aa032104a04903909502036030282619004944001c3d08801c00a80300d1691940104c0c0004010b40d01440d44500545450507841c00541c1ca559016055913100170036480345402072100d1407625000b01c200700c80407410101079082300c44400175124000104602050705100550100f4036000706008511550300c41a440d540711b840b03034000b800307215071503044115111640380000c9404501021442c091000020109114241518900c2d014600140390f07001301902400001455240c5001500c001c5108000200d101c0d8101b250a8088 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 15009314 1250 15008064 15008069
    0x30616020a0b010b030619060522120308010f050303030103030503132102061905060d0602090a0902070b0a0c020c06180a091109030f0109080406050a050702030d08061905091501030912020102040f 86
    0x700d403040e20080000c0360f00309c0c085400350300da041c281c1c02d0503210000c0083d038501000d5101a0108407028080b904041e84010303800e059940c01c0405100c10354941c8181aa039000c00d00004011403410004125406550086100e14034490074808007802e4080312005000800d2242d020b01680c084c80c1071111f484410300e01741402c0405131004100c0c918120000800580c00c400c400391040c0d41c00148103066440c0e01044130050000b013a0300750342e503030b000c0d15011210480407100220894038001c14241010f00c003280300844400300400c590f041c042c070b803144aa50316544404d00d640c442d0141c0070024181d125806480c00901405501e80c2c0c54040140900d0704100300300ca103816690340340101c503000148141090b01c0a0310030324a846038036524100d000b694a48034820010b94184250102c000d041d95104a20900c210030980c2d100c01c1d240c20002014444131780e5800741ea984525000001510288a0980001ca2042c141b40106180f4415291559003480000f1700304010703500041c0034084983c0e0041c04100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 15010564 1250 15009314 15009349
    0x10201050c0418020f0a17010e01050603060f01020f0d0203191803060b121006050a060302071101120906050f04020906010504030302070b0310050613060908030702030616020a0b010b0306 82
    0x260346007a4216680c180310b103028052030ba0308054280e800603026039058815420502c41c9140c1d8400d21200c01074100641e1000a000030010075001098403a03001c48958100c40c0c000d03201904544801007040301c0000c1c80c101c214114072800103051200f2070200211001040e140d000fa5981e05d41075543d150185494a40701428400b10415048000c0e00c464072003c22240c11500014a80340e00e04000382d89100c0030741d42c6d003216104101c5d1100324000103502a4086030701c1100c224030030b150b98803002e506134018444050405402d40d03030b206681d5402808401071020351070305d00085800e8030350b440f602154400c1c4c459011500300d0008010450410004954200341c0034203080741002c4c59030b40c00035580ca6803401603101000c8003001045d418034074018842d000e0b00c0001d101707540b9005101c104104241c000d201c0d0303d0000b158400c0c0081c1d4503d000c01100d00c0290080c01030301c8150785034405c0b12000b00c0307556598801c521412126901080c074011040d80a000c1c090450307075587c1811030070401032018041c40b030307030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 15011814 1250 15010564 15010571
    0x105040f0b06060705100b040905060406050f011703091e060403080c0105060402091c0c09020301060e010306091b0c0f0204051008010c08011d06030a0605090307140d020c1203070203030a030f0506010201 89
    0x780805e1001500780d603000300021005c103c465a06001c02c01401e50040014441c1c071800040c00b04014464000c00d00c05c500300720125481d030780d9070030483d2001c00c1c0c2103981038443d0f0010400e42141c0e04154802d01862181c04000f082d20f01480004500c03079a02c5540161071285d0301240000d8110001e0040f5a00254100c8040d0300b84405040082c000c1509107190b0088600c0c004de8100812281a07100c1c0014241048215240c0d81d5441c3c0203002c00701c6130700b05640040e14018021034500c19500c1070300c10540c1100c19580510058442c2522028013104059810309001601800180d5607405440d210300d40011388810124640800d481c2503c04004048040c0501c00f0018040041e44a07100140c0f6440482c0b1007005480f041c2c0824100403070300b2000b40c500f509140820814030710000c010464503211742000441170440302c3c0c42070380b00c00325201c0303250041e0400440040301d49801c822080c251a2040301f030301e180c10303c1a0b000a29542c401081000400c1d00c0e40000c840100c901d104142d4050000e00090 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 15013064 1250 15011814 15011827
    0x9070608010f030c150201110703030209010206090a03092303010e0d02100203040809011b0b0a27080a050f12160e040911060a0504030f0503090306090f030409020d0b030105040f0b0606 81
    0x11032181300d4002c5450005001d0500d20429100b50070a40c000703101d80e059169100480e060040c0a50b004c4580607026100e0a0040340c140303000054120215034040c0e03280400c0c1d03030501c14220403001c65046440b05020b040c00c204109030354203100741072044013004010a01c409030410041d00307003219041004c8601d441841000081809402160f003460002d180c444072480e0076504441c03118003036402c060701c14511102003041d91001544403618060000f41420294086400c080c0c941d8541202e00414104060050700c0d210f901600280c0400c888006096052000b1040034105140d0125a40b40c0a040d2848040c945140c004203528000fa40980d414000e03d4040c0c3c450202401e590300f4143d0254070b001030101c810b98490030a440103543e0000f801060b42007135080107944ca40254a90343c1c401e009000c0454000c8030005084582c220b0070601031424a85481180c1c0000d41200f00d00884d029180e010720103982c0d03000c1c41100e1207148101034240300d60149050001e4a0b04005010901070b04040180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 15014314 1250 15013064 15013073
    0x8060d031b020d081303050120040510110303090c0a05040e0606010c032307150203010f0e0601200d020f01020306030a060b030a0f030c030e0f10051b0609070608010f03 74
    0xe007450071035211a680c06907100348040361001600410280081d2404100307403590350084003000c1c04076030240d80240140c1d40c0d0010034083e07016a401118403030140820081140c0d0508070b0b030744036060407541040c180386111007a00070700f140d000b20f916103840d4000401420503403800e40c211401030001a1070030486040d42c0c116160396078401800c0c003410b214004602c0c208240c410303500c1490b80c0d0408165503030000102a46211607070001a4100da2210041c4c034a00090102c520a41c0c0c1203403881100712152a1411224064a16001c1d0005041040303244001ca0040b001282c41480140d000c002880c1c110440c40000381808428091280c980e4010000c3c481d0555000174908902e0382c100d00c3c00207030710300c091000038600121050000c01500f180ca0070718081c141c0281020b82558004d07120396466800a004000c621005958800c4d03100c405411612420b0b803003540030306000344502d210080d0300074145240300d181600c122281040382e4000301c03092012030f9000c8400c41c010301c440d5404440d490705540d507 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 15015564 1250 15014314 15014327
    0x408040630020c010b0604080106090f09020906010f02121b0f06010602031801020c100e010908011103010b070204020c010614040c090b0a0f053c0304020904060c02010608031201030308060d03 84
    0x107652a2094010840c12840082980120305034500100306540c1d69555403541400b070225442512407161400340c03800c1002d00d1314001d080206a00038124640f83c0c0d509401920b1710500e60342d210b030841c40350311101900c034080180101003401091480c2112202010107140c82c0800c11000c544064220310010016242c000080e22055240c4d0780c036030801d507a12000100d01e0700b441c0c030000c1948030b1101201d2002c0a038003c0c80c2e941a1207020303078a41007015102c41002e403da584900c906a6040f00800c01000000c070000d0241080c14401031015180c00d84061030a1b003502d03c0d5070004510b1240d421442121407505202c2d0301010340c01d40c14056040e40c50b28001c4170141c042c80288106100c02824000b54007440740c4115002d08202c0391102401040f40d604401c21131780c45d1130a00800203400510038640725011010f13644038941c024007010306541d07a1780e50074002e03010341404031040d9034903408040748162040c0040c003800050f421103450550b01d18180104540300c05402d00d4003441686082c080801c0d807100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 15016814 1250 15015564 15015647
    0x10c02030a03030c0e0d08030703050919061a0904050708010b0406060816020102040315020d061a070215090a06030203060f0108010f09020304110a06020307060b01090b0904051e04080406 82
    0x140004d035039062103c2030350520004116150b011103d64840d10801182c4000b44d405030001c3c1c0d404102e07a5540c2c6210070f0b5604140381980036886043c090312070000712190026540d4030075040445005001340c40c040382080e074040c1ca00302d40d641c100c0942841084c0c0701740300e44044401c0449043c07244518100002e842e600000c4c1440e0841c40340d0031110f0140c4c1d070003501101c00443c2e12800c41039070000101d0341c0d46c009400c4800180d01d514104000042c0106150020040803190891920318114055080100e40c991090100045480c20701451003d0fa031082e0740700f4010078441d1000b40c0c0d82e1030940e007081180c0450721401c0c1d050150307400c014801464501d0418040c2c0714855070050317403034440c1d09200c90259602c19009a0043e1022808950340d5800700103001503910554051120403561001501c001e04c440c011030b44010b01c148800d0802e480c294010640004a8000e0300c0540c0e24640d002e0580142c007142d0541d008080000c08012244c2d000704450701c50340d203840002903e80b1a0340301100000c4c41d044e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 15018064 1250 15016814 15016817
    0x4020301200f1629060105070b0703090201021606090f0503060c040e070e0d030e0102011a0310020a03060803030a0608060114010804060b0316060815060c0a061104090204030f06050105010c02030a03 87
    0x801c00380c5528203c030450a50458116180d00f4403a6481d4440c0d01c90300070141c911104120070f24000c03c8241d400380302035602e1541c0c400084050365a03030942c110000d15020030140c2c114411002103805510540c0102005031a135691000740413420450162201007281d40250300a82c480010002c04002d01401d0724180c45281c0005282c0303440f1840300722003240410070103d50204950b00010300b00741d00521040302ca00f60a030001d01c045504261052040c401a018494240d0840d0640b126883c41d01d600401c010840d0303060006802d070f02d82d8a10b0f403441c0c00886d24001d2040d1b403681e09000180042212038010200c0200c036651000107003000814030710003d0001801242c41e4800c12106550600c44401c05010310f200707811445a4076440240800c0e0123503800813100103446001515030030460215803024880700001d062603285642c1d148000c0011130040d1610190a01c0081903c40490004000640c018081c9074103000903414101c045850603402070b41804000e5204800680b00400c43c0144290107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 15019314 1250 15018064 15018067
    0x5030604080307090b0301121401050403020a081606060e060a0b03040807031202040503011a04060801090f0b090106170c03060f13020f01030b130e07050307030203030409020307050d0c02030304020301200f 90
    0x2400300580d112161a00710000072170010002254900d44184104585030203200e5481c400d035071030300c8080d00700c031800c1d0342c0500160042e40d01200883e90382d800a26000a0449101c9500710141d20b0340c904803401c1d60800e03040322009605210003450040d10220251484a0049145060031380c1c60702c0c03a41c419900300605110404012410061095068078014103015000b0700656111980c1c505080c83c42010081c440c5203401000b2030154814440c2c80d130400d6000070070000750f030003e0303c410b2140180141003450964a59001085001c00094500040300707000700180010040e0030105800e03d0002070403404c88840d44010040400030042480100b940c058824001880b40c000048001e0b00080005031740000d04100c24483c244810303032220001c45c0315402601d85440e180ca08140d20381c1d01c00c2c840658140c0c000e1005005142c0c0a50040d40c0107105410201c0c500410605000155071031030076613002517003000c400c1205505084c001e08032125a01580011500000a698255800b0312803140d200041c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 15020564 1250 15019314 15019321
    0x80603010618050a0e030405030c0603180a0308040b010608070905060c0109080a050c0f060106050703050309160605121003120f0c020409111309050c0103181505060a06020304050306040803 83
    0x1001e600c0000038080d080d03000e06a070484420b242c0c020704020784108000918021140e810458003000341d03016200c1c0140a81403ca2a4608000050300301404543c0c1c0c0040f01200310740c51540411406110520a894a130060b00c1c06082031912034405038030a0003440007100c00c12075480d41c0081c000702551401c03a4426190783d0740c40710550041941c00720080004400051200d603c0340c00c0000740042d43c90410171070b038141d90300b04038658039400207205240c0802d1082c0000c5000900a07000f40d83c0c8140303020100d42d80c0d5945041f4026448035503601950200710f00141b10041d1014041c0c0c0a0790001c51410349042a07031941e0f9507544580060314004c1e080040900030761303031900c2c811008024010f400504c00d018800e07413400c140382800d1283c10194030450440032202c0101d1403034002d8044494100d4003400ca1034203540c005401501a51803001c10341000310303501d9000250000c8022101c80402e070400252807510320140040f0012980001013954801d1104101998000850503401540050003940b00d45 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 15021814 1250 15020564 15020569
    0x7050703020109050105010e0a0606050408060a0b060d0f020d0506010c120f1403011e0f0f15050702060d050103051b06040902130803070602070201020607053c040306090c060f09060806 81
    0xc3d0311400500d1542000000606100c29612540c002e00c00318008111055030384509842030b1140b4800c418094000c04002000b1429540c0b08048100f0058038803480e2044510365a01220150070107410929400300341c0038115900c9100700395000e4001c1c200350304168115111f0382c104c1e51900050400f0840b003829600310061103030285080d0b00260400007904c9503103840c200c6103400c00e603250351a40509982c100103880d1080c035070a0070071548014080070140741083c00c5a400c115070309001c2c405125081281c1801a15000024681e41081c4440007980354110b02c0c0190070907a1070021021001818114100c15555200840d0216810a00c005a03600381c90010781e40d8546450f0f0180b000b034000400d0f00028409550010210300d4800d0f4250b9419599142064035036014a01540301c0d04030801c1c2c9070702440d03612440340e2060042010f04800c042e800c141400542540590401c031480d41d140c408942c100160341c44800c001d40200e040550080c400701c1c00003010000203200710800c02c00c0480105000c0e4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 15023064 1250 15021814 15021821
    0x40306050a0605061c0b10120e0d0c140a0b0a090b0906070f12060f03050604060b10090b07020d02060d0204060201060b0a02060402100903050102030109020a0f020114010902090a0506121f0806070507030201 90
    0x29005000c90307044001c0d2007c00390200b2590f20f00e0030b0382c550529820040740308021926002007021512a15018009600e0b5110725070007000c10180d06104060a03580898514540d892043c0789408010414003079900d010400c0000140c49403e503980182c09000945401400510080d0f8840c50640303010004661000060405503012014100d50301d0400310501802080980c440c0d4021441401551b041100b4800718010001011300010903042d401e01903000103d000b809c03103500041400000c011181c0004d040341e8003000c0500d064550000c0e080244d40c4d02806044000c04c49404031a040c802607040107919032000810080c8a1000055040074041c01f418201c0d020b0341c2c20400171510307580c603132110100940c4407084c0180401e00102c4065081407050199001c0e00b1003510a00301c83e80d02e08401000650884110f01e0b84c4001c8406001c5000d03200d0300080d00d000a00d140c0d10316003034241500e03040910920064092840801034006100c540000941180c100e0414503156540e00e440d41400c9005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 15024314 1250 15023064 15023081
    0x6120207020d0308040b0f150904030201020c0601140307090911060903070801050709061b05100507021002070c0303090506070b0c0708070f060603020306061206010b03060307030215040306050a0605061c 89
    0x4622000000b006141c0d10903841131140b44901c0e00c0e00302c140c841a4007401102c20840c0d4500394140d80441d9040c250600981d403c4c1c0103842400090b050443c00c001042c2001c8098000c00e01c40040c0b204001e41038902000100c004001003c010000d51856440b882e581078014000c41e8001c03800020140c44980b020815000100f00ca40c000304042c0c109198014682d40302d500c100d2000036440f6442d92024500303040d80c05c581c3e580c000b0041c82ca0305c0d000b01c0504040d0a0003082081503008046001c40c800189000600c40389108680c41d450444c207528001d45808032581102d406100103000310030016140c0c45103150882c2e280c64a1948600306450404900d110b1001e0040c9404546020202007040c55004401aa4803c4058441568900d000c0c028510101441c58983c0e50110b001041036030007a40c021a0020380c040c1c2030f140b8454a80e004103e07510300e000003041c19a00c0010f401c0080c04894803419030010301e040e5081c8a1303545020009122030045040ea8045903884104128110000740c3c8201c05 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 15025564 1250 15024314 15024319
    0x306110910080105030c04061401180503070b03040501051b0a03020c070306060324050601020a060e03040911040f05030313031506080f071703070b0f0403230702010e03010e03040612020702 83
    0xa4469101c9001840d0340300038440c1d42e0091141c10303000ca010f40340c540292000d1794140c2000c40720400008004541f0b0300d24420f145061641d1500c0b0201d100d0310144403110240c403139107c1150b56400d191408908480d0010201c04020301d002c48188450000c180c12202401154034016031155035401c0c0b050f0501c81180d2004115501e0050000208402210f0400391002130004002524646420300c60554004481c5180103030041c0c02c8010000380300d50301c4900d0009403e0100c82c141501c0b1081348048030703003100300350752046d4001c24100030743c03180c00544401070807041d409503040403641c4034060790800c0346003c010010a40303101440004a02e66026800901000d81140c400045000c913650303c5891901601340070940c10030310f40c0074004000040b14101907001d82c103980f0a50f9029944014503501900c114200500c241d903ea01e420803840690385550580c0d403115983e80410310005d4500110f00700c3c41400b90341400340151900401000f5501104c030350b400c0c410761003a00285400000e00c2101d60095 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 15026814 1250 15025564 15025579
    0x30601030c030204050601020607050f130302040905060417040503100507020109061407090608010308030103081c020d0b0a091a060d0e0102030a0f050c0304120c03110607020a020109060504060903061109 89
    0x2090040d8440c1c804112070003a03504000540b244401281c60b81811100f02000c21810400f907901607000000404100b1040c01c0c8840e41c040c2c076940041c003a039500802c140c1d1503074802c100f888180000510500011000c04145902e020300c0c1c072000c40d0704c0d80d00c04010b59071210f54820010b07a00c2c41c000c1d082292001d030b00c90010000f4000109000b8024003080e07030044006440310f2000310704980260740c000c0c1a00c6d00440d071241903a1840d960030f0701c5a840054000140341c1d0400f000c11f500001400600562000d82d1004616a00302400340480c400056014094450501f04182c0c154144801c80d0b42e0002400d0b21082d90300d200ba00d40020281514800301e00c15036100204000b03851a05502404100380309440900c100d41354a02c0f103803641d02080d40c000d0100211400b0051005016001d4100313158428205502181b04002c581402d1410480c0e140d400760300445035100866900c18600360241280d4205141850b0500d0b44c014404a1607000081c195a50344006038180103840c4103030752580c0300003407029 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 15028064 1250 15026814 15026819
    0xa09020103093302090105070807060216140105060409030c110303130b040504051b0d020d0605060406020303070e010219020121020a02160f050609040f060314010903090f0605030402010f0e030601 86
    0x2500700718980c035000110384550294a0b42e851065008940c5c0074401650b0311030600e00b03107854008180e4007a400880e00b0590801280d429291400310400752140222a043d0041040d001e8003400e58400030b00e020321407440e00e907490000030380014841840070341108440700c9485494011074514499629000e2841c00c0f410000980f07900008018000d64400356000c0c8940e0315281482c2d00700b41c110200b06039800350b0a12030501400840c2e0301a14189424840204604e90380f02c01081031a0300c0340e0080c80068000004200b900340c0c0010581005200a1004142400950600001400b88080c009040011030a0300a0103255160490f218129500a0031541d607020210081d640301030441001c0c550300d0881000180501185618104940014101c10700d494201001c100040c201490548020303965180e020003c1410359807032010309225000002041091428081c01c0303511182e1024002c01c480100a01080313900c1819a50826070a003445500e403070b81600c0c02e5441c2e01d4224880c0d5054401c00c03000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 15029314 1250 15028064 15028103
    0x703020f031b0c0901080304210f0803010306180c05040c02030906120403110109050c0103020904021c0203060a080601030822030519141b0118180e0105060105030f0a0902010309 78
    0x402c8080301a00884007880c062109101901800340304981140d041400100090b65020907400e111740d69400c88002c040e9035941c0d402e03204072030305281581d80d001d0200050040240521410716941140f80c070069140d05569928103c00d07000d401060b00498840090408550080003036a51440307008105c56241c000c0220100303c440000c03941030f000141c00c9144040c6048040c070600c00c016400038081d12043c444e030001580a175126240c1c03103421690800c80d050f2800c0c240c00181038021864940503036641003090070003244032800d401c40340c280c1d08543c0c010000144e046080b1180c801c070f4007000340d661024651614180080580c0050001d0281150151151240729500c0c00381510074506c00c042c040d00900702c01e540c0d20b07140e04140880e600700340030030b440c0d58050420340840041c4003104451146d00c0324455240420800400b010188e200c00312409030303080038065181d000a0a103070032800c47c54400000000d002026203201e07c181d03502d40100040d03901c207810103031526030003880044905d440101b1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 15030564 1250 15029314 15029347
    0xc032503030b010c050d0f09090e010501060807050406090509041109010306020306010f0504050f0f0a170109150c0504090b06070c030803090105061504090e010204080706021005070203130b0703020f03 88
    0x46000030b1915403218810340c02555503041c4990000020202d1a003240c41c26030318a8140803d001c2030140040000950410b1070040c40704026017040040f906515001c0040c00c01c24000d4036900c14402d0074802808200e600c141003c045640840b000e0380d6544450800007449607411080d1500f00c105180040284903141e002180182d07402e036640f00b01008900002c803114025405126400050113520103603070301e0254070f01d18864100a20080b5003540e6020708010002400495000d1a516403d0039030a018072a0380380408030b055090140900390307042800034040d10031805940407150b43e4007485860b85e107c0034291418680d20207140c815060716410009841c1d001241d80400b22341c2000c0020f6441e0600491036440c0c0303185480410305140c01c00c00804003920048110444640d400e020000d001c403800c01900d40201f0300e5401070301c4401c02203400c1c0390039944010079010541d40108080c460218039880a902110071703102a0b541c6900051a00301e0074140c01a486240e01e200104e044000c2c042e486a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 15031814 1250 15030564 15030637
    0x121606020d030504080403030e28030b01050301140f13020603010909060b030a0c060c06020c0105250201180303020d020d050c04080d080f060d02010c0506070201140105030303100b0c03 81
    0x8085070107150403120124156801154000c14400d130a220030000030303000707004000c22114002d14041510000d05d6290081401400c0100b2450662507402c10902c00072241440c05440c043c0d000303200b8400c0300c204442070350001804030a01c00c4e541000180c40041040f440d580040c0c0d008160b95901d5a44150000151410300c005980f01860040e000029140020754a0070690744540103c2c0b907246000000d41700301042c41c4066a0464080181c1c3c40010020700c03501c2c1c4580c49e0f030707086041e032280410703a4058030311400301d40c0c0015a89420502208441400003001e40141e05107405039992480e40c0701d94020380100d0b00d11300009030404043c4043c03035180401820980e083d540481e540d202c407014046407801000e40304422100c011401183c07184c100803203020515401030404620000499591501e4580b0032110b1a0042c3d5481074101c4159400d14042401490118000d5040d814800840607400210348216040c01c84002034041891405006a41800805e99080010141c0d00c808003010f01c1c80390f1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 15033064 1250 15031814 15031817
    0x6180a090203041505011707060e221407020303100315110d0f0c0212040506070c0506030c0a0306060903020603060405100819020a05030d080103060216022e080105010c030e121606 79
    0x17400228031400b41040010344940740c04021b1080d1752400100380e4001807450301d125001500405400d0f85150a40c018021b8a195a0400190303908405c0515016890113490401190000c0050080c0c0403942000c00040c0c1b13411481041c0d031009180c410000810800242c4d408601c80801c40d100342188551040c0103040d48504180082440e43c0b804907154100301e0b03818851204144414031190420030007034402c1030b1041c450400038540f43c5000540315002261030b80701c10a0000b030700c0c2000f6075040c021000188841d09108501d90706650010b0f5823400010b00741c50040da99900040c40c84001c01c462400205076640941745101c82900304100e1280c4584426406400d11074400901d07810006032210b1540c0283c2e548002903400c5a46900c00b84d80003403204c1c04060099610341c000b60380e41e002560f0000e54580c19428100c000310600c40c03110081c80c41000c09004e0003e004000d5a41c0100040d4440369251521103000c107801d030002240f4100ca41c18102091240c0340310901c0851224074050141c0d14107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 15034314 1250 15033064 15033071
    0x5120702010c090509011802030406020d061e0e0705040b0310090c020f01050f0c0702011407060c080402040c0e030309100c050f0102040602070e060d0b040f060f06050a0902030606180a0902030415 86
    0xb14014040305d1036080c401c00c0d80c10010402c6a66805030070b039028641051248001524080d14580340805a600d16000440000071098442d150b00165010035001003204200450091428001c0980355009510818091140c00000aa02e64400c1c03004c04c400340c402c400d42004050b88800700250f03615101486a5030562a08001c1032544903104403442c400d20035880090311b0000c440c0e00454081600001480801100b0710142c40041c01ea0f0091150f8140c1960b100d615903e8a0b004002c19a00300480030000d03c0b04000c00d03441151804400c5445076441511100c0a5070000381c411a05400c640c0005046405890600102100107400074821140c2650071070b9403130b58407209650421802030b920b49038085000f8460100044c070604500740c1c400e0203204000c4007030005884201c2a5441c1031546c2c89030550343c08041c0803074503001c05050050641e006003181140b03401d4011130358034440c000d81c0c6a02c2e041d40000715a41d599a08003041c018100d908400d540b00c1c1064a0020301c0f4440024540390010709 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 15035564 1250 15034314 15034319
    0x203071103030121050708030a05030a18050d0516061a04050f0910090c0b030403090f0602030f180f031005010801110910080603030c07030c0302091503060c0a05120702010c09 77
    0x100042901e040c0e840c401104d92255001140303111900414402c111051b008180300002c0045d02032018041c840d03070680754156289403a0780f44204681e07002481010f542804a1b00c4004150002007a41c42c001c3e560401c41e981355480500a0104042440c0003800d031420141e02c04a01088030300401a00141580d06000039202e0421140b4458002c840034042c0d5400b8080034660503246400c010b6020f400703065844100e988504019040d58012201038004c1740340703c0810429002003000e1400101f140744003450506543c00c0d4400310600c0fa989680d58814040c4a4010299032040d4281000c2d0f40003c04940c0d048600c14080000390030f0910904070a03528100440d41d980ca421001c884900700000d15014042405c40e40503500404050000c40e090305c001d0060310b48881d01001140302850183c1d8a0302d056602d9481080030a40d4000c00b0003414040c06e0b4550142920001072031078000e8500486943c031502640f0040303a07640035423950ba440000700c10007132014058042d4082d40040c00b03140e560f00f60407138 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 15036814 1250 15035564 15035597
    0x315030309031509051b0105040e1f06030506030c010507050709020301031505060105071109041b091a040b0f0d030201090209011409060102010c02030d090c09060b04050a080a05061302061309020307 87
    0xa00c0c020303010f00660480c5403881c10b0030016850303020786d0480504113117045c04c0e2a0307113000010701412101020f207000c0d1103000828050f480400100244191b19043c42149000d0340400e84944242c0380f03481c1481008990b0008114050080001519020004646179a502c6c10601948012181600c0c5c0d040e00d40400b0414a52047c0120b43c20710380c018695151800700a030170b0008080c00140140c42103901440654a520703160140c000003407020b050007194800482c206200401d0040049a12071407510300c9281c0d59031541044000081d1080311020f0002829041c01e0f80907203070407a070007503010240c2030000c10f0700e0050b4004039452a46c1654020f400356580001a0308039140030b2001400340c0e000340200708840003d60040401d41c4d1207552101c0302c660380c50b000481620b013a504510345c14100401c0600160a2904100e002440c50400421240c48142c807130b0f41d140c0a0180092510514481c000001c2d9101c1d4004c40f004281040110344c1110390f100d11040007508144c2d1041c0000342403542215114 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 15038064 1250 15036814 15036821
    0x3040609060e01080105011b140c0a050a030c03060203040309080703031d01020a1109060609030109050f060f0106090306110405100305010e010b07211106040b011d04050303060f0103150303090315 86
    0xb940103843c1d4030207a9080c02e0040d1010300604164042041078810410700103a00c114148081c201640c004001219500b400c1110004c4142c00c141d000d0302100c04104080b909114220048a800600042e5240c4540c1011100150341d40c000c0c2019200344000001016881100034104010200202c004033004a004a17100c15130240090030884c0590b031152821b00d851181c203608640000c003c51b240c082408082030079540e1045003600d940d003041c4441203041600340f100d075034004800102182a903040240142c02c40049020140459913100140c00154805070221009480d0043c118480d00303521480040150409000310712040ea902000010840000400d1758a00c990042c0304c44011901d0b540000e02800303050303500c0820031040300c10582c0035000034803c40740150300917804244558140722480c60180708004225007062038a004010106201000f5a50411001c079014503a1080f440012805015403442078507440300c0528000081640090a440499214280d0b00314407034101c2d00483c1c100d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 15039314 1250 15038064 15038087
    0x60712060e07030c11010f05010312140304030309020a1805040606050405090d05070507053003031306151502010c02011802030604030507030c0602040f0905060a080705010507031106090304060906 86
    0x4011080c0045220b80340250000e0240450b80e2800005000c082d4140c0c5013540c6c11400003150141c1d4500c018070620017040d2342c000ca402d129090181d000602a0b04c6040144402807000c0c04042e50b41900c00c04658800460200810740300c1341184001c4c03294075084000b80030948003220040d1501000180714185070290758840c01401024000d0b43c94001ca0036501c1d039001080848131070103039000c046110b40e100300d4140204264210a03045d40400407004a07074180e04400710760110381c403c0c4200150034000440e400c0d400f035813085d00442c822018941c0d0782101800c50b04441005107901160742c82140e030540c071004804a065009001021107810080380e41d0600b50400703500342d0081030002d80072038081e100078888140b0038540184010000d0301e55204a030810382014418149101c020040070a0354001c0a402c0182140c003505100d00d4903000b03980c0d9104503c41c5a0500c14041540010b150040b05490124080030b02a101680b80280c2150f40301e0340180911404240401d40204a0501c181c1d01143c0c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 15040564 1250 15039314 15039329
    0x7020609060705030a09110a080106051306030c0909050a02030a03020c0415050d03080709030501020403030c0314090306060906060d05011202030d020d05091507061404021509030604020405040501091406071206 92
    0x51340d00c400401401038032511000340c0d690241c1505004450700d40c98229801840807500028109081804008040c03040c2503101c112207050500500c0425005d20b9903104442002600052200041c43d00b681845408107000e07516018200405040c10380209000091080031201000f001d0300411040401e15028021141c000c59210004c0000078000d1642d41d81105003030502651041d62030391450b080e41d010383c104074005224074114604258002000c108614100d0b110707c0c2c00c02c4010701c0400c0c0c0d5003600610080c41030318403601207521620740208441081030841014811903031a0099031920240003030b003c0b800703440351120b8040700318400706002000005175540c0c01d2814100c18100942d940440014002c00c19007008481c002499901c00c0440082d0340e4080180c80f441c2600401855594410280080d00b0041003100c016550110707600ba441036040b0340c00241c1e07845904003036004103079848000303100101286516124000001d0036911404560fa1051b1501882040c408243c0c0d080b84600c04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 15041814 1250 15040564 15040567
    0x90b0109060b0910020f07080d09050109180506040b040e01020309060606090d0303050603071203030e0601051c0b040f02030f0a0b13020a120203010f24080309010212030a0906020a030507020609060705 88
    0x180c4a01d0000c003684081c0015204072a60a2141b180290604d02c1582c0300d42803691003d144002001d401000c2900107080908000100d58648594540032602020854201d10303500d0000440f256201c2c2e105404101d40501704120326540080e42c81d00030b601c2a94003903241c0c40348000152031342c40c04208031100c13010080d1054640c2c5200e41d07800e4000e81005042140e150081c02030100f0f64109009403024600c2c000d075408550381d2445001c40782081d5040e040ba50260083d500c0114002c00e09030006001180e100041301e05a942d1410040b0710b40424041c0203500d40900000e031801c02c00f00003040d040c414046c4040c0d25994942220b07194240c13684401c029081504c0b50340411400000e0109554414009070000c9032a0185507480b600725940c0394007400300f0f4440b0b2042220109490b80380d020140082030700440c60020b0401c0083e5842e018040c400d88540030000004400c44070f690003c00301c03943c3c05181903480b40005070015001d014102c88803001803241d400010302c2d0000000d03105000784100e8031102e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 15043064 1250 15041814 15041827
    0xa0504060501050f0c0109060f1406010c03020303150d0804090915060f05100e030604060c0e0603010308030c0c0a05060103060c0e03030a1e02030909090703060c0206070207091e050a090b0109060b 86
    0x12989504605c1581d9295586c40b541c40022440034060000084280740c1c0000c2c07415103134101f074006104090500f41c1007024020420b000a0f1300002126005040c01c84902c000072000030010342d0340701d14000c4c014405140841c00081c0201d441c0c111640d1030344200000150103e1a100311b90840300f05214800c040f40b00d01604114034181095150f60708201850001c000c0c060000200e171505405842c00c54a49a0340d500a0040a41c0040d07240c943c00d1040718035078999451a1100c0000d40406010052503400000780c2d10003c14003004411040340d0b0180503200c55680d00d040c21002000100e030042e010402607101e60013030f4640807040311600749040d01c800e4a8a01d002c002c060b542e10b43c214561003584030030000455140d468120b9144910f411034010140c081c01e41c0f07010401c1e208e036404203000750351040e0b0903c000740e90041110000c0c0d4611030000280c949114135011807c90f4442d20fa00c003110310748030511482c1807444e0482407040303004065010f100e90382d030281c0300b0840300d40c1c7c030480d2010392007270044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 15044314 1250 15043064 15043087
    0xb0108030a02030405040c09030b0f0405061302090f07110607110c0109050303220f14030d050301050102190204110a02061b04050d08210c0c10060e0613060902180a050406050105 78
    0x5002456410303d488c8070a03c2e205d43d50501984002c0d0340e18a0384510350410041002803c00c031166005031103448e600e010270001d5000c905604c802518281c440e045540000d035000b03101c0c0c0c0004540d80140f038111049403c0485026003100d00b0003507034401038041d80740305100d194000d4080804681c4090021482d10748024901c6244d0b04040140000e5a03001c041c00060070b00b054441c1501030f01501e540c1c80d602c19405800c0600e0691060043d41c18002c00780010417090380c02080c0c409040b4001030340e020554000f44000380003410314995400c2c4041020541c420b03821342c0081c1e19881211036840042e01c041e000c00851102d4041c920403960f100c0b070007035003842c00074500300041c0c241c6070004000002c1e03441c00404802c501c0b40003146e64034040100030816a8110204025100b0b078110564404c0081c682050281004501e000704002e0045207849140006903142c1c1d8448401484004021525103c01d050b4201d840c1c40d02d0303545540700340d01e984004641031a0521071300c0308a800507141c103454a0000540d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 15045564 1250 15044314 15044321
    0x513020901090b12100b0a092c0111040306050603060f0108060114120601060f080f01030f02061b0d08010f1d060f010908100209040e0a02010807030b0d02120304030b0108030a0203040504 82
    0x40f0303900924030080110341c0610400c03412400768010300010030000e04074010f0225803003140d485500c3e40380c05d25420840344d070b10b0900c21900315810741e612250009544400140500581c100316540c8680019000041c814542e00c03060082c10100e0a990300b40e2681c00c27644c40541400e006414841e0045001001170790800080480500c20141204910303055030980b9a081c80001d0344042c010030034110054114980c043c1701558081410400c0c0c0c070b075650454855291100c040b0310b0007409900d0004050060782d140400200c0210315460890315943c40c01c0c0e0700100005801e205002c07041c014058003203807820341c41c0401410800455031503403031941d0300c0c02000310b0150b409101c0384c1400101000070410400500034004210450200940d84189100600c0708480704001c039090300f50402040c030070050703034030881c1a0b80100a503d00030400d0300d4100300050680b000d40d07600951000240c03041140e400310220240007100c2c0107419560941c1c1e03a5107102901d030f201710320650703005130410001400702d45016270 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 15046814 1250 15045564 15045581
    0x30201142a0708060103110f1507020f04020708070f060c030902030a0f02010504030b0c07030e010f020303060103050c09040207150b04050c0307050c010b0d0302010209130623040e0d0c030201051302090109 90
    0x1002c4681c4540d0350300d411820700b0000c0c0c1066a0b03042140c500f20383c042c1030502c0c4c80034000005071401c0b042c481e5502100300003401803840080c8294912882005581c1d078a405484c070740c9421280c4c455035082c4924100482003e03080040794400d0600d0400c800c0c8500900c151800ca80d0003038040d1114417003c0c1c0d80c0151900c107811003281484028000400483c03500c400b0684030f0110014039a607100c1c40b605014144c402800c200a0411400600d200c80720395000c002d89030002001e0078085441d88424204075010f020342d40c242a040351010a00100740082d14810a02c02e08c1c20100c10400220b1320300c02d00040d1501120a1030300c405c0100007103510b181c400d800400d09402002c00005110241c40c0000d050030086440c1600180c2d004541c41c0400e01d00b02c1414010500001e604100261070071042c00ca2a02d03180580b4009403e10180b252050303106c41c0c110710b42401d80002035070510100d805d00034002c8203008900340c00640c030300000524000700704070701440b955800600c401000da02e8010010098034840 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 15048064 1250 15046814 15046897
    0x120203030706091a0123091308030a15050a050109030210020a020405010e06041407090605070302011103011e0602010e0a08030604090c150f0306230a0e0408030103020114 75
    0x801c068804600301e44a007440c07180c4078aa0100044280120905003100f060300b0a811841110044c2c5411800c205c018440d4501c0c1135031416400d90712090307803620140010300c014007581e000008000046099074041c201e0b0070025804c9652594640c0213104407004c1a00400e80841c0b0b40381c10900c05481d10003400c50143e8278034811074141200e140e003c43c0c06d5542c2030344140500030f17441007801213030f01d01401408090900301da162070313103454480c0e00100290214480d010034042e0000b00c9406141c400e400c0b483e01c0f03070481c008850350303540e4441c00000000000c5200c076041c8200c0f424041551403040c01406041c015400003084e0588207600d40a0480e40003501441d40a41e0350203810300018071f484001d8006001e000354030141c000c0c030190042d2186142410f104101458410140200c18884406001c000010401e00180b4070b0f940700801c5078040d8a421180c20105880108400c10070307803000450603240300382e0780c140c080450504024014003e99189844151051790f214040d00c045a038400c042c0c1c00b55 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 15049314 1250 15048064 15048067
    0x306010603111606050a0c0201140408030c04030812010603060806040809150d0905060610020c0a1203030b030f0102040302011701050913020102070b0c060f010617010e100512010509010b01030b0a12020303 90
    0x3c07002c0640082c9079181c02103604c20380759010069640000c2c400c50a0110700c81c0003d005401050307211000307d200081004106410100100703800031411415100a182d11058041e80c800317141c181039644083c24031841d00000d080100c00b203407004012500720300603a4001c030154105a241420400f5504850b0f084514140050204000410f6180601c810050007040078201c242041c5041c0100100b80820389030a6500c45400240252242d18080c4200c0708600c1414080c0d4011f0f181c1107015003160107060754107200b000807004010406500410407a1301c01d0302c8100c1850103c0b2408901d164091240d031b648003c605002074403d035241d6610a5043d0710510540d004c0c0e649890f449441500041c1030700c192540440d08004001041c100c40070f02409081c28105c1000700480300c0b20003100c205019401d505d8a1a201144c0740800740071910018141c000d01160040c0544050316000382000c8500d484503600b044179508255010303102c0d40c803035128060b00703a1810b0350804040e5140c40f1407900080340c05200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 15050564 1250 15049314 15049327
    0x7051b060f0307081506030702030a080c0702040e060a151211030c060f0d0b0906030309060a0207051c03170601020318010c14061905060604150c020301060f0501030606020c030601060311 82
    0x3600780c002e510901564a4444c02070600221600322240103032409400303503000300140101241c000096800034511407401c030b000c6640c4c00c2c0070803040b400780540007508903041103400c800707203480401d0781441001d0040c401c00441015160000c011002c51080c400c41c01c0340384481c84003050020b9111150398101508451704040342101068203a400b00c7c50b8140245070204501c4c40703040c031314021300030700000403654000c3c107040c0a0000307a1a889841e0b0b1580c13041d1000224060200c0c000e00001e0010b10000703004800b89400d080c400745281e41c030020120002141018003850020352481014090001a0300950903e840c54641e0803115411100160510496120140c000380d01d0a40c3c14180010701030182c00c142c20824040450050250104645641020200301e42a124030003a01c0850302c1c030b5109949040c2446005480b281e801a401035010350801c0300c0440d80381d84001c0e044c1c049900c2039a040200a54510049807285c01500401b541030700000010400540b20b5001a6200d00d4048051440c051 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 15051814 1250 15050564 15050587
    0xf08090f1c030b0411030a0509120301030605060108070314010308030c0f070f0308010e040809040506060d02031003050d1704060b0303040f031208010e0f06010f02010e01020403051c0507051b06 85
    0x1401011070104000001c40108005541030040c2c0c444400306a4040c0500f10b44240044160b0000801c00d0b0201070f03460000804a400c20000440350041006500755a035850f0301b4004041d2208441003804902d00201044800b0321910a4406e40c030740401c03c8071843d90850343c4042032a80040c24516800e0803c1c884603448a002000a062251003180c1c1401ea00403645005880c3c0c11059021404e1420001c0800000c9003664080b101481401c8a002038650b4a40000400c20b00480701401e081d20300c084108243e24019220110a890003101140c0d051086030300100e5140007601c100c980280274440220700000c41c9a0801c81c00d44000800352400d150700d842d4060014502c940c02078a015608100c5003d29542020400e4050100c0d0381210002d80761085542e007100c0301c0a00090b04010780ca0740d007000f40038400c0d4044845008500003c0d03548544d2814681e81d1030b11240c204c00c155100450790444240c1c0182c0440d60b07007551020181c4514114452480507102d5540e4982da0080c004008584e2403c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 15053064 1250 15051814 15051823
    0x30a0e061905090411031b0a1803060e060108030901020a0f141203040b0a02070314090a0b0f0406020c060909060108130209070f030f150504020901050405060c01020702010219030f08090f 82
    0x4040702d6030381c5519403d4a604102c103681c2c41002e458483d0108200380a0154600e24120700040340e8131041641d55240c94504580e882010000e900c178081c011034000c0700300400c542201d624022424100c8a8036601d4441c0c994682c4108009a400b6a01074030074000000c401c40340d4240c50718000c0c1451103a021101c3c401604004030914a0028807000208000c1000215030039141c00035904102180ad100d1559005000341c8203d002482d114079011541a81c03c0d564110104080c05010b000c00783c950208000590840d00310b40652001341c02010620352907401e00c0b806aa40500004203181210f03240c507001503a0040703000d0000003640340c11130780c01c0c0c0142c0c4980c4043e90040c1034030b5a50101202100b20010200c030412010b910b1f4090811054880780d4610340340420680701304981c01a5641d5080005a032140710365400745410610101d01500000410340c0601041d82c000e03001c0d18100003291030103d41d01c540082009011650750b00b8040d9100e4406c040565001103858102e4692940300c00b08146072 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 15054314 1250 15053064 15053107
    0xf04060902070506010f030203070b030c1903020406020c0301050f0a02070302100908070303060608090d110304081605041103090703081605030d060602070f030309090b01020a02060a08040b060a0503030a0e06 91
    0x403503400103403240402008101460040c80c1d203040c801d2020741941c3c00603031a540c1512441c2a458070110101382800315a40403200d400c00010090b020107218100d010300a50070a204181c0035009280d00c031081030806000e01c81c445d0a1080c40c41d801c580c1c3c1c44003c08025004a01e044d421807003002d002c1405003041e03101740441a4045d0506944a407a1480d004003500c03140c2d000f44081082c50000d21004040015011204030010708100c20805c0184002c6455030140f984a11030502c01c1031501c400c00c4c121010004160398007a00c040c8424020107070440d40701d100607220495103034042d207410404560141c018050031040314542c2061981c1a48403203146070031401c00aa43d060703035a4000c201b0150100016001000381551030744100346191809400e000c1c480c800c0107401911501c1d160b0250f842481410641c1e03a00409003500c45894010080c44044101e400700c0c0c00b00c0007080415224a4045921400c441000f0000c610b400b0b19664120f49a4040e81c00e803540048060151131080e09003070416191 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 15055564 1250 15054314 15054329
    0xb030d0302090405010501140a030903110a060207110102061003080c011118090603010b24041706010608060a0e070f030e010c02101401080705060a0903120809100e07140f0406 77
    0x8403541800c080100704e0b641070b4000c4d41440503408242c50450031f540300742c5070a4011410b000031720002c1c030f09043d1101c1070480903410071801984100010007010b076000d0812203008903105080c54007010010b81c0d54950a4518100e0825401c00c1000000c082000030103141200c9800414160031030900c040b0160007040e40581005408090601e8504001022652040c822402071002d000000003003090f0803880f4000d07d2040d0000d8040310188441344085034028185858014083c1114034641078592100703001d120005500700002c265985061512517081d600103500d009159216440f00342d49459503c81c070304c0f00f030603180c160041501c10203100d00300045000350090412607403511520004c07500300c4802d4106208030000144042080001d40606890003640e030301c0ea83d4442c680c025212501c2640c03004000f10503510000550301d0b803122a003030242583c00d0850b55414101d54028050741c2031fa105240c059444807200b0840c01810600d1040382ca50090a50780d10041d041c00490103481058003d8076 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 15056814 1250 15055564 15055567
    0x2030a0c02010509210d0b090703020403050607050a050a0305070c0c09051009090b0c0322030c02092401080a0b030105010e07090509070e010309060e01090302070504111213060b030d0302 82
    0x190400c1d0280545a0721061043c003901201c2506010040c000e54101e009140c01d0360049138864504c5a03690280b19000c0d4000c0031503040389444000117010394800d01045a5900803500454010cc0c010010f445500721144c980031308111110b40c084008010042401c01001301640008000c0380044403000c02410b4030721800320b50341c540003607000707614072069000402040c6019a0500815110b1513019001000e14020703d60f0398459402a0880103616110389460414188210b010944c021003c03244861091b80c42c13404603920592a00a0584c2a440d0008044281c1d40f0141e00c82d8440c1d003a0660001752850002900109180844e003100c000341c111003600412101885022508136180c01c00804046070b4809051600a5004011000c102d85090600d61502154000c04c0040d400c003d914800390f8000304041c01d45410000e507a58403d1081078001c03460510304041d83d100c400304440700b41b807101c07601e4460307500c2e15070044640120003001078810360707618044840c2c1c6980c180a200c440366256640503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 15058064 1250 15056814 15056831
    0xb0a0e04092102012f090d170702010306060f020a0204090201050c071412030f0f030c04030212030d0e030301060e060702030106080312041202010902010c1b03020301110a030501080105061c110402030a 88
    0x183c2120f00442d1130300c02800e13030300c09025a003c1d400c2940702440d01d1400e0780d25403291b80070008a4448031400a00a010a048802020140d4104400b502c01c0c58002d9a0170304c45c1c0740d5165003d5030700c0004aa001c000581100d114100581025005181c0d054818541685018820308040d030528204e5040318900000a0030444424030340304003417003c1c916100c0003851074240e00404001580c42100e2020800c1040440090220394030702c01903400568020740702004101024840984035031120301003181d0b0a180c0884102b440300d0010540c1d05a8241d0b86074040c034025940d007000a240c0059070704a906640700e400c0403c611b0028005440e82d9100c0c240c104600742030520340702450070500003002003160f00d4964544050b0382e11080003021a41c0014100c03510380029107a10b120038025400117034041d800d02e0707000b1040d90200300081c421a01590f81c100003c1e41c8a546190036204152402c941c4100c040f141c0768085d4481d0040a100306101c2c0e5004150540da03500482d050360400c903003501d0001e139101c610 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 15059314 1250 15058064 15058067
    0x22b051b09010503150106080907030203030a03022a030a030e10060f031502120105010c02130c020309040b030106050307030204020c030408010515101107090b0a08010203040c0801060f0b0a0e040921 87
    0x249003d03010071406494050481c03050b80c403100038144107400401669401003a190031050000c0d101654001d002d0320380d124000500980a1342c01901410f00345154160965204110204c10620079194080a1443c0c4079041404030040c0840303c403a240ca83c01a0758101440c45542c0c07140c400102400b100000129203103003000c004000c0d860038200300d880c4c010004140c035454002a4281903484c2420503818030b0402c1d0000c283d00d0341d030160749000c90318a00051101e14540000140518004c00c030340070311224a20805140c02c2e00c0e00b5100b036940551082c2800e1005181c940c02800701282103a0850341010f81c0da100b09800c0d143d040e12082d50b10008240140c01034140384800d410342c842181070100c10b42e08044a40e982c0c0e180c2034490b03000c0c3d0ba69140802d4400d6619504000011704d250402917441e8100b50403c030f400c903442441141c2040d07107030076030000f00b10240610150445112048060820580000a440e5000e10b41c00c903580c800c1d035030010140011300700c0750303d081c104c0c2d9041d44007118600d50110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 15060564 1250 15059314 15059329
    0x108010905071e23040e060a050601020102040f12080c070b0a080a14040f03020304080d0305010503100b0604120c03080d09030f020105060d15020c0607050703030b0904022b051b 78
    0x150340f030010a11a40c02843c80041d816800c841c59038440201c9410b0b85400b01e1500c45155654035481410407059941d94400006c0711801000105001c12490301d4440c01a400c030b00c00c038851400c501145200400140004900180341a801030303207494034085082e500b650a000070f64218004402003c03400c2210140d00000640d4003011140e410080c04d00c013900302c000c03003000c000d000400943d01000200e04161080c4242e4004011440485010410181c009000b9043c00d016403030085c41a645601030314a00350080c6040351801409032454641803148240c2d88000d0210191050010140000000b5030400700a001f41c203441d080000d4246624500101200d103041e581c0000c41e8101800d000140d03548001d5401155488064842c280c409446442c01a0050210451242c040ca104205281d6046001410f00314425a03082100c3d880304010860200002d4031f01a40003980302c51080c400c003c669201842c103044810b034041c0c010605d43d58082c80c0000404242000e10b40610901641e803c00f100d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 15061814 1250 15060564 15060569
    0x3010905010902040513090f0b101701090b0606030411060a051b07032a0302030a0b10060807050f0f0d09080c0f030403020303090402131e0f1e090209060909010801090507 75
    0x202e0640c5400e1802c00082c2c0c2505165100c25119642d80c50720604000c1801c42802d20380741c2c8007104001710b1400c3c8030000301c0d6046600c0b55804924540b4011500d038041031190500700ca60050040e410358640506010fa01d4200500c1103aa20040b01d1032a191a03680501a04010405036616555a042c8900f01012085c00144200241d03000c5241400020f80c0340a4041e06400701641d00114035018125500035008070354000fa4240c00f80301c01030414016082507040c82500317085481c1ca22260380d580c0440c0d0000303045440e0800500300340001d008440011004004150424a0060410f00f1906c071203000c0b0361010340b00326407403c00000c03020034060040c0100001010440c014500b45441d64021a890307125030024a4030540e40047c803110403600c002c91080c0904001401e01c0d078030410311407500b1034aa09500030854025590000014801e02e00b54454007050862800c1c00102450705a00c6006500700020b226440f80c401d001c0508951180c2107468000d01040c00003081c00c003580d0510504007000b94 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 15063064 1250 15061814 15061829
    0x1050a0e0d0c060b0114030109020301030303051003170f07051b040b0402131406070b010603090201080f1504050405010b040f0614010203070807080c01200a020706090807030305030a061a0301090501 87
    0x1645010080303600281d25100564000f080464002d08040048980401c0c1e0303048000c0000000c0000310754014640d002c0c505991098800300130540711070551011802c4203100c014041075510000c0032038401080c0242c0000841c0341c0949042001581d00e02e401e00d582d0b10480c0350350240310b48184045e46014081c1c030345401400da170308524200309414034004076100e900521038083c8010106a2050711840704480401ea00901507903550f58560b80010040c01c1c0c3c0c0d007401d0340007412450100c2c0010b40007442d101e00a40704580d10f0f01d02c0c07a40400a00c4043e080040040c3d605540e201d80c000c102d6105ca008546c88030000380c1d800a50541499485200b021103d5121411548180608030014250300100c95038940c0005400740c640102c42001ca02500070010b0540c02544100c03100e010066030b4030050240403806409840c105622410304540c0d4010714442d8030100d6101003020004203004100658026a4581c008680f0640340e01001648552000c032204a80c0c0000004101d000000d100701800740c40d40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 15064314 1250 15063064 15063073
    0x20702042a050c070603180b010b0706060902090d030c030c0605090705190e06120f100204030506070314190902030f0703030807030203090c1e150a090e0613090201050c070801050a0e 80
    0x880b030301d80c4da01c0d2482d000e150140f642c0e403030102c00c111000e42c48006903990301c825003513819038644072200700a41103490200c03106401c002e40402c9500c414025242d0014000c1d0a0000c2000326860441c0e0200344803000b07030300f44150b0303041c41d40104001d4003030188155801e00c01420464580410310652003c500204149811030f80c106000020120f21055040002110021095900d010115050807c00e201300937142c400d1104018128480d0303005801124012001e40d170301d6607107411040d0155800c0c107100340344559002e00002c130b40c501c02038070112156041090004941d94a580424a0919081c0d1980c0c050313440001c040041550000d286903010005140079415803c118000b10b1355181c00e44e408901c264907550385a100b40340071071008600b40c01d005007188450f5505040441c8903a100111060002e034400402060b01e40b810341c00140138540140401c1c00030030700145400d004180482e0224100181082a84010760301082007001070113941000040b1070030503034201401c441c0d03800b0324528036411 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 15065564 1250 15064314 15064327
    0x60e0f09040807020303040b0a02011a0402030709090e010e0303150415030302030f210a0f0e1603060c090503030309060105030c01080702250503030f09030106060503060d0807020103020702042a05 86
    0x1036000c15290031a510084280d1520454070000e03080d030086070040e442d02d00c40461803411203581500302807003030b146203014180f610016000384000c0e0311049070100041012800b0400c0304203120750002c048400f10600000b1951000000c40d400d5a0042d41c1c88440c1c4160401c00c590380e131a09100701b195008004241c4208513103950790107512400350040c4002c0990020945410281d50000c00861041442d0008080d0346090340c0f079040100030501c2c0c9101e00c03d1921241c01410b8400043d05080c0b03441d110184c4080d6455580e41501034107400c00710500700480100d0001d02600d040019500603c1c2c0c01c005000f0942c10841070501d481a044955030400c60031400b071000c05600070800d583c03040a20700380b0211b4165950f100c4a1ba5010b154003041d01440001505498449580c0c041e03e460030040b0003c2c05030300e650303c03000c40d80d90006560460f8002d1292001a00080b0444c0c0200007440c4103060140c2422420340004003140c90890341c9001c500d03030a24a20300d5900b035600c61200f00500509080d4140341d03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 15066814 1250 15065564 15065569
    0x3010203090d08060102010605100c20010207090209031002040303210204060e0405090a050d0302070b18191509140c1f0c0c030b0a020405130b010f0305180604080301060e0f 76
    0x841d00710590b0705201a000108085900c01e400c0203011b03010203404403002411442c80140f2000c1c0c00a001d0315140200d003001850320000d070840c4601d03403c0581c01880c00074108030841d8000d42c09203c4c1c40354148103d0921503060300c41800940000d601030340307070a650307000c04204081d1180c141e01030026031584101b00511032590409150446800305403000621556000101840c2810050001c2c0c51440760769102e4201551507001000a9482624070310303182e45915041940c10101000d00c207125030030071003000d03540107080311088449501601852001000c6c2c20311140c104d9644180c2501c1140404070070030304200d010807004130b03109400d03284085444107860308c0ca100d00311600034100400120465003001d01070110300d6003010759040040d4000c507007080b901a0009502911616000d4002c40c10040c040e5083c52082900304001a143c401c40140c0f400021401000024400d46600c1070700c05500340c0c82541000050710039031044000a0343ca5040072406420750071100d000b940308100240d080c0c809034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 15068064 1250 15066814 15066823
    0xc0d02061b030403080c090f030601080d120b030601030f081b0d0e0603060108150d080c060703060605072604030807030306050a0b040b04030f03030b0910060e01080f0612010b0406030615050301020309 88
    0x100046d100191120102da000030381da00242e03460290715128010022483d5100030844004400303164443e14104210700040e00103840c0c0c02e42c0c0050b030641001004101040c450301620041610811980e458411102103c00e640c613241e0403500c0706c41d8000b080c5e0200c12504034101b0f440982d0219620b600b985400400201603041c000e101e4004030060356510215901d50945980440354014001d03900d0711500c2c900c2c2e42c0c3c0c070395007110507a0019080480c00101903000342c08031071a0799005411700a803e0348000c0300580701c1070035801000349414100000008100707030001a008241c400d5a020429034503010403c44107c0032a0040103600c0010070041011080c184121011241d2060a03d01481190b00b001e40040004d040d101d6005590078003088003850b899551282559026100c2001504400004540154040310316042d040580008102d440c0703485460031300b04014400000c03d10109010104040d601164011185640c0b1781c042c5610340864604030501a24054008500b1407030724001d41a0744 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 15069314 1250 15068064 15068071
    0x723040b1306030b16080105010203070308060a0e0406050405010b10091403100905071802191803060c02150109090302060c03041104090f020102010b01030606140a03020c0d02061b03040308 83
    0x659a4401404032500c40c01220904a07860000c00c02c03660740d0720700342401c0620046500710003001d09424480c1a4038001e0240070f0603120181c0c002c60500e615650156659003003d0802d40d801a00b0b80000144682c1500500307124620414000c200d9081a14005080d121205c10592148010180c8204169888100003080381c1d0800c010b222801d907042d020a0600805612a80200e41000299000e2190000e09802128611a4801381c1c9000074032410080f400344000c844100c441140c884199a0311607801140c10580c01e000107101c19550ba5600c00880300b140c1011009608400c0304d21005402c0070f90902e004001340001401071030510341d4000d441e183e00900800b5030080200c040f601f4003001d2003c007034004102800c1040500c204d410103400d130700e01c045001c070f00543c01d0040c0180d071944a80180422a0001e03102d04100289409514800e600000303684410075500f80b140491000b000c00c001c60b01c81600c1c0c0c0141a185c180301402c0260741075002e20303500714104204248800298840e0b0501e62 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 15070564 1250 15069314 15069319
    0xb090402010e01180e070c0b150604050402030702010f09061505010908060705031f0605041a090f04050a090203010f09020901050108010b0904020708070b04050d0809010c05030103020f0316030506090723 89
    0x241004081c0c0344010019040081000401c5c800c1001c2541c0100c0301c140c0c114010300f0301103813540c0c0b84010301814a80d070310b0503a504001c0510081196080a0300a1030f0050740c1c6000105450b0498008076089405020301a2180380c1c850585030506162000c1701800b5000038030300341090a0410948544e0b8174406040502042400000511010708400e202481d0300d1400a10b403072480c2e51090020b041d90407500076662042140c442d2107240d01030103000c17074220b114050b000c0050309461b4030810005000c010b202c50626621007000d0001607400f88507040b03000904c40c6001401d098640180502248140c2006040c4080a1300604c400000c80c0180c90b0790f810110341c0940d0307904240c600202180a10080142a58452014442048404540101c00b090f0030b40e180d0625075038054a01e4203aa180f9a010000b0800403c011b0015041c060310f00d074401800178003290f5a820071070410880c4540c090f40240c541b9000b08007402103140090061700c1c010304641c61713688010b440d103544114054012016051 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 15071814 1250 15070564 15070577
    0x1170405070503070b0c01050709050d1202011d010504060b060a0909091a1e0a0213120f12050c060a0911010e0a03060204060513050405010e0708040503070b04150b090402010e01 78
    0x1400c0000400c05107010381000f6050f0342040b41d44441001994020b0440e8003215402c0c0743c0010701e5503202e908042d08480c0020000148401d054a500d05025000c2198200710b540380e14286d945900e4100d0840001c440d02d00001038580f40c982029021106810301031481000100101e0222075880340c03641050b00e2540078001445951450621410380401e800c038441d44900000b049044600504c42c1403440001c0c21001c0b8451b134500390030400703c0c4140c588c3d112452100510601504020a02c802441407285e4210b0b003000e0010b807680840343e55050007040004d4000a013000e0742010910050f5000703080080288840c8120360f0700c00303481040381840241040041e05c0c24144035641d54103000700454008800b10340d22030310740da0010034075071202403290403240141d6000a00c500341407007090704883c2c1c0c02ca142a015180c001045415640c09003054400c0d00c401d200c8140840c61400c0740c00d0280b0b10034140301782e01603801d1405405031805101d40714072452540c410000540d030441461148400c091a181 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 15073064 1250 15071814 15071821
    0x60a1e0f1b0b22060c030209121507030b0a080304170d0c020307060e04090204060303032004080c060702031f0b12010c0801050609030a061e0e03040614090103110310051309020117 79
    0x100c400c2c00c0441009880c13581020b80d445543c1e0b0305a401010b80030400d641e46509180244c0360f255a42ea0700e880c0c3d2014800c4844006000544642d11002003160f0090404002651307484027a442c40d0001e0704401c0000c07009880901d0000c10410404c140309056050141485010307400182e00c1b0101c178400c440900070703203030010f40990307645510201c0c84a40c020400c028440e142c5c2001001040080803001800c4040381ca171060079940c20081d1001c50b410440108600c0702d04c0024403406400041080b6018400c08200c0d460b940000503c0200d000e1003100000342e0408404200200e80c00710012007013550f41b40000d204080e0798840e03820b6064444c2511070594400c02d0b2000f00b031420184010160000f1319020103030f800c0c010420b81c41c01803030300b410301e042c00385a0400802c3c03a120f11440c490380021800140700300c1c191a2580e4042c0c201e441c0141000141078800b00011403207644111030b1107004020b004000d020b40c1c07030413501001e0b07984052201088112469800a0322200550b007410300703450f0011000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 15074314 1250 15073064 15073111
    0x2070f1202040b13060801050108151501050432060408031603110a03080603010506010e0a0e0c190206100e01050607110607080406020d030b09040f02060a1e0f1b0b 72
    0x780503c1d00240600b1900604036404500800b01801131420b5542800000250701e0750000b141d1100341c0002c4000110f40d2a1408032501048000388403506101d014000081d001751644021100303140c0d071752880070240b044807202103609544145840d114140c18001400410000802c3e01c0f00c1c0c50b9240c048081044690800b584c4e80d41e85089072281911922003038004040e0702c1201207020784000c1d4001d212545400c0b006440e01c00000c10b8a54008111900070418081010350f1181c121404401d0240380000911140c04400300360444803001d6800750041c0002c91002403400b0000b8540f42c90550113550401d40090510b00c5000406003107460400f80300c0c00d042d42d07090211a0070b281d00801e0955a1a900d2601a4031103a100008402081c503006440304031b420702044080c440c41c5d1042c00c0403c003040e182c6c20003090740c0022990000304140a880900560f5401c40064541606900c2d212402c0401c0500104030005c80c000d00d43c1050701643c04031002504482451382c221104070402030540448540c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 15075564 1250 15074314 15074321
    0x308010312030e0d030c140c060601050d15030b070809010603050c01030e0c04050109050601110f06040201030905010b0909060115020106080304050f030a1e02090601080402100807021603060e0d02070f120204 91
    0x10301000f203009580310a001e40b40c06a02c20000402c02d074071400d044441e08540c0d0940c034050b8403012038040c0c0003200080e1496100f04001c116280410030300041c0810308204c400c00c00c3c11941c00c100c4d2401e080381c051003040c0e80c01c07000140d4031407481c031b0080c000141182d95858484c1c04000c10103040c151140d0100100980500c000001c4030030181040000d5a03440341014040d0030143d40280c0458188960505042808515400108403041c000d01c041d80780c5500441c02800710503001e0b01c0b155a122106605a41c0d460003240c080d414500042509504002195103542c4122955130b05580c5006030400c802d00d008800e0b10200c440840742c030701140002c44003190608598440091400420001a00d030b5143d00911000005000b034070000038a42d0760340c00640700c000b025500690f0046103180c00d0203100340300c1d12049500c100b003441507900700140c4d160f40a0308080c19400803a0510f46418106001c03001c100028151140140700421042d840d001288403080c15500610641d89580403509040d511181c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 15076814 1250 15075564 15075581
    0x100207080f07050f10050307050306040b0405160f0207050109050909070b030108060103030f030603110d0206090301090305070b0601030507080f0903040f03030509030609071406070501060302031207120804030801031203 96
    0x806590304208244240754aa2460b40640c0703200b400303076140510003414070018400210b01075403542c2e451504c481c0c0702580e403070704014000d42c1c0c49a2501c610410355199805214081e03caa12403800078109800310246c045001c6182c1d04045500041040006a90121902c0b0448406503800213040d114070452904003e0241c0102032080000000003410440006800341204c0c080e41e601c070b16a2034400ca046055641c1031001070046144070b902240c0c1441d1914410002e02d1004229905d0040820b001c2420b646c2000c0003500480c0c0085a400184181d4140a5074804001d1030200302514143d42c0c090720401e005000705c0d40407000d032800944980e90800445014011a410703c51141d50f072841d0007040350307008502060090060b100414a90800055502c059030307050b016009030407032090f060002c3ca4101c0d401c1a1569902c400000000d6282803003601a85d503140c4055503a070300c0715401c0c0041d42960412504d001c100200301000040b9501c180d015040d02d83c0b207030810f0020400b00408030090030046 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 15078064 1250 15076814 15076829
    0x1050903032802120f0d0506010201061503060315050408070b0c2203031808072702070305040e0106090501120b0f030618010608011506030c09090204030506040b0603010e0a02100207 80
    0x308000c02d40c5440458001e00700192030b03401c0700c42d00b14000e910034095004840d0400d21041e01840030003020846600300e15808013043c0b000080b5207940c0c4111040010302d040801011035074400c418020300ca640e80c64442c07050030240e81031006041c181d0312960386202d0088088c0c882c0d05c282020400d4882108202c1da6007e0450206201c0101c42c0010a48908410710044010801e000e59910744c0c0c001c020315241c00c85004802800c1e89a19001418042100c225030800304225a110a0048a402440038040303440c02548d45507240d50509001002030b04068020000703020102c02d042100342e80c041c1a003154440210004108054404003160380c2c0c07105a030300e460b0325005240401a650060035503007420007480c48002e01c021941c1320042401c0300d60a0020466415040000784981d43c002c1d04800048160703840d00034825a640e020700002c03030f0419041120181c12030400d120510126964503030300080214020401c141e40d02407038590b0340c070304d410000340210b42c403100c41d03007c0074001e002240003131220 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 15079314 1250 15078064 15078097
    0x509010e2a18090603060f070507050313060e03070311150f03040302100501150203090607030504080f010207110f0d02150d1401080f0c0315060307090e0307030906050f090105090303 80
    0x51411150054200d0045140b000c85070140e042050718026401c58000d0714050064446030300e0b1170398600c0390100014403590a0100800c040b20020303004000800b405003d041500000604090b0000c00e48190b88032610b210fa03100100900105824004820120320111402c2c1c0c400b040440c0f082c1c4081c0502081e0050300400071080005064011800407115017842c2410020b607a00e40100703034040202204881c0050b4806c0c08a100a800e10800074900c00c0c1c001d081007428142d903401d41070b11380641c824000c83c5503500490000200052003501012201c4104c0d000198420711700041a0100480c40c4064031402003005003c08800c0c0142c01c96007a80003003a0248140c0c0f40282d1000c110380000e101e40000c07845100c41235581c1101c04101c44104110050182185544203041e4107840100034099075854003900e180000c110513244101c50501c180580510707241c55142c2009840390140c0c3e444842409030030026003060020042c00c491640c5400d00b4110346424054020901c3d41c09003c40c0201c1d080413 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 15080564 1250 15079314 15079381
    0x603021804110a1218020118030b010b0c0607050f0f2d090306010906121515032102060610030906090803090703021507030f0309050307020a060801060909060509010e 73
    0x2250001404002c03d2500d81e00d07000d08000c10350100b00d801041c060f90078040d414104c01e00540c4285c4400d0711840182040681c17498483e212060906420703403121244480004240098107028014982d01003100d00b4032500341070000d010410144542d50041400f8400003841108001c0c2d07000c43d51540711080316441c5414580c840303c2030040d91042c40351502c60f06c10007000080e030055600404042e80c0e20000020240c0e4081c2e170387c201d61210031501c1c0307030b0340240c81d074030203410000746d00210100950040c6546018088071745a600c1070f4011601528003150810010845540c03150418a000c00145140c001528034850030024020206890002c00c1c6800020a000c0d21f580c0008007001941d008031082e0890485007900308041e4810054000d0109200b0242c0b418000d002e41d2145500718000c400356460031550358000b0b0104560b80e004140450102401030001a13400b145000c06001049001c006003402d08002030115001446280c481030003040000712905182171740d1850710711a610003201401c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 15081814 1250 15080564 15080591
    0x100209010219020a06050f0408011b080609070804121b060b03070815150409050303070c0b010602030a021e0309030703030203090316030f12140a09030b010b0f040603021804 76
    0x51110110900600c100d00400d68000303112259007042c42d90051000e00d0440c580740c4103461a80295007200c1000d00300b8440011404401c0c0201d0001990b82d1848201c0e11401c0200a4002807000e0a420301440098080003041e5400041c80e07a0007a800401034031540d03400e500d0071100241d203d65002d40b6020700ca41c00004200c02900010300c0900d00f1000d84803100d880300368240d611115407a1982107040f02001060044400d480030000b00b42000e08081446040764850520319401a1218400501c03038107450b20a016903142c0060140c29148051031400c04503c01c0250381e0095280c141080d01020b100311070020f40200304880f0360060160a54800a40da404e001c1e4880d0071800c201030007030142a0711940204040803884040c2c0354050740c2c20315000c0c2d13582c440645070a004140802030003058886071050411003400b8144200302641c2e01c3d070045086181000c2200010707800209000c4042c8850350074200340c0c0080c2d07429600207140060300c686c0c14401d410400045032a80c290000c2c40c4c40324121000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 15083064 1250 15081814 15081817
    0x5030f06090f0c01020d11010b060f0304020a0e09030708090414010305071401050901121a040501270203070203120c0405060d02030f090f03031603020403050102042c13140f1002 78
    0x11049941a00c0100102c251070301d89070340d0381c3d440301070041e04003000641c20540a2004a542c056042000043c180f58400108000303a020700448005030001004003c1145040d9203168040c0c0b005203411045400d212a85030f56901400000500c00000801c01004503100c642c003040308883c06d01e203594925652420a140c03950700c40c0c05110445216001e450202c4d50141d0f040391140300d0f06959101c0d2401083ea000001480c440480c649009020021003000307560b50b024450190000e403e20f96080030788014140d5061003841c8242081d030703005100300b03c85543c0200584048082e4625400c40e5581d81c4100c5c06003e201c0c0385c012035400038020504161b0b9484a0b40558413988402c001034110b81c44d6003440700d6031607015501c0c000e40c13584100f0004d0689490150301610903102814058203040d00e0313998040c260b81258224010b41d104801540181031540466402d0f4900c0014040c80e0605102600881c0d82c601c1a402030018050068031820b003540030010101c01c106d5043c00c0d900880301030360b9104040d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 15084314 1250 15083064 15083071
    0xd0f050402120114010506070501150b0918010308041202030304081006050f01110a06020c0705120109060b12060109110c06040501050103030f11030301050d1e050601090501120b060f040605030f06 86
    0x191020079942c1e009010502c1044800764492900007180c1e131070442002160380c40240c080740e05540b12105508101c50f0010881c002d030080b081990340381c0c9046030502c00702990300b00f42c4030440c80c5100010130218060804070303000d9603601c1d048034070414064008207245100c2d035404007007030744162040c40b034403c4220751211041d508125082d50a80703844200440d5006e0a00000e0803150b000740c10f00000041c420fa006105403d002020b9036a0541d40380c00180056402817040c2c0a142d440760000c60030400c80b403152881c4d0741c408035022850708003081c03a51640d51030705015004c1140d0391f076a201d09402a014007a1000402004100c47c014a402d1030001e028003401c0c40220041280500b02e00c0700303d03004070a04440014139000070b40c1075a180400700400381c26440000c0ea030303c8180340e20120202c1d06180b41c00501c01d020300010885945804240000c44005a0001120741c004801e5500000d080d44030103a00483c0c00c50321030741c40140010016006140562140382d2510540c5440500d0100c0860380340d11 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 15085564 1250 15084314 15084319
    0x2060a050c060117010c030c051204030201060510091805010f0306020a02070906030807050601080105060102030a0e060702060307020607080604020703080105010c020f1c030215070e06070c180203041e05120f0d0f050402 96
    0x500d94408400e0342234030049200d20b40071603402d100088040f1400b0411070b510074068030000c14440d540304089500540c081820034001255000309010114421003551000c3d41d41d0303002080690f140c8520f000d101031003030000420700c540008045510030710030060340026140b1034200f04031440d66031400700082c1d4400fa408603080d000c0c25000190340038041c4a454070401040c6c0145203080e00f240d202b19440c41100b00c01943c401c1080c0080809a15035501031449000c15400070720140c20a04009000740328020001440b41d4010011701c000283d00031440390456000303090a4032005601c1c80061506908450455040303038040f0344000c5180304032001e20050f42c3c02a02510140030096080b10841481182c404001c550240034014003402d01000501c00940034006035800e4540740c08503024406100070100c84069008802e00c0244809900c1e108002d40b400c00820140340c00c180c0d503280d01c2d98034440d2100c01021000c64021440a004800c844c02c4130310903041040226490703114400108010741c0c0c203030b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 15086814 1250 15085564 15085571
    0x112050c0a0e010b07030507050f010b091501020304060503280506040c030203010e01030803070c05010e0703030e1002070611070e01030503031005100c0b04020a08011404061a060702060a050c06011701 88
    0x680ca0501c4001c4606541e904414070b0026800e100141d401c1d9072111004804200d0100034480c04980144243c0c82104103100c00840c0002c1c2034010000041c0003e404240400300202d040c064582c2c000040303c0440d000d600f406600c80d0b0312494108415030301301c1e071036006480206243c0c00c030b000c0084c0c1c003843c41800c048038100308001100000710101c0c0802d025800b80400f6010060011a0b0f0001c05142d0021035460f0541881916503642825a080070407071941c254013111040c410144c1045c2d01c641019400d850015412a6043c2d0096071801c01d44291024000c422001310441c00c014410000a0403862904021079607491908554990040710101c402450618010172580b614424900c00f00d83d007a0313556964603400f5150004805005030040f44e0101209800044204081c0240303010781d622549221201e10301810414251000e00e41481e80e041440006002c880e540c0b10192560250140ca0842d1540030683c0240c5161140e8040c0004500c1110000140c3c04910030442840900c3ea40090 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 15088064 1250 15086814 15086833
    0x80709080703020a1a070c09060612090f060e03090a06021605030304080d030b190803090909030405180915010b0304030912080301060305100b03090f070e011217040e011205 76
    0x1079140e41140c0002035010000d82010030042820b0103914106014404d481441c085240c0d4036040000700542c440300006485000400010f904002e80c2e0149150252092110301c5013a0740d4010049042e481c001c051940d145440d0400d0a01002030f00c129000142400540c1c9454070b80103035840c40c115102c58050f203114030000c03d55040100c203a83c1121101e000404202d8100f0100f40c2c044c0203801d1500d45c00014082148980d01e4043c0700d208002e140c10700265544500341014026060340c024108070003a40700b00300030000e6440f81d40b400340b50107000400704070858032615085401d0540d02c00403079402c1e032504800400c0d03d500d0b180003140507030b03c680c4422044503580c10180800d200c1510014003d0102400104080341c040c0d044658040c40540354103141e1610307030003651b4407500180d80c03c5400c3c0c2d004030414403542c00200000c001a0031469509182989046a00075004203110b1000784a144440400183d50540d64262400740800705071486a5603151079221504000c0640b05071058030805445 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 15089314 1250 15088064 15088079
    0x50105030f0a03050f07060f02030703050604050402030601061d100e010909051909030203090405091605040b03060109020a05070b01030b04171206060c030f0403060204090c020f0d0e0406050d03080709 88
    0xa00802074070480684a03110654406130768030f0300241080074026034104100320004078540304035102e101030f8030b00041e100c5c21f040c0c5008044450041c80280100e103000300744405070b030340041c03020f04581c404d10323200c080d440c1b101c1e0070120144100050260010318601c02d0701145600114807440e800b2003030340c074068040c0d035600c0e41e103081d603500f902d002214050710100d05210f980d043d000101c805009004681c640a6080c020604a807011030300007a644d04141d4207540c140c1d00040404c3c0040000b2201417081601c40000641c0b52503042c851410029070021324081080d000d6001e4480581c0c02254001407580d42c0e04209001c07030710459007221740345900881c82c118111020150b880000300421003005c00d40e5a0b80074802141d10030f450182c280e220500842c03140300310982c01800a14880d281c05600c0e54a06a4000191014030345d00e0303015500039020141c003143c030014069100c240b040c500384529003c1400810010300c89504200c0d00f00f1060000b103014140c00c1000c041c05010340d0342d80e05501030750b00e50340c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 15090564 1250 15089314 15089323
    0x6080c0d030c021014070b09010516090b030402150a020d0807050a1b0201020709020409020705100b0303030a0203041707050102031509060105120a06080d020d02070602010207030e0d060f0e070905010503 89
    0x4024082a80d00b40d1032005810029403a18450f0814104075004113241c4003244016040f161048034a007140c107041149101c02800303400d0700329a410011180080000300060070010f400e0241045240e40400050295038521400c41092210000201da4030001c00e10000d4440805042401c040303040540030458440c4500211540111300f03a880c81081020a80360401c00840b01400b81d0462042c1003000c01c031084940b0081004200c601801a42d40b003030b03454a5030400715280205485940b030603d1895551301c0200c11681e02c0703003402c840107aa0783d8030703854400d2000700a00c6a118160201149490800038158011030156040300090f0060303044003410880004421101280024814400b00407250029100d0980000542c08086030440e107810030342c2c2c50051490031402c0181d100c1014000c3c1950103014501c0038140302c0c4020342c03130640e03142c5000c2d0100000b040400d01a03c0319803422002d1061030340c808801108246014800c1e021100106030b92210140a00c0d01014548000000c41e4900083c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 15091814 1250 15090564 15090589
    0x50705011d130f02040807030b0609011d040512040608010509090c10030e0f120301030308010801050f15010e090c0903010b030109110f150f030709050105071713090f06080c 76
    0xd10140c6441c03a01030041180705044aa0681ca450710200b5804800d14009400948810f40003032040514509085440081c00b4060714010512036005118100200889402189074580005080d0b00c85285c41132902c940107003440e010001c04a004a09198003242850480d034040781c00c0446a144c00317881503140c44100d4a41c9500c204002c11100b541ca000340c05c080c0c0356a1400701a01d200380b00f149115405c000b1040e010850b4280300000500405420120480c0504102802008545005001101c01d084043c0502603220096001607080360f1107403075007246070072000d003030444541010710003071805401440031541b02c2e5003403210120f600c1c14148100c6041c25005500c0d20b0740714000c1030903c841000c1d003e11f40d40d004041451000c8600c401c01006002c40114040e002c1c3d500c1c5007100c0c00902480040d003006042010401c001340200799002000c8141d0b50614443d29500c00307040c030501d40c079004240c0c8011003503814085040075004081c4d00001c12034003840142c03000892040104110446540e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 15093064 1250 15091814 15091847
    0x30c010c230c0a0b0709030501020309010203070305130b04030507060e0d0f030b0d050304120204020403050a050a03020106060801030209040b101802070c1d0f0901090212010b01141606180614010305070501 90
    0x40000343c01103049200701c181c10180c2d90826600003502c1ea1116400c1e1383c001c50b80801c160390008140f205040c0c7c1403140c0c580c00621420303017440342c425a598078041c03040054005001c1080c0031811030148421903019400c2a64020102c44080c00b440d10050040d10483c946100840e142008001c1607050400d040180227074044091807a0a05003007045484e00c000e01010381c1c01940c03e2001000250080007002e50181c041c0004140d071205a2074000c1c2503d00c290002e01c104003031900100700503210107000741e8229610405900380d0ba17480c5030343c0805200c100d601120312200d002c010210010240c0c1d00410189008910071031405403613185402d000c5030700814694407903c08800103004000b1008402d45c03c0b10b030700d800109402d4800d4002600d00c51901d84a055036035035803e10143d9940e04200040110322035001d01e0381c2056024400844240b0412801808071074403450603800c103450007a4060111680100c080000840070848084894030900044826204422000c142d039805035144c00c04c207a105 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 15094314 1250 15093064 15093073
    0xf040504050a060e040305040e060a0612020306030a06060b070c090b01020c060a030b0d030512070c02010203030c0702030123040c0e15041e11030702070512150405030c010c230c 78
    0x28001030100621008080350340c115550070000c41d1111480c01840c1c0030340d0203640c80c0d03038035a400c005600140300720203440b440c41804141410070403550441e0b81321003102d200c9600142c03680c1e101c1000c01c0c14a02e817170400030a03003450442e001c00c440c0382c000b010705031700c5028004246040317072a071400e0030880311100003103409a4030850340c01209140580c02801821510b103008501c00465034040b0780078400340c1e030007180400c1010802880780c03509440c0183e4400030030314040e2080c00e80b83c0c0002c0d4503031101810000c0c6040c0002240f009545094021404403000c4552501040192500320924003106850440d03000910000014a038007000c40050b008101c554044200d4028050400008119481d07400b5503610581c0020002d00e0024820640d000d040c7c0c54a040d902c5c54502802420408a604107d114a034144100166414000f40c20480b80015015003051900c80c1d0901e10310f10b01500589072030b2507003001f607a5840c4c0359001c21618044280011203900f8607c04000039101c0d40650078100c20390b03510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 15095564 1250 15094314 15094319
    0x4032303100e1e07030209041a010c061505060309060f1305060703020703120c020d090906060503061002210403030f0f080f070908070608090c0f101d13050402150f04 73
    0x1002e0034590b4100c00100e950100d9451036407001d40075a00c080b03a40c00c001c20f0380460401d045042a0191515000e2a0320300500c58540f188006002081c840201400840d42e030515403400303400106100002d000c008003080d440303140000c00250b0b9a4422200f1004809000000c50003030304c0b601000b4a51039a000000e880c042e510090118004c2d00812026410030805a51034175440300700d44200b0744402e6559001d007440b518117901c0504680382c240c0c4000056071403c43e007001004d510000341e0750401401c8654103400d107007a103801c91038100108801c0060580b003009070442c00440c40300803c1224132030b45448100c003544039000d4400103d80c0f10260041383e8a5000104210f4018450541c00003103801d050740103603150003a0b14689506030700108080350300e0406000c3c0c0d1507000c01460100d10411174450043c2d501000c04110030051a440d00028800f0700b14414082c4249401c401051000c090b0420320042c0103c60702e41c000d0701040d1804c1e40288060500a40c0078940d01d4200c4150141203840c01f45400d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 15096814 1250 15095564 15095579
    0x20303031602072c0106020d0c0f06090515040c0b090603060d0309080601080a05010e0d0504050112090605040f020906040902100e060403020907030209010914030d05210403230310 79
    0x900c200d4041d02140540f80d40465008491214414860203002c0003003122403540c3c2440c4a1210183c10074019903000d40c1c3c24101c141e50110521071001d51003920004805400d00e8580050700641000402c0d501914002d8000c613265038081300c2c80f40d0301036204000c2c0b03582d940f401d458441c42081c00d401e401007800c00005105040055100401502c43d1419914803a90b0f405054100002a00100000c0d000411404207002090041c943c1e403004000182c16210400c0a026200d4411407003150305101c6810751158031a00644d02c03140440307030002002c1c042c51805240103052107108500c101c1c031440c0802e0100701c0e41d0400d4828800c040354007506041c56403c0d084002e880300a070350140c031503020703004000210060712185100343c0100c00c2900e001d41c0350200403002404100c5103801c80728400c40d05034082619540c00040030b2400c9241c600704243c1d90100c10698031540c0c1c00c240c034043c02114040003440201071780985049801070320620782c00b14000ca00c80161003e40720a032110a031b420f031189001d001c241c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 15098064 1250 15096814 15096841
    0x103060504050307140102220e010501180e0406231003080904090807080d050105060309070b0a110d02060f010b0c07030803060409020307030605040203060a060602061302011107090203040c050301060302030303 92
    0xa020b4000c4a08200c4140d03a0700d001500034102c0d0403003903500400c11490403102c481070400d50650035410050b095042c9024002d030900148152410080320758000300d805000c0c6d01001c0041c02041504150034034180c10b0941c00341103e40e110646488020102c1d444a050400c0200c1c014160066500c2c541c1c6d246440302540742e080406440ea1242d0f5801548002620030401000b107903100e5072441d40c0340c500064428007200c405a10a6004003000c2003000303001c803004900182070b1024541a20f80340c8072502d8044a1030958240049410b125207600510702640010f06203103c2c0c1c466210507485680c82e104088064000c824044036160302c40b41d0103000245505001c0e5601c81c501500000c1d144465400003031800600c0e91059550b6550f038030512045d42028030142e588481070b450240415441c0a80080d5242e200800030341840900030b034a0400c681c820380c1c900000311050000c4410243d212030b4280e0084d441594110780300c0000c05800151400c040c011041241c0e0010041c5081d55110301244009 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 15099314 1250 15098064 15098071
    0xd090b0405010c030309050c030d03090b011d070503040c030b01060c12020c010c0305030c0d0203040804030605090a0b0412020f07080115050301091205031003050102131814010605070302100c0807021204050901030605 95
    0x5070250302c0508040b9282044ac2b81364006c0142e03004a042d002e10300b406035000d034042c3c10400c4110400413100361945902400300d5009603d07880c00c26900e680d01c1c1090050b06202c6e1300024001000580001412a804085000041c3c022070007914403024121050b40c0c0c0c0d1144510b102c2c0400c2c404003810000c20302030409540e018140212844c50582c0000d807000880e8001c0350102d964000210382071051000e180702c0c141e44600c0b66401810b0000440d11492111070004000400303051004540503070380c80c420701034419402c91240c11206000d0700d80601b14040c143c00c01030740c202158152400107030761905014000a03250004810200c21042a5007162540c3c0020145226900b687d900080059000d03c02040d2080c800042020600e040441c00b00d45003100810400e0340d5810240700d000d803010407026060441e81541000e40d0703603120307602c0c0c20390030440340c00d0a0200484c5400000344042390086844d41c8038102660980d03e0000d0300700c14980c824003603030213501e13044010350005100040346540107941 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 15100564 1250 15099314 15099323
    0x303010e180c0906100302040b0d060f0909021c1a040b01050f0a05090f0903071505040605010b1804020c15100f0b0a09050d080d09030201060302090a0204030503030a0b011806020d090b0405010c030309 88
    0x40c26444010404156100441e442b03030280d80d90904008002c0d080e0390340302c003504800c1c0c42402802c3c00d030b0300000c4030300314040c41c000d02000d4208010b030104450314900048241c8a008121400c1c030f0942409141c40d00240f042034011000611011a1032400c0c4030b510341501e81c010202d914a840c1c082c0e5441c04664002c009205910041000002144040003001c5a40100f24008111481c1c00d00c0c0150541f03006034000c04d000035040c0644c0039010300810010041820948005858501c140d80b5140b1340030fa07003074240d2404884070b403d10100714150318640c8160b541c110742c100400e0381d80744031641c807e10440c10030034001001400207004a00c0d0040305400f80d180a015401d0510710842c0c80c0301c044800c0c0090803002340c0e565031010421410140c03a42e42d80180d04a10460400c4d20f50745801c0c0d164800280051038140d60b50402d00b201c1d0f070003014048001402c00c3e0031040c1d500c7e19003901958504e003000302500800c84514001070b54020800448003681c9040c0d440d03c40348446a070f810740107048090070855 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 15101814 1250 15100564 15100567
    0xa020304140f061605030c0a080415090f0204060803090102030403060c021c050c0d020d020c1c0602040b0408010506190611150a0c0306090203010806010303050d06080303010e180c0906100302 84
    0x61440208040c00060b044a00a414641410004810480011440c600500100f4004c0003034854200d0306441c05c2e0082410005030503642c5250151010b1644c45101c03001070714100c0c940060200d108025140b4a20035103040101544807a01c0d10307034a020316018113005030320801c41030000a000740c0004541140c2e0707004490140c901d01c84031800e103110b11101240001e1020462000000082003d09440100d60000e40511405d03500700940700c0100705aa41d0268000402080a07200d1581c0c82c40f5400b504030408545642d115000d050709a0721500c2107801c0d41d07003003101088413440c1c201c54070461441502c0303150315500c0c45e004041c4c842103901003e0710000d0040b07801452128404500180c4075280400c80040d280c100040090112401c90b088211040d20500052018100010700b85040d86d030182002034031030001c5558580a4540340c2c2240700306000101c000a40e0030080a0240e0044e00301c00481544004c0c1403d1140d580c5a0183c0141d522048403000300d140380c200a00b0702d402202103442c0c0903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 15103064 1250 15101814 15101843
    0xd0f15020a030b010f0906051801260105211b0d06060611070801020309030a180b070c06030b030a0f03030b010513030f060501080d0f03020901050405190f08070b030a020304 76
    0x441240c22450342800840c0e03e42da4000310341d42e44001c0141e07050100c0e04003001543e081007002042800740d21010311825040d00300300300e032980c000c03843d107407058070659101442e542012080103102e02c000c0c46034501a02032050f022140008014810b0300705a1107200920031500c250114030b560840e02850103400450480c0c00c40c003c180c00780188006002141c076400010400e0600d00c52400c1c100d680000303000d900c140140401e01c0000300450f00c909050b40f6028240090518203511f5074643d50748100103283d00001d10600708252011000101c030700d1900c0810020303484c40d00303141e02c4601c2014001d03c2d10040e04a19000603019910207546a03506261123403c080030201340080741c0000307030401d89a1401074550340e01088500d00a040c09482c2d110043c00f01c0b58000f290280103201d8241007101450b80100d0303010880e174406e10640d40200401130002501d02c0f5000035096500455000c0c400030b00350070203004200500002002022100c070b42d61035503e15903940301c0c200c00940016200320350b0060b512166 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 15104314 1250 15103064 15103103
    0x180b0f0706090204020c010507020f0a0203030301091a1011070b04050f090c0903031303020f030d0804030503091002030c0901030c05040f050111030f0c030d0507030504020d020108070e03032113020d0f 88
    0xa8241c03185d421b00001744a0a0200001e89000e500e4030307003400e241c0d000312a0040161004001d40e4110340f440170740840d44d5041581c15108012003e0301042d00f141031070f0500c6003c04c0d413000003240072070340724025104060384420100d4803e12681c01406c1c2c000c1d002030090303400307070414540581c0d000ca98080704500344041100001d0031a8001c0076405607070581c1300380600c15071a0581e01400000c108034010031821aa600010b400d0180041000d004d02001200140b0807010034001e1550818266800b155645407003840e007805600618082400280b80410b11980103029608440c00c2d01c100c1c03c2c0c40340f13449103000011101d0381e01c410203150560105000144500c030502020b00340000d840b0b40655215000c54210400710382000703188408050a1006000250312920b01001d0300b682c0a181c14081669140c00545400c0c00710750707005030981300002d011140c502011380e10348040c1c40c1c1e600074000740d42c448004030224403420340400b075031000e207003940580060341500e01c100550b80f00303c0a207804030160320036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 15105564 1250 15104314 15104317
    0x15110408070302030c06130302090403020a0c1d060d20062203020111011404030e0d050d02070501120608030301090207150507030501050901150c061a090406020406180b0f070609020402 81
    0xc400066442040c00b032045190078800002c8010054030214281240c161401c0c0c580c018622010340568a000041018580309102c485600b503088030340c3c21a00e6542e034106808540070390000c0407015020101150360791401c0206d007115030350088a4550042400311250070304c8802c00d0050303a4001c00030032941c0c3c001e01c1022a2248841e07150342e03585e8100d030f2440c00050814450b0f030401c4a01030345850040202c990b00c2d405181d4000d40c041c548903004018410200703030a2050040e010b0300b0b0348586480c0c42c007041d50008030201500c1b03003a41c850007070a9000c114001920a1303801400141d400503c0144680c1130380d40c1c00f8181c05030190351268200e0b112014008101d50080d541c460020b40c84000600071401c1203a440b0b80104030160503036160240c10b000081085809000081a154899a04003a5900c9401d20b04805040007040c0b803a26040c00e2030400004c2d4080c0c41900d010511900f1000c452010301c881490440f06040364043c07070318140e0008040250b2051340201c90030381c1d5a40c02e24025894610 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 15106814 1250 15105564 15105569
    0x91f051201020301080106080a051507030e030d09060e010605031f060b0d0605030d08040305030406050a0609060b0d060e07020a0602030405070b0a0203090f03160512010b0613030b060607030507151104 88
    0x10006039a94100305c1254251007941e001140d00794130400008000890009802d00d03803000500d04a401074903540d4080300500032070140d030032582c4000f2414444490660348060001881800104590084009044d00f645e031280703d00f641c584c0200e03181c0050b0042002e01318038003449240d40000c07025100c0c00700c096560080034078610134a40e07501b414080f504040180f890b96101038200301c1817a24140c0d40c01400751000500081c0000c3e04c44020810f4820982c02000241c01e00c000c09002e02504c40300c0100883d003250308541e00b01420302e00001845c0c814018124010090795001c0c0090b505c050700e41b200030b90b0001c1c10403141842840343c001008103203130300900898211903019641d03807003907142000390701195602141d1098100078440c403a108080d07000002112010347c0d41200c26402550528010b184400c3e009410120000b00c901c03039803651804e917409881c402d000c0111107840c0e40c1c0500200340100b03e4010041001003010078007042d0140c0c0c80800c0000540004101e55070b000546c01210303003155 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 15107920 1106 15106814 15106849
    0xe04080301060509120102043005210403020a06050a031d070612020d02072102010507020d050c0a1b060905010c0c0303030209011404080d030b0d02091f05 68
    0x102c05c19140d09080002152501d9545004039804000c10000c0c200da8041d08500241802801001c0064250400300404803507207811300c0302c2c4107420003028040364100140000030050b651361a4100203081560b031225120100d0750f6001d01900d09138030042c80381140307800c0c5000c100403000900c072007150700074030b495100000402c140c0c0c8002e100b2402c80120180c00041c0b080140b102404459401a060342c840d45041c904852049080713a405035040d8005801a625020007180300d400030340364242c80502628802013407903888400c2110250425008e1520003c42000072582102018006100a080c038956440a90b618000c41c4545800001e0078154081070b900d445034810000c20707041603004011595150b0f2200fa41954aa5950034410000b03414a44180312506110844194040d030140440c1015240c1c1818109141c00320758a00d0b00107070341c034400054656210505c100a0007404d = true := by decide +kernel

theorem cover : BRFrame.Cov 14928064 15107920 := by
  have h0 := BRFrame.cov_init 14928064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14928064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 14928064 ≤ n) (h2 : n < 15107920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
