-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4399
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:29:33.188911+00:00
-- url     : https://prove2.me/submissions/1e1fae51-a47c-4271-b57e-7fef85c8ccec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 791007194 ≤ n < 791187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 791008444 1250 791007194 791007197
    0x60b130b0f04030b0c0d02040816120506070e150414010305090d1d0a1d0402030106060302040b030612010b120c0102010c11031905161b0501080c030103171c0516 71
    0x305038010070903400500540c400500207081000101d074109111004440c483c4808007401e56885454034142070395408040d0790701d501844031b0a4000ba50784084000c124010740c0c400050801626585811102c0400c6100c00320b5001c203100f01c2011a000e1000014401030800009907110800c2c5000054105c0e1070050010f90310f6000580e800c408070f40c0c00001c5240c40b03140c600d0311701c0c902960b142c0800c3c080d0314550080c070f54245085c0e049180c0c0c481d001c505203108600c2100240035440c1c1314501103060b4010707840350314030007070041c0049509841c02641282c9121109000010400c009000140d4840084403480140703400c0015001c0b03040d60b081c0124030240c441402c20500c030082500c02156a0302c40d08412282482c64042002c45881c0b0800481c2c0719405d20500c1a080707985e06061914003040691551803620080002c0002d082d4000d0302210300c18812051141e09581c6544c840d803c603030583c0164044041400c0051780c1401600e1682000c00f04401c840000305443c15084107190b0145c1c0f01030100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 791009694 1250 791008444 791008447
    0x2150c0712050c120403050a05061f05010806061312140d05030a0203070903020907091805010e01030f0f0812040b060d3903082110050402070510060b130b 68
    0x1045040768481c140c4074161a010780e881011114003810081c02040c0743c070401400007070000c2444000200b1a102c03a0080054405507225441c00b10b001010542003070300d00021142c001c105a60003000f80340d82c4000080c0c88a40381482d0048441c0c0c0d10700342c1d030304100d05010064181c02c090210390403419464141842c0200344505e443c4d20050800d0100038045205c850f000000600001d1081502400a5901030405095410300340300c05810b80006024414040580100d21003605856010300fa0481d8040c0c5845029a42581c403140e80102d036107007003560000305803140100080c1842c3c00510003d40b80c43c2c588480c0342000d00c2d2540000341d0250030940300703041003240c040226001ea0000134504030b40d2400c0c00c0070000c04102d41410804038000d181d901d04c000c20400414480da40008003001c242e44008224401c0b60284442044d2005030381c24030050b04200c1d0309001070f003030a0740100b0010f405842210444004100184c0035201e09402070809540041114100c0e010b04e42e01c44e002800f000c903440d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 791010944 1250 791009694 791009707
    0x614040303231308010c0e0102071d091c020703020109050607020306190e030f090111150703050403090e040c080c0103090b06060706091703150105040305150c040504020a02150c 78
    0x4010648018003440d1580c1641a440030201c1d611048510030504050301c0383d40d942d51100c0507030081820f404a86c000c035071400d000c01d4140d0b10115601083d2511488103200c0094440603d0004210084c0741d0401403040010004401d070a1441d0344203044840d0f0f0041c8695401c40c4001450040a5440940682c909110050050741c1c01300301d481c3c1c08501045030b2400300c0310118106015003256100d407106030200141820000d4500401003e00c2182a200c0007440803115108503652803040c2e80d1101d0310320701031000c500383d207110b5040507411501a01e082546d00e40c407851a094954810f9a04548180703500b44100311907441880b611400120034202002070500d251901c140d40c45004002c1441860000f071603604203c60f0790302054030070742c101c0d10150000c08402001111039100b0b035201e00f8031084030446600258410003c035800e40364040702800e503201c0049c1e203180d049903000e07140c80c0803450700f40004141070b1580d01c0641450107040d40241915900c2504000c41003002401d0400e5406040008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 791012194 1250 791010944 791010947
    0x705041b030c050d060902070c14030601060804020d0b010608090f07080703020d050f060f0a0e0c130902180a09060b03121e0f13240206150f030a05070614040303 71
    0xd90246219904010580100c1c03420225400d100c0c00100a07212450501301144a61003503019203541840b8010f0420416140c84007990980f00a112155065009100500ca2240716200050f009440603011040c404034568412040260981103100025501410844503000801007265030112210140c08824100410240c1386c20b000d000c0a400b42d8041e00d0b03000100202000803c8103194400c0a407444ea09142042e83d40d0128162228075103a07041800314124400003041c0c1010340d000050480c640b81160840b100054180400c0a80e400304450b002c4510f044201e1071300364030404064100040f141400d142c800111010f10b00980e0080e17100c60003a041031007010701101d024441c4610b2026403c0005002c400c84e9100d602001020401c01203128a03c4181122581080e00d071000722449a20340c01100584210303a060070b4140c01030b8044404502d01d1000c08884100c00c280240640500090f04400b00c0d00d090101d0700d00700d81c140d101d4003040100d680d02c4480c462240c40e0040d0518a424590b480 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 791013444 1250 791012194 791012231
    0x20a02011409120a18090b010207080609150604090b1f140901090e1c1716140901090302190503152818060b030d09080319051201090509070504 63
    0x4101c1803155000a105607803170700520702e000114250710340072940c26850345840c00203020101c0109000d4480c014004c01c039400301203207181c464050007008140072109407a008890b40300240c0340c4c2c0e401c144d03039a80310780100720b107060211300c40c20500251000c011141c0c80c2030003881031aa8420090009200f2850a6583d541180c190440b41c403000081074102c0e103407901d641400c8403d01c501d0138038040b01a500d46090380141c8500c2c51010800b841c9441562800c0a4440700d5820b00180000100c0c52031421101c00480310107082001c1040c90410342c1c1c151a40e002ca24005103103004032001c10b6081400b0081460b04000010000006011202060802c4891000070f00a40501d1180c1c1c01c00c000d0030076035501c00a610444114510f1110003042e000d01d07041c90300041100b00c0c4014000d00800d10003413140ca001c6c1411030201c80280700214940941c8e40125102032903007402c5030041150401c0b4008403401c0d00e0041038040e180050001582d03003400c08040d89022150340c00701e402a0b0074201e4841d1180b04540 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 791014694 1250 791013444 791013463
    0xc0a1703270a0806060411120610030e070608190b010206130f08070b10050a08032b0203091501240305070207180606081302090403050a0e04060603020a02011409 71
    0x3908002010311803074620a2000994100d08080000150288002600c40c01490160340402498004003440340c0e40380b043c0c0c242d0000244e01c4070045119403d0003149140d0702442450b00007035181e25131302c900c0e041a09a501403000902c429040c0f200003201c26030310b0902401070810400400740203200103500c400c1c0050003062034000042d03042e418029000b4118040305e600404031a560682c0b441d000035111019601801c288041140210b8181013810240c0142e0305c034a0000c608010b01041c0e86004030240c05860020f00310454054821a017007800130798010000e0724050301803465540b4000c0101541680824609540810308000c0742c0c05103d1007886110b0b103032902003101d03a00c1d072006a01c1c0007100c0e40400040c250003450b98040b034407942e0102d8141d0307540e542c80d424075440b0543c10900600760544080c0d4407a450802190020303010300700400a910960818601c004901c4000a00b21002e907440800031070703000a030111a65074207200b154500c2c2085c940c04942c40c2004e050305c13a560110368 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 791015944 1250 791014694 791014717
    0x1b090f1401080430170703140a0207030e060c070e0c09010e0f0d0f05010e070b07171e0a050a120213090f020c010f1a01020a030e01080c0f03090c0a1703 67
    0x61010300f03280e000da216032030008480c681001329980303424500185841d155a101c42e20200c207100c0462406803184c090340c0801084114511819190144142d0096018003400c40910914030201c0c80542c8528000e001c0c039404100242403404d00d416100003a8007001401c000c40d810007003103811000da80200200c1c42584040c0c811248104080000c01d400b9032000c0c0c40030303003100f86894010741001415080a0341e20382e1800e00b5100c240d603076000c01403580d01804c0c0000b88556400b440545964107102c02400ea50405002e1014003c0d40c0804507084a41c0401c00c140000750002501014007500702040c1101201c42034011032420394200c51242c00241c260052240480d00c0d840c03000c00068168041e18170007a6404001c02c510b0001c00c1c03003000241030f1040c084880c1078a007124102e0543c0046240b0101d0358141e10f66040a0240f00011610a400280034a5003501300b8889010007040040c081e43c0305d0320302400103150050b407080070491452416442a9400800d05040034031002e0080107541590000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 791017194 1250 791015944 791015963
    0x1410060c0f1b05040f020f0702091b040303020d0206060111100b011404090213090903080a09150c0e0a09021312140d050406080906060a050f03011b090f14010804 71
    0x251900c500d03014950a806854240100c014101010202c05500120b941c100d4040000c3d00380070898a0683c094040d015400401c01d100c02400750929005056100550314031080003004401d944401c0c581040d081500181c0c00b10711084c0301c1d03680400c5015040310342420018500c4030018403070742d921118454005000b13901e400040304242d0140c0c3d100030160300e0454006450b503448411010094100e4200300c0e078040b60542d0001000b0700c2500c5038800742c1b50560380d02c1e103203646c0390701c2c0140260041c59822150304560140140464249104521103001c85550b201c04100845040100c035654907001080401c0c8100301e4081d01e02d9a03c11344070f04690780564914202c16180c144006600340750202c1c03000a00840100b182c8080c1c2c081d004100b502c105445145490316144407030350351341070112015908402d50170002d004074501003403090a1054020f001040c04440d03041030b40214040c400080c00071491540003809250410703801e00004d40301401e900300d410030018000070140000540042c101011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 791018444 1250 791017194 791017217
    0x90209071116060e0f0405131e0b04080d0b03070f170304082b090305030418020d0905011b080405060f0402120d050a0e0f150306030a0b0910141006 65
    0x418003040940c1c0001140031144190f6400b40904a1809070201c5442169204201c00702454144030b2036003e41400d08a4a00c3c1203055580c006408520038111462150500100300020b0800c003402403142d4401c111480d101d0b0303e109211802ea0b5030001201344240c22095050151016410801007120b414421500701198000c40c0ca506503c0b4a41140d641c0c0c3c080d0141e5214a401c0d0244182c0c07560009508641d03100380315010071200c064440c0001403450700200010041c0d40074020f500d02c2c40c0d641e640c00040ca0312a07000c0c0340340102c41403070100f140c1d107035110b07000007002d10341c000c0d44480c4001c40e0b4100100b140c68103590f42900c400008103981c0351001494081030a54540007615100c007500702c0100d40c0d00c1c8070500300c00b5040da0425400100001c602801d807150307600f041c0071001d0000c5805800e0001148004460b100c46410003090560507108141e035040c0892115171403240580ba5140240c22030350b250b000180156800b05030202c0c1004d80800520100010f521008401c40d00a460151071582 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 791019694 1250 791018444 791018477
    0x10b030d05210901091101090602070905101d15040b130507110a03050c060610050304030c08090618040e07030209071209080a05090a050102062a0403020a0806041509020907 76
    0x14886448104007558a420081c20b003c056012002c00390058901c202d00c041c6841c01111840c0743c0c0d00988005801c542e1080100399110307048036411490544001e0030440c0c460a5500d40392122070f05410f42d1480c11070901202440c840c207032040a95080c1c80a00c031102c0e101700410185448107100b24402607071030001401491143d020b840c202c070380203c00c0c0ca030500b480d428024083d07040640b425119000710300214006141006a84a00044503142e460440d60b803511705aa00c20071030102030351424400c100f44522a501d0300c0081c0704919641c85202c0020400780184002c03181855400902507100344800d2000d40c0e40c02d102d95503c0703040d03482e2090300c0c080000c1b090b0000d4542003100615a240c0481c422407483d402101410700001c05844202d401d603602d0700120b0385d0314000c8d00d04c01124901c0c1c01ca902400c411003443c24480b10b1071440c04501d4203540f507000c101d20110b20341c004c019070342201040c0803c11039001407500322529510401e200003d0380e500000c00707605d8040c0c2003201340903480b80c1c81054039 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 791020944 1250 791019694 791019727
    0x71704050a080c07030302010612170a030e010609020c01050109050103051905031909060e09010e011721090117040b0c1812210f03070507020a081902040e010b030d05 73
    0xd540b000d0b400d80c9a686070922640d69480500045000d035082c40c0003c0f42d5200d000004110580d01b0860104010454203070603102d59208849030001c140d100c81003419120f00c00d0250000801d0211401661419070715070160841e40d040c0c100c0c4d01d5460400004001007680011403660104020080b022040d8003407070101d14500c14019101035032401c0d1008440c8050300441400212000e540716084c0200300c010802040c80400d019804d01429000e005101d0101e003e5000e819824107541100d0340d410601e43c08800e6801820003007088200b0000703494100d0350740300686002100000d484605142402e5440e844803900081222070550004503070510000e0300c0070302d12000c01c0700141441034600c004103001903c8031079420a800100d07052200d081200d0b04107004481610311002e4038203096440750041118a5402448140d0340a103440a001c03070351610a100079500c41c1c1c0880384240c0070600034414001500d0340e45541411a0740b400400c0c800ea61400f049041e460344480c9841c0b035545811080000341c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 791022194 1250 791020944 791020963
    0x50a17160207080f1c1808010f0f0213170c030102070c091b0c03050a120e07030b07020a0c140d12090f050603010305100f23060328030807031b030b0a05060307170405 73
    0x2240f10141b00044196040d8401340101c1c4001c0424005039040c03800381816072007800d091190612a0038010004101c1f1001142c002644441c01c3d80c166140000000f401c1e40c2000d001aa1b10b0010444200044003030740c41a40000203a4842500151006200107000031102010241c00c0c00b20005901d400d80d80702e0203050000c42c90100c420090015500800c03035a6070420700044410060700c00104458030700005160410640c000120041141080780d42c0d00c40060a004082d040740c820780d46640022100b1100c0c8048642d2580c0300044a4908894005000351a42c071090107038034108014130114002103551000d61000c0d03003000c90441c9142c201c107402003207401400990381800b8112040100c0202112034040e45048040700e0b44403402900b10206112311002201d031061150003081c0010b40540e1509501c00c05e03900b030008a2002c21700b5800451303640c0c0b00240c1d00081e0b5988041103185000580c040241c2001c4d6522411460b0840c406050481000010301041c207150300041c04000c0200034074900c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 791023444 1250 791022194 791022227
    0x11060a0e1009050105070e0406150e03010f0903080411221e150f0806070507230a080409050a06050105090d06090c090b100206040b0601050a17160207080f1c 69
    0x112a043e0030840d0082c24156040b04c0004d560781c1c00b620003460319001e030209a9075480502c40303030806105d1040e15070004000031650555260301d0030b00c000b0582817042d002010b020b81c48e078882c103150914003484045150031030b05104020304040b90398441c4141c00d2003050b0400c032440003e415054048941ea10b1803080e41415219400d00417a20b844445040703e03001140c451010411a0715214485191180000c03500d40001503824000400482c11100a1501d0681182c0003241004103a40030541029003c82c3d05075400800010200100c2c1d1a41c40b03070a0340460f100404002d510300b0403000070071911400340a580700e44540f441c100d0910645030f1001107081d0740003a1a04500f5a6100d09001501800e180326210b440395002c44401107001256031403040380d1248400d40d85645002c01500c0360780005c0e242d8005c12013250600e185520741071020300d01508c0c410a81c0010351500d01c00c02841d201f9103030007050158000d00d650f030704184000100c9a010b041032401804100303d0403002100c6042c01d8403013800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 791024694 1250 791023444 791023451
    0x51302040522030f031a030a0305070201090e04030917010209030a0803070504080313050411070c030818030a060e0d0c0b04080304080f030103080705061003020f0f010e1509040c11060a0e10 83
    0x104254200a0820480d1801d440a10813140000c010503040081b2103095500343d0010240710740000e21400007401018414100700e261503454894464909008440c1180402c02041042c0200450500c1c2c00f50a516040025480d0440e0784011076100c184104008140c40004004a12994002c009943c05009549d0880b46c841652800305403001c1014031400340903034a071400b40a002c20484040300c03c00c903040351481440a21316540d80c03601d507201c1106100c1c0c680c0300310452116950144450003140307000340340c04508104103449260030051035038000001d1204811042c00010078581c055035005400500301ca0b00d941c0e4038200003900741714000b6298401c1000000100070040700801421569010310221840d0780d40340c0303c0e4404d8012a0b400080d60080f1100c12500551a000000e030100c1070061404a101520950120784500284120340e5403180340440d0700d0102e81014890780f6600c44040ca8080380c80022118200e80301c000c05401d001c40540c4841810314039600402000d002d02e22000c0081 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 791025944 1250 791024694 791024761
    0x10f09020f070b0402150c010510062c13020403052505010207090f02070209070f14030f0a0b0a0503030f0702130b010f0c03030605030d050a0806040b1c020a091a12010513020405 78
    0x5000345003c41e284ac2800c24403275408190f082c481c0303900c1c100c054000b806040055041c2c1107400c921505a44115601c100c82245010340e80060b400900000c3d03120701d00420410654220020758581c011581d40403100300c0100070400c682c1c0c002180821200d10403000a925140060158040d00c84c8043c0690044456410301c05000e50000d41d002c0851688d80e03c00d2a51688070500030f9191005a40040301003040c0408500700d41100c1e4440c05020364001c021022032a91030012904507003100d0b204502c0700d9008205c8400754280aa03166900c880c0d1110304000500954001902600f1030b04e41d88410080030442e04c90415019500140c00f400c4001d0407240008440385000748035601c00b189090025412102041e0241481c1c0243d00311008014030f5443c03a13014400340480609440b010982c1d11000b00c240000c2d03802c42d18030940f251150700700d10031001d20250100784440318400000d80d1f24968900070420a241d903c00c03211001762a812100810603844e0311004030044030522850810b45420300454 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 791027194 1250 791025944 791025967
    0xf0c08061003020403110919060f08100915110f07320c04050c041703070b010806010b0702040b01120f0e1b09041e0c080303010f09020f070b040215 65
    0x1164440c41007155144051070700c0c401c084060340a94071000704501d00141c002103c46c60000c1c1615448100c134800c406180b140c00c005242038959135488544a4010013809000d010000d0080c11004c840710201841414079942d03074000c501c0c0c940d40f81c950340d45650b00080e80e882e01c074003021141c1801e15401825190034507400c20400f481c200c1d030500b00003402145107514514040d1600b5600b10881d050203003400099000c02d10000c2e01e802080b00350124020400415209210307034904400354100e500031905c48a8a240418640c401030300080c3c05ca83c40500100311150340700044542d582e034107032004a1404a4240181ca140000911a1703608608201e107440400c51603900202110f9030400071900f070844c50031207000319600300085d42c1d078000300000d0009004c1025a000ca18a02d15204a500030f1000e440d01d0b20000e1180b80e0b002460aa08000010030061003e01c0d182005003190481c2180703021510890728078544192074008003100140e000140030b41d5100281c2100c0101034441055444c00721004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 791028444 1250 791027194 791027207
    0xd030507030506090c0a0c031817010e0115090b0a0b2805030603030f070f0803011e090203010b0a0e041103090f071d06011b0c060302090405060d081c0f0c 68
    0x1500c600007450301000650b9880d1034401240a9810420301c5450804005011180c3c101003420680a00c0420300020110544034907205d401048404018100b180d440c006032802c0d10740c950640d481ca40e0404004521100500c2010002c0b42c018010000f10b10342c040c000308501007055444080b2410010480b034000001101c3d01000301c00c080074074003880f4200010269124041034550740d40603441400650310035400b031801800e5550160003050482d626075500c0100e268403d82089100c1c5290001d20b072034902d4003400d04409440c1032a015815507040030a103076003d0164a401404004510345480155111035100266402100601559a01d8034140459650020000d920f11911031403c0c00075034900d00820405c01c8040c581117500107504c80800456110300d100e5200001284c00340a06400034200355041401850384d0349015894040d0b68082008a03171000b091503000700c01a11132640002d04200444581080302086040c2545030010000020000020f900d452503103827030000c81c489034000d1f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 791029694 1250 791028444 791028451
    0x11031b280e10080108030306190f0816060e0303120c130803041703090f090702100507091508061005031003051207020901171b1f030c08060303070b1909050d0305 71
    0x100e016a82c40100341044034145003d204202440d041030010603858580100110101e00d081000c0c42c2d00f103030f1940e00000f03980c903555010390b84540c040d401e0715002c100204031600c010300c182d00301401101c0c03c810111f92648540308540045c4520701000a9103100144283c0c1c00b07500006004190182c2c495034203580d00da005000d92812840c1d40040200340342d1000045910080e809002c000311411020144150008081d00c01000e40c02055222440e020700d0344505403240302c4541d56801d149140298020354140008850410001c000081007130580314042d0f0b1500c0c001aa1503e160b49031781d43d0442d41d03446005a00018001c2c050202420003040112001c1c1c204540202c0e00761086e40da0b98048038508400800800400307800c181c03490a8100b0b1071581143e00300d00041d003400030b0300050803800900e01025441410100c0e0765000100010b907800080c050344030400360011803600b030f0340703440d0304009a10080c15018890f003100702c141d030000f02c10340144c0101c9a1100882e084072440c8400a0007412046 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 791030944 1250 791029694 791029699
    0x609041d0d09140d0215161104050c07050d2d03050411040207050a0308040606030204060b1c0c120b060f0a0519021603020d020a0807090902030111031b280e 69
    0xd010414103825010800400001840d02400c4c5115609002200c5c4541440d021561418000d0742803c0c0444000301040c2032003640d086008152203020481200e8002d040c242c445030b010301400700000c200060b040c0051026040000343ca0700310605046855010780503005040c0014860307221010b825420090085204002800c0e801d40006c0c14807003207029810f00900160300504420b40480e0013400110781041c022800460b40f140c0300e40110302513564039404036103e0320002a100848844200e62030400007142c000a2045144500340184070516a03041011059541c40708208a03543c0c40c42105d104111120002e0307254040c40801a081e5080700d0300701c40500d180780f0542c1e041d084c808141785140c080d05036001014039065809202c2101f010070002c03030704a1a0080089100981040104010b08070100c1c08a100c81461061500b5900384241410300d441040c4207209800a00100e00380c1c034000341c0c0400390744030240204e00500154031500c0c0249522080c0212400503035000a8525002e1003d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 791032194 1250 791030944 791030957
    0x140a1b140318030a23010e0610030515040b06130b0d050d08011a04060f020a050703060b040b040b030303010506030c19080402090c0715020307020c090f011a03070c020609041d0d 78
    0x70b0401c0c10f4880040b0100103243c0f149100000462903040328504019003003c81c0001451006064010310340380082e50012001c8100f01400c108118080104109000c41c0081d8505582400e550f40003050202801e494860700110f00f080c0010081a0300041c0300c45401842440c0000003810400e84402417801040d00203050b046c004500d013100130210842e00b149242c280c601e4140f500c5800c5039805800088007085005141c4080c0201e40304011034009503008000026203225648200300440d003c070b4a0841c09a410302c1805c072120398010041da03046a1041d1744282d81c035034031610385100e68854600200100e100100d00808a0b5070f100301074611503407003904c6001d51521401c4150a10b4098484020b080300c03507410071024004100d401541d000091070049600140f07514000a1510000301d402c460701c1c1004c3e900401a030640600b4442170f01920f40c05503840c609081e240281507100e0075070068090240081d90481c251900d80c491070100380612140b240160310340c0550780c2c03920103160558002502 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 791033444 1250 791032194 791032237
    0xb180105190305130b07030c1e050414010c2015090303030a11190e0307050a05011407151b02060906071704020a08190c06140a1b1403 59
    0x14204440c40c1c1c41c841d41d0205a04200742070110b02900000f03000e400c4c0c0009035900e40c0c00281c1d50440080c02800161400702d0b012030800c00041c00c80403030503c07036865049001110700500340c11808481c142d0311401c0b000e03004610110300584200c05041c4000b40b4403175000301a003800310f40c01154520500011600302d00107034416000c8004500900c10075a51640040012400142a55000003106440308007881d0500d40740303844023500340102c107400c10701046080403d0300f5280b80074446140500070843d210b521803401d080000380070310300100d007520110f88005111014000226580d0181480100741807083c20801c80c060401c001129080b82c0141c4600c0b00443ea401c4804240c152003207450356180520350710b00810102c0300d560054010b80e003017440034401041300c020a00c403440b0310b2040c00802121031a220728000c00f00c20b125500c9001041180351102e00502c01110440302010400d180c00703400522040b1002600000c000e0008204901100303040310b0310b40c07021000d0700d008500c1410b804421078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 791034694 1250 791033444 791033447
    0x40e07020c010e0d240b040b091006050d0b03030d060501030b0901030506061c0f1103060a021e03091c08100801091203020a200c09090d3203010b1801 66
    0x200041012404100c44501c2c0c5203213400d1643c440701d03001c1c0c012068900e180900f03d043c80082d0500151001d4260b84510890040303003024001c0100a480981e1000742d203242c00400107180c10064018070041080004520f070404070190084121000f0090070f5907030364000010090010162841040c0c0402c0c10880b2a084600d03091000b40e049907086409803070315990b81c200300410700002c0007102e07020390350f24018035021800b6042c2e110b400610451029088844810030945004002404000651300400c1a000702004042607140e400c241607100b907403a5101d552599061001c403038544007107092042c866010065021440038000c1e50008260f0745140e40303c00e412400d81b4941000500105044814000460b01c00c1d801040300c42c509181c032240304015940c14000a403801100388130180c1c44411003803e6844c0402d0b10700d1701310040400610043e00c0c0841c0c050560a884000c0d5010f0305a44220b80351180c048c01490b010014001504503a6980c40b003248112580050180c1000c1d52040103111340c407035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 791035944 1250 791034694 791034703
    0x180803070b25031e060b03011d1e06130509161a0414060c0a050d140901210e07060c26160807080715050603071401080c0f040308040e0702 61
    0xc1505102d01010951014140d0190242c801050513001d4014000c00300c0082c0c40c0300f00c01c0504041004140d481d4501440341d1a209040e0841000c41403100003800b150f007078050307074800300a0b403903c0c07039284a5a284800102ea07042c100124240c154280000c001e080702020a81a030881900348000540c1c6441c2c00c06241c100d0003001e800082c100c0200018400508154503c0c3c41003a4018510703441c11407a01070480c200010700c0c00848881d481064103840e09908120901501c0882e50b8980303060114030000280750455252101098541c1a924103074500c0071900803000c11034440085940d1990340365001030500d00c181106881001081146d4803002c2c4034210402d002c81d110b036080070706115085484810f524800e28045035074204c200a0500000c05c0c90000d0700e0414026a003031a0040f10300c7c40ca900650b9002803005200c0c0d045001e081c07015901104144540c1d02081c6806003082d6211105a1490700c2604005800d004012400008001c406002031003564a600e24841c4580c03100c0030107980e034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 791037194 1250 791035944 791035981
    0xf032d0703020c072403020c0a050d090f0e04020a031101021006060e120a0c0b030a06050406030812060f09010909030507020a0f08070b0c0715052a0f0a050606010302070201180803070b 81
    0x10b103001754110041182c4290040c011a00e001d900781d404210655584500c0c003100c2c84030300300201c0da20785001c01c00034140d03025031802000070703452040c0c503071616030300107206a506800010840c2c0084502105280d10801840c00311000c403030300c00c000d040e8603030034058207002c6000c01440c480c0302c041044068696010640100c410b234020116200c050400c010301065420040801301903a50391000041e460b521402400002c0d801030740015a0744506102d400b00692004041c1da00035240c200c42c108503900e810100f503044403003058000614a40030701c0c00b12031501c504507000c0c0d4044906c000114a12030b6280441c41102d00040844014030b51b9680c088030603004100540d41a6081880200038041c02000000103032101c038504646009048280c03000c900519803805506170441004000054800304112205010450001d11820300303107503601c9564400040000d4101078001c03400d0401c6901800c02610000c1c4840c1042c2a00d070303100c0038003c2d600d400910040e6848420600480c600f1003000c6000c08a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 791038444 1250 791037194 791037239
    0x90f0d0203190213020301060806120f0607030b220501140a06080402090a09300201180204021803073506041b0b0d200f032d0703020c07 60
    0x101040c045090825000344841c10f98008110ba440e11401442601c000c5020f001c40391201c0c00c55091900c00c1c8180c40d4080d00c80051581d008000ca4201002c0020344140e011105203004181901070601050030482c80ca244601404001c0b813068940c1242d13900968141c2c3d241c0760002850300003600410804407658458030010600c0340001c10702604002d4080703035004600340c001084a0390540d803000d400042c03000d41c0030003054008060701c4d210f0029032289051841c02c0c1c40280003a003c2c001b1038080600109400074480c0d83d00080110480c80d00103a140c0e0700940080c26590390540e28400c104c0914200100070701d542043d00c03c54100011a04907002008071000018043c96440303903560010115000d4012084142c50080024030401460082c104010303000d10104034201d00c108a0140381d41218007103459030506200d0b00c09546000c00950b60b00018500051400c484480c41e601c65400304100403207443c016200c01c025540760190020701c1802200000c40700101d50790403a050043c24155150039 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 791039694 1250 791038444 791038453
    0x100804080f0d021204050c1009080c010e030c0301051e0f040807151d030403140f03032a0301060504030b07090e132a030b01170a1509020901030602090f0d0203 70
    0x40d10724000d200504994894640010301d081092021a1001c40040710304985a03030000051916509201c09242400252424030102d81e03414400f5890301c54011110b810b0401c4040401035006540400c103070301130210050000c1050381885040398242c4006401c41034000d51501c004104040303044500e051255030001c0e0380e14181040c90b91400c5032000d44d0941c0700041901c0349a0451101076640c0702c1d83c149012070004603541d524500d420030000c0703410011418a034100c180303039408852001c0102c0758031180710700103181c0c140c0c0c20036030040f815245124281408200130002150350340e0420300500a990007105140b909075103200c07040743c00344a1400791420752003100d00400c0c650000500403001e4640314040201d10400c041185c00e1001040c01540540341136826820410f003c0544010740c09006d49590304c03070304e101070070500594511418100030200210a8030701a40406960300000381a45d0080030418296540c0c285007001c0d400056140e849030075030b044c0b101c1051910304100c00860b64040c0140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 791040944 1250 791039694 791039707
    0xc0a050301050402030a0f1b021902150a0507050f06192d0b0402031f080f060c1e07050a0312060501080606090418030309030e090402061903020c0102070803040210080408 75
    0x1001940006d0400c2c007006890b4031481c070100c0014080e0b40c80421022000391012099050000e02d8103a0000c100402341c410003070141d001da11005e0700800100d03c250030040d03659446440880b0740b4803074440090550300800090207000400400c103140611380603144000d0080131840c406040300c0410782e0298008280b00149248555400c1d6086000c07110110005410a848400305040e0703801158910900e0241c1c10000d0b450140c040e605070060000e0100400e02c0005c52881e4580d109409001d60258a41c00306020844e0304001d081200382403880d401c880d442d00c1180c900140e681190200440120b58103a0320300811281c030384078240844070146d49004c000c0d100e80d010300070a80c0c4064501500700d42c89605140350100504685141c95100741c3e00020240c0c0070b402c00609511b4180402441030b0314150511025941d4070040d030349415140007141e55400314006054000b03101d000d40c00070031540041482d40c103108009000c0c520032030003900c0900d44203840c88022550303c841110000c0042e03005000c038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 791042194 1250 791040944 791040949
    0xc050909070201020f070602041701020c03041e1d0f010b0a0e060f0c1f0b1806040507300b06040303050f0a0207030f08040311120303070e030c060f120c0a05030105 72
    0x100303402140d07a000062400e901c9041c80c41165120000c10740d000c80e00040c00300f02102d0760120f4001c050030000c00031810140c8190300c01c1c6d2240300390b00c0751054060680c0b54803103c013805000344000421042d000d202c0441d00b00e08208015800448500201c80101000029041d070450102c1d0050308456413030100d00d01c1c040003004155040a803001850180520100c0c4050f04204400010140410418090080000700c03a105a4056440f05030140b505222285801071001181d5908441c1c100c3c2c0125039076980880844031040c0c040038401d0082c0b401900c03d00c0d185481c07405001070601401c0e00344a040d4510302800070501c501e10004000034003c0002c071141002140180040c0b22042c41a540c145599480310248540c0d0241c042d280c148001074104100b08204803a02c1c00090180c0368490040910075586490b40002841c1d402841041c0540c1681030ba014000b4036207600c801040280c13070702c040b188059600d0308403404500f0b9100990300410500155441941c0b00c100040d0b0362145144e080100303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 791043444 1250 791042194 791042209
    0xe070b0705070f060203091c080304021e040f1d010b06091212040801060e060108040b0103110402271008090a081e0a020c0a09150909020105090a150e040c0509 70
    0x400750745a020720700001c104218000380e00f1004013007950041d9120301003141005a140706010708840100c1c02a5503503800510741c4010b4a5100741c04540d9040d004000200c000040c4400c8080d06030b01901d070030465488139070990310002604150401009148482e011403600300d502c501c0c0000c3d403191b82804400b0304c914148620b801e80c8510f01058404182d40c2404621700350f0810340010740c481c0d444d600180040050b85240a5008800f423816070304504203901c2da10705c6518103000142c503a00e0b19201070001519940c04840112141c03424441d0f4104601e1811035104205140b00c034880c480011403060003900c9200868000e100400c0036124800c1c05d6951202160302c0052070101686400c0d10a1000c0030401000d003001c2c010f150054407501d001c000130400006d0140e00280055442c1c0300080118110b00c000500030349031a80000184016680011fa8090081c801c45039880302c0200004141c4480040c0b070111820b0454640300d00c040d200b0410002a592105c411100140f414014801c4a140c402d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 791044694 1250 791043444 791043457
    0xf03060405040f0c06050409050c19030c051611090601020f0d08130803070215220f0203100e1c1412060a0503010c0f082d040602091815040e070b 64
    0x1060401c0403c03541e40ca28068031113522403004140045810040f01d0903070b006a980c000305080c0f44e2441d000c9110f244542c480794404440d030402d60f035107200040c01c43c0140100d5003001c211301030074040d500b010f2428a080003a41d01c20305e80600c0203c7e0128440e0350000460300c030b40c122030b14040e041c80b501c1000b0850390400020213800840c9106401e007808126a48005c41c09221240e0107051000c41482ca40120741c200903106050080d4022441c010030607032140f4106410781d0003001d5034520011400000c0c030740140d0b102c413590071500e8240b044002e400c0000e048401e000410408a0326010b288a040d5208201d07540b41500c048010486030040782d013000c10701644450000c0112100ca82c840000c41c0c21500d0300d070b084a0119804604524419822030741c81030b440f40400030210121390500c0c610441d88040a44512550162940447c08120840d01580e22a000c0036055030340384000c101036082641c0d0240c8803134691020a8508078081d080c24026003d14200540c0201042460700c04180034961140c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 791045944 1250 791044694 791044703
    0x303011a04030c090b12061510050c010c0f020f060118052701020309070f032102030706110319050f010b030a110d0603110a030b0c07020d060e060a0b04020f0306040504 74
    0x20003000c40042d1140f620640038141d10b000004464120f0320a01c6039115509000d81c005038402c4c0104044130f020341e421280151015107021558602d001c030300b502c0b58003c10b54030034055401c040079003021650040440074242d0340c990031204d40280385144207445580038014a8182440341c6080304410966422645e007182c041c400c125102e080302c42500b1080120a480182165000002d0140843c2c0070090300001d80549144001800e19517900da0050140c03400d40320124080040d1281d04241c02030060b035003200d070070100a210200c1d01e0400003c465208848451201410a008a250703000300d2084904c180300c03c204050300b6074205442c07142d0340c0e00010f10700c0100356115a1000c011400700005001c030804601d002266840c00c518102050100c418003090043c503030024200702003045082282d800003050708065a8440c03182c00840c0c40781100b01d502501c0c650034600034644000c0c002503058802c0380281c00030800c020342e0600b080309034450000c10540130340040c0045145032505902864011b03100307 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 791047194 1250 791045944 791045947
    0x80f07080a0903112a10020c1e03070312030c0306180b060f040e06040b03030703090611030f0a050c12040510211103010918021f030f05010b0c0106170303011a 70
    0x3c4d0f04800e1a09503403000f03480c2c02d10a00c2544910311503000055045960003259003010601250300300039520100112454401d0341000490815a0800540000d4015001d401e40d840b1648034200b004100c0020b0a00000080c584020404a14031910581d4144c0f0341040340c8030200001070002d100980941841d55a10603410452410040b01c02c0c8020002080d40411441d1103103030203001c005c100d52420400301c0c002d820402401000170f44c0502e4a00603564103090014510700c01d108035924500400c0e5140b4a05007001a82c202526008406001004600300441e0441110400e15201d5401030f84260740d000044c06000d0002c050184000008441140303402e00c8150b03070403d44000a0758144c4005120b03030b21002005202901003400b075a80704050b0483e08448020300783e0302080c1c4801008580c1c4007552840701003110396601ca03400010100ca01e5000c1070116517110504508035034000700380d100c03c9611381400090204400e100319901c401c0702602860170b6030310f042260500308a03d810101d41c070060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 791048444 1250 791047194 791047217
    0x601090c12020c161d0a09030801030f0c090f0605040b0a05060301060f1e09051804170703050c01091113050903030622050a06051509150a0306030c0e0403080f07080a0903 75
    0x203010300c1080052003104940200d481701d000b83c000314000007400d0300f0413950604140d040440d40105600781140c1d440000f04051800c103007414410300d105900b22507141420080e02c0c5112541e0340c2c100384241d804c121400c01c8564420020801054201c0c07190b00e40121060004101003401a02d10000c2c0398042d00300311107040841c00c040c4845a001c0305500307000c90b48412085c4514101001a44003405c2c802225203103609060722082c0f075a801c0410841b40f000e0001500b642050322485c11780e6070301003060000b40044400e9180c5860608034010840e40240c0030030a0311048114640a03241c003982c40c0401840c9161154028403100c0086070041c1c00b03204800210b62010184a07100c0c00d0320804042c180040c2da030382800c04010740d03040b000c0711401002c0400e00c80080103507101070080494101070300c141c030b40da02c00140066010f0312203030b0b201a0410002240c00651040460302c5d03144241d109a6680710b80d651001d07442e0115100a980c0c400c005030fa8000003440741405544030207800c5020781040714022a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 791049694 1250 791048444 791048473
    0x2001090e01030609060506100909110f03090d030507050a080f0402150a0306180e030a0e13150311061314030102070b16020c06040506070206070f060204080f0601090c12020c 76
    0x34001e81c41100c500d03583e10344a00c10b200a03032080741d03040502164001c1280103003c00061a0882a000300b014080d070f40e40e2182200701d216021520115054120182c032851324081c46901d80081c03802d0107020905100010700304034030950441d00d01c40e849840d452441d44842800c1d041300c03c00200220b03001408011042c500882c0c00002d0180005c103680c0c0401d1190030010100341c91030080240c0300b807690514010208031240401900c00d451000d16161940454120005580da000d015126680500d442c411032803c4c81d43d46001000c0d64001d00301d00c0180d07a0443c080c030415101b440d06005000002074400d118104a18441c00c1a03000e00074005420300503140c881030568070054070b180360014070b072050b14803003503405000c82261030204991450038680340c40f010030b0b5030307102d8903038001c0c8102000144002040905d111034080e981c0c21031421074403580c49401c40b41d521007803c03040c203c06120308800010041c204e03003c0c1d2580c0066690b45c038101d80180326802d030040d4100280340003450144506807203005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 791050944 1250 791049694 791049719
    0x304020f0d0807050c0118140d02040c020d030b06030c04151413140109180e03040801020301080304030b01080d05090d050c1012060f150c0507090f0501030c05060304200109 76
    0x1240502c0550b551007026140040c0b40003504503c075410300c03044955503070700c2c80c0b8101400011070704d8442c1e0198501e03018100158140c0e840301c80c02580240f03055000050701d6800a01150481c0c2903840c2000b8444e8203400b00540c40c0400c81d4481c080600400060140103000200031085140e682441401c440c500800c219168126100309008200041c0c0208a500f40300380c0a20715101003804c05c0d124150410031b41e880c0c41c88482c40b91100c0262105481412540304004680052401e400215280d58480070300a8580e4000c3c48140d4030038051100100e0b4034007002c2050b00d0303a0152900d074645060509001d1000111039140c3c2502c09000d80c41d00780c9200c0d1038500c01381e109200d5a40c0d42440001410300d0460444510fa0000e0701c0c100c00741d0b0000d00c003010f0014005c012301000f9050000c109499490190701d85a5650403949025044c1100c200400c5815000305041e81d2142c141c240c405602c1e001803201902041310301404409055280c20258100c1200f0804102010714009040548541060310300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 791052194 1250 791050944 791050969
    0x6040306140f010b0a0207060f09080f150601050f180d06050a050702010509010c1d03210406020705010c0b13052a0901060f0c12051911060a050705040b0304020f 71
    0x19071003450801c500350b5071101c0340a02400320301c2120750600840300d000035610001402032209110403112809202d034003514070b0a0003400b2640896401ca6280d905403515410b147c0c1464800490007400b25810b50f0041050300d1240810108540c10400d2080c6001440b401da5080290005203880081c4003003405801070070f12608040c4408181c03400d00b000000d0865400601c02c400780d03450046802a001d9204441e6208286200d0304001d40c0800080003c5c185000300c07104c20900c404d1402428880300c05280a002214103d800f61144e0030343e140c0055500f8112050010000ca640d10001400a00c1400c86001003501800c01c9039004041c034125502c42c0c180c0c00d80a007920b4403883c43c0300c02c035500d0b004282c680500701c00e00e0b00f1680410410310261000210000050050300d0406040d02154031601c280d400065200e4980c42d03144401040141180041d0548a401e0340605800982d0b450024051030380181c103a5550f4501e02850112210410380001c0c20807030780400d2500d9115210780e15074542084 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 791053444 1250 791052194 791052221
    0x105130c0e0d120f1b0308180604120915080705031e10090b04020f0406110115140102211b011b05040e130308070305060d120f0311042306040306 64
    0x1030000c0d80800981441034450031075007000b030b03010307060440c800c60408005c0c001545070a15010603140c0820b600400d242c101c4c0383c0851881144100418401c017034240d0445180d403511030842c000d40f11407141c030540d030f02d0f10f24440c00300300790a01007000144120001e40d8420122100c1c62140705040c001d4514400051364041c1e28001c0c481c030284a0b103030403480303004c02c0c4503021901140741281d10b01e40c00f03000303014912682c0140100c0074071060f005003082d0031030700c2d0f0f050058900700000f540714203540c80010b40341807181d0b0041c407914103145511090207481c14000d07040540218100345514072030144020400428a013155221261031400c800401c2610500900a844250706c83e4144000040b503180300030b000b500b0b1110010344510100b0f40003205a6004217041c503010400340d0328000411010400e100000f440c2c0c1100486c8086541d07400a07101c00410400e035014040c000080e03141c15141e01617800303039181e030031100c40842c56034640281418401c080042d00c0d240c206540e9440c2d83c4200d4139100203820 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 791054694 1250 791053444 791053463
    0x50c12030903010c0e01031505090c0304241a010c020a0b030703020c1516020a11060f041d07030c0207061b170d020d112a0322080f060105130c0e0d 65
    0x140f156030180502234aa5040500c0072000c946001c0008200c014060154a00448000302003011700c011082081e0009400c0b0a942080c40c00403107009000b08404a4500d0b40340300031440c001155072141d2000303202550028a001000f500f0320306840c41c2c1d680301030720f18014184d00b00b0101c417581c01c007484640803509140381c640d802494440c0001c50b005000042a10440d000101d0900029001c5415800a02010b07a44161103042c001c071b050915128907040100ca000040e0703154400d0101680e51588601c4ea603036024081c40140d84001d907520741c4a801580302103440c02c442e00100c0c1190b081c070300e28124002c103034840c032109601c1d0a03210030b980002e5150605a4001507204403294603401040c1c1c1400310102c03841e280810702441013103011a559106004100d080380740c0e1151050400c15a41036000020640800c8000d000444810455604c1002c03401d005450b010900350310041040f904032403000e080014254043c2031050020070032040d041c8240444c0c00e0b00c0710700f141c44410011803014420f04561 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 791055944 1250 791054694 791054717
    0xa15020c0a051e01110a0302091c0609020a0b21040f170307180b090d050c1e03010b03073b01031410060b0417010906150e13050c12030903010c 63
    0x481c1c00803070f00b0600846a0303050041d030b01c00860ba001c003200e15102240ca40146c80c2e07551500050042500c0e0704049841c011800c01c000d00340b10981d44501e401764400c8500694240d61501c07804e40078050642c20f0108181c4482186a507090340009840d8801c3c403c4a8000345450340343d4840c84280f0b118001502540c0000c410000d440b500213030040c50f0510241003a1251514143d01450244680f00045004a034529040c0c410403008000d60124442d000b01a0f9104401225034100c0c95064000807074801c3d0700300140b10b552809c001c10903d068508080540728250006020190501450302506a004c0000c5079606501204c008005018500c83c0141840c2c410014038280c7c6403560280c2e42058540c07418408114100550741210f085414844464126080707080501e40100302000c2d01a241c3c03400c10002400c06a0300000600560b8000c404007103198a82c1041c0d50320550381880010402e0340000712122444c541048150060901c0ca0216807510100358082425946c1c1e03c02950701284800441 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 791057194 1250 791055944 791055973
    0x1d030d0f110304080706120e10020a12020309060106080402120109080a110607120f02270405160c080702040222030507170a0803150a141c050a15020c0a05 68
    0x7001c50524100019810241494503064030740d1224400c400c2402440d24120f1074542542d0030186001c0800820f441014020881d0305002e036214400c010000f80700d82c245608141600d109a1f8000d00310900100340c075038200f140a80b140303400504140d80c0000c48429000c2084000d0040001c00c2d8840e01e1030b55180c403242000945985044d00a5070b400e0b41200301001034a5600800e12001035442c09804100c074a4440b145100074428006009040308004001e003110207042c014031804e050040d036040109503110490038a001c802d0360111400501001c02c42c2d070101e03068030040c04066000034001460051080c4060081c1210a903c40c002004040300800c20b001e41404000c000f4038070140700c140c0e401c00703404183da151080c055005024101c0880800c000c07017012422180301d0407014100d00801da0b00e03030300c44000b42d0040703440d4148500b01e14000301031504940d03100d040000b0f0b44880108416000c6944140d2217620b0001100c004542c2031000280c0c3c04800c00000d0b16060081000e1b10800c114400b8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 791058444 1250 791057194 791057207
    0x709021803030a02160b25020f0a0b0310090509120a0207050a030b1008061b030a09080a0206041401020f0405011d040510172b120213060f0e060301061d030d0f 70
    0x6d4244034800d008400242c5080304410226141c4284c145c41520003601c0050681083c40d90a40c0c2c104400d000b001c540310002c0002580224a40b07178881b41e049075184003140030344a00f1100c0d500650082030688001136200000740000c41c66900545100303039143c0300864000002640156074003501481440550002c0700014006004081c002e800c481c035040e141c07000140004440d07441c1840002001030816401e0368055040d140c0d00004065440143e03040080d921007040c0c8059a603803220340491140000c051080301c0300030841080c401d040500c2c09006445400d142811468861a400d40409031540c0301c2c070499104403601c8003c06501820300c60b49000907142c9510004456224600301c4071542607500c811200d040c102c20260f501c00350f06840071260b9245c031211296901c0e00102e403004424028032640821b0b15400d40d20450f0144506604480c0c020080c00801e400030300070801448050b110741c1e2045c012412449a46c0c0c103c6039088003080c60304010381921000944800003102080760b02c0311 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 791059694 1250 791058444 791058449
    0x60e070915020f280b0f041401140f090f070303030f0b06041d060612040f0b06030c01170a0b0d050a03030b061314150a020d08180709021803030a0216 66
    0x2c001c148560120b0100c0740e42d03650104608480d4412440c0b881d18444c0081ca6409000c1d50084030b9484078188030b041c0000c1800d0a90342198102c00d00301c0c00c080075000510503180b110101c05d02c0701040d600c8a194142d240d19006e0801405070280c854181d40401d000c00c2100c009612a50307000032030001005660003120284d80281d840707103004000400031040101c281c81d80701010f0500b450541d4643c58001398491245504400070902d40c0c908220900220205404241d0300804102c0040d950b40010181c4816040e40458040340941d12031101c41d1104050039544a900000300040843c00c980014100c004880000c0f0740c0e1768080c80c1c0f0041050b0b8140103440e86020140d600c1402c16050181c8504961518014002110444800590381d69144400c9441c5d21008003034590707644040c102d009484526a02c1d0300b801185482c008518841d42d0503c0207041184692301412070340c0d040c05a5940603601240070f0400300310500c07100d040300d0384e003d1000380042085a002408681c2d030302c1d080032210081c1603 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 791060944 1250 791059694 791059697
    0x6090b0f07050f1e0705191b060503040f020420031b070c031514040f120e01090e060a0f06080f0903070b0103110406090219020606030d140706060e070915 68
    0x41c801d501c2000040400c0e140802c000a40c1c6a5000004c9451240180100c041c0a4154401d000e080c400da1101e000403076000b28000e02c4172100301001070002883c40d0025202d150000380741080040c0c0840d8203c4403200e10144001e1001c1b8000009600c500d240841040010524450005c24070808480f21080c5040b00034840c550310382000c0c9280c9440038201d80600c0050003029180c803200e01403460750362000c0094005c41c4c564024a09140c00c0005561610310760851b8108428940c01120f40e0003000c0b03058041805941d5004503e0505410048140c00070300760b00d4209082c11004034a1102807000040500903503542d140340c074584200d9030340c003c040c00703801c44007150410420400455000b0851505594004070744030606854240450020305031035100103003251020800004455401543c01c1020883d0303801c440f85901c801c1c0030140c4036150725800902088000c2c1030583c040380017a0150850a0040d1000612a0b68448000060180444c1c1001c00501181420b0114507054042c4050340c0685 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 791062194 1250 791060944 791060947
    0x5010b130e070c0312021603320414010e0907030e15010302030a0b15040e0c1003060b040504110706020c1c020f0c091003060e06152407020d06090b0f0705 68
    0xb41d9016012000000c000b40401407800e191090304900c1e50120b821020000300d0070f12000139a03040003082c4074240e00c1d400740300c1401c8007808a22040c62401ca090b91144042500d0316243c641400c5102590b0a44a00382c1486030b900f90f00c544954031455041c0c41032420303450221301d4de00d01d9101c0a050032641d50f60b49030750000c1c0384018000341e00c00080420209502070348140082d12105505112407918180c5603a00c582412464000500041345403025848140d030350100c0009000c00c180d043d58594000d000c000b140c288801c21a915003074110300310080320464401d18103000d6482d00c1c02a031340403401c10842c40d0b00050719081d24141c000915039480180d440a00540d0266480040d01c0f048050850340c800e6038084046640380f0b00d9658030500465000e80b04000c0d28450112490725818203c840d414511041c0c1e01e100c40d18284842e007200c044000303060006000c0b90b0300c0840c4050303422442c81a030b081603028204c000054400c0c400e5400d1503025a03038a01503858885c08031b0410320380040031003040000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 791063444 1250 791062194 791062201
    0x5070207030525050d050d03060602030a14031513060503070506030609061905030102070c050405070513270507020a060b01020d1709120f040329010311120105010b130e 74
    0x140820108419030a100903400e950242603d0085032940075040141e00c140e0344015642004800184130302800c00715101030020ba5a5003030243e859010b480501800300f01c0391488066044d0b94000156030180300780501d4030601e60404042a0291000d0483c048101d23618007040c040c0340340400865004040c102c41883c1b031413a043c4003107000c0f00f0740904010301501310505170f640d20369500e1051b107007d404040e00854640f07c507400e05101e01030b418801d071400340b4a000003203141c15100b90304882035a081017640c440003a2801041c0f83e10281000720b82c040c181550a41d0a8800005024050003039419a00900f04a000707414680b003182c104d0500300d41507512007255240703219084420120b40354203c20020701290f45280c00030b81404040104c01c0094503002801e149615001c81c090010703240203426050314610140f5141f00f0b080c1500c80d1031601e1288000040001030f013800381724101005d01510540002d002c044002e07007503500a801c0030300c0141d00400c40d01c02110407045004028201001c1c0c2915504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 791064694 1250 791063444 791063453
    0x914310509031804200a02010f020c071a070201080c0a02011e06030615080d0e01050c16180618090602272e0305041b0e0609090607080c131d06040507020703 69
    0x2110b0082d00c0c0404400072606c60b940c24000e50103c1c1c2d0010244405640e40c040e656078031911b641007400b80340e800d110145543c0c42d0790301d0080d00307031540c007607060b100c5880703d0301c0c2d202018186401510199046648408620004000645000110354490740d00455501c0c21450f0400075280f422000c4143c1650643c1c040182d0300002903d00a5080701d400c0180005130340b100103d80074461583d1840091017040403074928800035100d070104941504000c001c42c264140c04400c20355a9030b100714090b0400144040c05c0910599004c00e402c0d6110f0f4400601d4481507500421250b080500010300d0000740d84191880750804401d403034400080d00940841c907000411018103018010307000d0b0380c1016a2140003c0401110489040b681d40050009040c070642c1c501c0204440303001200c60351300800801c0080f5140e400c00003000b60240f0f0290f210710045559014402c100360f08800191000030030f006000045040015012030940d0901c228444c40c14134082c81448160390001d0300c03000442d80448403c10205 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 791065944 1250 791064694 791064731
    0x20d050702031e031b1605190804030201031505030d0e09060a06090e040606050d0b1e150d06060b0f0903070510050f130e07030207030914310509031804 67
    0x140900d40041d504c988661402c010310341000071020b4120140001d0364424090341c0c0c042c8a500a214008443c121107981440360060400024010803200741071005200560003604001c003d005103200302b600503592200024079050280c917010300442c50700c2d44a0109403c209451940c03084050310a4505a032401c9002410b26281e441a0303902e43c203091000c01c0800c01650460b10003004001c1c031a070701002160408400315001595028500741e602c2c4c042135034241d0603e942c94820014140c1004140d42d292090008002071501c0840360240e444101182100d44200500107400c18941c506846801c440305040ca0204150402c03803181072010f03c1c90f10495402000c580908128407100c43c0c8403035200c21507504d000c1c0c20750007401600d04460100700c0e599034154083e00c012406a500c40b000310369592013a911b04460300020f95040305440014904089074000b11003540c01004283d95500114a000d41c0102c440c01e8403103403030302c2d0400240c188120706101c95000d82d2080440d0100500c0712980c21040c1e40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 791067194 1250 791065944 791065987
    0xd020d0c080c070504110a02060109051603092f030c06030f0610140d050a1802010e040e030903070e0402100201020c0303070309020f0907030204090c0c111c0c0306020d05070203 78
    0x109540042e11502e07602c0240816802000b0140042c0940e01907960304900340d0300060320050040c4a0500005107207a8140204c3e4003948501d1a25004c180700c040c02200038106a5209135180d0445401e43d181071140d04682c8030208146154241400b407164081600705101d40d065039109280a00911100c0404080d41580244041341c50483d05054410142c07008842c1c02246032021102143c10010783c0a0380c7c2003036220703a0207650100840307466080005e5040213404406800900041e8104506003440d921503400d00b8414001c4038104000140081d1400030550404102010b2000c1448114103181d07001e040505d0150000350b00f08a940d1382002c0c0d0742c1c00018003820415450300110420354a41000f012034000028110480500d44080090042d600a110b0100c0541c075090315052500e114403060b050751a030140820081a84500400c1800700d007210b610342500313010069400005844d0401c000085104000250311062004c901304100d480050504055401c00c2041da409101c100360010b41 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 791068444 1250 791067194 791067203
    0xc05010309030c050d0906030c110d0503060f0901090c030b09070f05090a09050901290604180204050603040b0a140c0304060509071e0302040606140d11090d140d020d0c 74
    0x16101242d04080b0b80071501d00c07101400c140100b0b61034010032640f000c42642650740c2501c0500c451000b4075012035904442c1028101660040d01d00c1418180c4500015070f04802d0007440b00c44014880f4001800c06031b0203a00c000c0b8510307914240d0510481c1c150042c1910020215440d000034075100c0406801d400380b03100e1100030418000f400040700e40d070341c810f000041c0141e00350402461a228100e00d00800f14203d441d03017036100185000c2481141d5482094005601030006c0342458134003070220014100d041040c050340e940911010841d070f00d654016520071400b8608481d058206000f43c0c1007113403d1050011141030440c4200400c5c0700001007103a4000c7d40c48140021290b540100f04c83c01d00b0180e401c1590002c480344022680c4c6200c0380005810389008070703010881c0903541d200c10344085481d003060b031003200c0c01800052155080c560281d00c0c2c896100e03da0750700e0152001c0028030501e030f10b80f10860384c226070740e0041c0c1010117003004544000005030009103004900c101c809000041c80280041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 791069694 1250 791068444 791068451
    0xe2208090d0f1103301b01020c0601210201090e0405011d071a090f060a0c0206030f0906160509100c0f080c060705040b070b04061d030301080d05070c050103 69
    0x30035520340c00000d00d92242c00981d030100b00c000900d042c040d607070000e0900034424803680f49102c400341505000c003510300030300208a80940008160f690300302d0700300d4501ca41d000001015003d640c90b000303000808140d420301e00034000940c1060b8208170840d01c1d016040e15400070821a250060b42c2284000c0140c810070a83e02042d03540b540303441c6002d07000c2500a20405449400450304103100010181c090340c04003441e40b41d4001032a04159071030302414682c5035126001d04c00e042550300f482002000078461a103812740d441c9140e9004501c050780203a520200426030201045141c000c207000c00341d0032803598241203c1c0d12883c200010014005c40030410b01c107040c022520000e0720700070152840181d510108030603042c443c5041050168001030742850702401400001154a44500c00310f9040e295422142411f248040d02c81e54080c00c4020004c60310305540d18035108000c5c290020f248410411800190303940e60611082508001d0000c1900c4103220061181c08000345808140320117462080c038002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 791070944 1250 791069694 791069707
    0x706091d07121d241021062f032802090a090c02070e040b0a020a11011a12010b01320a020102130e010e0708091c05040e2208 55
    0x600819200c0f0300303c3d0401c400e1a00e0b20a1080c40032a55100324500c1141403980c4400c0c1c85181c00020b68100d44580007801c01c454148104030003c2d6116a0301c40903d0038008100800d50744500032900b00341a84d500402042200c07050304070110b03952411a0b50889241da00b1030400c4042c00440b5000c1c02c885801d2803401401203221000c15505544441e00e0081039060b50a0b6501a910000d041035403c120042c01210390204424414071400f50207142d0202d5090240c3c1d031604004402500107410304010040c0d1110541c840e00001d00034808084150b00050240e10444010040321015481c003228081c2d0400c0c951402c2681c000f02000303143c0e07140b000c50307480d11102c0d00b402209500c10700415203030041c0d02003101040c00394154064000780904a041c81007a0b81c440c0400d544032902481204042c090381e0f400034a40782e01c40c03031100d41c010031268100c030036001da00a66013142c1072407980044000385e00402c08008403000210110f4001181c6c00c0c0380074004101500e50310140d03800f5440a800d114000442 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 791072194 1250 791070944 791070977
    0xb0403020f1c0b07081006110642180106020712060612050c010314240402040e010f09060f05060d090303090b16080604060b09012604150e060c03011412010603050706091d07 76
    0x880d00c00462680082b00b254002d600f054009611a81640034116102c80c4000740203603408198184c924980044c100e04d440c3c406007035540025100e00329429501c03540005000803c140916901034401c5010380400c0e0980000101280d0720300c01041001f401303140502c4a801c0b49118107440c074041e4051020a2010703a1801f05000e44503940c08050100e9004000040c03030f002c3e40b14008143d03a0701d10700603c5034959420000014506a0007441d5000c2c8007001a01ca01d003600e5404243e0251290801103501022a1a0522404070450f0200340c11015101c0e03007003c4603400003506500c840c04550421925080002c0103c0b0780c010801c86038141b280c2c0d009588030300c801f01f680440740212a01e0311403007145080c1c42c04503600181062140707200ca08005405401180c04510700b445a01000301c8642180e180c0b800d0180800d180a080c01e400001046200c0d072092400e005407800b86000e0f400505116141440081c82507105500c603154201071110442000392032290001c0c0c0208107442d00300c1402c0d4001d0030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 791073444 1250 791072194 791072251
    0x260103032f1c11070302060301050d0501090b070806030f15060123030408070c09141611010203040b090c060c06190e0d180b0403020f1c0b070810061106 67
    0x7520091032107000e010b40c40d10080707120302000844055480b418010450243c20b6030303880741404001d60000044c40140964281f00764600350040c000c00000c0340d1040d00c0c1d1202d6451241c2501e206c400222100c00700002c0303050400007403981290b10001005020201040b01540d48006000d8a0400041d00c104250070581a0211900c200402541980d6170909140610b82d030740c40003c04688003803104c01d000a0303c0e0400e01c035610a01181e4074110800c0c0d55150340c0080814030130f2401d44213021400c2044488428240b01a6200e80d101326005010750802031031b020300d4400d80061807480380c4010032031181041e0003c01c80e5a00825001000041c8400e40403210015255126040a5522581c1b40c149500c41c0d1200805644041101000300c909803260103420081c8074602001e03421040c00007040d900fa0800711404d006c80406098a0600540707156501402810700756410320003c2d04460070f00c0641e0890a000800601c0d49050040000b142c800505442d40c10003400da071509403030034881d070080301d90700744 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 791074694 1250 791073444 791073527
    0xf1219020f190f0b03010b071202011104140a0e0405100b0126100501140a0c020f0d0b0106030b2b24271713050301020a26010303 57
    0x908200d281c04000c03051000d0101c1e14860711030228201000090300c0314280017168107841000c2422490201e180d101d507801c0c41c004400c550708640d42e0303c16840d0b160018801510103080c1803650041c0e0300c00000100030010015030481401d036404070043c00002100006c0059031121071140c042040380400c801030b0381008907140035111034158441440740c41001c40d8501440360f1000b400c804c801507280c400443e20409590300d001403c00c404c103d0f000959004140c030f0061284000d115503440404071010640408040d00100e0b00000070388014050150503000d15003030380005031114016403600c010300d40d000b44015100440c2d150814800c030400e01c500703001060001349520010f80d100c25242e01c0f040004207400442000d2501203030302108014110f131000041030941005020742d880008542d201401d41c0040305150005141c8000081d50745c83c2800503082104440c0c0700c080d00c2c81613051064241c40d5020301001d81407091003005000186d0410301403281d490b802840d83c035885036144a040751400e18003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 791075944 1250 791074694 791074699
    0x40302130b040f09030f030b0a0506070c0f090207170f03010905071b080406140c101d01091b0e1311010e09100317030f0723180f1219020f 61
    0x444020821035540d0040740e0200d03c250303110311b41011441022021101040e40440d402151703400300308070303515140c40900505401039080c1c483e0560341740a000f81d401490b5200fa40520740105500d014040b000741228010840c0e8200c040c64280c2c03900c07041641d031005000301c1c466181e440c00460300301441003088880c0300118066480c081c001c07605001906400034400c3c000086d2030400340601480e00e41c015202c04281c40300042424940301c401c040c1c0a8680009400340550740b21603110f0702e48000740a07026031180610080d045200c03504c80c1100c050300365500002e04e82e03040c0303000384040840700e80040b421454004041401107038200300102c0702c50b0030030b003c1c0d6544011490184188100c3d00072841c1c0440b0302c00c1085400f402c00003220303c0107a00080303c02100c00c0d000d100c0021212409810035591055641040302e9000c1030510003103159030002c0ca00040c20501d214080c00c022b0410b115103213070385641140c841e08041e00c6414890341c0c640c103103e01c5e814084c000003048011501c0c1d1003214070211800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 791077194 1250 791075944 791075951
    0x2304062a0308010810020c0303040f02180c120c0403110405092406090a290d080705010c0e030106120213060e0c1903020a0f0813080318120a0203040302130b04 70
    0xd4140105952000c3c00754405034004e6510181c000d82c110b00c21140c1a140031005541140d481e80c5449280c002168803c0e07810403414104800d20032040c5a040b442860300c1c0d02e030551a4011400715900f2514014481e40b0210f60800050001c51601d02005259a400b150f010500b81d82d0100454180141201e810541e5180c0c440200304654200d0380c130501c100005c0c0e603441b280f641e501c242c0101795402d03290f01a5880da150043c4840c40035102440c034801c40c9024295404034401641d50742540e5021210684803a590b0300603040d00250f100b080100e42e00011402404240e081080030082d90840620080c440d101c0441000d060031480c0d000800248814145080c1d80c1c6401d110340e031040d81c0054802d03440c1c1110650005020b600078401d480c4a11900c1d5501411340115010669010a002d0455010a80900b4040c0001600f00c0000c6124141687c01050b00d040440c80071807030111115a11310004074284640c032000f650000a50382200d030103c0f00b03140c82c400d40d034928800400d4400151600b1a04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 791078444 1250 791077194 791077277
    0xc05031812030c120c070803180a080f040501030c08070206240d050109050d0c110904212a0809012d021b06030622180b0106230406 58
    0x40303c8010301490040365a064149940352075603100107104240f0001c1010100f8030214040d003120001c08080c64040c1c200300c4503aa030264552a07003a40000c00f21921010002506100c10359050082010345a4103043c00c000038109500041c1d120807000307040004030351112411803103e01d01c01e014071341d01087c040e120107400113031420701d14041d000d8158203032228415440e00100151240c1c95000b496504100200c00c410180c008004248402400580d255100b9011156809111441c00035100a00da103d400d410191150088a8199070f50000300403010b03072951110106040c1c0040310000002481c21001d02e6a0042030050708100e9009000343c0c0440c1c002142c2c00f1941c0004d5405e40f8449107c080e10345040181042207000d2100b160000e800c003480d0060f000000d54080f503031600c0070800d480c01003035800c03c000e9030302c58401c40b244044c0d4031344000301d00400c030590b008061910300d030030020300b4400c1e12580d4400680080c4524131500007004080c8068669002c01400c0c400348194843d451203d0160 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 791079694 1250 791078444 791078461
    0x9080c06010812030702120d0f0f05040201081b040e040f151a0402090609090a0b0301020c0318030705090711071802090a0605040501020a020f04021201230102010c0503181203 77
    0x542401040314510456a020104840f00c6041e0380c070840a82e8002e00301c0b40b00300341041d03a0700d030060041c0c02e0344030743c40350051509403c00e030160501005000c070001503e8039086c0001003c0e4540030300858401410500d81d8544011064111401c8d14150801c80300f8507101e5261002100d5060030018050700102d8018064030607480c1c110280010f610f0704200300c41c03046802004124801d041681d540907600304524141d6041403c9869404440c40c000000d412141f100440d080ea4820503130072295800000c0c03080c03011004d540c0c038141d40141c10f0340245186400e0074042648007502600360001d1241070484503680c03d50400640380908240019440c401c00401c2e82c800180d080a003400c0e03c5460b04c820b020030031502c00c07402d81e004c80341f05a004040c4924640c080c8404440340012041d007040d000c00040c1c00d40c0003c0300c5d8581c000c09045001c40360075229401044055030311402064110390410911580ca154003106494104242d01a00c081d402c402801542c0340c2a0b44880d44d10300680044208507100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 791080944 1250 791079694 791079703
    0x402030405060a20180112020408032a03070b04151b080a090c060309020d06060608071409060a1b0605040308010501120b03030406030c020313032f01020604110409080c 74
    0xd4500340418030902c500302c1034404d0901000c03942906254028002c0802c40c40e00304480c20030218060408204014941094100b40c0c1c0c07064201080a80c03000500c809509081c0d9841d4084c480c0a080404041a244144036124442e100000d801e102900010405021003000c084442c0e00440e03000300310b01007404421041c00d841d519155400705120354000382c1ca60390303d4040d10703480560026044c6950713030038a40142c0041130750798800ea800c1158925041c0019a652096501402064444a0703951426810003052800a0644501180c1061103030f090552075640541c0c00c41c5080d8207001c40302c800e042506584400c40010064038082c00c04e01844207241d0400d003254140c075000e0baa801195001064200107580c00c031100c12790194000c2000b0808144aa400350b070f42c80320a8810350b441d04013155100f00c01c942060700241c0303040006800301c220100000d942240d4400406007920b03140d59001c1c001035105c802c0108042c1016210314869a825038075179000800e4168015606038603045e96400e081d81e17a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 791082194 1250 791080944 791080951
    0x10e03030f031009050123040c050702060c010203010f05030a080301120f080310031401020c0a170c070f241205090c0604170606030609032d04060210060b0405151602040203040506 79
    0x252170f100022800c4420750400b1580820030f080e000315051503107007e020042401c54a60401c12005211900045e030b100340080482803001000035860b9418604c5100c0070700c44503445140300742e104204280006541509407070444c0c185030301401c000105400c02902c0d180415030001c1541e00000100b0404242c285208026203004190000203400b08481140c200d101f041d107559115800960b040c00090580000d50780d20304c0180304442d0800d03091100840c51320b00590040110994080f0045c003002008500745083c080b80c140c3d0190f1300312000c01b00038104a6581031a241c5039a100c0002031440c0c10308019004241c00007502e16903403207a445400c600c108100c0d500081c80c601855010a0040c600041c0c0140034403840d502440c41c00d10481c0d9034090100030060615500080c019611a00550b107201802c010328030307900a03044002c2c005540b07208660b16a0056181a8020300080c0601e4643d4200d08880e40c003210105550f413a10741059214040c102c00b402544140000f041104005020490701d00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 791083444 1250 791082194 791082209
    0x6150918050c120705040b0f30010c0e0607020a080609010b010810050306240301090c03031e050409200a05040f090b031218090f100f0311010e03030f0310 68
    0x1c0c0510b00400c128500e03a01405006690b80000010702c080c0c6800e40c400c4c151020018150a03001c0203400108900464101081d410300107101c40e244803c00400007103d0500d00d4600080008052414020b881c0540419141d4080c110201c1d03101c2c1152222022080034112980495506151031711071039001c0d180d0610144d00040418010520780c0c10015010b5041d681c000f03025242c165141000b60301c507004d000ca40140c030f250032001500400d4500f8810001c415000301e1802042c4d80c1582809050000c0d400038981141003600303150352410750300100b0b035402d0b210100000300f2a812104500398000822b94101000500d0005032040c030160840014021510518180d403070701556000c41400300c48460944a0b01034006c102000401003220008000e414100c0d8883c0318040014804a80c1070282240e030b4000b541034100c24400c5494002004100605d04615000751003802c66a45101440001c07003010705110040c50901c9140d0b60a0003070722a50401c10405079200d240c070000034481c44596120341807 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 791084694 1250 791083444 791083453
    0x10e100b0d0203060103081c02040e060f030307031d0105040807090507090509160503040f060509060603012702061e03090309092410050c150609100806040615091805 73
    0x4981484070191403019002800303800203030303e0350f180c0050742d42c44a2400c2c0d8260104036802d14020b151440503001400300c41c52400d015103401402c0c040c0c2064028915442540b09202c5400000d502800b080c590301444191030901d20002070040e6118060f80d04800540d00030250007142035903040e840244921840d41d81d00021541e69403d00101050a840701c250201c0100c1460000c14010002503403c50b10810100240001c43c0d00d44c0d01c100c5000742d83c100401e4024100784016841e0900030a01d1440a110070b0400c08000412024404108118024040c03500803810070058490718850300010300701034008681c2c80c0790072620b07103440e503100d65402c9202e0034581e408140d20100d0b0034041004400c018030380c0c07090440c8100400c5007a540001002040100400181c0031048040c490880d00e601020306040c01d9051100401c000008005e14101c140c20000404003c91302c00000c1250300301d034000d03000040191b4000c81d5030700840f14a4001c0c58150341001d0340082c0821001d10310300c558502850544 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 791085944 1250 791084694 791084711
    0x5100501090614090a15050d0b0306070e010305060f09040507181a0d060f0213031a1303080a09050a031d040c0f1b0b0c0304030906140723010e10 64
    0x19140c18845000e1040000c181c840701800039603c80d0000c190b64007000f8004440d0030369905806a502405c80413400000b40301061069440f43c141c052115010f604501601d59413401074002010503101c250040d040544030008201c17541c640c120f0f2054203520207003844110385054202182e43d41d80c5c902c00d1a03440e4041041040c4024032070320034024588090000c140b9495031910405c0002c003085d0b0802c1d1040303070307407000e07100c00e48107003840144905a01010b4440b40c05185080c6180d2066000340c0040404444a0401c012501940c3d0400038140c0d250030b003990503440b202249001012a550300500c507218205070038040c190070500c0000400c4600300140b410b69070840900c015150f03201050004102010b080c0342d4968001d00e4803805400e06250a45151501c1751140c0d40c00000c25a03030100021000000c0c00b090607807290390000a840107080c400c0c004030b02d0200301300062003800405418206c410740130500d6181c80240c8800d0740b40403a8000e00c082103031306662980f00e5948220590906203400300c030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 791087194 1250 791085944 791085947
    0x151515050a18050108010302130e0f010b0a050118090e0f07060e09070c050705010f110109080a08010501090303050d110909181b0a0e0a0b03160305150402030d03090201180905100501 80
    0x1410a5840603175540d1103e91039036081c0709204a80c0d281c4d08641d19254518420710007400c010088024844400100b01c081442c014082000fa00390081810802c01408450602e12295000011940012000600240c0c00c5158508080151703113032058500a1003000954503030b00104e080c1069004681c0c404a80e2914a4260b41d42d400240004110341c2164404001560107046488000041c3d410311140b14170145a400d0300711013038402d0840c0c0316000495402e140a6000c41107c2c0504002c0c02d10840c1c1d2030458802034954040d0740b6040c0c500e980c40b010700c080d2580300c1c1c00c00c0e00c04c0481c020b031400b00c85040130102d440c08076603a5500c14110b44a1054600103219140c160071105450103000e00000e2410012003902c0c524004004503210f40e11000d01100070b803803c00400e0f042000031291040c0c40d50451528a040c016585120400c55031100b0034040540d5020501c0080c3c50010b042c0065090381d0707440180d4100b8441c0000356643e048020000580028a0308098410740d00d001000c08074640310f200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 791088444 1250 791087194 791087237
    0x105041109010c021203220317040806150d060204030b0f0a020313110a051825050a080721020417010515011110060f090e0a151515050a 60
    0x9140000d00a20343c280c054142078400c60401c4160200b507034030b88460012203100c1c0e02c000110480c2c26403401d1404009001d02d0074070000711200d59102051900b480c0128066403140c0251841d1101d00d00341316080201d54641344000b504c035034070900035502d807566410985010b0004031103029000340720200040100d0b1640c42200d208800c40c81c1410014035035a11807401000c80405c50136004407080a02080e95603803510a00c4070001502e80415141c41e14009181c1e503030315070b808205061000c0e49008240356030410305030760801c41c2e05d2030040195a00c406080710365a60303500d100041c048030200003665046542c0c00400681c0c0428082540c4542c40310002c41c22070b0811a0320642058131817603152059840303540b42c0420a5a442c1c1185d1000080030300b404d0807030700c0c1c1e54856081819025000c121a1509002d06007c0030b5521028016080058403a2410001c6186500d0380c0603036124480603c0f1050b10704920050644a0750301a0138000032a006000c2c0d0740031035455008a542f451510346036824000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 791089694 1250 791088444 791088457
    0x6150501050f0c0f15180109111e04050907080f1b040e120c0307020a05090633131a04120609030309080a021c030c0509060906090a030b01050411 64
    0x303441c180b038901c045031803a20640020210041d5405983c40032044000c0411089802030040b62890f0000d0500340901c42c8840c60165808805034146040c1c400032803070606800002e00c10503101c0b90f0000369007420180e40c450050b01780740e500074504000d0040c410720000301c2c2c0e800d580911007110a10b410300c45800e56901c0d00200d111005a441215030f1140e4102030304924078542c000710849802481c5004502c0c8c01e40c01048014080754004a560001c1d441d02148543c0181030944400c603c40c1000c0000c00e0f904e0008501503140c190385880001d0400040000b641c40c0c2504a9100725116103444201d02c00c402a0b500c00c1000720300b55404111483c0e101070040318210b9112a004001000c850394940001e4254000c0a0301450703174501200c008a01948010803507020303640d002d40502c5030704000c1c8540c1c0100610017241007500d09080003400a03004411242e0044003200e10799100c4941b0300010314a44994104290000410350001040080403081d26040e01c400711418003000c40e65a4212107180540d6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 791090944 1250 791089694 791089697
    0x2120708240d020f030a0f030302070507091a0d0212030a031505060306010519090e090327060417070b19120b060702060d090c060504050112060305060c0c15010605030406150501 78
    0x7032128001807404240a84c900e01024060b5480c403055601c0b80b450700d00350b100e000e4006c250002543d034108601408084090002c0e000f04000201ea100880702c400100801050301a07250005508150360710081c00140000d99441125655007800304020003400040016000e07425101760040382901d0a542940d02c2040187d4605080040c4007034254000c140b20908401440074842010410b454600c40035480350388440e0044d642c848240041c00e15400207048010030400d505929844c6680e100c4003200c044520960781803000e0281202c00505080c003541c0302210007040080e104403200101d541c28191a0250388822640d2800d0121030420f079058840c03034561142c0100850401441c0c4200038005c6200104030025070401240d403042490446a004075010901c0810704000035a48035002d282c4485403404144015440c40d654030b696288007070484201000f020070042141c40081045808102d07411989420550751100d02030a258030544d0181d4141e030911390981c03550b4441d40c5401c801c0300e006 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 791092194 1250 791090944 791090959
    0x1b010203030c0a0e04020a030c08060415050607030e0303030a09050f03090904150e101e060e070c031209060b0901060201091101030507020c03060a020306090603190b06040212070824 80
    0x80c40300d2509180d121030030b0702091104a24006480d0746a031b101411005140b510001010103442c100608020402008107100e103040140c50a00015004421000c035603094490301d44882c0d0b40e1a044d00c0c400130280c01641c00d031101104004601189820010b6958081c1c6c0682c1c50404031001c00644a1180440458101001e031010034000742800f26600004600100c5c006a0102d83c2c1c40c070b5900701441181d0300c20ba01920f80c91100500501200c6503a914000d50314100f04071840d0807000d140c2504000c01c1c020500c00000c01640c10b0601420b07245025690004081140c0d0740c5600d4040c0003003040240e506c2c02500e07058008911140140b29001c5030940141901a0420701680118068a8001d03d12021401800d80340ca1940d1420840386002d403168000c05a100e140050038041d807041e0040102e03200303610042014410640b9500a408060340081541103640da030f20020401038802c90090a401d40a2941044030b1254805601402502054091281c19a80380510900d0064480350720f68071022 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 791093444 1250 791092194 791092201
    0x3061a040c140a052505070e130f020f01020309060d0203010906060305190e0c03010e03120604020a122a050a020c0105090a180603061d0f03040e1306060f12051b01020303 75
    0x244c0c02801043d81081c02d441c00030030088900e60800c20748460104c030035501c2600c00f446061180400c031588890b001ca8220f69108a50322203c0074100410f4010340144030b5100726003e164801e0046448041c0041c1c0322540d1030f04c10341c60b160003d620922940d50030510b4204080b0b006442401b81038020756090141620b00c1000c079110348008c006000c0d946d075071885100f200e102035460030f004600d1500d91142c0916110f149007100382d650300500600c200d00c21803041000d1000340340c1042c0800c6404084c00707800a90140564000c12a00c3c000c0080e401120041100704000355034440c004202c4055603a083d1828504200010b484901500c000a03600221035001404288035851a002c89124a64804030b5100d03901d484600407100f42801f9a42840120401c90501c098200010340751806d42100031850245030490740841b8100c040d20018508418441c446d00b801104d80094010700500207560181c660307541d020001c1981041d00c200c0d01750007400a000da03043c10400c00b1180c0c0201c1038000e18955038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 791094694 1250 791093444 791093447
    0x703050c0604061d04271704052103040b0f091c051e01091505010302241902032101061403220201181418101a0403061a040c140a 57
    0x310400c1c41320b0f00140d46500520790305800102d0000e03a8459107560900200c66800e1000d40f854003016100c20946080200b041207031140030780360f030710140c0d0303a10300c055241c0741c400e40582075102c0c0d94001d0504410100300318003044a80030061280c1c080031245950048108400703045010451140034041e60000d280481644194000410300e55100c1800000c94240075074511500c0c0001c84003c0b00d00d607544000500441c140280104030701580c00138002898680030021180f0b41c41490718011044554a000401040c000c00550f00d80400c0d1003548810600001c1c4c0e400032442091140d10001000052990501503002003101e0042c80903040c269010541500c0340420108071000c128104000d918a00c504945e86030032417405032041304101b42404285c10100b1111444000418002ca01e5800034440300808110361041100d03c204c070280320501002ca0340f00d989000780d6001601d810b003060800d64100c510752030208c54289044504015402c1000c208558004018020405000c8108106c012a6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 791095944 1250 791094694 791094737
    0x60907020a110f0a08010f050c121b04080a060c080c04030309050603150603100e0c0c0c100201021b0109050f010504121107031a0906061002030d090507080f0703050c060406 76
    0xe00c040d10f444509107041c404101c0c3c1c01120f0344010b0841e550340004e4220900d0501840d5004a0300304901e50800700203e015562080028088421440d50121400b101030758660071f440003010441c05840c0440c244d030410601600d81790751404000ba600340001680c0b594040b058909a0b505503845030110343c1480248107843d0701c042d04001c1d440c04103245000300c42d9604001036104410030119846100d20708221070201804c06044200744140034081c4041c590300c0007940c640030b494212010081107040c650180d0082c411404c006030120070607859040758050541080c650b1605c035a04407a40390341103c07208d901300d510070f540003040c0d0b80c8180c030100d603c0d40c8100c4403424243c4a25080d00c116507903a07512010201c4000451016100030a800c00580702c00901000350311400645211404210384c46000b0340301d200d8800c6600c441036072003c090043c030204020308001350100b0811202002001c0b244940c1d208014401203403140704c0c2c11403c64480c2040b005032412107025840c0d5200161411000c904076 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 791097194 1250 791095944 791095973
    0x8010b0d15080712031d0f010302031b220b04080d26040c06110d021009030507060c17150112090614180f01110a030e0a050a05030d05060907020a 64
    0xc0211940e00460005000c1c00f80c0c03001055051103811070f203080c0c1c2c5005004a0304e07946000d41010903400408910b0f03201c068600c1d49003e000d10b80141d6030390318113614102e0f08102c82c6407850a4480401e00a85150040b96410424070b6003104074070780c143d52807008101d41c2c4603d0142100c0350300034010801e4a9406003543c003075601c07068103e54030342c5012020010960002200c05480d48180c0e000e04029490304110740300e4625511070050404400a0300340a540c1d071141610001c05156590241402d25105d503064032140b552016040c0102c0311105401046072040800d600c8180d02688040b540c5101c030008a06418001078491940304520890414002c01d03400f842920341d991140c1c070a40700d00c1801415640700300c42c0c06e01e02c100d080c0728260b1140c1c43c00c1304030b40303401485030700d8000b2442e114442e0509580305480300d0703d000700d580325800032801e08064001c24010304a100e0320745508100800840503000c01c0b00e1a00042042e03603520002c120603801c0031348000000d07812154509010038144004280c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 791098444 1250 791097194 791097221
    0xc030b040c0e0c03180f070605030a0204030b010b0d0e0f0c060f390a170c010e030a020c03010c030b2206120c05130b1c110d050a0308060108010b0d 65
    0x7034265501088084040b040b110581514000410044400c8031983c010360005060710040c02c441c5000a0682d031760b0405402140b051110100006013400ba0030b8044401030755201824514559566080c0b4100d90017040c44802e01030b050421020a08000007482060036000a00600c07205c1c44150034082180c3c080241007401d0b1000b0480900407003041580c200203440c000c201c3c004001d222800703285017100c2071854800c16070404030710840070a042d44d840c0c00c65003440090260b60b5a55030a52540117052020004200d80070114410ac10980c010943c070820100c10740003400910005501202100c00350f0642540c00124000210486180e000030620134000c1c0b0740c1c0000760a51650b8204d107984050040848071482d44800c184158108504021f204046026091200c0304a800c00114014503200d9054107492460004005205131401045c05244024100500454241c146641c031640c0e800c50035800b0405440228000e035200d02c10440c1243c0420028906041818240030003800312601e8454 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 791099694 1250 791098444 791098463
    0xc0309020a03140d0906021005100e040c09180b150a05031e070801021602151903052403060606090d0210090e0a050408160201051e0a030f05040c030b04 67
    0x1006841e2007201c80c1c041c0d400f8148403820000c0c198011407800004051003010000f0300142001000d8002039218500070b010036012520780e4603171000c40c4801c4980c6d4071811000440d02c003880700740101040040c0c1510b14502c41404800910307904291f040b42c404100a00c0104a4800128010b012201440207000e00a043c1120590f44a00003807900d000007080042c81c00d0300c0c00750341001e66410850030001340300180c02542070088180400ca101e00300c040000c7d004915a81c040c10510041170200c4421109a84100c55038000c8400001e00510007200d01a01e051040342401034201c48181e441100302c00018020901503482906102c0c0342e4000c1c00d8101d030007900c5c4411450060386e46919204500324155106030070305150284c0d5401e941405072618500c1890b00342400042001032040b201c003041c4c43e2484a05038a010b1004880922030440c500c1840d40001c0003100e60052840010308800440744d0f82482095500d01c100c108403281510010815041c2c5030081000a138075a110f60b90003401143d414 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 791100944 1250 791099694 791099711
    0x21c0e040534080708131202061501080103020a030809010c0b0c0a0e0607051e0106030507140307170a1205040504290f06040323190b15031b0a1701230f07030c03 71
    0x60700e00c604801f00003c0581c01010800c40c0300203c10070245030390070007483c000030349501d9034020480c000504d000c05010382c400003520340c4941c2d01075081000d5aa85c0055542200c0c41d200c01307280c0b0a900925000c20000d2140c0c4801c6642e407900c041a02c0c207658000000d0019801c0f4842c2207107100921260061141d500d40800102085081c024031005107010060343c501c42c2d01c40c0c010175052151a03041403045039001103110742d03000c0d070001d08000300552040b041c08041845100503611030040e0707407080350b000b814a004003114034500b00d0808540c02c28242030034080900300c400c01000d48001500341d50000000e00c41040484c070706202031002c1410220f214282003400c619240d00305150071161412110802600310108222081000d81c01865001515110230b0988000b94031040c003e17503400144140b5540c00c100d2580c41244102c0185504103100c0000b0030030605031f9006c1c014071002c880490b4a10984011f403403030030034002c03446001a0111022507a0300c0001c04d400a001c0c0300399110405039144030b00e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 791102194 1250 791100944 791100953
    0x50705040e010906050a050108060c091c050c01030c0801060e0f0a260f0a120503060114131403060601020304030305130f180c0f021c0e04053408070813 67
    0x110280c500c0040c0002c6402c4803039041c5201905c50280c0a40c19039850400100204003020458540104421089650341e4120400003084002c000400e90401244080741104024001900c2c00d0007840a88040c49000310440095859600074030809011400701c406103880c43c584044039034a000341c0104a42d00142d142c142043c3c0355881e400a074142170244108410500307034104017030003d069054004102c8004190760385c4c149040005c1c01c2d00305000d070100100740241e0007118114020441464540c0c5c0314581841c07240c00c8406944941144202c25410068050070b011450074818401038005603c0c00d8903540e02207515074800d005440441c0282c07000405c07032459070000c480c0144420281004d1100b01d090802d0100d84040c0b14800034040c06680b0000066000f00d0f010303444a81000b41c130041d0a529140c02d540c20818800c0c010b500515000030442c411014003203519003010290b810164000742920b011070254850b10442000c51080d90000c0c4440e0b21075103026238008000040c3c1d80f80743c052550f4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 791103444 1250 791102194 791102201
    0xb1c03030e0313080f07080c09090309040c030c11070b1b030f04150e09070c020f0a0b03040c0f080304121211030a02010b2b06090302030c06091510140d05070504 71
    0x116800f42948040410106100b008043c0140005401134251349140c4030003599a003810000c101d000b001001d0014154607410310503138a103900050410310a1507400c44004000309035425500d80456403400030f4080010001030448150b8041001d89450a0001c01d807800f5401158044186140b00030844248595000c6001e00020000b41c41105554010303154081c000c0e40300303440d003d0f01808902c0104084243d100550541064042d40c04841b011901070110384068100d400c00c4001d5140001031004110f041b060003011034107500d12202c403c98491394010340724403961041c02001cac0803e0441c14040341030120003e031000c0280c100707003075804003d2202c5800c580202d507186005d41d541d00d40aa01c0c070304280703403a1003500e43d003210505904040560740210314a113504015000700d40d1081c1c4031042500070011950307010211400c0f11590b10b03080c00000d0361810242c42003a03c0601c11800301d41620800c0c17190400303942c04078110111020b8180706020b04070f80c414500752158452641c000071992210711 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 791104694 1250 791103444 791103457
    0x4020616080309011a03250515091906080412210213080d0f050c072711030708071805060310091b020a0807110a15120b1c03030e03 58
    0x741030b141d14042c0c0c80107003194856103052503202c030020054115540d020030340740fa0001c201c03403241c0600209401c1a07254803106400c003580000c0c82160381c0404880030781c050504950200c03070403c0c1c800c4110040c0f40c1d040909100305800710345580003107000206a4500410380084e40d29062420342e032060701a901050b4280300d541c00703990f0f00058443c004011210610040c004000050440745111a8000c12804102c080781c0c0801c03001003103402000074240300100003000070710582e04281a42c81001031301d0030209810f200c1070fa46000000313041d850510040d20310500441e01c410081d5030340c4900c161170000b011412a00c5d0983e091030041a01e959250145000d0b00d20525501c050350b00b040101012195102304070300300468510700c80401c4550005441105039405411252980d2052803c0c404c880804c04080d5031101c041440030448294a90100501c1500c50303407031003155001404e2000032035960200d041d801c103548500810382800e109510002c7d0511910700012441c035246142d50440d00300d107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 791105944 1250 791104694 791104703
    0xc09040501030b061207061b0602040812190318140f0f010b030d0e09070311040f03032a0b2e091d070f140d12030b090c0715020304020616 61
    0x43c080c0031150511644000e041062600200305a41c204140a00011241450008200c01c80d0746440108006901600c0003030404d441190081e880482d107500303a03500484820900310b0541010441c1031442070046c900b0594003660407001490803500d905c0000c0d00541c0d204041d510600d10207002925081001c0e04c0c10350325500001030b06080841c2010f05000310002000200000540070b444596201c002d80d50b04601a802c0c002800a0440d04014440c007565205a2484c0c09080c0c002041c150031a000d443c109a04c03c410340059481c030800912480d6040c5000340602e00c8010008511214049040151601410280224070746402410000c107600b504010504c85d01c907c0000c40d002c01801440e0703a02c954000c054201141002e5500c81c0c00c02451003140140b01d014012304025131580c00180d0303003940c1c1184900030b00c40d85048028001c2c0035083c034090702030044c0b403000480c1c900c83c59041d40c0000340d100519450031003280c1c02240c06034002520030b80e4880000c000c43c00800030325110403161544035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 791107194 1250 791105944 791105963
    0xc030c1a0a0b0103060303080a2d091502040b12060a090204090f110a020d08040215030103060c0f140406080c04081c08070203190c03021204082b080402090c0904050103 74
    0x54550141a2500381402c10305150500c0010710000350008100c41d4000304443e0000f517482d1044c170301a904a81c4040540200d0a80290800181ca01741d420401045000d241004129036104090303001300e1103a0712615001e500300344a00c0e103980c41c1500041d41c001d40c1c0101000503080c3c4803003841040b030340598000030380310380da070404056400c80f98005c0190061036030030014245880810060340390800c2ca2144010003140344001021582c0c0c1703441130101c0d0042e55070036580725070710303450100000c01c3e102d206240031074100748900d07821502c40c80c03c0303134002c00e124001d040c1020300d0500301762281c1c900500280791002c0144000310b1103880070805468001c40f511000b0402c440704010142500c10007030180411904100308400c2502909071200c4100c080c1c52514108242d0030742400c9041020365441280300280005002844150000c0c04c2d80000f640030612a0044201e207003405800703029100c003900400c4003c80080c0140c42d02c0241c03542e000b003481c06a10325003500740000404841c000d80003200e60710071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 791108444 1250 791107194 791107201
    0x3031d0f060a050601140f04150306050102011a0a060e01090b1602011202091c02060c010e06010f091b050304080c15040b010902070f1401060801090804030b0c190c030c1a 75
    0x1020401c803900440d881d10100014285600000d040a00c680c1000c1c44008000034194241081141201d005008044282d00d5120940700c004010702060b104490044d0b0030300401d204040070141d17540b80c04100060840358141d1904100ba22007050100007141070007145d05001641c0b20289001748841c2002085100080b40c0b98400548001c200c003141e41003da1040c8808507041e201c003510301c000900c049002d01d08182d20b502c0040d0507032140c0c4042c10b1071542001c80440950f48005040c81c161085920141c00c095201c406000c11181034021003a141c80100368003400c100d00482c015900300b40910754039450000391980b51460041d01d00c00d011229020081041300b40141030110502500e09a60154a040c64a840f001040c03040408051b1121240000884010200b507000314000e001d14402801554480e040183d4140c1151000ba640c041c100f2001444205400b011526682092510000d8000c0c041d14200c0b00801140c5040342440704081c0120042070305901920b40300740b42021108583d18 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 791109694 1250 791108444 791108473
    0x1e0303070b0f0a0c0519080a150e1806100308030c07020616150209090103020d1103030f0a02010605120606010f2f150603120306301015030b0603120403050312151c03031d 75
    0x1405600be61106030004800e1040103420036080d01c040381c2c0c0210805490340c5400080e01c6c424820540000e6118400003030034a24842d0b40340728625400d0181320403001d4031019610040583c86180009039000160320010b10062900e150341c0d02c0d0b982c1c001d01076070400c507008401191843d030005000c521301003008a02d11781000e909000d00c202914042d224006900c1205003015600d0304040e003024107100c101e55668040c5441030303465452418810340071300040d6111015081c0000c1d461140c02d401da01440d020306d00c1c444139850380140200390241c018010b0940c04949200640c1014140355840640e011480b031090b9407006102c61040c00e1103031b02c080c0315003003071302c0843c6000310031401080c0460802124002e905481c40c107910469401c24a015544d5440c44002410030080e100f00140c05040030501009001000011700340403e00303049080c0c056200c0040251042c0c1c0c01c00c2c0101e6100700074a03c401004120b94000f030080d81d10070300300821001c481700c840c422003500b01c4d5180101039120084803601c28 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 791110944 1250 791109694 791109721
    0x2090603131205190e030a060c1101060e060d0b04060f140708091f0c02120c150108010605030a110105073305061e0303070b0f0a0c0519080a150e 64
    0xc12141c2003151504c0c0020084549240340c06084009020030f1209040c05501d050000400859210808010b001b9070b8010150461901f444e034005591702e01b200c04280018220301c840d028090040850300d88407441d60303c0000c12180140201c401c2c031b49440c8811141c1500c3d0196114a030703032500d400031940c0391142d0010032600c802000c10071558058210f440c1c250607140460b144c400d481010100e20b400c0d07000010391030814420084d109035607000503400051100483c5802ca2001050ba03030407441e0740e0350081c0d1030980f00355004640d4141c0107410a4000142d0383c070000011060b060602900380541d58031500f2005080580c0a00542c0b1140c0100380c403030001600d40041005111010806801c142e0045102d0460710b4113a80d2000d00d240309541c81665003001611003080c2d1001001030203103881c00c5803c11903081501c3c070003191230500c05038881060003401031b2500c0c0002d1031801c0404542030301080f10405800b90191100c03550b15000c0303001034142441c0ca8000382c4809107406580b03040014158005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 791112194 1250 791110944 791110973
    0xe0a0c090b1305240120060609010b0408062418011503090302070509040f15020703090e2211150310061806050a2a0b060402041802030a0209060313 65
    0x1080c0341ca02000140761a10407641501d50204d0391000300b800e00400103030303002040c030a407198180000000100364600d00080061145606843d03d0782d20b6642c80148a00324051401f604103603070044c1c400039401144485a41074011350700c100c5001500381850200b8a1548615542014460b140e401800f068441114a600e140b5081c9002c1140c0260703520000c0d11502580a43c510500031a804902407141110300a50065080040d4407443d03051240f44134000d40c4800c4045002c10306401001031010010104d01d0b203d900844a8401980f0407082281c0101500c2803048030b50500f00c1001f4105a2940e24464092000066105640c0c1c182011a5a95003429034480f10411981241c0c4d01c01da240e40900b903008a80c0c1a040490310303a5501c04c01655020084c1c0403010743c054056030000c0d20420101c49191132680200c0b00c1e050540c8400052100341d2146000310802c0c4500741c80e000710010500d038010b541c8880c0031080141010304407000580c85030b00543d184561041ca08955505101014a003441c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 791113444 1250 791112194 791112229
    0x4090f15031a240d05010e0d0206040b06060a141e0c010c2c1207051801060807082505040305070303170a1a300d0219020a090e0a0c090b 60
    0x200b05006494103c0e01540b21030810b4080c1410701c00c000c08014094000c44e64a89103401556083c80740454001d50310340c2c085030180c4000048c1008a0a81d040803811110360300c1442c0d40d01c4282d061923503119078155101000a0303500056605600e14030394002c1c009000a1102000089900410a10014141c05d40b811044111001c2d14002c2030046c4002006407a40362429100c2180d40e01200780d030541058025403026403c0a1800c1e540319050701c0b0b22100030b040c1c1d420b80d140c03600d01c0d4449941c2181d0204040740c50003440000c414400092078a401201400c020240c68890f00d0300d5140d5683e5410180d541e40214080358500c1800560b40f0031804403254055001e00c403c016034280c2104120745221386902e89402a50035010208880280c11040b1407000d0042412040e5030642c100c3c160760310300b00e01705004014040c162240d0f408400c2d0040700140e50b50003c00d0f1407680c0f828a00d200c0c00518046c452002684110100100062040d01207103008204841002071400000b00c203200250407081401d54 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 791114694 1250 791113444 791113471
    0xc0807092304020f0d050109050114070507030e21030f040305010c081509060a0302030613030f030b06030612011404030512101d04020324100e040201020304090f15031a 74
    0x7a04001900e184540c81601114440d00e016030010228441d0518034030090025400c1c011040d0a0280c150000903a442106004903140d6544401c101d03041d010380603000700051a65491904c840c07178465650f8030b2419424112603e808009001e8520b5a0b2052000440e51100800c0820500c1001e200d0018144410304052040346003c201d814000a20a8001482404c01e84045802d60b2503440300000a550f000e411241d49051000c3d80480003140250101d001420442c04440502e00c01d0080481960000c3e001c81e003580c41d084204180d011010030700002039035032480400c5544442c0005c003800f46010303880e099607601810400d40c200170801021003441700c0d0344100820107807000d00704040c0f0b01d00221131810350a8855100083c00c0c91100310306641508045503604c1010640750720168014841400c84030204c0e5070303481c09a41d640c0070840340680580c0091004101128040e041852020700d0355400043d100e90174800782c40043d18640080e10713880340400e1010150a1720801c0c00307070070451194141 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 791115944 1250 791114694 791114741
    0xa0309050705041518150602010b130e0c220c1e031506120605151c06030b2d01060302121308310b0a02150c0d11070c080709 55
    0x4400801040c42940c41c05d41107400d6903030019a4540c881400f0201400c000020700d541d034034009019242170030380e0714880d0145006046c1d0190705449001244800c04026158035110b460411681c8000c08000d12910310380075151561000c0c0c28810f200b11403560b500d40099480644081d4070354210303010b0b90074050516050310031148010184102040f2607507440e0080d440c21825000b400546040e0b0322035030b0403d10000e02282100381604c06081540c09000543e07005019071505041580c98a200c003030040701002c004903503644080d078035080d000d641c0c0c0c0004d021441c1e2280c00016051000340e00140c0000c0e408584205943c034145031071500700300781e01a480c000182e25291031289108150149801c6980e002c105001e45030013100c00340d18614200c4143c440c030b96807540000c26a620100025006001e070b10014820300c45ea00c251640a4010811400d0500008500c8207000b0880c903000c03004846020300c984000508000ca4245c0500310707800181c1080c44c540741e00d24ac2a10300720000b1124201141000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 791117194 1250 791115944 791115971
    0x20f060d0c080f281415040c0207050d02090603071206020a091202010e1014070c09060b0708030406090204092f0105041a0307110d0504180509100e10020a030905070504 74
    0x40f40130403610f48564801941c034600391000601008928000790b0138218100200c0c60300c440b2100024410a4405104071840721500b241ca800b81d034040c01380e015a8400d203000150404020035644407101030201c403d29078803504100c1c00742d950610225502d0f50005164400345a00c024514010010580d0742d01c240d50b450b500281100d464100ea03103025081703006240803038920038182c1c2406e40302c0b14000d090b51022507090442d071070401401244d84041c1484c03000251102c3c6007040f0307088a41c0001241c0e0540d1203c0c2d503013101038414500c1c10b80c1c0c02600e40c0601c1c40412009044684204075440400790700c14485000264100e090100c0070b41804420702041045605210160b00d034090030010280d176a94442d0003c5d141460311298a034901c0c07042040f604c546070f802c07034001d00c1035410502d0281c00c0000b0b41c0d83c1c04000d50790210744240d0150000142d0340388190550300400c4170305c1042c105682a203246114000105e030030541a42001075120091001880410b000700c001a081c180c07400e11584081e80c59 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 791118444 1250 791117194 791117221
    0x2040501080f0705130b0910050408100f020d050109090b09010501120204020c211321020108040203070e0a0b0f030c0609101e030f0e1513020f060d0c080f 68
    0x8503450b031034501c4000943c001d00c107800300c94000d0b85405660341c0075526406c1c01d007140e80066441e18080c94845483c000114029400d80f400c81c0c0707110000740101d04850420901030300c00c880e81c1000164090141a6140b1424002c8901800000703000090464160404c0e600001c8060060300240c0d14101c0144114080d42d4851141540c040d03c0160b5650606d41085150608681c52254980c101e44c000083d904a01c20003041d07040c03040d11103140c6460b10b07001d18150074100369401ca0038210594281d000154010f00c4421b900900043c29a055070344d07545d50101144a0072075034800e00680d10301c0b4540c1c4920f0440069000e850060700204420f102420101c0c0721072248410341403040090007602d0018610600401900c59100381d180d2000c0c488079500600a48012500c3e2052a4100240c01130000400610001504c8030f08aa00f41c02e41c90f00c2207a000c140360100c0c402c2e0b13084849401d82e900d4985514009050001c054000081e0300001480010400c80c0301030098149003040340203203d4001e600b1071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 791119694 1250 791118444 791118451
    0x16230a031b0914060403082b06050916050c01060f06022406060304140129102309030307050c0108130b0705090f2d04090b0f0612070f050f040204050108 67
    0x45441d04100020009a8130380200e0b0b10080c0341e90b100186019101d8a8040409042180c0076a4070a82d0f00d0039a01007070075101d15019894002c4995000502d048500c9464000300c40041d042003490103503900311007130a40e403043d000042d803a151181c007002001e50400085204000b4528061050029610702c4034903000003a112504c60000400441c05124203017008407480b211190007040402c4070903071403020f1061040c120403807080b1600f0140c461030802c500c1140032654155120380128140d41d13250746580c00d1400d5806003c440034848070025803820401800c60a000304010055103c082c80010a4000006e0a6006800386503404d4000201c1c50794080e0740107070302c6d82001511a034880011502d03034150f541109620000303440403460500010289a1003040d100514022007002d498140000d075002d10300020312020801c4c000a010798042d600b8503400c141c006122540300031421140d149400169000080504600503041046250842c1143c03256001a1402d500341403410001910f8210011f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 791120944 1250 791119694 791119709
    0x2031606080103081b061005030c011b0209040c08070b04090c0224040201030b0604090209030706020d0e01080903120f0106030501050409080f0315061602121516230a031b09 76
    0x303d400e503035074601c1880010803805e68038212803807441d01094418000c911803140c240603000b410000261035114a0035081e0714010420707030526503c0d0a40c24480e484070000e005890055014002042d104000d011180c0105045034045840c0c0c2e0804144804450303d001c02082954072000304842100344030034944240300d002070440807403503603036000507005040e14800c4d080d0300000002e40858005119030281c9040d0100b80c049a10842d241c090076030b510782400020001060b583c0004038090347c801e00445511191540a8034107020002d045107003555000d6803840880c0350841d005110050741440303181d00500b0101c7c1e061000b074105407680c0341d1074031a2002c200c10342900040051400445660b1801c05003901070510f03691103070602040c207400b802d600c0040b03124201502d0384081245001400030300108a51110441395100c14400601c003940010000302071009100d5140d04500c058501d11062901c2030310025030760114141c0007011a082009100c8803441d1840d055018150f20a04d4032090b01c016 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 791122194 1250 791120944 791120947
    0x605030613150609050a0e150609130c0e151203040312110c032a060315060a140c280506060411040302030a05030a0801050603040f0803070c05010c0c0203160608010308 74
    0x481d0b0128003600254001c0c1400600303020902100032415400000000000410b50b08140141030490360045d500341d1f07004d940090120f0101b041c04482101070700f00d540c482c081016210340d8503080705403d104116141c2c00f661400b0104401281850110720080700c4030031000e14909410740d03030303580210b2202e60146e00404c0042446921020301c204551030882d48000e0488015040c0248004482c10074803122100d1010302e405420789a081500a0324003940a186d298803541d10681c003880202d400018446040122608494501500e0718000f0000158040064001e04900c5001c0e8032320200c80c883c0310800c5111480000c404500d01040740b58100c1412200031601c0800d010a800c094021900301a505006000e50740d801c0003400001410f5503512038590003016179840082000b20300080350081c00c8000000701c04400036023040300a5078014040c0c144000310380c000b9140c45084603036405065022a285491020552070108541e0000b80703462901143d000c0c0c286407000f040194180b2008015400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 791123444 1250 791122194 791122223
    0x405041d06010e0115050a090302091003050c0d03120902061c0f0c2c010918020405030c100203031306020d021b012406080a1b050a1803030504030305031305030307020d02010605030613 81
    0x800c080da000214ac000304400c01030b040210b0520004c01d0944002c950380c0c0315a81d5442d100781001c400c601140b54140d182c0040340305001000001400550600b00d91010040103068040310b040030581c104a101b80c40001800c0070001c0007402102c59800200c02402103020404840d0744c00c5003e441c07194601c80140d140d03c41b0900d00169002e44d802e80100c0c0795440699240c021200f201d81c043e00859204408540d101c400840500000c04403010010006070010800111581080c40c469841c181c80780380300524040190050750101c2e049084080f230441d4540020701c0305da83c82401440f000d510554445c0e040902d186255800000c003520038007041c40290400036020b0302840d400382110310f00b15840f900c0c8410f40104000c0603a408540710310085131458441c0e01e500c100c03d1014209581c2e040d1074070307440c2038103685043d541c0303420003089800401d11364200f0100150003480914000c2e601c5400420070190315181c0a404d68086410060090788200b0400c402d07200584140312840c0d4125032211040d10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 791124694 1250 791123444 791123447
    0xe01051c05120c12090d0b0c0c10060815360d0903030f03020a0207170c0301060e060a0b19030e0f0105191103070f140405041d06010e0115050a 63
    0x1110404040c00e01d0150040d5103482c428140c008189024103041a5030392810024403910881c003d0035046900f0007102d075011000600c0710700310b2a40100e0306840080c00c00300500107075464502c004014201d52030301c03140200040d4000300301e101c031580307140070091181e450407480d00f0501134440c0034141008820fa070113030f0f1690790304001402210f82a030302c181e6a007202204c0e0003500d1507100744811000100c03030960b940d15142c407920988645100a502604038586401208004941111044117503402002180c00c0c0b96a000d201c0c100c014407c00c0310b0381d03019103440d100b005801d5101d944038003403a480410400411050010042c4140845410000303460180d081610385001404003035403450f0f41c6003005001c0b5510b4814403820a084c42c0400a000104003101a01054001528801d000c1000d00c22122512030182ca5190044c10008a03050700302a41c6a001406a510111260782d01da0001130b209075007487d0030320001c0c1c090003804031004140d500d410709084100800ca035051003002070100d1162050b5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 791125944 1250 791124694 791124739
    0xc0c0e0a0c2c131508060f0f0f06100e030a0303050a1a01170c090a030c0e13050c0f0102011104090207110904031d030c060c011b030c210e0d0c1b0e0105 67
    0x11941d04003d0310006031039805056135400182c0b40703519902844d60000302384004008030a80f0540440700b007049542c40c1c0c0c8050020807014030300301030700344030032010008170a480811011010078000d58000c961803c0c0000c2440848810802c00400880e41181241940c4d0b044040700e800303159140403085050355003800d03034900ba0040e006100c1e4000c240440c000148a0b03032078088030680d144c0c13810442c4651100040d5103103500702050002c00d01c5d04600781c403802d18a0017041407407095a041c0008910035a51603018650356002d508191003580d4082904c500740955a240c1c62000002569405200d0800d070300d002e440b040c11250140c0440e408000034245030b0b20103009441e8070150241902d034075142070b50310284c00717419445e09d0802c03004900101c2d841540e200740030710308091130b8580b901540d120f4103082d0070040860b180c03100b01085441311070208070350301d081100c421003150590b112009000d0501d0700c5290800441503c0b441c98800342024041661000b000341d044a0080f20711540c840083c4016040300c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 791127194 1250 791125944 791125961
    0xf041a0c0703030c03020606010c0c1502150106021f150b1e04030305071407060f0f0c1208010e090c13020c0a02030a0605061507120c0c0e0a0c2c13 65
    0x6034024080c00108164000b40c0c0000b130740b4400c1e000d4862654404004556510b03080c58040c04420311414104a01d040f10004207c0c40030a13071040d6040138200b000c4111690100b80d1001005074058079940303401d01101c00c0e80f00104440c083c000d0010042d07500e41500c0f07198540c0030b076000d80c10000898121800000b0b43d104407034610340c5a41c5844a54900303002d01507070001802a1440d180c2045190703c9003c4c00701324201520417945440c242c00f00c0c5031000712144140381c1d4034002400389800707410000c1b5001400c650402d194660701e40440750f041c00c543d2641e1840142154a4035444448140c2c40c5540300c403071f0050700e0890b20000607124843e003c259464038000c8003019416000740035440c030900519402c085e01c0303080c00b40c1e11305404044140b0031010354400c5c0c1030007410301c420300001c10300421b01c40c14604110900a41c0103041d569140c0c5a1031112281c155032401c51541d40d5000002441c5e041212001c034124150034004411000c0c5070010742c00400303581090711500e200c0714128000318103988001403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 791128444 1250 791127194 791127217
    0x7080f07090e071a090406061b031409092401080106020a0b1e0702070f140306010b0d11031905010504090525080a060f050c070c170a08030a200f041a 66
    0x1803ca840c0c3d40b0000b2a910600300326010304d04010012030424040e911503030005480c40785940c149d00898070110343c0901c9049501850f03010070016031040d980e0344009035010f000c6004203808011440940c1c1c040450001c00c01505000201004000158011440050b05074100c1c00310700070b5a1701c0c4a41061445003c145051000c0d500d00140701c086030b4005803c805864038054007108094440c0140c01000005401207945075120300d0040c80040c60420141101c0d4030602404941640d2506118007260000c41d5040541a0608000985d1903d94000c09004000a03182040300d60801e840d02501c0c0c500300200c01104d9142c500310201e8511045040d54020035414043c1e8811020324501040540301e004034001c1c200d0300f88404100b04407200380c201c0d00400e50105a150140386421000d86030b01d925081c41104a01510710000d0109103d100154411a0030410005050f80a14040408482900040300d040c242c1441900a0002040119001d40d1010302c0d2040f0754104012260280d841441c49a14 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 791129694 1250 791128444 791128469
    0x6030302010b0a082a0f03030a020a1a070e0915090c0a142a010b040c080405100501050f010509040e0a05280201140d1d06010807080f07090e07 63
    0xa05906511207440c195044483c1080280d9690349a692901c1800090b212a0703240c128082c2c040b02030b0f07002e001008001600c0800142e01400001c0e0441c0c110b010004096001b15801c44204020070402c00320280c40d04054109500703007190000e1250642d00c501314050314009000c14820043e40058882d90000145000c00b2880c125651b00e44681003545801c02260280c42200310070107900302604c1d0000b244845400380c035440e170540803061520b280b500023155503941c0310a034082d4a179070081105514050b00c4400d4582081d00e001d91400c00d010b141c81003a60701d418018461551210b0030601811030900c0c009840340f1400740010028040d0321540000382c4917401c22038040083c0820401845071000081413140c0d0300d074003a05810101c031584028000b8850f90380c0280d40030104000303011200007101d0001281b002540d00d41112040300398149205511043c01000402c07001c00410025003040009000140c408038041c99a0303650314010050719030307128980c07914070b12020440c6074000d080711881c05 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 791130944 1250 791129694 791129699
    0x507170904090b04140c0d0f0f08043206030f06010e03100f0c08160203070303021315020a050c0609060d0b041b03092001080f4b041709010e0406 64
    0x1200214031080600b0102e003d01d060f00d00491518007004100c7c290840f6044042130500d640c3d42010040300c020441d106002400046208030741c0b280c10411601c81441e0070321725403102d01310000c40810708086d554455182081044202405014403035007010080c00d051607005000030000341001010090b51218030f01d0f08104003082d40c900e800c24881030000303454469480e15401c000c1c0026441100d480000769104003c1c140c0024401e60003040c3c2034260100c0440510744414030034030284d84440d0b0020040e44506509424400240f2203610160021900145426908004030b809401020300204641c3d58440d103600d46612207400c00d0040031401003024402003c102c01c060f005111290b815a020340410a00301c8268000441691513100140c540c00c1113541e4502a1179049030008140503103c01140c00e403a0460b0480d4070014000e040554550341c0c80002560800728a5614071404490f41c0e80c0c2c1700180800301705090503880101da142c2d101d20342d80d0034184005840b00c0c5201282e00d5041842c29000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 791132194 1250 791130944 791130953
    0x4080c09131221141008060c04060f0c1e031403060d08070606080304061805032404020111030a0903200a03020d1b1511010b10030b0f0405090f06070507170904090b04 73
    0x4c0303108000005090000d251503040140d9540c01c100c61410f01c003403080000b40482030041030000d220b041140750500d02c040c515a00c021024107a1145640300d0b03442a03c0c801c0c00c040e009800303107100d8604420505e046280c140e0000c6e408044000c0c01800c00500018070740705120b070300d402c001e015100e40f9044a40d91135460500400801c02040709501d11904074101184500c3e020940d03d80d201d40e25040382001d082d4804444041e5117006d0b104a0500c981039889500303a00c424000343c41c80c0221500c820440c40d107581002e10361786801c0158180d08400042d40340c10780c0e5842d00c540d00152501590404130800080c608000500034443c0c041c2001c6040b4031000031401c0100b00c2c0010190065540c4640507005c0e001981d00380c44007040b010b80c0c00510f015140707400b6440784d8041036150350010600981e482c0001c002c84c0840e601a220b160705074000505219415000304070030754010305a85003c5180c508541c40303101c1951183e40c00c0000b0708600060f1102c55a50f160001404d154008290f40711505051070b1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 791133444 1250 791132194 791132231
    0x80c060610030504080f0306030a0210030219080105060304080307020f12070213020306010e060a1215030201030c0903030212031306180b0105150304020411070804080c09131221 78
    0xc405116501048010354918403030700420f03009503485154507080c05042500b620068100414040d0144035442c0e000000d0b0f030b51094284002c85264a0050303884010303404071070804178075566100502104c000108056100e0504580e80107070400000c1d41c03242c0f10450101c0c00d0803045101c8859034420600454000031b011001050424404c031000e41090310100241c4090780000c403038003404200e80514003019810000300504880026103440901000031280340c9080360000c491032035003807540360410f104558061040585113007603400c1041100d0b02d10341d03000755640a80d200c046124070020001c03a0b20b00c4004c00381d4243c081da00001c14484442e6050704031100021502c0f00f07a400c540a0070001410782030040c04814500100c2c1c800070b06d036a855400f800040c00240541e514020010000d00010481c079601400c003a001210181c41d43d1105101000b07010040076184651104141080740001680c0e0808030400780c030b007070401290964034514894403140c040301c1c9040345a030034061115012100041c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 791134694 1250 791133444 791133451
    0x90c210f1109011e14030604121407030804140303041502161202010e250501110a0c0b04060206280917040f2108040b0d090c030f050c040c0906110a080c06 68
    0x184d0300d03c2010760f07138507086004421107009290113401c100e0101c2c01151903401600744407081400c0110444004154441d800d0b484040d0540002d810300c0148001c00c0b0fa01d001404078ad81c9110300441c1141043d403240502c130142d1014950186500050920f00200010059603943c0d41090159404690444000c0d0107080340380602071039805040b85413180e4103503848000200c01910711410440905000040d90103c10030755540600b03125043c1800700148044c030a803000351915a0319992943e01e4030001038074103007000d407280c0c840162422054044072400000010f101074282c03400305100d00103050511000f01051800110407000140109a41da00c036240b003812100d0301c0507043c03118818401d02e1110108802c40060929404110800524403000098400701d4a420000206401181c0c2d80c03003043e140540c800c641c00c4100600040034000e00340285030200300305950174821000143d130000e024902901a210901c401c05190f5005050104011130500740e201140565034420400e16603561103045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 791135944 1250 791134694 791134739
    0x8010501030f14061006030e0f06070504030b011a030a05070c0b090f070b04030203060109020901270e060612010b0a02190b0f01060203070c09021804050a090c210f110901 75
    0x4441c1c4900340f40340003541c940b140904e2480841c4041c14980c080780540700c0c01c1c01d10b114a00c1080b00041c0ca081050110300d0007407005480b040d64541c86c510305942e07041c1c0143d0140742c04620101c5110300c0143c45000b01c0c2e900004445001070595100041560256860240680415000b00070800d182200285040c000102182102e02d020783d04c22a480b941d20844c00000c0d0181c011200403c141a055000740083c4103050520a004900d007110120080002607501a40f8900f0160100a4400401d108a0308050162400d51501c100c065441c4c2d0078410601c1440c0c4a2500000c00b008094400d1281c21310652841e00d02c0b0400300349508211419200a48040a244400d00000503400b030000046441d1554041d907501000d62a2100040083d04002c40380d00c070550325800c9224082e0703228462544078000041c00042c00301c4039810725001d507440607008440290f91070320945903480c41c03071114004c3c05680000b004440c03400c90b162040500009031010f541012070840040340718402074600356505104c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 791137194 1250 791135944 791135963
    0x3030504050f0a0302030708030912070807122607090506130806151806190803030a060f1d1b071202010f090b0117070803040f050406050a0806070c0c08010501030f 72
    0x16009143c44525044008000d0780c810401d48001440d8a00a140d0100440d004c0e5283c3c1040d00b0900043c0341d002002c1200d001b800001d00c001040342400c81d204942c00645414000080c1142a40302d8aa2060024464003005c010010300014451080400508405848983c81e0030b448000d90f0b100c4501030007410200e0040724001943d50700f04118141e10048001c2c100400c070400140d582e02a03005c00f414843d0025081c1c420b0800318500000000018000c240003140d136440c1c5642108200d4241e90409040d0400c02e0a00700310700c038585c1d20003920082041800c801c0948500741803040004c441c002d072813442c1c14003040d01000d00480b80e1480743c034880d440e0024800c0d001c9040e4803004880171060b0052102c12000d005122003034028044803584d11071031041f60b0017176854419944c55608103612010a88140c40424403442c10a4016000188019688100e005007809502521404020010400c001c0c0d000b8841f018440740005102c010034003d0000c210030758490038203024a548154094541901 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 791138444 1250 791137194 791137213
    0x171e040501110418050f070903020904060608030f04030b060909071a09100201050402091b0d0c020a060609060f0501021506090c0d0915050c03160809070504180b0c040e071412040303050405 83
    0x11a01c0c64447d02d20750b41c0f0003168034256820400701ca2009002079400587e2240081000c10003007000f0300040e080d4001c440d40b0b403031441c0361510140d40002d00d4540201c1d544024880c040f00005001010b5541c10003480b500f4010b5440300280c01d00034070914603402100022640b81068040d4011400f032402501d00b91529039a0880000c00070b840250b502a1130b038001c00102015484039801012005d16600c103548602c0c0c3c4a84802d000d51f80313250080e9800c140c0d5843d00f0030044044007188802008203001400c01c00b0780104100c42d0303000004011a000385002c00000300603c10010840741000c02da5101040007140700d04000000701c4404c06101e90342d5140802290070f034141441568800d580c602d200c00051140d1140480e4101c202804000f003078810303014007117810f546130f01420041d81c03588030400116072502e080000725088040d00850441c44100300c284811020aa011607000f0410309000344121103240107085244100030003280c031196040140003c05a01d500064080e9015800b210311468 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 791139694 1250 791138444 791138461
    0xb060702150a410a0c110a030813090606020d02030403350d05060411191e02060f0a14070e1906020309100e1c020406080604050d171e04050111041805 66
    0x4110320303032070002c21500c10307048000070100c107206c0d00c0003d8003400140c199035696440d412180c02644803c40418102c040600401e01181f08071001002544010710300d003541244082e45920450002a002000f4142e010290100d250710150b00c0c3c01214404004060014490f074045411000203c40c01909101c0400c0440c9454003030300000c00d151403a024030308071100491000c1c41000316010b0050040c0107260545003903251203901d101c4951600544014a401000201000b00007400d0040b806c1c904a4250003103940488030560010140c00c060912686000000d808003002c2d106103200002510400f181a550100203081000415100231b03043d08800901034503507050049030315400c029007181040620200b07215401e0708500180c40001c0150f00d6048003405e010b41250103035034560188803404540355002d583c48400d607020703001200c0e047c144001c41500130f00890b10442010410318012400b440020350002501010503101503076101c1d5a102d100301900e682d0000c42c007407140f4050010301c081 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 791140944 1250 791139694 791139697
    0x10080414070e0a0f0f0c021609140c0703020102121008100606081306020f130e0921091c2402040819030909140a0b060702150a41 57
    0x19600c202070407140359503c2c3e48240c0140703030380043c1007105621041030300c111040300e1058084261080d80940002c90340360641d080042103d50080382c969203000100b6400303012001c50300b50000b0505003000d80e91107490604030702a0140034060841c0c003040105001001f484600c00344210380044040d14041044004082700311a16441207802180940000419121511080f00c43e0140314450050400d055919401d0403600300b03002441c143e8040c8102403004400386600a81d10000d001c0040914006220101c85124290b4502d40f40c621800300c3d40c131111317603554100b00c00c031070502d404014032903030180c1440040300e441d401c0050007400041c0800e95846100d03000319070980f4280030042030988220a2410f02e440800c80c400d408001c0182804140e203a058010b0516480320361000300c44500b000c0d054001280ca448640c1840717518108606401a1107603500703100c058801010190300e410110301c1c00d40e00c0611b902000b2000c42d030141000141101000740740401c2002500700c8001d02031000c0c0b54010706 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 791142194 1250 791140944 791140949
    0xc08011e091104151a03010509060a06050a080a060929031504020d020607120309060b100c020f03010e032712070308071505090102072f0603040c051008041407 70
    0x2d4000150aa40e05400d25030450000c41c03020390802c0c180300b0f50b204072002540340d4000a02e0241c040c0000104101d180c2141455000041220701c003c0703540c42c120000e030161140d591a50f050001d404001183c2404950007040181454002803280001800c0c0c0c03a6903181150024491504095030000300354140000c000441a11f400401c0e801504d4030b4080144200e950541268082d00401050740094030206480100303001c41d460224041256103000c00960720050501c60060061000841e80c0c2544007009041040c3c055600038486280c0ca00400c0c050200e10880145074480002c000e60001c0701041c90200ca410089903540b0700c400031b0000c01414141c0c10032007102a0380203b6007403010407100401041000c0c429001076085404c215a104103881c1d0494074041c55940c049608002d00410b0441246c0c8423010201c0d10f14108201010841107030700e07069460380078101c048005010440d028080b0800341070028940c0c15149402c8a000f45145000c580440b405001400981c44007080051200305 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 791143444 1250 791142194 791142203
    0x1b1406040501120207080c06040c050103140a0207050f061e0603070e0612030403230607090f180207081305030706020c0d0605071e03020d0e0c030304120507030c08011e09 75
    0x9000e00d44001152a0440c6030103443d80030354200211320008035410000d01074200302801410f5145040d0038580c1c5540c480380c2c011414541000102c0c044000b58029091340080705040051b2600c0c06420720a00e0812043c00c0d00c20b69200e25800d0041801c040400d0206440d461a040b10b41e40d5511004c4c1a21044140302d902c0c400c80d443d0303010403178502d05200d40400d032807551030440c1d0621b99692107200c20140c2410425004030501c10240c070b10002c3c244400d561225a030f00f040c03d80c00c1d11f8405280120307000c9114070070b94003066068105404515404807550240c0058409480300d41b07216819030440902d20600d4843c0c801c681d00055214004250842d9440e4000e2211312000b956072100d001801303000b413203181084944601c003840c00000075081000d00c140740d5401a22001c42a10b1007007100e240c44c402c00e21503400105c00c030406039000400c0b80c1c2034074002401c0d03507040a01c41c50041e01c7e0210700c3d04028603854041c4004580b080301544901090480c407403034410700c01030552071441150003d000141 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 791144694 1250 791143444 791143447
    0x71b050102030603240f0c07120f0e010315051207030c0902030105010f32070f0308040c05040b030604080c030c0607051e040608040f020f040c020a0203060708131205161b1406 77
    0xb06c00c80010511194040d40e20010281ba040e5182c0c5c0d19198185011a03200209800c5081c0d1408150703c414250038512003070a00700f140500400c0f501c50301e40000e12455101d004c803080003001c001d1041c41050300441c2d010349421141074590403207001070b420900400340091100007150501c03d114002d4070701201d80c10f2080d801035108034120707d000301300c454100799245902042130000003032213121000e5603540203503035403c151b05044c41c002d0b00e564050b40c0a203105904060640b0700030382d808202c1036082540071200a0b910140100042d0850142e84110440342c01190104640e8a800c0002020b1031000c090f0300c0400c042000500c001580201d010700000035080b140080c00064064038025070b4140002c154a201401c180b0015013503681c2c1c0e5440a00507001160800110304003000016003084107030403d84801e01c1c0584107480071107480003001c1c0080c0c0e5651060f212150181c0c0440d42448000c04981000210318108104000c462280c0343e2402090040300143d640498880e000032030000820f1107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 791145944 1250 791144694 791144701
    0x50d170f040203011b0309061b0e060304050a0501060e0f01060503010b090118080d1d090402030c130e0d110c0f0f010c0302120403060504140d09030209071b05010203060324 76
    0x1110311560080c02280c0665031409401040240f44502610990513a40c01080e6001a458640c2c155070842e0031145034130242811800380c05403c0010341804690a8a00c95240d5896090151426003ca4400b1f0f0081d403921002040d030f4220100d0084c820001000c98499503603856030103c0355440b09126105e0010070900071100079600c6802c4c05070b4034070410700b01000348503103c103041b0741007010701d0403914040794400d4160604104522601c1b454140122182074146c603054020948400c21640c4c040c2c4100780700d800e000c0a4010315401140c2c19410171048400d4100c009001034110486620203006a10801400144070f28001c010500040340290941c4080009040152552480e1000c00c80075402200d520a48100b04e0030302400c01140103c40102c3c482c2441c1c03e108030001241c803071005054101440c20759000e03800015900032280c0c182da40a9090340c0341c000445452101411501a01c4480402482888015000741d030042c10304074107507651050094540c6203010034bc00d0700c5e42400320241002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 791147194 1250 791145944 791145961
    0x140114130e0403030f0c020607030f15120c09060e0609180a151d0304030c080a0f020d0303090501020d0c181d0a0209060a080a0b0a05060d2a0c050d17 66
    0x2241c02c54407904001c12041088420342054580c10a200070050340030500f08a0050750502a4540040c5140c40400100ca04a00c2c44a481c1c002c9026007181c2c00b00388041c2504120424800e0780048c003182030108052511610b004841000a031005032259000c480466884c0d0320911146500d0310011004000710101703a5a1040709020f41c02c45540da10f5980c4c1381c0780200c407050507400d40d4a2484c000c044d40d0f50b01d0440c906000d0351150f9405c108000e6000c2e00400001030b2001005e0142e042d0112403180d01e0100d9450304402600120318014203035400071600d0f6401b403c16402c03d0b030b0541200e4076441450000040e146101da896481aa004240001a94203100c6a1410300c0e9401121180f405490070b0044400715840d9032100303254074001840c40707003003241d1708000b4841c0c1e41c81034408858012455151000080c110700034052442c00c8030f40d403040d420803110300e90880d10b4541da014256103501e1400d4088094000e0280210598460050707204090710144140d5144c9098210b903171040850303440d00c0a4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 791148444 1250 791147194 791147219
    0x1a071205060f030a0803011805060312090a0909062c0a0b060a0b0f12010e0403200c13060905060603060907200304030c05030d020703020f0d031814011413 68
    0x242d000240c2505007031180c0c506108111242d80104c058a0703030780d45400403022510441d42c91140d1124900400d000e401c0e540412142c100e564450b81b660f4a81c4034810001d5030ba003030543d00228004d4503000d41202006000c0d0002030a80d01540002d0300307541c5c80d100301c0130f94845070101d0b01315040e001801e4160025148912194204402510140303000b600d0b5160f145007a441040700c4001c1d81c1010500e006640c0d03000f0700b0140986070311190001030b41000c3d0343c00352200f42d000c2c141c0c4880d00040380410886110401046045040c010203080c1d1030b490415030007009162600440d4117460030003000950301d0402504903030240c030000c1c061065503907401100f05c901e07451241c5128414201ca850540c000c1c80204003138409180182686d000452801040500d41030800121b42c0541d002903104201507030761000030900300d0700f0903210000c0008007480d0880710022a0601d541c0c1d80c3c9403020010540707144000d9980c0e1240c00a80b940085494000c420144600805a2060000c1c448450074449004a070f00d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 791149694 1250 791148444 791148451
    0x2d101b18030206070503132c070203160c0612091106030627070e010f0c030806010201060f080a111f0e0f030318130903120e12070b01031a071205 64
    0x100c000e4040c1c803540020301c2c44c3c0c440b540507078942e070010410400059143d07601400030300e0540c407684c10300d01e02c01e000a1404000740c100948400d25640010b07200600038003c80d0920b007100441e01c0340e22038481c9480300d41d40400f4001c00001641c90510041281241e21a0340402a0000c0341a1090015075081119541c40100000d030825240e00ca0b1080d5081f44042c000e03401c01000d0b150750103929151000a003101020a402810412561400036119400142c040300301c03501803420341d425548220060303004d04010780c0240c086083c40761000400040205009040700d1150301803689408080042020000803a07143c0200100341910000802d030140302c0701e02040c1030292000000c408004002401d64128003189480850600d43c444550318241603842010b9030b250504001d40d0140b624000e00081d0312005a4400543d941030300b500010041044c401c0a4522004283c0d444050381340c0400b0140d0217201c05c890758806551907141000b201c9141d107118082d0b40d5907580b02421440301001c00740c000036 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 791150944 1250 791149694 791149727
    0x109050d02010c0210030504120e060319061208041d0c04170a06061203080106080928140d09140d03030b04090b130b100302011e022d101b 61
    0x220703c0d1000503120740c0f242d0302041d90152000640780c902420300b054407901c0c0a00e103604008030040414020758864058076003201000703c501c00ca07007212117142401031145801ca941d030782800c002c0b11820000890000c00a85d804142800210700540850348004e5000369141407030103605220500807074024040030700b40e40e50369204480314040c8540b50b0a0840d80c80382c00c00703d0b481078030a100c181410340015115006085030326124a00d894022400c1c0d48034401482c40b282c4e21596000c0701b80400c0208540c03408920341041540c80f806c4000110159102d4000b0368450100b2031520000031304201004510402e0b03203024140348401c00031584d0840062051450483d48590341300209004250f404513800d10945003640064002506400c103002104001000f1600b8018120310600050340d01001c46e028502410304101d400c00400c03c1b0590800440c40c4040203906120307224120a1030218840c00f149120040076213020b24807541c0c5500560710010541022060b280382d044600c0d500c655440c0c503040012 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 791152194 1250 791150944 791150957
    0x1c090b0c0c0c0a06032703081b07060e06040512070302060103060f021e1812070b0f0706050a0b13140c030702070b12061921020402090315180c0109050d0201 69
    0x420001901c03000290044400259205903071070781c100341c00c61b901d844540c011035001484841550b0080060300001c28028407090981c001084852411003580c0750316a1000050003031402d610303445a40c1d4082101d06a44500c00c00e4040c000344a4401c04407001a601a4003801941c0e08648590b0050600d002001400c150b0070419061b07400303100c4105ea85000300c10003c065484800c2c91054103035018a200381c17032059006007030250103640300040034400c8812440419480e510b580c010003803d402482c502410781c5007028104000118658400205039001302d40340100c01c0c00c01035510040f1403488018075040d241c40c0011445000c8080081d50f480b00043c8110360030251260390445081d004801d400c43c1002ea4a03003440352500e0141d00c001c1c0c11644444811030480e02d4000c1060500075043c000030520303201c100c1203a05544441d0111440b64002800b113551400b0183c108014042003103e100f254000c0140003025102e50101e01401c0c11101607503959801410b140801c24a09044942281400315 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 791153444 1250 791152194 791152213
    0x5091c0510050a0506190e0601090506130303080c0a1b050c06040602070906050423041502030c19090501020717031b060703060803030f18120f1c090b0c0c 68
    0x8000000340300700081c00108080c200f111010b000d075100506000e01c81c681d403a180e44115844014000c003110070004204a841e111500181c03103c180c280c0020340c02510000341c00c05015450100c1d40100c0740700b070340d603034042c1d588510031540c06000b41c101c1a000100984803201c01c0c249e00300c2c07490100c01e009501360342821143c071000400c2a401a8814800740e0005031040261484921403d0f005010564083c0601d0380f002150b0060000b01c40c051000030032003400401c080c001e8039054025105c2074603504641e2400e00305061502500301e44421aa0703c0e1344d1008075011b0350b10501d00c1c0e208840041c1c0080000904040d0300c0044100b01701c0c0e01404902c0f00303015803441d0120001c605180442c1d404064600390901c0c0000400362103541d08040146d82c010020701903200c18800180340d01c100e0808040601d840420101c03414a405070401091702d050210f51192103821990050204d680c58602d0789007940f40b0002404255150140302034200c07100180003e20b4080441c004212102c030b0718055429400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 791154694 1250 791153444 791153453
    0x4140c031b01090b04030503030412030b06070b0f1e2403030d0b0a1221020f070605031906030b070311040f18050a050f04170904051e010b0a05091c 65
    0x280d60030490740da401da40450700300075940c00c6010302029040c0071030341d1450b190943c1c6681f0f54911018000900200281d03610001c114480d900451010781c005080e10b9440d0818102907080c8103040d5580400110141e010880c44819080323100120b007210301582e095990f4240c0c2034607500b82504500301c1c8641240300c055980340d505000529034503a84410000b41c5070015010705c0210816900111100c0703070f44880b01c8006c2904065a0b050100c16040e0070840c0900510040307040c08101e03000814244642c01000c14803c0d00b0101030b503c1074000c0c501205600c842000c0351400d0341c15511000c1d02d00340c041d130081400c8070311031b40141c0b10550b940d55115141c5603444071003c10703070b120a520182007003030304512580a8084d42e00509411014043c000d00c81c2c3d081c810075400c1012030241004060000140315004030011800c10354a007014000c0c01080f9614081c007a09a08441c00d50450200341201c80c004291550840207603400c514040d0750740d40c100345d881024040e4062054034944080000d1442e0500040d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 791155944 1250 791154694 791154703
    0x2c01020a0b01080708070e040818060910020706141e0f070c0b03040501050705180d061e022a1015150e0a05090c0a180504060b07150b0904140c03 64
    0xf0030154000b84030140c903243c061400c1040c0e5801030807000d100f00041c0408680345406071802342d030b04c00e11802400e400e03050000f02e2511803440d000d50020003c034410198950042083c008640c543e840f11039030404804243e0506d44101c500c50b4120300c10b0420384501c030030760900140c8102401161280e18000e42d0b92540c082249056005250b0140c2c00000c102c100082809100d4003c200d0703092803810400d2043e0110b10300c0e0704c0d00d1a40390240c003120b8444c805006664100411401c586210042c00e11b030603543c140040e60000e0321054281d04800d5880c0b0181d40250b8240910407104006810320303034a09540131014080300c06a40c0c0c4000e285070303c0820820301c8502107800300141501e6204180d0141014803030b11036001c2d070105116002400402120b041d01808030386008880d841c03c02c0411210044061241ca4160071031030b040307031a014003c112010b001004110003070040a440c0c40f201201c03c003200a40c1c840301c900a40000d00315020400141d41d0f440350320701140d04842a0b4200c04000400720f803030b1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 791157194 1250 791155944 791155949
    0x903030906040e04051203010506040e190f0902270c03090106030209190f1103011406070f030c031e0e0d02031c03050115020a050a08090118242c01020a0b01 69
    0x9000c0c0004d02c4100182003007601090121501e90f0703815507150200007116406280b00c0c01d0003c0e1030581c0090321005180000d410100c50380c4500700300244810900750018000b04004030b0103a540d0700314610103403003440d181f801c2c156900d48090f4056a00c45d10105055000500401c2c030031364071600b022005903034403024140b003030701044141c000c001842200780003940c1c064041d0a440c80d203048010102e407503400341103a041d20350300e43c444180a0500340c0424424410014041c081e00720f600b55243c20194080107465200c2d0081ea100303c0341c01c888078484490b4417181c80c8a640403500d0340f00c03c00307254204048905280c40c0000c066030211005202494804640c9003c01400655642d0060103190740700b1540a070200d950b8070081c4000003843d503c8039a2540781c110040c0c841a004031f03622050360b201e103480540800c02004090328495844200c0902d64003d420440d085060313110786130701e0320392045012000b942c20506904201810403a81410481c150342c000314110f000703480d80100416007040d2030900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 791158444 1250 791157194 791157209
    0x51e03090907031802190509040c062c131409060a0e0106030209040b061c0b060a0905070e010c030e0d0c090c030c0507080c030d0920030f070605090303090604 70
    0x5940c6100310402a8900340208250207140c5000c08407808020040108403080750b056619070148078180d4207000342204558455644400300d04c00301300801c55184602d000300c0e001c54032418850a200349910b815030030010040c0348002021618072543e0b281c0b0b0480041d80b5032603544000b03804201c101c41d83c180d5000440d11222582c2c041028090035940130310691381d604160344001c104050556001400c0780401030406440e00c140703107004c60354a03a102d0040d0440124100c510441e8068039140c0701540d034030200e45c840e20840003080c000800c0b44150040340e1142880303079560590641c844d4015500070404440503800c01c0203010742501640c07260b840508c43d4600819400c0f400510381800081500c03284c0c0241801c043c00c005d02482010382110a80d040c0b0b81c0d0000305140c0b2480c0e00c02d000c03495400765a184001c2c890801c007481d000c2c494401e40013900c048100c030900010440310300515544643c800c9007040c482e80071000404c01180301d0005888584001000d59241141c4c000c009074581d0400d810418 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 791159694 1250 791158444 791158447
    0x1804020307020a110613051e04051911070c0302090a0e07080a0b340e04050103031205091218030c133e0306040f1d07060228051e03 58
    0xa003803001c1e40140113011001210414a0280748280e400b0303d130100313407150500170045021900003071251a15000000b0401600401c01c40c94404440f421540917040b003000d41601d000b2198070b45800e079508030b6000603040342c8086901c038a580e0034490a008010255150b0300d55420102c50080403e0020800800648004003000e62050030070440c112409080f0031380c8840c5c03400c0c10500c2241f90031400401c1c40302d0558a1040c0c2404000251110050f9024440c1e000d0f2034903002008054020104440000106000300000d5440990903982d42042c144c0d841240402840981c042010800e4180402000039094070b54000c0b581001c1202900c111076041900348c0c031891814031030440d5400c01103a000744210900050050407a4031401c616409028412281000001900070340701c1c0e821020100c201560108040302c025800540c03481b030183d4040740380d801112400203c0383d200160348999840c0f0f1640603036940c40810b4003d140303c0c2c4400c208468600801c480d401900c4003014104c45102c45820186 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 791160944 1250 791159694 791159713
    0x13060b040914090a020d150507020706090603020306030c0906040f0e03070b07140301050d06060b18010905180f070c050303040f11152d040b0d1107080a05180402030702 74
    0x4400340c8030b030070380e907407000d000700c1c404025203c0700014900942a805461a03146007403d0b082204400d5001d01101444a00b0301041c00681c540c0010303040c0407140140c0d6501819512404e04805901c03060b1941a070680c80200c04d1202c40c9008002039030444401440002d005c003000d4440020b0700d00c1440b420724960400300307a0b9818400d5480340c150f8840c0b4980780c010030080501010703170180c1c0818011607001c0c49645000c03108000319a07028401600d4400714164841c4445410144d61101c082010741c0014520b0200042904001141101c0d101229130341d246aa03491309510b14013014002c0a500c20401c01104100101d40217100541c0103034000d002541f01001541040d6241c4d50301c07822110300400d10600300300c032440395260658101e0740c0c03106100c02e0014121100843d2710700790780e2500c10040c400014006070000d00c6400a140a56004209004a450140d2040fa05004000c0040c101001c200294415030748a0360013032205110304801c400c941c1106501040817a0400c0b81c04501681c0f02c1d0802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 791162194 1250 791160944 791160959
    0xb1608160203130b0403020f0d17130906180c030606050702040b15031008012910140a111908070209070c1e110306040c120f0203010504081b0705010e0d0213060b04 72
    0x81c031586019270f41d503040010250348200204509204401c000d100120f000c00401e103402c034000004146402d003d100d542e44580c25041030003101d1054064140c5401c0c1c1c0c046046001703016841c112003c0c0e85840b41803c00a0b0280000391039900b20003580072100c036030144150381d2880b021f14055075a405038203592500f0a10482e00b181d07000c02c01c0090303c0306a21403000440402c20f81a0382c02c02c0068940203680c504165085e2100194103440f9004c104003c0f83e40841c181d0b2000c411203d2200034001c407013550508402c814101c0d040c0100150541004012443c00b50800c1d020041e048030301454200f40f4009a503d07007140c180800c43d500b001840321449103506200444c10341b220108002c038060038150038955915200e11010f481080c103100003170509803040c0440c01c407514060b641c003d002400903140501e00700030154062058000388292a81e20140350301e4001400c0020340c1c4044e11600c0c0003840d031000300300501e00d1892089a0110305035030000300c022200d018650042040c101540e4899080034103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 791163444 1250 791162194 791162209
    0x111030d0209010216050a05060c0f0604050606040c091802250303020703030e0c0d060b01030b03030d050403110a1a10030609060f0f02070b0a050916120b1608160203130b040302 78
    0x20343c40714405da040390510480d0740b400004012120300b100c0741942c65a9580320780c2d043c104003002c880520f024940810041c030501040c03a520031f1600f02c8041184107002042174800c24664011000d02d07900440d001000c0b5011b03903000f0030403258404901d00c819401c080702c0001008a401085000903004100001015018001c042903988a00040c0560480c450080348000c1210300c1c0141249441d0300090720b09034001e51044481c000d001e02a40d50f50b800144541e0040c2070141c40440001e03600020390003403410042001360340503a10090344000d92541180313440382014090218141c0d00d54002c1c4c0040064418828011654400d900c00308074240350b4030420007103448a455103072690f8010088100064211250507070300a608120008250311843c01107441c00101c02e6607650b081c1c1ea0320001044840400d8001d0021520075490011240e41d10030384180d054008550b900c0100d12080040b480b414200340300c01d00d988601d407044a023060074044100d40c49406070341c0101d005900004052096081410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 791164694 1250 791163444 791163463
    0x60902040503030702010f1b08090907140f0c070b0c0d0e010807020c09040c031e05010c02030f070f0212010203011503061502120a0e06070b010608070e09150111030d02090102 77
    0x40086003014500000b0039200d1040d0b0800034100408104001c03181805010742c100c00b4480110410400d0043d031500003020341c014184603104140a900040403903104074284211600c0007070513a820040882808180c40e0407651850320386000f803140200f00e0559142c0608507c080b450000e240200340110040d00d01c58000100d01d0400c03c544040114040e00041c20460b900c0d41590510090b54450804e04585e00c5a80c00c0281401e240207940841a40542500701021740103000810410100c000143d81c5c0340f24079613552075401020300401000c1001c801c0300a002c00d0001d0300c141c403480851101142268000d800c480085002007014281169252159402414500503805840c0d20080c0b4080c1d0788510020240500a5002510f000440e110f0f000c0c030904118060001b0351600e07021701d8151400c040c2405058000b4909a0024400501c110141502104003070001c0045854a00b114108051144104c5050251402d140e0340411410001080e40b0510302e000103840c1c1120303c0009061000c0344 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 791165944 1250 791164694 791164709
    0x1908150102010b03120c12040b0912010c08010e0702150c1e040506040308091507030e151207050307030e03071b05061c09030908100518010e060f0709050d1506 70
    0x1d07210030f00c60b8034002540069548032030301c0941c950f049000c9491401d000382c4c065032654140405c00207280014007000d050f010104803641c08410781184a540d080301c00c1d1403540346c00281200010802c1c0300000028503005100d0784141e030101c1003284c580550300002500c04500d443c04c00201c40d080502c40108950000740c0700041980f900f490500011803e000700d000140181c1e0340094100c880380e45506140140210b14502d0b10b0719400326041c0a00300124441085000305c044040e101020101403084402c80344001000078401d031121107040742c0c42d4100912920525507503c005616405040004c0c1426601c101046110111002038440c910207040d8042c41c0035202c18403160000744100c0303110144030410744000140e4980c4900f0201d6003104d16502507145401a5414075401c0302071a0020340c4560b80c40244034140012070000d4900300e407214000403c1c1500800041826003602c3c112441e0130014500e0110352240d26107000944060805c0c1702201c0355129450401c02c010900e004a60051808 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 791167194 1250 791165944 791165951
    0x80601050d03080609130c12060f06060c06090602040b0403060b10110a060513020d0303471f0206041103030304030f180305190218161202190815010201 67
    0x1c0ea8024181c101e0142140313202d5611000058075045a0b510880c840941158950301180c1d0f90b001c422115000103c0250354807401c0c0401500c000b4154082e03903007140d851342e583c0e2512641d180c0380d000c014441c664045070f41b29000c00000541142000281020b0340c02a0b00010342420b0f04020414003150000140302400110301e044071b80440003198004e4a20b0300128085040d9441070780480c0010031249000b903100d1410f00c990710525500d5408a00340250500c00501c4001c20421203980106800c14448081503508680c0040e1060f0404074001c00000603010003101106c0e55240b0800200001c030080040c1d02190030070084c8000905a000c43c0703034066000e1803440c10726440051012810201603c10710000806521200004a064038000c41d0040290b4190282c1d030060382c1040d404241040c0d104000c10b00140b03111401b0014510f0041d003501c0418a9181251712080d1080c400e0f01c942d22031201e9081c403d40c02d0741d621704448244150043d65810400340303001461450b20002c12008203045a14 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 791168444 1250 791167194 791167219
    0x408010e0c1c0503091011010509060609152d0901061404210c090510050301110306150c030f04030201120905101d0109050c01031b050403031808031308060105 70
    0x441140c0301c6070705110b4540164660b80541022031940c0f14003001940c2084000941c20300090b8071403400041c0200b010028016030322000c00d21a074405090300c000e5800548203020503281810182d0040d031000c00649901c070461100402c000b00d0512600e020300401142616202242c601981000c2c090109414410840c0e005030441d4001c83c0103e010b140c0e042200b031300b240c005048104011300a0307180d0090080300801c0c1c0f1565a00060f0505907000d040d8006d802c2d8000c20549010b001d00750881080b182224103640da450304125102034002001001d40704104880c4000d01c806000030180000d6000c15107980394914800100200c8103100200348803482c03c4c041f40c00003071001c078880c5450b0004080105411480101008900307224a142c05034a610b803180807010000007280b9011000400d0701c080000401e030107002c1c00d5040b0500941d2000440c2008240002406004001c2206040c601041a00c1c1e440e29040c2d03255500032134598540c1011b6881c1040509410003926015010981c1e60a12924 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 791169694 1250 791168444 791168449
    0x16080103050c0609041404241a190803120105240a0807050405030706020f1b100c080f0d0203181603020609040f02071202010b100827120408010e0c 65
    0xc0c4004940f40704240014804485075955080408007010b40040c0e10a141041c1c43e01e551590101c0d200c0d000c0c41d41400e04802100c034010f100f90004086059440003003260318000300005080d1220198142c0074040074040382c044c404002030410880603110740226541003108125880e940b84440100e03090074130300070036041d04650707080c0c0d0700082d91804c00307500f903844800d0b055550703004540184e601072280800000380e25500140030b8000351245030580b12040084008814030741616924240c202482c1c0c000f605280d88100040c2c03040311f01450302181000c649060f0014258801d0700c904001903000b0003803101d00807812014000742c00143c0000c1c140c164000800c410074000314407019100f864045040d4549482d5900150074441c01c4000840d580d204600d0252009504a44900019841d1401e800c0f02800c01040340f0341e03103400649443c44a9550311070b00d80c40d946001ca46144040c0210082c02e0000f130801c00800000302d6aa03031255445604040c10142110703842c0501d0041e03503101020407440764 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 791170944 1250 791169694 791169703
    0x71a0705120a0b030d0306030c0509330603040309050f010903150c1205100e0c030403020705040f2a030f0614010c0804030c0b0d050105010f0807080619030b1608010305 74
    0x10700c480c95a4002a82e6030081110040484240c241d8040c0226401180d03081ea060f4011010b4a00c15204074091648400c180185038008072044100340946e00f5010790561440c40c400503040806141080c1c03138a204501150300c7d9081560104c0104145603400e21a501c1c00707101d18224143c081c80e144041c80e1554032060340f80504242c660804943d1030441c194400c0c03050318007149000a4200030702042c102084000040000e511882c9500c10000300807030401c0300c005003101e000302e030140d004144003030134a01000018005c41c522140910f1ba100200b501d0910804280c10329140041440340c4081d95082001e8182c4411016a080b079038a0800240040d096082c1a11084502807030406d003100c0407450026130900c01c5030006070114044510010700302010000030021640750280502c2030384d07a14001901d08001c1c07140307520301240c801c0d40015103840c4203c0561790310410003040b10612124170100ca04400701e0a03002525a542c004041081c001e2003810510082c00c7e071450540415890b645403161907 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 791172194 1250 791170944 791170957
    0x121602070510050702030114010906064d0c1314040f03020f06010905061c020d0201030908130602060a050f040309180f0f0b01030b010302180405090a06050903071a0705 74
    0x40c0c03101c490042e4959100b0026140816809402080301d42468149030307200381401d100f000710341c44c100381d40411114410005040c20b002d1103060010000c0c0c2d10102c00100700c2e000f84075a10b116403003504105042c000526000341c4201a41c000d00301d540c103080309100b180c51121500c1e0807030b18104000e441e901c0c1070014059030b01036082a50141141c20f5442e0032410001c075000000f0882c4114000450782d010301d43c0c44a4080c1038200c42200c002c200b0142c10302c0380320007000800782d40f1030101025000076502941145092078407408180e031900c1120f500340b100c0003003543c00481c010303444101001085103282c0318403500f0408541c602c101034a46a0760013804080c1c14010801c020315104400d10b4594400d40148034544156442803020030030201c600c0700200881d152180c0000d01f09140c119207540607200301c0d1000e1500540740c00c00f0950020a0101910340541341d0690740c403d907020b40c0041040c4e80f1400b8019107221001c3c1d50380308114203040e005c503030107600003100511400042c400c5440d0010201c981 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 791173444 1250 791172194 791172199
    0x3020412060b030a0203011b020d0f050405010c050a0206030901020426070b0d1b0e1801181508030a18150f03050702011b08011d090a2d06021216020705 67
    0x3070b6070511201203810314880c148001e41642c00d0296011702c0380034840000c04042d503607600b11109810450b0046902c1e098941640022680030003050166501c41d60000d0030031400782003251032041e4180d02090f1990b00480d1040311a95000c0303000d103e1300704c601c5a290250b2580c112224031103d0b0310000b10761a640c0742d00c90010050740018450410b0030058201c6100c007034550b881c104551261110181503034610744240c030710600081c5500c101d9002c04070f03074032070588412503200018107500c20401c000a04400e425505100d1808500207001d000070002050f01c120781e5512259482244001070b00703504603503000404481991900708131070941c09007615056003114600482c0c941c83c0d0b10000c0c6d005016041100901e1003481903405800da4110148038102c0e814507002150500c01c0c500700b002050010703921800c0ba60054607900d4041035809910f114100b5000705241c0c864900d20222410b00490010219a85a00031480b07030b9808090601803640002088004d80010291b000004d407500c0d5540502032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 791174694 1250 791173444 791173451
    0x702090708060a0f03030906140c0715140c070303030e0a1502251407171011040b13030506012102040f0b0d050a0b010f0605120601031e05060405070302041206 70
    0x181d02e5a5a4415035004000b503601107003910380c0300d0500410b5040d090048102203602c042e6824100b428081c122403555603000d000c0d00c02d01d402c2030740311072044080c0b0300188204110710a141d08031980440003007048199100086ca144c074a90b140180c1a01e10350007105955030400c0d0902008544582e80003250340751449401a540c60328030306003040154100e0301490f00b040821104104002c1101c0408a0111b8020200c501141d6030703140f441c0c001440c0043c60300b041d800082e8034a4040320103401903c507120b064800035041c107032125401c0007030741c01003a001e03041c544840e8810024400188007050142c41c1c21849180409126660741e80307040b034100002400349c2c0d034611102117098520f60060116200041c4540d001c107585003050b43c2d4410f40c402c015075100e07840200014400403405610811561207455507410001e060405404042d001400d942c18503480752001c01081d00c0202c0d0702c080c600000c400004060130408140021503400030101010303d84100800d001e22400d00e143e40289139480840031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 791175944 1250 791174694 791174701
    0x81f06140306032e0509010e030409090c081203180303071e09031721040f021c08040b220503030f0d0204050a1d07020d05090d0f02120d11030702090708 67
    0x1e10340705101c510142200302c40c1031050f44c240d052502c0d501500c1441c40080c4955151155064201e81104c0c0780b040715940100800c104020168104c0b0842c503028800141800780d6504008d814004607044008030749400108001000c2c80300000c11000c0300c0369100840c1189400071019005100c01a55144034401400007502010303c603180007409103600c002000742e0805515980e030a0b42d00040710381140300780c0b00381d070f0702c00c20440120344584120b800c501b11110014494081c0000040884a20041d003400e24100c04045182040244000c084140c00b171030752100c1c1002925000c000d04010000c00c841001c20070000c56030000240ca0590705102c0c94030340d45100c0402500002c0c4916800241c1016078004001612040710303102c1f002c10062000748601d03541c3d800c40c1c101d0b180c21520004601241d414481401d260400c1041000441d102d4581c604411005400154005c11140d8811550b42d006d62034005059621664400307150744070a0096080610550000e440c440c401841e2500300000013000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 791177194 1250 791175944 791175949
    0x61505030a0f0c080901060b0f121003050a12030e0114010b1c0f0905011128050c16080712080f03070207050a170105010b0909040204050403020f010c081f06140306 72
    0x8148802c00712402041100710302d0f00d0103480701008580c84030140d440c02c075002031050726000884d022040d400c1041c1d4941b9505090344004160060603070002564015004400a0000c20142c0300f89800b90510580310304000000405441811001d48010390400f084a0000c040000c10300e8156066507030999101d9014460403a000400550780920441c18a82c00c460200c41b1548040411401a0000c1c425889801c600b405c1610964608044d2700e0600c0d145148100700450605001d0001850441d14051003140315525000025035039142050800e8410004c80f0010040480145400000905e00d214240c41d030f00c0c554010744020020120000000414051084c08210042d000c010200d010160720741600340422851600703000740c1586044004120384580c00155034000000602011542d9601d030309203c00b4110240044007944904c2601208001083c09114821007055440d50101c1c500205a0b0300c0f600100900941d181c2c0e044141400a141d1262141c0e01c10787c80601240d699132180e002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 791178444 1250 791177194 791177201
    0x170a020405070e0d0305070c080102160611040e010611071a1b011d0d030c0206060d0f0c0302091f05151e040807090209090619090b0d050d2001061505030a 68
    0x3c2c0716038018a151031071001c040d0003501404800340503030800395a55031644401c038201d104103606056062005480040000c2c407503041811003820480d035140c02c00c3d9a800180708019401c3e081900071070480900942071460400000004180c11890b10412880204078418944516010400c6030b0b200e0b29003a02c8142005d400c09507521480e1a0301340c008418072888c1d940c032850b55800440001e82071025003006103100180c1d8500030751005209100c041d1305541c900d03071400c00b00c2c901251200100100040541d0322407079500d20401c0c038401001a003410784140c007122518190492882441d03003191056502010318242c2e1840f09081041c40c1400341032020303840d0319005035481589940300b002d20100700302c1e1039500503141154081d03c0085181c1c440200300600e1902444050b0304015000001b04200d9400da0013124120001400d000c120400b40e484441c00c000d51000001e0218184a80c40d41550041e00c98400418469100800c0400d040030003444040380448a144200100031003c0340808400d80d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 791179694 1250 791178444 791178467
    0x20f0f0f0d022d0a06020609070e04061506030209180c090f060409050c07022e031a2115010b0708030c0c032106010f140d0e10090606170a02040507 65
    0xf80086040f00d0780c070035030320b074010002141c01c0c056880036000203942400060006e0160f000b18000e401030b1420203000d03c841c600020700645460b80c661401150702c1a458564101400503030b039000d030b51940124140710400b11a5904020742407801020021017030089000d42d244204e04449e006003a01084000441d0f078000d6800c0b0141e05458a0144441d20700580d00900703280d4400e540f416541a40c04810503031800040c0b5050b03180112800c07000c05018071076840105911224000100d00440c1031020400c0c1d0762100c2c543e481d00000908070820741030020440f0340c8a02c03940d00b601d460158180545103000e8092440c004041c0c6801001182d281e50184068607400c601440440b0f0302c60f065452042090f110785a005c0d010515a200801e0855102c3c0c0b403504001c816030b40700c000159001281c903103403d030b000038003040410383d0303c8003c100300d071a052011407030701146a0f00115000b421800e140c5c0407168030398040042100b0303032101410696408604840102c0d011500040c01e5070302c2920907070380003034080c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 791180944 1250 791179694 791179729
    0x60509031b1f111203012103031d010204080114070207090b0a120b0402040e010c091703070f15050109022110080105160813031707020f0601060c020f0f0f0d02 70
    0xa02c0c0902c1040ea2016120803020145011608608506100e00003584000e00072024003528001610001038200481c0202e000d01c03928000441940910b0700c854407a034000410030341079400040c1004502c0007401104081e504400b00000c40d0304014130007070354030034440c420205075544038640ba003166900c241c460300007040a808030188808940c900808482011102244943d28100c050134034180144602a0442516110051a00e0406210982c0010f1500c2d0400041c801008034200003034140100c41c1c403d40c8224035201207030241501800507158160401d426151040c00a001c0a41000c8102c45c8809612840d0300090340301c0302c42807604808960012080c0390308102c180080e40780340540301d848080c51503440c42e000740ca4003c58900ca0003c0b05030702a0000c4c0c00b07140b164060010310002d46400000c00d004032181440c0c40800701781001002d90207840810031203d01441541000c0e01d00803288402101d0322904100c0b010006807034450303030400150107403e03092215030071512100581c0130483d80c0b4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 791182194 1250 791180944 791180989
    0x130317010b0d0c0207050a1a0403150b030708060405030d2f0a03060504060b19050c16032307061b150f0b0306070c0209041e0302060709060509031b 65
    0x440001d90003540c8404258404989400f20b800c2150f07201040030300640d0380c006e1403200074030301c2d1406600304204840f25110003503004000010010700510440100310120103004680c2c000751504040c204601680b280704e280d00440b00300130009801104894110421a00004100341010804507441240104c42e102e03506440b0800c10001040c440907185107a80b66906210003612901880182c07041c9100d11030f41c540d014001c01440414180d03100c0400e09552801604107103401c0051840d099080f41d901c044480008010300c00d100107840c884c0140707100d0700c0a5080c00c80a800c0d9255607080d81d846128104040b00c1c400c0c6180f004410142c608054000c2020090310b0030340c0d04081c000300900e25101a003149005121074090a010a80314483c1400340c481000b4522070707400b880030701e2100510032603040b04032084801c002c00d40080e007555034a01070740c0100030500d0148000352061030250001010302c4428080ca0740c941c1d80025122004d50fa942030f401043c04130000104121000059000004c40e65 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 791183444 1250 791182194 791182199
    0x80a0206010911070804050f01020c090a05190207052a03010f1a0d031b0c030605040605061302032206150b0c1903080708060f03060a0f0506040605030613031701 71
    0xa000a845050325502d52040003050045046112680300b0240c008042ca40148000c12081c81c214034a0b0b4004070040c015286082d10400021f51040c01c00c580c1e2200d15a80c03071082c001ca213034240184001001100ca0114988181038489070b69445050404d003080152024113001c0d0708420016840c0d003610040e0090015080c1150181c001e40110101807400320316003c0314182d035240440841001c0b80e01034031904407941004500c02c3c0c101e5079041c4240c408001c001b9001002911901c40e55100d14061000000c1710300b420f030204050801501c0c11103102c03500610503c030f81e03040404031103011000c0c403411628800640386800d402030120002100c031982146030000a030003c1c180001c2202c130320100b041c2c58500c08142c0030001201d918100280c0080d00c83e03000075200710700603110541c2014006061024003000c3c01e00284c07401200315000c03c101c0d61201c0c0543d04101d020300a59801c69401c0300c05102090034000403170b80c1e51000420340313404401106580782c207050048035441049100607a01c0d00d96980c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 791184694 1250 791183444 791183447
    0x402041b0e0915090c030903191205100f1401030b0315010e070201020705060a050c07020d060218030a0203030d050c04170a03140c0a020105090a09060e0405061e0705030a09080a 78
    0x400d007500c0c850260000800044040c011402903803003812006210b500c01e0f85442c0c21410442e007004040820030300c01000703182c000d001b8003200da00c0b03e040166500e550183d500c0c2d005405403030740540100d07295030500400348209404030f85030b04103580006800c00c0c441320024004801500c800100300d90503001d1b03801c0418910312800400ca0603200c60f00d01a85035601d0314002213080b0312034804060440c1e0490741c0030540c4c165641d080150407290080c7c80c80e0070f1401136000690050a0210120f402d5940040c1d00c080c00d2400000d4400c217400110050049003541d5004203440e845006030a0383d203156620002654404400181c401030040e0180c00d03540c0c4c546544000b5a078229603202a00480c11198200c03031900142c0045414060580f006860490455401507490350001100954002020307000800d0198803442000300800b100d0340002c00b54200360a04904160380900030803902c080c904c81d020141111b100029401c444c2600e441aa40d6840011078002013440c401c00400b0000300140a00d50326 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 791185944 1250 791184694 791184707
    0x3080310090b030d050307030b011e09060e0d1e0204091b0302090a050402100e062b0c020105060306010e0a0213080f010e0606030a02120f0102040620060c04050402030402041b 77
    0x140ca040d01d0800109400008040d9110b0142d00000002501000003507045071082d00418149071040c1084c410200c1c0600410044461516801d0f0000c2c8001500300041e5a011544455240c0185c034000c0d02131302c45840d00d0075801d2405214040c1e80e080c40002c0001c42d1076990012141c650440d07520f89500030603018400c078000392880160312903138548011481c0280b09104460081d580101201c07582075186805860841c1c20041e400e5000d00140202c0e01b25070207030354000c1078006d80c0e4103602c100100411500811502070b0800d0200310381c50207040007119180001c58030f054070700911804030903503101c4040d01c0180c82100700c8215010b44041c00002d03410000101810031030203050003070203094150a882ea0343e610046400320740c1540a00e250f000542010716000000030458019120f4440e6007801c10703800d81c1e100c0d50022001400014241c1e034030403194120107032446440d501514141c185582550303542c0c0100d0040c241700b6640007020038115035490740b02514814031886140c0d142115110054000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 791187050 1106 791185944 791185949
    0x1b0123040b0c0a0c090b100c140601060309020a15140f040306060b032d071b2108070806010e0f12011a0418120c26211905090703080310 60
    0x180c800511009010340b0330360304c3c0422001443d20600c800710905038020341421415168440c0100e82c040040612070420a9240b81c03908020400e04d050361140d580003c2c411468080c001400141d03080c041c0d485895030011010203036030b0030540a0000450820740d2140210b14400080209000e403048070780d64544100165041c4004d0741c7e8001d082c0d6442d0300581448040684003090182d44114039a90161141c07411a010b4208600042c02078202c8480b4203100b41480036410301d8644443d001d00c46900218002801849600302500c202820700c5031400e80031707900b080e8503103446012400083c243c403940031860701c0c1608904102241c1d5110181ca0840d40580802031052020f00c0c0c010040c09007220201d10103599000070382280c05103502e40c2446240440900702008442c02c280300304001203003040c520102d00e80c1e48081c205030a041c0345c2e4100510952010090001c038003000503c9106 = true := by decide +kernel

theorem cover : BRFrame.Cov 791007194 791187050 := by
  have h0 := BRFrame.cov_init 791007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 791007194 ≤ n) (h2 : n < 791187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
