-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4451
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:39:29.618409+00:00
-- url     : https://prove2.me/submissions/2f86fd3a-5a49-4eca-b560-a4fb8cebcefe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 800359712 ≤ n < 800539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 800360962 1250 800359712 800359717
    0x12020d02010b03150c0c1209150408100f0204080706030905060105010f0203071704210b0901020414150f03040f0c06050a05190201060512010e010614090c0a0201090501050f01030b09010e03 83
    0xc0d40313100c0e840c5000141c03008510400303495046500208079014901b04006640c06c1d03030700c460241c0b885072158100769820300b07950600b1101039640d1400517101009801c201c03000501022008004816000d10000c529000b041010400802d4213942c042041c0041d030400c81e085c00e0301a0030190400c80d003140664111a00001240c452070350003001d035080100c0000d81040c4501464002c0e241101c04440e4000c110851107288048150141a01085a85581520138204e201d81d02c41c143d101003c2c07070011a0310b85040140001650031180c1d09074034004080c1e40b0042e291380111340c21940d40300784501c1c0c1014828403c0b20340300504031034209907103015042c141c05021805100c803020141240c07194405a824401e4015100500c000350505084c000c82c0d2901c1c6000c1c08001d02e40d46070300d40c0703080c8000032001c8001e4030f01900850003401c038410948441280d00380542c00503505000351743d261603108002078400d1041e01d00c54000ca0b4800540380d41545800c00003002d025000601c1c40e0b0410045d20051127004c000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 800362212 1250 800360962 800360983
    0x14010f110909190e120403210e1e18011a0a05030c070201030e060405010c17100302090403090e1302120a2a030609080a030b03030a090e040c0e0412020d02010b03 71
    0x1c3e10a420b212802000090844001d0b01d111500401744100c11909624000d40244c030303c95030740040a0080c081c0703814410040081c010340090144009901e07203042801e40c0c041d0621407081816001d540368400b0542c81688080c12805030b0350800010004450003923180100001c4851000d4076001c0488002802800090815128440c00050a008582c002c0e07004010711601541514041c4c9418106507000f00b101c2485400843c002d50710344190091050304183c816083c1d0a01d00340e0302350079a020302194000c0104224203001a503800450f002400e03040f510b102e41060105c83c69100b0251041c407000000094034030407181c2c0014600350000d20340e02812000850070031030007104000c5250030302e41e62140383d41c0301510f00c5140c9039000e401e1050004c000c0401038100d842c148401909507007071560300d2140740003c000241070a907050000c0c1c03101d108030381d40040c00b8008130680f280e2107038210140c41d03000380c404035207900c0d00c2e00748003401d00c4e01442142c0761510940000c101101c29035001c20344030385d4a0003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 800363462 1250 800362212 800362231
    0x80f0705032b080c0d0c1205010801090327081c0f09030f0b0402151c06150f08062b0302060a0e03040b030910060611060c0301180b03070314010f110909 67
    0x200081c192200e2201031710168040d000e0103010741d034032600c00501095200010541854100400400c41c044140600051f550b4159542880342803000d9811001c1000040341c1410000300000001c0c0901e070422804440c80d11060104122044030f030301c00740030040e104602209100c408030007003001c107141c0e4044540d00c1b41c0000c4200c4a50303031144005058a445150071107990314000c105da5010207450b405148264040f10b03800c2041d41d84400010000d042c0c1c8021a00006a9104000d00c003503104a003400c0d0041e00181511649166101102d0072664008e01c1c00707440f103182c452030a014035a0400100d6044072048904021001d10403404984910440c0a11030310b600c0300102180e8081c2c2c1c100407036805c0ea81e90700420080503071510002890314803a4a8140610b00c111804a0702401c09003044a0480b610282d0700302c80c0c044110701d480050100074200a925026200c0000042005140800c85001480000140c98030030140104110741320034170f0794410b408051007016255140c00040740e4008a00301e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 800364712 1250 800363462 800363477
    0x90e120a1d031207020307091a1c05101e11090111030d0e031201090b090105040e0a0f030e15041404050c0c030705071409091510080f0705032b 63
    0x180700018560100c048040c0c040c40392240702203903000300d500545010707032084043e02d00e95940e03203101da000e41d010100600e00c00c85c00c0544948892a01303450b0158125090b400c190140c55950320b0303031400c144012081e10141511050036080c11020f02d1220009003032524420000c1081d000403070003150044000c0c042c14002c1c40030f0580140c00c4100141c0340c1b030386070a000038081042800c407240c0c5c80e030300900a0668014100000486c0c2030003940103024503034030068180c04a5a03e4070081001804088940318041c0c0500da2610000c0390101001021550007502d40720302038640307201805400309080740e501041b000240030501030000a17071403d500c001011039000c1695190b04040301c03603920078030034032058901c80000e011082040200d00d0804580080300c20f0100000071005000c0b07100c004071540c00d50394101c2e8410799411410031a00d290800c40c0d0b4081c0d03000107526005601e280c607a80000c0d50580b503210900c104010320f8100002140d10800444800c0071540c0d28000d00800514083d410b01803000c003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 800365962 1250 800364712 800364737
    0xc03080403180e090a0302010606391505040506060f01020703230d0e0a05040e100c1b03020c100c120c020d150207020f15040902160f0309090e120a 65
    0x70401c044000c1c00d40c1c3c402402c2181055a2259501e030f0b444d4600f103015508016000078018002c100800070744110300e003039054070019208441480502c0300032980320003282028640200f49910542c334094a2a050b0005141c101814064940b9000800c2944208034100044245990104030070007160b41c0880700c3c64005040324070048011038040c045039581e114071010444800d0340455100401c081c243c82a8045517182c8040c041601c1042c10042100d0344090481140300803d0f5015000b48107591506641413100240c17698034040c03201000f40e005922002404090303140c500751856884400781440319050f1955a01c0240c00d141ba40510014080da214401040d500c408840c52200b41e480349220003140060138201c0c00a401c602c2c0141d010350211860348110741400128850044400c03c072150410780790007041c0b0301a5002010b0100309030344d0901160001501d4040002d0352512a03195100081c2c10511407004030794001c0a5800240d00480920319247d20301c004403030070442c0e00c2c500125100032 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 800367212 1250 800365962 800365997
    0x23060307021005041106070c090c0201020f0a0c02031005150310090f02010c08090619081003112403180f0c0d02060a0c14010f0b0a0b0414130e030d0b010c03080403 72
    0x1550100341d8000000049640801240028684c152000c40c0020000b010072b11008074205e0040c0c0e030242c29180300401034403c2d2a0300698464401c244000d08542c1c0340f403009983e59007960f2041d00c5002580030182404109460107000280503400b80c4982003100d0786142e01d400040c0c1c0001c4801a0611016554140a01c003464048400795070323015101c3d69580300969515840f80305100d240c0d00c001809500400c090000000c0c4120880ea00701041101c90000b8008000030841101014101c120071030b050500141044c00c0514491b40c22a0300307a4119450100384181884010f482403031168100103601c220300e90311199501181a01034032500e449611020042d1030310541075030040d22103050402c0681c900d581c15041607400c20009007061140c40082d030305114a80c5018000e1884480e018441071160307903554080d880701c0d0f0800905100c164130b14072030320b1421680c500b00d484e0482d4100180705c4030460428004c21051032428a041002e0450a403030041c200c08001d44000c00f00580d032401404940e0303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 800368462 1250 800367212 800367233
    0x304080306061c090c090608030c0d03050a0f0e03070506010b040b18210105040c0603020f04141908010c0801140907031104080f070801050f060904110d0c2306030702100504 76
    0x420f900b040700f0b4a450074880303500030880c442c500540c0c1c10f0440c08280e61704003000b500c1c44500050300070074401554603006e5024000c01007014481c1590390f540d85980602a0090440303100500003e0342d90340c8075030f0804a00b0f00905812540d1400b00400081182004420484a031505200c901064440040d000500f42d19144490104013101d09807a680c00d0000c10340c031043c0030b03921808201d91999500c800541c1a8000c00c51035049040d000e01040041c80307280a136111500d48004e00e201c410101984c80381d0340c10ba040340c000718500e81d5504600c0020f590041082805442001031000c2c0c80003105000800c10389004011000f0140c80d1010f0314031000c414015500a002e0002c103850729400e2400c8401c1c0e0b111101d01ca18000307982400045100745190301e001c10b01564001c1e141100c25900ca4449442d041c0007008200d40241c482d080d50804668400e0305032018140c964401e038241003540c248036202c0401d0180c054490102003041c000c0c480d40000d44240ca0825240000c075080d507803800c1911020303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 800369712 1250 800368462 800368507
    0xc03120f03101a0306012a170708030c0a030c03060321030e0d030b1c0201140f042601150e070e03070515130e090a030c050f010603111005030408030606 67
    0x941c00c860500d6910320700c400103188203034800e03a103640494982030407101c450301d111f40c5e02c0d240c484e100305001c0e0f02040c0c10078074000392601041c007000c0c0b81442940d00c00090743d00c1200e00d040a241e010540d036480b550300d4045d82e025469940303010b0101c0c60443e224200082284034030f800503141c4101c01342c130340c19009410008541c03ca0764180c801d008100a00680640b000000740307807080c0e0040c2122070105068015201c2e0441d01a500c000d49072403580c0c050070303880d4400300d0b80400d1031005120004444149058403200340740c0e91003074480c0e0806594611800e40b144000e03280c0c070000700b620050095100c41c501940c0d00c90340c186030503490b40b00f10401003170920120750452604509425460614401240c4c000c004000701056520059540c5007100120a4025110b40f0f80940141c0707421000b0911801003409801d0242060f21031400c1500c22240c219040b95004450356142c0040a041c2440e14611002c9181d5031804e05501d9890b00e65150b2074103100080003548160030100315848044100881036245 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 800370962 1250 800369712 800369729
    0x31a062b0516060e0a0e0703240f0609090c080c03060409020604030606051206040804030303111908060915090c070302010b03030703080103063b0c18090c03120f0310 73
    0x20180340200b01c00e07502007809850f02050041d104808241040c4080c003040310b00c06060703240035407188801100071700f010259140415641c60b02901d80070195011070f100a001d0307a4544040d007454188094000e02d01079100c400b00c503141607000c1c4140e54000041551050000d02d10382da1300da658500250003084c0100019401900104000c02041405c0c0c2c04030f0241c4d5800ca0340802520030b01c0310b146035075010407a00104103100034007042000a009410a07440314044c00703007043c14407001450031280020540c1c808e00011310701c4802c0c06024100201e4103a00300400070403000060006101299003110f001d030042c3c6511000041c40800e0510070f60108200000c01826a0380d2450300b801e000f02407000a01050f14114901018218140c4d5000043c03c50019810b5600d00040145010300c0354195018000e440c15000707100503403000755141c0501440b180d1401c9540001428607552281c549a90080920b000781e110002c40b04580400505440520108003601d40d6203598a007131400d1658100d5100404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 800372212 1250 800370962 800370973
    0x18060f060a0b220f0503070909060216060f0c032003090a0507060507110301090213090f081611150403021302190f110703110d0303021e04031a062b05 66
    0x40d0103003003002c00d440b1015042070040410752500c007188882c800c2c41c400d080d1b055018100030894200c00390082c80c03081e4007502c4014101101015010022101034108864041d601e03280b04034144a03a10076846401410310b4100f094000441100141c204108201c2d404600c001c400210289020003500b40183ea006040d540500e949683c0035250740c01000c2d04842d1034410500303102c514101480f808901035001010511141c41c0100c4000080c140f5583c291383e40000c620204010460400041070a800028034807a104031300f82c204550700c441c200c4c42a6118440840c2c08038550880c0300140c07000d413a0121022030f85614aa00710030000d20407081d0b594042000844850520398002c0350001a900143c3c40d102d44a40d003054070340c0d440f80300f01e000040500c030019444041e581418000d8068091103030400501d05001c41c0a000410f0000880b070081c1c03e50001820b104022070001c400380380890070000384840d400e000001614981240b1500e041c134241c1c420504c0f102902d51070b10051a580c00c0401d455 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 800373462 1250 800372212 800372227
    0x1a0f070c0323010203040c0e04051603030f17010515030603100c0503010321121806020d091407030512090f1801082808030408070209010e0f18060f060a0b 68
    0x41481d08401c40100e01042c40601c1c802c020301c10300880c2d1040f944060f0840140c0c0c14401c00c810f007504090802d07074407441802050641c41c4c21005401d0007560080d00c84008010040300c008090700c209180c292140c100c4000100050303106d202c00404503010034100c141c1c0341d954910101b4904051014001021030501c0b205561640c6c200c00250305890003001c122081190070700043d250b00d0b000440240c000341e00004020b8400b41150310100740b0b0412040d241d40b042010b9111b2409a0300266600b41c526580c44403070388204504680494040d054200c040c0c2002841c60b05c1d510b0702e41d020281e10038103410000444203070980d6281c90310369844000603e9a017003040c89448041720f421090040d40300911481911160b0f2500c00d103108450400d00091900c051a1180e41d00107443c1c0001d03104176803040d000d03c0b0f62070060303681502c200e019005240d10390540b803500b00c05c1c0e0ac0b01c041d000383c8030704070f40c5202d5085124009004a041c540c8029029820042c41e00d449000c9855400541c0c00403114400220300300d0f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 800374712 1250 800373462 800373473
    0x70605040f1a0a0b0427032001020c0c091317040e040302010b24040501031a09070c0b070903020f061e030702030c0f03091f020f0a080304050105101a0f070c03 70
    0x2e402201e8103242008100603003401c2c801100e003001c0301001a400065200064903003001500c800f1148030b8a40800c150060b50701c41c0300303401d400541d00409a5004580b040181c1020000590b0040c0221040b170520300308042000442c00004c040948070414421581c1036041d254022035000b0072104202e83e07117901d420708000f4020503844040c0d600c00c0840729803641d01070290240f002400481c11503950b140902d484015030050290081e900300304140d81102e500310344c0d6204030181c401c2c4c4041d01d07100710401c614a04074074002002000c2106214801d40244007685487c00355045002c800d44030b00e5501d81007901c8801c000782d01042e260801610010401490035404805001c4203000c0310111021190501206031f00c0c0d00034911513982000340c048116006110051801c0c0921131a401620202e0394200f84203801c0500100f000c2d103030714200001303100802c0f00910a5580c01120041d030300c2e03006401d10500c0005401807003000e4107845404a04445500300d01801c0345c0d6030941c414000b60b0300c48e9592400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 800375962 1250 800374712 800374763
    0xc011e0c030509210a0215070f0809070812090402070501092a05360103050304140402090d0201080a1503060603061415040c09051206011503060b070605040f 69
    0x100d8000070b0400c008540814030028108180b50b0700180b0702c100c0000381c2480e50155800a043c02d10440c0319003080306100200204410f80100c81c95540c004403003000380c1d07000e00103800181000c089940034003401c2000d8507000c00c94038121062074a646548050b154001006400b1314500a055540303000c20200412103240742d20400b240a00c18110360043c0300b043c0303107403200555128080e044a40c070030403200ea1100002400490094100251740360085c00340068034114001d0b00111100d41c4002000d01c1110081740070401c0303082e0112400d515041d11100402c0a221810300004c1c1448000c002040f40c1141c29005840c0041d000c158a8070600d035203040c0200a0207540c8415240b091a08148503420310f0442d82586c86418225082506140c15106000c000d0034624000020003205810119141d40c0340b01e91210b40c080143c00500540d414800138442c00203900140e1818503261039030400000c2e01d114241e44041d904403400003816a16414070700d59001160708000d14201034000b584144001e494038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 800377212 1250 800375962 800375981
    0x60d0501140613060509060f03030c030f0d06050d03020a032a030914030304031e021f020604021e010906030f0905010c17070e1503131e050c06120601050c011e 70
    0xc05801c443c40c800040400c5410358080e0305e030045060000074055042006084191a0003d41200d240866440616055801040d682c1c00c940100080742c1802c01c0c5035000e850007404c0105c2c0c9000013035003140c0d40079544010f81d040c01010b10110b983c03448202c0710000000c0c0e02e102c84038100c4488009080c50003c02d41c0c0000e0148048186481c403580c449800c0002c19901900c0c4d01c0840f07004801e03024192440c1c8840c10074001c030f0b80031240e0082c0215118800c8810f000c0121540c00a01c540d003820310420012142c400c40d0310712013040740e41d1101910380c0d01c450402c0484006003400940c00c546000e210b4003400c006100500703550709101c06070032402e030f00061006440325102044020707503c0700c80c02107540c43c00031382d84240e001201108440603c1d05050085400c84104684446566216559801d000b0b910810010601180da010481070190038042214214000c075403241c5040711210031096900c401800c8541041008541119040400d5012460340c0e0035030303091070ba900d440c15030145015149588 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 800378462 1250 800377212 800377219
    0x181e0709050114240d29040e190201020f03160b010803040b070303020306010e0d0c05010201060504020c06130203070905160e010e030a0323040f080610060207030209060d05011406 79
    0x96483e948800302d000c90403004125880050f00d0104005010750f400c0403001284108101d15180381419105429107164410f242c82d807921a41c1e036215000765892503025002d14100351185d40703500808120780040a280d0b0b10120f11803411400100e00d020341c42050034905101c00500ca07140981040708440c0000c0c428090b03020751b81e8854501c2c98407070140f071152001c1460280030f16800039000f40c002d9a0700107018580b4410790b0b9641d5000518090f040c0b013081d50311105c400f03414055941d080c09150060402990194680000c0c290503564a8a000b0725201d5208c544240c030700c2c00c640e820300102004000480081c4030508125990801d4104011b808501041010200b40240e50149949808000d0300901030001c51405440c251140120380d502c03c404c203490200710310822000003002d0405041d40c0c001c2e46515500b003503281031805a0152807900f0300840d5480c10000e03564006041400d0b40e5054075010082e03213960000c22441d0480007030040c419428484d9124281409411240c07140c0c41c200c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 800379712 1250 800378462 800378471
    0xa020d0f11240304060e060a061a0721170910150e040b1005151908010f0b07050a020612040213061511030d05092112181e0709 56
    0x1c01086402e03036211008840e03103400c41c104181107140c0040550b0f40f00e40102c0b400300307a10101409460400340116040300c5407a9554100340003030f40381034010800345e0a1440145282c40c031a0f88a2003011040e0440b0748190130a01440d1004151240503016920341201340c0c2040a0b041c00150701d61200c025a443c0801e1601d0411610007124805a0340011280d8404030f252807902e03070b0340b5004500710000700f81c800381003914440080d91343c60740103420036078010b0405010f4484244a2101c440415545054000c0085807030048c02000000d18100c1e0854950a50246c3e0316901407800c03500707013166441c01950105000c9034101c504c0a0848890344254401c603114404452441e076980f044585074001c00180070b9012085030f1040c1d00607030020000a410004481c1007000646101081d100101d8a820140d04844166806a43c98843c40e0000ca80701502144c1440a50812400c00c0d84d4002e00c0c0d081c425040c0700f440c028405050103018070281062541c6c212401803011003075600d084070701c03a000005281 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 800380962 1250 800379712 800379743
    0x150605180a03150509161d0603031822140708060117011a04080a0804051c080307080a14090d020c010e0306071116081f1802060c0a020d0f 61
    0x2072003911040d02e9201d0140c1c2e07072030b0600148103801444c0003480d4610900c9680c2080b0b0b0080b03409400c1c00010540034883c1040e003034840d09407815802011f08520300070751003449084401010b400d8141400f039001c0e50752002196070513402c0e00602d00700c90180020503291800c007180c2c0c650041d68151007140a82c031880226140d09004481d890514807000312046100c5006016070b8a6085916003c0c1000350f9843e41800d4541c00100d08140e070100e003c40b0900c4002804004505040c44d00f464000c1d502c1301e041c01e03e6020741e100c00c2800d05c4010b1100317003003000304000120051000d80c8080d1050b03441d05146041403901d560740c660740c1d850355900e82c8050f11424a00165540c45a0380c00d59103180045c0280110340c8801e442075800440201d0858240e0060001c10460b124410803020000c220000081c401c3d40b0840004045040300740369640e20642c10319030b50844200e28003441060040e8140c0e81d1945e100307009107891f810082000d6000307600c8111000c0c401e0522600c0382d5100b1140380940c0c1144040405c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 800382212 1250 800380962 800380969
    0x212131a090d02040b03030c1005010305070f060503070e01030914010903030b041109040506030c0316030b07050301291b06010302130b010801030f030504051816030501180b0415060518 81
    0x2107400003940081d10560000050405410440c51840007404580c02c0880d050700704d9007880d50700342c0e6004403d40e0321030042050100c1046044000e1005028168000b420240007c0007880700411080500400150502440c4d100b68410740c01150804805818090354511041c040c102c124010790009081a000a80d80d01d0035125138025400d00720480d81c60041c1223020f00c8003601c801490f032030303140c002e06444842e903880c140220040c0380c90002c110f41283e400c51404085040c000b50540301000010700060000c1c07203850032540c0c00000d0f40c00f204001c4100400e8907950521400c40740b24449001018800805900029614140c0b4401c0f01c0d070b180440a030310210400c80707890b030030102d001900c10401000880c01101c0030b41030440c002c0c54024905910355002c40d000c3c90010f00c00f240c0d126445020000d0410415800580400d0302e46018040e5526003800041d0003444103000f4a10340f0350b10f69101400765203c0d030100305810740001254400356a2070300040d25580122030703914241c0c1e03050001303104070b0314 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 800383462 1250 800382212 800382217
    0x9030a1e02031c1107050a12080402060307031d1002040603050a0905060c070c03080a0815010804053d0b120d0f1215080633100212131a 60
    0x30129401141001018405031042c52400001c01001030340d1440010b4003924100000d10031280503800a1000c240585005100f0390105c5006000300b00c0d0744000e03c00141d403160104d80c5c10040524000c202885910b82c00e0488500090900106204d4501c01115100158024004803499038408005954a80c0803803c103490000d076000700142c10080010704110f07044006841c005000b10b582c4280b4589a58071001c0755880421a8008110324804100124105513130714035016500303282641c454100b60703a60030390b9120014020202c1c0d51240066801d0a4082880224107d000c921b032510104118aa208010b292189559004910304540c07004002c83c0021090348142c0e541c0da0306502826490001c076286105241280304e070f151100a42d000307002d900d50fa184050032880000d0030300c5090840c40041c40058858012140b24044c08905a0744202c8540c581d00c0c214065440c40f01c01c03598600300b20300300051540103640c003030310102d035000003040e0694400090302c003120300c1c2d2400c495408112030b9050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 800384712 1250 800383462 800383517
    0x140105030703082503020c330306010302161a13080a08040201090305010f050a0615170c2107080f060f12030415110d1106220b09030a 59
    0x41d8022041000018200030040031a402003003002e040c03104182d0403100e140052540d00b0341c0113920042007402140341c1030034209268484143d0102c580069044603a4544c126659402d00d65600400002d0b403d9000c0c2c0c044880d45102018400300c444417600d00005a0b22071004c59a200010000000e4940c80c032903c18190820740050150b8105413a03105d00302c0ba00140248201c0c10004003413800000500300b40140652000040d5010401d460100c442800325650b90740142282001e15890010349600030707506000a00b40b829000705641c1d00c003014044580f1482210303d00e0b40070841d0711582000070389404507024800303942da00d0300940c546030b58000314a1015107050780d00c00700e01c010012592401800140050900c102500e04141c1c0e100d10128080e140c400c50900402c072030400400e2840e9061082002d400c0581c1041d4084560912006944060080c1024401d80760014200d07544080b140800c10007a03401a0800d1f098900b0a8085481c1d07005a4094030102d03442d101c00c10410034041c554000b50 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 800385962 1250 800384712 800384719
    0x30903031e0d05040501020a030e07211112150a1b26190f0203040f1b030203010c0e040c02060610051e030103060e060108060f13020303090409060f140105 68
    0x24031014001c04000c410803070080d035018080c1040320341d011842034020345105034050800161a40c10300c3d0303005420f603912000790080703e40040405010b01070081e04c16039042c0402c030340e60400e0381049244c0b11484000742c19600741d005440507520340300b00070b0000391484104a103040059507512520300d844240c0700c88004c0b140c900c905240702e40710100d01c20b81c40c00c5522050042403034035070318098085a02d00c02c41a281c500c200c0303e0b20340d03840000200e580292a6855031100307003142b4614103500c40250758050941c0042070284c2400345c0543c0c9510565a1101464000700200180c400d0208007404002613800a24000c1d400e2030f4208860380d0020480c0c41c4100c002401624000d00d041404039807035408082400b141c07a4107110300095803602100074501070340c41010009401c040c9142102e18100701648046101d500810400441080d04030362143c1003400c041c8820040c2c4582e1001078214059185010b41062a020441d0207000d10b9410441420442403800c00c1040b034080d2021803021005d02a4640 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 800387212 1250 800385962 800385967
    0x207030f140a032301150e09040c0902090d06181e0f1401061d06040516050403023a0204050108030a0212090a05100206011d041a15220e03090303 64
    0x2d11400ba03000700d14022100c61000042e0b80300300300c42e00e104000c20381042000e020f0740e60406000c1500469080c50039001100c082d43e030b03840d00341d482c8550f5100701d0040040940e0040750420340741d05c83c001d030701180c1d940c400c1c01840682c0155820010b90503011748140c0d41e1145542d452a091000ba04103616201c3d0000380c5a242c8800035140c0d46002c4071110394040b01c1d903603916000101412800d00200700440e02c0c40501c10070b800d2000070841680d0010b07089000c181e106000072040c1d1900302c1c040f282240c0e410340355185072030036014440e0314021079201405030904134240c00a03084c81c1d4103000c0380c55540c030840e401c1055903210690b217543c0340114a2010056441000240c2d040e41841c4041c00014900501c0e040d46c0d00e481e1004105041d1407524030b034000d0790260f00144400e0742d8080c2d11940b292292000d4400501d41070701d40e5038099403d0700110038205410004660003469114900342020800740001444010f10414844110300071911407200c5803622030381428001d0007208a030341d400f10042c001c60 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 800388462 1250 800387212 800387227
    0xe01020c01111902151c050c09100e04060f0905180c01020718150e0a0f050c030406020c1e0c010e06040b03270d17070c0b0711010209130207030f14 65
    0x780d2540300f1040699021200420700840c581466000300102201c61468050340ca0b1b10034041429290b0103400d51003041014040340c500e1b0b4492600d04100c44280e842c00c528020020310100e4001c001e903030007240701035a04100c04a04028141c010a00030410404000200701d2171080741511007810080c06170068010030010003801c0500720840d49040ca070144001a20002c4038200044001281c0c80389200341c03a60420000044400d10691051200604080c049440d1180c030041c03140c400100001c1680350301242d0740e4040c00080005003007403000121001840c0301d40c010400c0c1c0d00c94000d80309500054000c40c5018541c01e10303005407021030340314585480c00c503101c0c0003000001d403140711558220b0044941d500b0310000c0040107a108011056201d08441041c1c1888038a42804000d000000f8481c0314445000010070340c214080e400f0070513150440c4847c20a04030140644519400c1c5948040741d45125007540c042030b0300824201d0301c641c5400c100c80707051810540d00c6001c0800406070036181400510f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 800389712 1250 800388462 800388493
    0x50f01080c2d07030221160f0f053408030316050c150a0c0206090c01081b03100806010608010f06081504050a0605030f01020c19020a0509070e01020c0111 68
    0x410890814000e0b0b5002040005039415603600800b40650046c3d20245500002e46400a24090908000300c0c0312032400e18080c12004104500302001012840f032600b00b04240b05070030303600b1001a07038040291514048484950900c1d02c1d210034074003000400145d56400002059000c10040700c10700c80240d070441c0e03030700003c000b0380d0741422070070000340501041005403250003803010082044208514070304600380200d160b0200c404819091341954410401e11584481c00641e40c2400a0240b07082035855441d070b01107141103da54403d403416088044144a103a080c03002c2c4000a8a01c5c442c11034016a903035481c100c83d080c00038418400103034401c1d581401418440c004080d0311040c4104215074a65008021a084030011140302d0309407540c4840031311440c0360600c611003404034020002d42c00e00210521094550601c044403c81283c601c2d940351045490310030000008100041c05d246c0c1e113141020000d0540380b070302c80c500c500502511034545241d6009001c400720040245c4000d045046000c1d181 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 800390962 1250 800389712 800389747
    0xf0506090411041806120807021306090f0218010305010b07031412070c06050106050a050d0b1314010e09070b1207140d090303050f1b071502040906050f01080c 70
    0x10303421540b1030601c1280b011034000104020425011150240c0341445100400c41c0c2c0030750810152541c1124201c00410703c180c1c00d41c0c48007034049645026000610b401709000300303d240e00c00358006080120600c1c550711154060644201c0031781c900716030504032000441c1282c0b001d00800080200074450312011a110f84416980c020403441c160b85040303400411044580c00c205ea4200c0054072804d400c804011180c00786900501040c20024141408400050518010b0316100b860f92903468046049507551101c80740b5160110010401905c1800c0d80c0144581d1400d01030407a00040c1000031480c48440060b00208903140c00000a0800c468000041082840504107900700441503561695103180600203001842c1400d10010340300b00701c1c1c50301030185c400007404014800c87c15002c0211200420300c1f0758140d22105031310195030b02414a80440403000c0b8041e000804ca01c0400c0226000845074000401c0d1541100c841014603680740044070032620403507001c150b1540a005009000341c50f00307003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 800392212 1250 800390962 800390977
    0x3030503150307380409230a0203160806011d1206010e070212070218090a0803040602090901090b0f09130525050102070f03120516060b0f010302040f0506 68
    0x4a5006181c261400289451020f8120b003460407941d29001c1c4045051850b10700680e0550402c0da801c01c01318411640d0207016038030440300d0080d101c0c0008008030304c01c0c1d0850b15a02510110214003070030507680c600001e400489241e220b202d20903000c0b012042c0103640c01403260314146e48419a1074140c0001c04400701d491a00c040d00000900255900b540c001d00c03109010b055420142441450501002450400c0031030340b03c0e805038070411030b500260326104500c1001d85103108100d01e29071190b07032b0000d01e455418000a0650382d80403042c0010000c807a0001d042001d01207031082c040342d80303404284044400d900052680300b1300e07060051a02d800e0403601250311404000100c400381a0907150581803091998015440500e02c0c8020800c828440070303030101420081c030041800ca42840000b154030f404a00000e400060000302c560a418450340441d02c0c2a0100754562031300194516189014110305030810340f0079080c0c140360708040d504c00d00c02c1d40d084400c5000c2d402c07e00c80c688420b00c922070340801d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 800393462 1250 800392212 800392231
    0x20f1005061c080421060e06040c14060306090408041502030a0306050901120209060105040518041407060f03021602060c2103191a1809060f0c030a0c0903050609010903080906060a03030503 83
    0x8a030002041c860f1146288600c5201c02030300c2c9910382781c0ba0a100703002c103a030030864008010508030940d40d250a4282ca0b40140d09036100200c036155810f082c03420340250f6000c0c0c9071010350003130000752803540400508102802d9841c00e000e800d440d10b00700700142000b40264091a55226144030144c50840c43d0316803c283c040c1091458151680e003c6000645c141a045044203440c07802d1104002d46032807404201200d0b00050710200c2d0804100422400d0301c90760040800da0040ac403040b521141020340c40c0b03502d500418266480c80d00861854032402c5480e00108480000d540e03101c07854900404980c07045c43d030034611151265030004a0030003000d2803d600000a40e0041181495032149041d000301341c001e1820550312803070312541491520318001c00551f8900640818440078421010030340c2e420844440000c919444950400c0b900c20340035a00180883c4200710074007011401c11760010b03000b58060340d034580f10759507081c4100c3d0f0307522001d54150b60450410f400070000f081c4a100607541110021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 800394712 1250 800393462 800393519
    0x4060605043e0f0a121d0f060403080609220b0f0601030e1c02030d02031312110c01110319050c0c0d080a0509190f050111061005010e01020f1005061c0804 68
    0x10110340080303d15800341d0100140586c134284032200070070881048201030000003403510f4642607600601c6000b0190803a0b000c0c42448020980e00c0e80c5144010701f182c829403504152803001401c00f03900481003524807030703481003009011132200d521a014000722216208020800c00d0404400c00c0b007a0074000d050582180014480c5820390840c0740010741c042c0b45451903d658400c014140810288a801c03070940c24042d10032074150500d080400e0002c00b640d0f007400c1440305403d003488064194480c0320605404c00e4560501d03001c01c180c0081c040c10320841840c08070342e0030664150600000c0780b4142c07006080c0d25420b00084109034825402069a108040e01604029403d420004038036030a64003c14421040c07d6014462541d01039001030701da03410702c0014000b034208107801400c0c4440f07900800b410800001521581640204032083c030351aa02d40480303822190f8500400d005003025a01284100c0800f8114002110301043c9120201d811450451030035241501c20305503c000090328201c0703000746 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 800395962 1250 800394712 800394737
    0x2150d18030305071d221a03010605030303011d0403140712020c060a0207030b15031b1306150f03110a03050f130317130803040308060901052704060605043e0f0a 71
    0x7103010308403d12140c003210a011647c2102010700392001074100601036070080c0010050000d001c20001079000d044010316600392140e090482e1003407102c49a0881f0a1030018480c01080803445040c1030110381d0f0341c250346183c0c00100421a0385d10802c0c80c0e180041e440b201c4280b020600c8034550f82e8200c1c01140b140d03500a522035011034104030416036010380d41303148000c1482150600104200904481c50700401c03004c1d04001d4481c1005111105440c2004106101c81c40030b140030350302020f200c1c9000011541c403002900b60040150500711032818840750350201107078950803810840d01d01c2030744c1622807108a80603a003e0b007003180d00041c00d0b00c040741d21810712040441e800100440c0980c0c080d944400d5030f440e02c40c1c14055079a1060380542d01601038801500d05003400c150780c680c41c0390150200025552078508250b070207480907401041d8402c1c42c0c80b02c002c09030170300120320100d11030034191208a04100c5283d1541030740c140342481101c08104200d0200e450b201c40004002c8401c0318185000309500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 800397212 1250 800395962 800396029
    0x10306090807230d03062d080d1101180201090b1e03011e081606080c0702100905031902090610030609020c150a0213120f0c0602071703040b0702150d18030305071d 72
    0x101c412a041c0440c0c402110f003c4442400ccc0940401010010880c0001007550b074002031030b2034018801e0400d90100407500200e0020300b105e0b0b14900b41c020486054030703035071110441c104840051040207013100c0b14810010715207801044568100d0854084120101e26044007503134407480c001e00e00c9140100802400c0c00581e0764402e0017a41950380c1d510306401d00d05010a042ca401e000300c030402c2e020f00300104200b0041c0c0d0f0b5003258503803006090b101030f0741c560109001a0302814940d0080921240086000c4103c800300041022240038400401005601c0350540d8400301e1042c02d120030380c880851801889110350754411025001d129850900c030b803021944951041c4c802603001280103800241080040c1c2036a290741c035104070080303030140d41350034503001e0301100320b128039500240182000100150701308101c0058840000089109004a0031020982d1301d5020528500310b001c40d25000200300200d20418500c00345904041203d551200c040341044403041c1c1000c41081c00f8140d581c200c050305803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 800398462 1250 800397212 800397223
    0x20d060e010203010e060105072d050f10110403151812030e06011a0316090e040b01051305060d03080a06081209031002030609010306090807230d03062d08 68
    0x40e40400142c9039418001410601440581600d042100500c0024041b1b4205034000c8004070305203415810b000c416951228036200300d0301c030240c00307401040300401c03510030045414640455110800c116000501041c150b9070700403400050128084141031545d1410076074040e070040500301181d4031a1814030740e266100180d58207403002c006902e98030326025000d0200300d25405006085000d0310040b009031030f00102800010306140428900300300c0d2500c100d00070070130800030300062003400089103081d04008810180a1007a01d0280a09544070a90150244036050080c0340040000084090355141100c407848042c0508940d07698404d4001341307601c0e0412600030100c58400384280c2b646002000c041c00d01c0c400820105200d4010001c20100d613450b2a021070549510410001d03061501d81881c1031140241c0b070004120046842da00e1400c0b0781c541010b01d4501b00c0441c101c0d80c1402c1458401c8041e0399072031240364084c85100301c00007541103c00c5240c954840820308800d00e01659649071a10f0131 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 800399712 1250 800398462 800398481
    0x2070b1917060f2b080408101104060309030e091006110f06010308070f080d0501031101030905030a0e0f13090c0806070e060703020c09101d040b01030807020d06 71
    0x1041482840240d1a041000804114081c10051a01d86014030104440440700340d1240d100d01c41d9150030400d00400300b180c249030800c1070001e40c11001c40b60f01d4010003035803181c00307800e405100707144250384c085900c0c1c0505401c40492041003810281703801130076400780c40f420340200c041c00040306550001340c50301006c480c86400c04c0d035511001c01d40b51020250074121a40305644580c0c124140750302d507140c000291710b411aa03000e004187d4440003401c104c04a1500070100030944040002c9004010600d5003043d41640e0240440d0102c502d03d460042d01154074802c4020720982090021042d458002e058440c2c03919806400d8114100c084c100152aa90000034002001a602d440078820b0041c810300c0c2c1c4026140c039078000c210794100004080e2004a40c0c2d42c45510541c40028103508062091101c40c00300d03e0041e24442560810101154003007a990054014070f560a820f400c90f03c000a0224a029907000454442d81d80d080d5140d40190b940823400907600805c0c240704500010301c89200e4900d40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 800400962 1250 800399712 800399737
    0x706080606070203121e09060f0c0f01060e0601090509090c10051e0703030b090403080121020301050405210a05030408090a081b090a0c02190516080109060b06071a04020102070b 78
    0x322001c00d1b80c1d0302070011144402403030480e014043c1d14400d44075801241d40042e901d600c160349400c00b02c80400c0c94403c0030498a0025401e26200103803c04802030310900406090b03c4110541c0c0e00d400905c101c0302d408641c41c580a501141e03034001682040c240c0c04240a44502e0b101d880c000b45007002001802c00f4000b101c0302040000307100c0301071613418451140380000071a07100031181880d0320002e00c14078042c080c3e21010405800c0180b04c120b0030303400300c9440a40c083c00034001e504d807500f00079496500c811108050050780c4050f00301c0c098960011155034280603169107056845917154001d29402090401f81c0001e602140803d110782c0421012058850148100c41d05003580000d01c240c144000d03104468445c1002030450b042500425440303200ca040841d020b901d4503c90426078a070110220345a403401c01c4004000c580488117400001c1114000e103410300c0701804c0ca00a02c013880c8610000a4606908111030002c0d248015002d544c006005104582e450fa4807070021082d1a80007403c00d002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 800402212 1250 800400962 800400967
    0x2010305150301150e060307061403130c0b12073e120703030c02010c09090f090210020d0206130305041a1905040311040b0a09020904020f0a0e03060f0405070608060607020312 77
    0x1c8450b25191180d0310030386c25030182110038685030340603040450345000024000c0300407000803d074881900040c0c0b4001d800107560500b0607600c0020000d1540038600344010700106a00041079207000d00c0011001c0041110308524220b182c6c8000c14003011050300350511460100507209141c40c2c20080e11540c2418810001e668521340d240280441c1c06280070b07034080da41080841e11065800004400869005040c0891305c455060b410070020860504000e6000d18170511407a0030a03400520030000d00d0040e000c41d159900c070441c4800306141c00020040004070100814004140d28001d00780300d000352015010b00380100c0411160100c0c60303010901000440c04641007047c00700c84041800b04003019201000005901d00c04641181d155000b402d90207a0005100741c2d00d40c44a0341103510145003042c801d80c1700da580900003440c006540030180d10900c41d140108148114405201d0f00a5a0140041402500d0300d002510340c028001c1107142c1c441e40500025025880500c4051240d581c0f42400303d6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 800403462 1250 800402212 800402219
    0xb210d1103070b072d0909050a0207150605011101050105030a08130f0b0d0507110a12110312010e2203030c0905102a0507050d0203250f0e0601020a0201030515030115 73
    0xb403403140c911701000215003585021002c5420020403026a01442e402040720303981c015541d0301912840000502042d46802411183d4040b6400601074950990b14030a03611070065615081c0c410038080c031a850b810100e44840000c1c070410050418545c200703800200a681c4000c81c02c0108440e80c054909890001400e409110b403612405500107010f05010328a19104400c141da00c000500e4010000740714410082c10090007000d0403840b6444550490741c1d40c00803007209041c4441b00784100c1d40222008404a86da6920400800824901124102005401c507490841c00b03410038800136424080b98400100e11601c40e030604042c0399010351910b503509540800705034003900c40c00c000350405001081d1807400252012596404070344040362040c8803030150303000090420824096540a030310a003400c24203401c0a00402008540c1c540400101091360742101500402c4200d9010380182c01032044240158001d41c0515001081d504041d007240d400c01c00801e085550219900784d480c4240c14080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 800404712 1250 800403462 800403497
    0xc08010609050a0e0d110102040807181d1207020409060501030515010906120b0a3c020a09091e05070c02030c15031b07020604090b210d1103070b07 65
    0x440d000302a1810400c20750080f245111780f12000105800200302c455042424011800d40564001d130008409440d0030b43c1d0b4840481601c1c4080214a118141c100310f003000c0000d502c4400758151408907405421118020240701603154040101240c1c855590041e41000c280c4600c2114040c501c10801442030440b221088400204140d02c2541c099003001e03402c1c054104040407142c0c1042e0700c10000b2045846400001c400f0300540f84aa0360040604150b030045860529507194040e4000c4007003d134010803140036030044c0d1060703680c1003000c01d2510108022a0101368031403e40c00040c0c520565545046031040c40036100142c45d6140000da41c02c024506520f41406030106010040301e2005086151f210210705500005000610b000d1558012804680d802c4c011140f800342e00900315aa1961101d47e124024101d42114601070030685656442c0d0346032089144045503002e9004000c41071000d0303821110030210f18843c282078013060080c640060016107a0310b00649043d242c06116030040c0c180c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 800405962 1250 800404712 800404721
    0x180106050a2007151d0112090510051f0b0a080103110123041e0312030c0215040c0317130e0c160809090705070b0708101806060801060e06040b090a030c08010609 71
    0x5e14a07202e061828206a03800c24000c02600425400101d60f42c0403d040c4a410210200c100001d4a810101000032a10004903402e500c4049041e0090034240c9400481145020303114032400455403800043c0b000c0703010b031914150303080c805260000c401c00a0280440180702c0041c001c4041100c0801c0c1445140001012103e41c40084075440b0b400f80e145444400042e840011484149a540c0b082c03500d1480c400d200344100c10300500780480850805150401c06000720b84404c0d50301c107003401104d051126001c0100c80080306004120040a4103080d402c00b0381020250842c8100174040005e25100c112038400082c0032809800035030384845110041c020002c000a0070032042102c10486000041c241160054011100c1d18250055903500f4296440c04445c81e0821230015000e9070300046a074000b50415030541e18241da80440302c2c0d0b41c0e000c041e12102001ba40305680427005102c103100007c89030025103c5e0b030342c0040c082e8000658940700c0d840e0380c00b1982c0001c04283d4440303034184001c1d1040d024 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 800407212 1250 800405962 800405987
    0x60d210906210213080d0f0206060f0d32030c07090605130e0307060513050d1107061b0f0b0103121b031b02040507090302180106050a200715 62
    0x2d1031146010074440c140d03680c0c40000102e60905601148900c41510144240c0016110800450703d030b00750307051b070007401c00c00903000c03420010302c01c0070000380d0107040c8212820000b6001420700c0000da581c56a480910780c94803515030350f0919242d0744d0000204107500e5881c0c02440d030440595170f03d0301500c0c40141040722a411a01420381854820801d9031a811206102440c20140000358001d451690340d04511403e54054001818081401001c1220071019040315120300c08a504203d486075040c1c455126013500f480c16604902c07000c0080030f00500070b08203d007240403176440d962666661782001c90b44542e18283c0700112440b006008000c103018810b0780003016400d0401c81001c082241c060a1303254000000c040040b6640a042d54100005005240c5a0300400a104030b10f002c0d40e000704182c607548400d9100b020301281a482104800104a05942041d03070340914001803203d0541e16555888412886031401800d5483c40314405d01c25100a410308160140700e011021000424092040c5d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 800408462 1250 800407212 800407217
    0x7030e0f1b01270510050c06040b0901180506060f011709010e0607050414010f020a0c03050f010b06030c070209040f050601030606060e0f101b0b01030c03030f0c1208060d210906 78
    0x30b207105111030000041004a60084178409200044a00304942c54010440f04941c1c1d0f21035a02070104001c002c2d60198450f829801c005c10102c09000e141103c0081c020001514a80220300070600c10304004a80280d0500107040210300c85840341c03694444840c0c00c4a10055903599010108807800091115940120151030400d04040c2001034524400540104550500c200400e41002090013406843c03030795900111868151696820069181d05070300c0b8400319194030b800340c0d46903071b464560242c0340602c900c481118104030007039003480a05a00900306880208100407000000b906c200410740c06548568804260741d8a400b2000e003041c0741284110b03100303102c3c441c0341c02215210f02560444100303561411404100311b1505920502000d1a006408010001d001006022a244508040301d1180d03407240307003141130160200d8602c1c60445004000341103080c00c6018440c441d18501d50050002003400c00702080549d40c0036620300918400c02040307000c2c9611000391540160b0761000405407030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 800409712 1250 800408462 800408507
    0x607080d0e1b19051207050a052b03020312040302070602071517190c0e0f0603090a03080408121e0c0309030d090825060501050a05060307030e0f1b01 66
    0x11a4041c0d0000b00c08100a0041140c0e640c4000030426150041c0010b100180040c410f81050b008420b8440e0700310b01455006192080c0001040d00340906c5200c500e01c07030040d210b0781049442684240362003a0280c29411448144007442030112404090750140d48282c006100451a244001e402c015040d44907600f00d0307420ba0b8403403501c41d4100b4100c003894030aa031500c0d1900c0c0d813030089040d00c04c95010020042949021802099507411540701c5000c1003080320150208030352141040340c2444100d070b04600580103003a884001900900e401030b0054403504056043c1813100c98801164003044401d58400e01c4a109040c030490b40080005801c42181c0825515620b00000c420303a4038031035000120140ba41e203500000c28482494107030350103103404012140121680007504072003000c1031441a01c2d080c2c0303481c000007040e00d45446103800310740000e440c06003160381e2100260002c2c000e240071004140a4124000c65040040c84a40c019404004240034205010400182040420340b454044c0c58603c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 800410962 1250 800409712 800409733
    0x102060c09010503100f0810201b01110f030a0c020624130504031e05090d0b180703210e0d0809221a031603060f06050607080d0e 57
    0x64604480d60700000b801c0044d0b894640441144520411703900c4410510031208000c241840049051526808510b40030700c8000b1318003a00380e14082c0c044400c40074107002001202c0e5400e0314072a0a0301c1c500c2c4c0d0303880000740c0441000b20003c0c66074052421000040000000c0000c0550144219000603405200400080c61310f1043c01c0030481c039000d46000400c0110a10591071354581d070301107070400c290700300a01c202c2c1094640540112010031803007102110130030002c0e080b1881207013610a144002020030442d030080351207500600030050010304607005030070318000c2c406004204410040d40724401004004d418000000003804903100340c18201300104d07110035241d54403800ca0788405508016215614002440002c02004c6106a010031100c0c2522050007104040e6100c03070080c0e2448544409810704442c01c254032440700900992005071a0b80060001c40c0c0381c0d03405500f007030340305940001c0c0c0315440d0800183c02350000c2d2000c0707a50480020324580019418010010303c3c43c5040c00602e04001e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 800412212 1250 800410962 800410981
    0x15070209060f0307090e010219020a030f18080a110f0a0302090a020d02090d0c081504050303150a05040e0c0f040c08130320060a0c022e06030c06120b010206 69
    0x8000d05001c1c400d4401c0389042c1c0d0740e5a41840b00c140140241c0030100a01c01c600b40c0440e020390400111080400d071444001003a1600210b400540c5d603070300d0f50311602558080d070410350315036180802d0760340001c8540f03501045030501000b070f00304264090041114140d010604000307060064440c418041c031050141000161180b038201c5d50090000d1001585500101072040001c0c003902d0701443d8480c13948120070090094111440c020754640c003003500e0360315035013005480c00114280e4004100d03901c01c000082049542074880c01a424005224119055464002600f6280d500d035401c0940c2d000302442403a5407a00c11004c00b2045e80c10313074051062100f1040c0190200788028a134007803109589220408051003900d41d828402c4802001042a80c8405280d5aa07254115480b0280364a030580b0760324424000110801070142070701e00e840140c80d180e40c00f142155013501c041c41c000e589813440400007030340c40c4460b103000e0301e602d070784010b07011200700111000d071903030004104e040d5000101031082c9000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 800413462 1250 800412212 800412229
    0x20705121612050f0403080702061201030b0108070603090c1401140a020c01031b020a0210030905100507020c0906100c15020a020a15020a0c03111f0c02100b03210d020a020c150702 79
    0x347c215655948400c0e00d0700100300144a0040c284280c4030440001000308000880f20a0687c0c80356411254070380d03103600c4140c040700d0005102820054041c00b0030400251500307006014003906140042c1c0340301e62a44a480160030041030b0f1009070300101d294116030351b8184580c221300d00241010306000070080701c01a403250700410007c2c0c0a00402c18440f901a4041d410075541d0a0b80300085840c5800301500d0380c1c0c001c0400b41c50000050003a402040c0d182e03d001c03000d0074000d00d001004011505800d2109030f0315002e0000e07081350326442145010070605041c0c4040e1100c1000c43c1c0203040c40d1062407801c91104a5004150b403c45071060107031840f241e030320601c260340c0303150b140c01c0c00c014403d0f14081c9039140150391060003007500418081210901000d4101c5000c401d40c0d0780031900c800041c580c10000f07580b0081c00385a00743d4050722144140700602e103103d10b0f820b16006006480c00045403040c8003a64000d804803005680082e1420300c45081008040b640c200b07400e070300142411450360010b014032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 800414712 1250 800413462 800413469
    0x203100b0f1f0f021c170a02070b060609152802120405221e050c0a081501030207050609030309151611010e01090f06150605070303020705121612050f04 67
    0x1064015403048514001c03c2480c0c00038611103031109000c00c0c41035000f406181b50030362103410400444089007001c0c510b4003d840c949603104403102e5841d1303212000d00020384c100e01d642543c80a41c448040201103200d0006001030a03400c0c00407101680050140c1c01c0301e04404a0400c1150301c00e0765040d0300d0144c80c500f550103a40044907419509280000da80700440e0343c0c0741710850080e146c00d0701d0078041c032500d018450411088080900a0740d03100008100300e03011300252080803c61000000d491541c00302d0308441d181c10141001400c114607611058900325040300c641f402c1d03030b00000a0008840c01040070700403e089146042c0350390315004081d141c490303407034828138001e03c6500130428102c0030b02074001c0040305003104000c00040900b42030034901c90728a440305071107640c501000c03c880000082204020340c1d070030b515030364502100c0d42d5049000b503201c01000d541602a04180f0000d1360249001420350351030300c81410140c0388442c2064680010303c6400c800c01e0102c104240001840c0320010794048 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 800415962 1250 800414712 800414717
    0x10515060c100e030417010b030616090506031003080a0f020f0610050111010603060e10060905060603040b0903130e0f091506100306080601030f0c06020105041104090f0203100b0f1f 80
    0x83d8003650203001d00d54040c0d90092071a82d5060003080044003415800300c00c903010200c04641551700c9401c2420b1042a084044100141143c82c0034451410001d0056030450010866038108540c0c03500e401c102031300420707106800a80b414400d2200160704200040c00c11075110060561800c0400c1da00101401d244034141c10b008002c000007010350020341c011401541c03c0760050040320082c0084945505440501d5520a46000008640003c4072301c502031040a000d40601e140d80c0300d584480400200040c06c00e01c55110412071001c610208944050080400c150b4540d032030300700486800740c4910014110320a071750250000030380b546045020107402142c141e8103030401c10580c4004501411254208844910400c07000108000b5100d110382507580c040e410000603c0d840b6030f000c901b41d5105440140405031403801007070861400c0d50011013194810130320079621032140c1c2e01007800d010b03c81070050903040d590100c6024604041c1040284141c003102c442844143c00c000401c8220b03c951401f904 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 800417212 1250 800415962 800415971
    0x607080c030a0c1e110706020a11010806190b070606080f0703110604091109030114010f032907090503010e0309090f06210303010f0e04031b11040608010515060c10 72
    0x21014010041c2c0500c03001c02c44442001980d81c8070014000405c280301d16403692140c5100000c0c5c440c03010a013080319035441541507020350760070300c011580d6500c00f80c815680011001760208540c154424003100405810682c00d45a00440c01d104007155644d0307020240c141c0140283d4400002e0204941c02075a500a2041010003084808030b040c07402260015030440c0c0c07504044107000200480a0b02040310300310001d02100600c00300d07440d4900001e1003507005d403900250043c4001030b006114107044400c00051422039900104030703203000380d1050700c0c460040364441e0401d05c4242001e00607440c1032003941c40210b11303251500e0089210b0110040c0f00b1b0040604400c0841e58541d14410f03010615014088500760844003044581d0310f030f074001e11a41d400c84d620044001052800314103480d100d65010380300c20300e4080c6aa100d15180d00040441210709000740000981290788501c07403a0098486038000041c1840d006041c0c0d4644210701400920603407003840024050f800c002200000034000384000706 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 800418462 1250 800417212 800417231
    0x412150204090c0e10030603051c12020a0c051203010b0d0e150405030a0810060c021011010204080d021b090126030d1a011e1404030c0602030c0607080c030a 69
    0x10020701554010030506400c100d0b10300c21955003c045400049411242d09003822003c1c1c3c420341c01c458541c070004016400000d404000400c0f4440c40301a03071142410088202c212080c800e0049a22503061440400c28410b20201440010009504040103042c503480c07555051605402403809002c918240081e110040300313481240902c0b00c49070842d481e190030350643c10146040742c0c6a41141000d00d000030020000120382c00c484000082c00c82c2c000383c83d80302c0c820090380c0030b020300206080c6a8805001d4507a40787c0b41d00100903c000d000818600c030140601c0d03621004000d0404410181003c00c54425071200c2c4090758030b5a6100741110030510811100d003200440c400441084000760b10130f10302010810908040854000304160481c00110644900341800156103200150600341c1821281224460503c1d00801d0b0318180c0c43e0704250004c0c20b15070780c0e550710343e075201d15504032800582002c20302d01240e01040284036005015130400d060680703080c1442031683d00008040a070703030f2512000000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 800419712 1250 800418462 800418503
    0x20f04030506070e1f0c02060c1c09090f020c0309040b1302070c030b0105041808181306031106030108190c03021206060a060e0117060a0e01091b050412 67
    0x15002550701506a41e12482c1c5510301912a0584e84442400fa65007600c81081c44d070040ea0500d0210222600e480c00d41608a0b001d00c5025000058601218811a03050316507000002030354807880c621541d82d0090f46400d01c040707201640d03000c0050038620303401489004440e50012055602c0544140c400048a16510002441000c100b02d9220000d03880011060107009003e00b03200d064030f01070241c09040b40d0380d81c0148803c482203010080c6c0c04d070f0441c082050014150000070302038030140e00018021a203a21000a500a00c14010b84440c81d9582c4003c10420000513046040100219050380c00c1d50300d004210f68880a0785054008401c148003601c80400819000d800301943c3c000d0205142840350343c4140e5914001940c4032440313029a404000703042072040900074680c2406941d01d4030341e00c0c03401690000c4000082d1000c1e51081d000740d00842e50100c681040c0340248401940415661a00a0544070410561070f5070b800700a4100418400031215117548280d0390f500410101d08504105c209 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 800420962 1250 800419712 800419717
    0x120905070e0a1e0207060b0f060a0c0804050a30151104180207031202160620120f07020705010c1202010f0e0a03022b2a0303140721020f 60
    0xc0e411140d44a80c0f014650700036a4058080c6921410081049401307820800c424010443c001950041c030030400326140d0391040c002062240c2c40350010a0610b911032000030700d0400c0760b800c20300003128540d00240040d440031703c210300c40094002d01c1603c0ca4030252141d82078800b854501c2c03841c042c1c4409034814003411110071074006101d1241d08420040914018070040e5200752025000515640f070b400c480968944200e684602e04000d03100744512481d541c1c3c0e00070300212203001c6415900882c91400c080b14802c0145a001400d41000c6c0d00c6160010340da40c0c2042015107810708640c0072070410321003070760000078480030a0303002150002240070002d01280941002c4500801c01800e000c0d0100001c030000402859840c402d80a0b61002040100044e90308038100030840c0550045844148c140b50041e90365190504602035a045880b82c0b124802e2294003001d00c01f07d00090746c98203034100c200c51669043d5049a070902c0c00e1040c00b40800084543d804512001e1301000b54000f03905150303500c0d010308 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 800422212 1250 800420962 800420981
    0xd1e0204090b07020615060d0b040204030f03200a021c060b0d0b1501050c0a02060705121908010605070209150307030614092104120311010e01050106120905070e0a 72
    0x420311800700145400e03082c01c9801d842210240c8650000309000026072400c0c088003143c05051241880000411a80501014103c03603420690812002c00410900c0f40041500d41c0241c482c40e0034000c1604800840c0d00460784811942d070000f40400300180d440350b901320440480c20143c006a900039040850091025420b1190f11032411407150f810041007940c510700c51018411800324542000c00152101d100e4103904504a8009218040042c0340c05005482c2d040c1c0920115a414415041d600c060340d44000d4100041e40c0380807034002040c07603220f0310311401341400b03203012030078154550b0200f02c0e0424050031050f0115030b1a1140c0d0b0351524104043c1c00207540000023801000018480181d0a8006407039110f0036000307401e0b840652000c5c08159105000d501d48038686803600d08001184851140c0c0011004c112803205004850b60090144c6901c04c0d0000d40006115450201d01410849443c0e24820505050600410125030045814011030319400c8803400647ea0b00950320f0001c0c070304042c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 800423462 1250 800422212 800422219
    0x605030c030a110a110607020a0305030a1d0604051c0c08070b1b120609100803030406020c100609020c060a0b06070206071703040515130c050616050601062303060d1e02 74
    0x1803911300c0a0f5000014120780c0404800345d0b401c903201d10000300c2e2100580d500240c04910104089807104007290310801c6030b80080b04142c0003040340201010f080c43c0080e20300752200e500a9406041c012810400d1205d00c145a0030300d405d080219668440072030240403c043c02102c10100001d502d401011401c42c03030080e01038004c1d03a4030400d041940496000603604280038060900000341c840400007581c40945118500a41c00c0d96103070b559840c040e501907144a106030041c10000d503102075050260300c2c043c202c02c400150311034120030301061801100a00d0008035a0814002e40c010744c507014204c500c60b0350141c1b1403076070302d140900342010480e9510b1b0a25400c1e040010810003400004035180400648041440c1c84e03a40354851412007092480710068142411405c0030011071402c1c0005000e03029014020f5580122a41ca0b028109a4241c1c0034801140185c41d9106081ca584444d01d84581c0210102c14207606240011801400003c08000c0c069892040311021080f5100150210a580107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 800424712 1250 800423462 800423467
    0x3090312020a12060503010608060c1e03240f24040509010e011802030403020d032415110109121412130605070c03140a03020d050901090512040605030c030a11 70
    0x80001046040768403d0018036510704440440d079403a041c0a490200d40d0100020040d0f038030b078201101200d611401d0401d0000d03c414000d002c3c881181400307103104014a032a00c1c90304070a078104550702c0c0c80890060314810000104200d5080c2e40c6c015801c070251050320090301c046000345a80d0101c03480703030790441c96100c014100005030304000300c8540c1f03050b2080b41004207215442040c0b0a004e900081d44c000b00035800c10740c00b10040c2440390f07008040300108018124900c07186048140c074001c4040c0c005082a00b218400071903102c3d0004c020000d00c002002c02000210b8003610b07180ca0301c9801750a41c1c020004964803c84207101a582545c011a01d009070030780040c18100c2c81820616880072007120480c3c20200040c1c8040d02500800201c240c041d1100604c401110a00c1d00c51030f441010f06109042e824084c0d0001540c03544a8203219180040000400c00d200b8203085143c9100004510902c800c03c11091007101c1c1d10105594124400c0903550b500c0c0d450300b20820303014180c81d481039243c50001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 800425962 1250 800424712 800424727
    0x10110c0a05010f0c09060c0209060109030206030906042d060b0409050f030a02072403320103020901090509030f0a020c040e030307090906050d0809031507080403121b0309031202 78
    0x40d8060340b109480700700200715040c074513001524000050b2180c1d101007032105601c03d000d4100392003480d5100c101458000d482035266400244681c0042e580c9154aa02140c20001040340b414000804000e45400c000503803000010b03034240d03991404100918207603d588400c2d149840301d0704618940c55010040e02e0029426080c200d0352600403a28110040c490688001031010403010f103980e0000c090300f11903125001004054002e00942055112000020281c1000c840500b07115587c6c0518a4030940016502d14010012045410307082104d19514040620010500002c129854118131003a03242d21025075070016400c2c840041a80c0c0c1d0010304042001a800e503020000350310030f0040b52103030744801c0d40300d80703910045951030300031160860b01c501061000305403500041e2005c0e00c0000e049a0100036411010301e50020300303440700c0000c2000c16050104058100030032800d500240f840400c02da1b00c00c0e50000d03000301408071008091507a40c2000344241446134001454000c80c4000130342d600c100f0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 800427212 1250 800425962 800425973
    0x40b0c073f0c0e0f060901050105070204020c0a150c08060414040b151809061510031109190e0c0a02070e0c0d05010e060a0603150902030c070c08010515011110110c0a 73
    0x4444484001380c462000810300c4c03402d104d4003416160180d640c60305041d20f66007400001e511011002d0814424680c3c504000b4071850010300303000158880c0429050251240a0503560020307100c184100d060012000710010b0101543e0380c841d802040340c0c40c960300c40c81440c1c0070650b40c0c00e041e10341050034212003c852180b074403003c0340620b08120441d80700d076460f00032002d11005a02c09a40d403040c4404055181c00348240c00c0342103040c00100e0030314900500c0d031000071034605601d481c0420b201540d02c01000480303400803402e40d01081003502c003460b09100e58802520740d841c0340240c1c8800141c0d0004102030441d041c09441028a040d40200320740c1d610380085c7d60032000300700d5605d4460f54440e0000724809100c0e01988031080383c20a100c00c505405c0628420107500001d00025400206101e11404106070b100d400c0b0080079560300000780c0d803c0c0300361a4a400318540c00340d1030612900c48801b103104140055980745e9929100400103206d0103043c5070390414460903126800910079404d22100344403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 800428462 1250 800427212 800427239
    0x6041128090b07020a0603050a1e0b03071703040603021608030907080d09060207090513050d12060504091a2d010e010801112d040b0c073f0c 62
    0xc159241d984046980d181c0041061242950094001709030300740c2000040d00907000a500007203078600101e15118585200d50580c1e08548060401c2c40d110807045015017400d001c0d41c0c014040102072800e140b1019036143d40e803442140f2840b010550300160080d18840000010501f00d0343c0b01c8c052542c4d074104080c41d9991079009010b01c2e07071240903120403110701c10300550001e07045074880e802420120385014030000042c4002429104030341244004840007030000e000ba201460384507203441042c4001d043c0198121141500403d02403440d00c0d07400d20210b0850307900d441c0102c0004060010950341d000c07c02d80c81c1c0800700b9046015039440c8030702c8081c000c036001c0104d059540550340c0240c26030740c40c0d410a00b6501da00c1420501c1150800c4040440c000c180b44030301c07510b1903000f40041c11079402e800c40050b5074420b81c019007008101040c0e421180780240302090040400700302c0010000c1c020b481c07560714002d8904840380070000b03000745181c04048080c0100c10a0f40c002c3c2c500c151084c0e0711a200520403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 800429712 1250 800428462 800428537
    0x30b0406060509130201082203020619090b160315080a02010206090d0e150712030204170a110d1a010e04031704121d030f030406031104030803060411 66
    0xa038245007000c502c5050a08500e0300c205949145103102a040b03030019a01c220700640040d50012407410080d021500e2010f45091481c4240d009240074502505030f4015507103021015007050b030600141d00b01003501441703200e400c4054a12400007003c000c442c04d600800403603440c160860401807000900380d80c0841e8008000d4000e80a0351f01036555051041d840b18a050784201c0898502c2d005141c3c0c5061821a05a400a12500c180d00e450000c0c0c640c45100c55018200200094001800b030240c1441a0502400038500000602e0315004030342c1c03800051004008407034083d049800b000c20900c0700000780d40081403c0c00120f20104e584500c9048201d0303034200d8003500880e10400032a201e5041e035004091041c1d400015141d0f4041c5029003c1319204604850104d2119074054a400d0b260341c184040211000700c080150f82c1d4500e0181d02400b60340001e06460740c031000500082012810010403030342d000304202c40001e0800401c00400180740aa154030400e0201c0034520b11059100c61071914641 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 800430962 1250 800429712 800429723
    0xc010b100801051509030604080702061309061d0415050907030615140306090c06030403050405120f0d0e0303041703220e100303050703082a0304120c02010207140f0a030b04 76
    0xd050940051302410310030120510781580c03061000802040c907100150020301e1000f020b007850494201e600d11150043e54200ba15140c7d079408c01000b01f0b10b40110807140c0034038460104600340c034080d143d800b28015241805180c4a03101e400051101500340f00101c0a164052010030466100124480d20002c5d540504c0046206800c0f0b84421883c000410702d208032403110040a2a485130030a00c9a1900064012424030005010100f519550b01c15904082501100100009000e0100e40d501d08070444a84900b840704401c08032080c3d403000b0040301c040d90540c03000e4500c45d07800c08107586d28511522100500c49600c400c808403031450905142e0f400c4905000300c002090311810020000d08009200050105508102e1400000d0041c0c0c020355000030140c00c10400000d106418000607070050000d480303c003034004108020802c40d40741190b01c0c026185808090b01a540d400070f9510704950041d6400034030244810041940e440100140c0c070035000c0c0c0b000c1041030341d86c944602004070030b48040b1007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 800432212 1250 800430962 800430979
    0x1506061b030315080a08121f15030618020a030b0406061706030a0b07020d0e0f060304030e0d060501090b0102071502030f0d06050d0f020306071409040c02030d020a09060908030307020706050c010b10080105 90
    0x1994004041c0c610840c0b8646511b100700172789070a0840318030000d101c02500034140c070781c0b500194241d01c1c00c07008801c2d0182218050f07512115010b00a0881f80d20050b4540304500d09a0180600b650264605010060040385051305484100000c0d00c0d000b2444001032011050504100c2c203903a001c034082d50001c00c140c40e003414a1102c1002c110301e0700122400950440818000140840d104a075184071061010b4105100c030005500c0340b406440c026082400e01c652107160703002140d40d040103814004e21030b82d084801003603d41c80009440303104503108a00660b0300440c444030041a207501403002404002c1c010201a41203251040a0346030312941a840307070180d5400510241c0c01050040c905017001c15145148c180054104001002c115405c0700862005104426200b0201c0c4014003080c01946c5480440d1850060000c01842ca00d0b041068107404c24818009095000601e9030b050340c00509040d034071406100e5086004200c61410103070b20040b455440c02d011500b0101241c160cc005403001d68 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 800433462 1250 800432212 800432221
    0x2b030c15090b060918010606020c0a05040b06040314070801140609162a0501060b18030a0f0f030c080a0906090807050a050402251506061b030315080a0812 68
    0x40c219500340341c01a00c21990400060554609a092154070004669001080ca85075000396030031940560031940150748405000602d51030540d00d40e0b4018082154240100e001503004070758030f80500c4c4001005406441d016414911040c0a880040c202101c000c200841d203109802c003081c1d406503034440c02090b1400104031006040c0007540890200e5448292041841c00352404d4030541c00510400f1060045101c1d10000ea004c1c02808020489005081c0d103d007590300400c481c0c1c94490301d01c50700c640d0184209800044072a580d14801641000001166880b9030506682c10011324034020040240010741403285500304128100342e40711030780c80c100741070307210040702d540d561180c081c09901c0b503202c0720204000c2c40c040d0000e20340340d050400c1d04004084604861800201e80c420116080344288002d54031611151003044010300291414400500764445404050000003c3c058209a00c1e00c21400007041c803840903000603c00b910440e8500181ea04080074550402441c4850440048010a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 800434712 1250 800433462 800433503
    0x360c041805030d090614281d0106050a050a031e020402070f03080406060f26010b1207060e0102010c080c07050a150c0e060408030f0c1c0804060b0a0b092b030c 70
    0x46100b400d41f126800e01d1030404640702d8030900d5144002101c0661550305440d40c443c2c15010711044c3c51031050010600300e0608041240c2a00b040d00424040e640c0c05104201192844070503034001c09511448911042c000e0001c60080c0c80f424402800340c504400d407040030168883c0d101441940601000c011850b2141074441e1031074141d100b200b051a450b0160920305130721540e240c94050324208000940411113030080303004e01c0942d02c08070f200c541000d61b00304402030b0440364411800e1000d00c0200240684d1607400303015000040c06030140c440006c981303241040380410002d5100744d00800c60310488020044040c000d421458003000008001104844540c140780b010303682568a110055420400c3c5ca0700d03824050780041031000704603c070f00c2c452104417182c200040b24080c0002c0c0e5403800c1c1413030305051140c00c0e80c04100c02c01c0d005d190720302c1c0b041084c0c0c20140b040c5c84c4144021a08a012500150080c000c003041c21641901005003503c1c00508040e000701d43c040a407403003610b1804c020344180105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 800435962 1250 800434712 800434751
    0x305130503090f04020d0608032206080a09060213091a0102190b1003120215070e0f011101020708270303120a0903050f03360c041805030d0906 63
    0x20314591003408005114500140c18100034040904011308003255514680c094401e282d010203455000004c008412a0702801ca030710070808001001e90065150000040210600605c0d8914044d40c0315101010000290129000d2540c2c0c042c003160065204c0c04034034018003075006600302c4200305200c42001540086071458510300700065240c20034030140c171845081d00c00100b2100c400092228040002142c25103a0900b0201d240e00803c1403a642465445000f40094500002e20a100d010781886503112010816034100a1038506548103202000c030380039020703200303008000150100f544c5840015105075404001e9042d00c1000e00c0700000c805154503840740080040010340160001034042506800c8590300d00e10a140c4070307140514466003c09103410079699440210250008003c5076403200001ca200190180707007800c0225404d203166643e03070000c0724055000c0c68507861a4500140341721461882550000144d030707607821485040e0001802005004c0b5521031606820041c0f486d00e0720761 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 800437212 1250 800435962 800436001
    0x180102010f06260703120228050c0409060609020d0207050c01030c0801031e290c03062206050607080d0c0e0a12060b0319050f010203150907020114040b04030305 71
    0x20400d4500c400d514600e6001011903c1001c01d4480c00030f000000482c5513440d08041e481036400707096803026071800c0d51602d078a582c000e40300021502d201c40011401c08506500ca8103411200011814003900c1c011010b4180b0b81d100d004c0e11072002c91640c184038099002000c080f8410390686074140a03400064003280c45001510000480f04401440000c0c03024940c9501340c10f821907203021000c10350780d440744400903889c1e90b4980710a07101c0f070402c1e110070006100c54211000c25140c40c210301d400d2010402c4522480b00341c0052144483c204120b0310000e5009501600b00640f049a0340d004900780b503040c640c007403181d0308c109030703c1c1115031090079214a1400714100401402c0180541c41d2440c20700c403039900144c003603030f20720340d10840c4034150756042254903012060908071480b0f854903803d0040c241250351002c9001d03a401003081001641007410348000b6043c0803100b030541344d1500c600803801461800016590a21b44400340028010355445071403003a8400d0340c0c10300107552a417072049070f00d02d00c250 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 800438462 1250 800437212 800437229
    0xe090c03120c190c0906030609020f0d030203180a0e01090e1504050d030b0303090904051011120f280b040606020f070e130219060e0603130f021302180102010f06 71
    0x14009541442c5400c2d81e6860241c8545544c55440302d00c203030101c8035164000c451142d0b40c0e500303000031818040c071a244a14011140240e1749007550324069242d209041407025018010003034900c00b0707a100340d0140d014200c10080d1400b01e60f11800140000c02d8450741030300031441034100142060200c1071841d48079035400b402815002188520030f8002e810210ad140390305010a211580058940a8140d4030590080c0c005042c07513128440b484d0100c0d140c000340741e44600001c1014024800c1108143d9030050480030420301941d449001601482400c542c1402d400c01d101a81c0802d6100140c11181080800f20781c10051280c0d100c0b41642d992904144a22082e000b18070100441035000071055400b512503907061030100103e9002803014080c28040040040c40c0e0b6000f44200756018984050b48401501c2e07051035400e000d500490040750078180180310801001c2800219114029022140d203000081951250000c0c0034141d40c42c0300284040340150310b09600c00900034880d008220841d403980 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 800439712 1250 800438462 800438473
    0x6100503160614090402210604140f0c040b0f18010905010c11011206090912030e06010e1b0a08061003020f0d0e0304031b03030306050423040303060e090c03120c 71
    0x6419a00d005071901d50f40e0180388280030704030903030b180c0d0300041100a0052103400344003102c2c0700e9401c10040016201500441c90a8071010004c0d40554049810501e00300d040740141d610f401070b4117914410b6400803002d20b10b02213429941c06010401070f00c002c0301e201148003160380041004644000d01442101e0010703c155a03240082140c01c20f0070245420189072020321850000080360555110303a1003080100d517680844428000d42114601d900c1c101c80c981840031102600e040750396400c3c10b000e641c004011090105614104102403035001002c0222055200d00362080044d040c44030803610369005d04808500a0410340c03192086400c81c800608550781030150910440008118000345601079110803c00170021a00c3c8105074a41181034201203040d0f1070941c5002000d0311950b90020303005604000344e45244400420440300e05e0030084940c03c84541c5c4500302203026044c4d5030300001010141d141406011000450182c40150096040310070034410120070681d00d01c110448a503554201 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 800440962 1250 800439712 800439719
    0xb04090b090f070e04150b0c0c12280c1401080a050c04091a040f051902090a0b161209081204051507020112110904060b090121090506090610050316 65
    0x203580009810f0310152000600c1e1620058103e040b00c11500003001c40b10000c00c8c9084d8042082287c03c040c500140d031005811610314860780c1d41d44600e401400401e8039100b1300c0c028034002c8401703417100301b6030006d0040264940c4d403c2000c8546840c40092400103403d038002805600320760080030700403014004454582441c0990b040003d0000c0011341e01001202460246079554501840a2060390b0302000103e605124000e644000100f40c8010902c5c1e0060017054641c0d81c541109200312074134504940e549040000140d2201c48021400400c00640c5050718134085621840c05400e031060442210044401500744400f24080c1d40f091991000802100f0199140514064090240b06040843d980e00010004000313881c080e01c0b0200510070081480c805500d03090107810000c01c41c124070640303000440c1c00020440000026441c0f45a1030b41040c0191440f5958412b502140d00a002ea80d104e041c0540402d445002c02d5454034804110000041a40d00d0081402e02ca004486104460018034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 800442212 1250 800440962 800440967
    0x30c090e07050702030609300703200d0f03270f03031e05070e010f0206060108070e030307030302030a0b0616121218140106080c04090503040305070b04090b090f07 72
    0x41081c02000030600c140030050b103040020034000d04407800a0301a0041c105101d00303000b0070b11044040310b0244800280c40131450001180d520903054501100c480c0361a00245500c4401e40b2151403c5205002107002e006501c4495410781c0f034141d41c1c00707000c01d6801c40020900301c41c13101140c4c1c81e40b14220294000246003804010169403281c180441c000c3c0c4010349203206030300002c40c00004961204200001c0035401000c41e4421003090a128230400080c0074001d40d100340081603039044c401084046004e4902a550382444000d00501722565a2104e1a005001c0d400644501c081c3d9414070b0842003261410606030340c0100c500100b640200c0c080340c0c45151201c82c020901d60240010402c034054000e0090160302103c0320841952903030888245401826000e8028000e8003a0745410024031101c42c01050703446508900b21000b03d90078405090690540c03041d41e000030014400e010001a41c068039801030800c4882c0c00c1010003041d1042010f1010740c00044418120488410000070700450 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 800443462 1250 800442212 800442239
    0x2060f1b16050d0f170c010b01030207120323091b04060303020613060603050a0b1e0105090117032514010911041e0908030a060504060f03030809100501030c0e07030c09 74
    0x14010340d0700044c0812103071542c00700e0711410125041a000b0014504000c41d000340a44a140b506c286021840e20344c05440f140c15111032400d01001b0985c0355085002c01c29008a843e2111208407600b16609080c8210025a10501004910051a050030f003400e05c40c6458803d003011aa090f8010704504d50300d4600d40c0c640101045d01c1102e032259902400700121f0802c21806065238440c2950700c400f401c0082c42c244031800c420fa80380c04824441d40060003646c6072010b400d411107000c01c0f42c00105644020001d401c42c021008244103816030850240c001d20f0b444c2e0b461403050360255150b056140342510146080c0ca03e21400601421f000c0200c01d10642410382c0014152410300382c0c84001903c13480003c070183c0e00300201c00d440545010041c028500d4143c45284001c1504403005c02240e403402e441c007102d0030031511000d01405816400280c0d003e50600c0208910800100100990362f1646000300031500c0c00c0c0640c00224200e10b0020301070500a1203544112862510390706100b42c50440c2a01c1c003107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 800444712 1250 800443462 800443489
    0x7120b0a020318101e0213230415151d091015030c12060f0e040c05030a1b09020f0318030c0a0308190606050f1602060f1b1605 56
    0x30100f0481e10711018280203043d0210880400072a0400398000c00c81c9407182d20b444484d1001d07104118021500d1402d040d003104a846003520074480e049804001d000454105500a40003400c04132041c0c2c0e19a40303001c40c40182c07003680804c58480307514a681105e0280003484030f0350820a1306039401320340e072070b1050f0b200f80e0003d45081c5104500f5103c0d9600c03480d04020320460b9011984901100c540a030300080301a148410800c0704200e024642a445c41d119035092044040c0044014042000c0c0907480c2c004c030300584406801c54020140b14504402c0101090640c07031910300c1209004035514505000725116010551b16403410b68650000f0101901d80580040300d16100030810740300d0b5080305021074829a4001d07191070055247c10300d10b50740b0480340310146042482c03400c101805815002010303a605200c03018507085d156046003c822440500032a4040d40c0700101007101424042414000c002e0342d02e8240d49141038083c0b10340040d42c0e80702941c10041400580311000d11050419540c0607168 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 800445962 1250 800444712 800444731
    0x31e03041a040f031211031e0304020a050630130209191104050f1f0810121103010c0908120c010f090303150e040c030605060f041d07120b0a0203 64
    0x2055516843c59805000b1503008807501a1300e150914500d43e0405842e140c4102482c0241d49400305200c80c3d400c1800c511142e200c2e03034103404400f080664640c0e64011001c0d00e00500560350380c1e00003100000c0d1008140c902640c000210007100c0e040110b05482c1517006402c0300300580c10501d016420070950b22300c01841c0e010341420035a40d005e04008c2d603004600314102c9001c1501da44034200028803043c90b00b80714040303015052800d40b5580c2d40f200041d031015107a0913403800d94015203c0c0741d417581c500030855100401038020210300d54103126105504854400c004c0f80200490070110000f615035243c0d1740702d101d0380c58010f00011003001c980c03a0300805e91000b02d540001880482e003810b078000c40302484000d40000e5035900c0c201d1001458525078030050190203440d000e017850079580d050782c1d01c411804020000340e200e40200d40c8607100c04c514222007980040041c01010000c2c5001d907400f4503501ca4001041c402e1008c00070b15500c1742c40c40040c1d0240c104c04094015940c1441c40070184d40040c015400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 800447212 1250 800445962 800445967
    0xe010309020a0e072303011208070803040503131d011505130e01060801080f1209040f0504060917040b0f0a0908030307120c09150e03010204051e031e03041a 69
    0x16a1624009400303020303c403a181d00340b400c0c19100100110403128500044a14003106140200b403120141ca04641c005041901710300c03918505542c02d40204900103044075004821300040000210203014000200350ba012a00c0c1c0c0d0300c0c800c20703640e4400001c0070580d0041c480014000100c08454400c01e90709139050041c41c008095034020305008850340040c0c0507421140043c002c040e4003620131070044c03540ca00240b2034010f00790b5860b9190f0b000c1030780350120b0040002e1455490744898028400030f400e01041080107241604110f006800060b0007140c0001c00100441c050141590070395094444d491405804c00107010744003e0142d201108c000c0600940030000101d0141c01c100651203000c643ea00c4101c0500c01e288800151160040482c0a2241321103090080c1050048281c064072060314202d280c000c85040486e00a02c1581c22280d0420303220522625000040c481c400c1c04000c09604540300c00640540c02c504940316805a0b1215404c2040108030002d070303a03000003510b01440b02d03504d407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 800448462 1250 800447212 800447231
    0x20d23150105040f0e090d020a120c151a010f020303090a06050a060b0309100501080715051b0f0c0102190c0302130b0915180f0a1805030f130f030b04030e0103 70
    0xc09504c49030301501444141d0010040d000100b03121074030303c802150005012444040e9561500c9144425401d020401c60f19015018441e100285002c000400c44c1c007004501803d103403100100c54400c00c1ca80c0810352611194a01e1480081164440c44400016140461013540c074140540005081c4105040c0c950300c01180e211180702c0103501551040004060081c203030b0314a00c082d02d030140d003d0b09a40e084540f0030048841d01c4d00c01300481e06407a1402d80e94a0041c00644248009182c100c1111442000c040c0c103940500020003503946c030002d070202e4620301c940062017107a01c46500b8006051801c180420001800c00c0c501c880005a490300c408101807800201182c0c10100803100d5107400741502d120072502d420040000000c2d8402050001c51504d02502602182100500518241130340c1c0c181003011101c09034038683e030450303100058035984c01d103000d1510000e07082074041e20191003e02c0300009202840461440841e070b40a2404040f40da110380f015100400c440800c94189520340403481c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 800449712 1250 800448462 800448479
    0x40e0a080d090c0b09090a0c1e020c042d15080d0e040b0d02030c100e13050a0606021902092d160e0d060b06090a09020d2315010504 58
    0x3014001d40c0714000056484090070148090742c0b460b48404440300d4104034810090f220880c4a40d0f200b25200c1e0301148a64600108484a0f0441c170078000c0001048602080d410342c0c0403514410b404000c450030300034075074101900c0d11000349802c008082c00072030521100c00241b440e0049446501a440f060001d9030b07481d154a03040640300350000d800039102905a0304140390a109014072103906071184680c054081e07011a80c0d40b00540005882a1004c0300850041c5200b2591004104005000e031588030490301d0f4040050007080e1103044001e801e040021880d6880014101244031904050f0b0029500c2602806015480a4900610284007602070503030440750301540a8412000341140d04107203413100307090144100385806001044015200030f90710303984080e000f20066400003400150310031040c0010341944200100b140d0070840300300300014071260950141102801c00007007480b5400c4200030b03140340301042e001c06203000700504020400f8240b00001195503c00103041140c903264a46980 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 800450962 1250 800449712 800449717
    0x60702151503250e15010215060622080f030c0d02150f0a06050603090a03120606050405120c030d09090e0604120e0109081b011407050304050d050114160818060105040e0a08 76
    0x5180d403840e5005c492800317940c0c10000481c00c0d480210903250395040880c006145440b4624808d9003da03103030303031800d00ca6102190b101801401d800717003101d250b030076514189a125000384400100500035801900c408074000324450f1481d40003101c0d43c0d00340d0f50b2809841d0907020009420404182e55802c0045000d444160003180140840d030001c0888000501d0000c0c2000060803240c050f040c141242042041d80100603981034680c1107030046022648090003500c0d041a2201c000d600d445580b07080c7d50f0103034002c002a400d450392101c0030b02c001e485201415946280c240c2e030007003030030083e8403081d82405c0c400d0f1804001101d0500d44003400c20741d0ac42000f450040441c5881d20113000724041d82c4003035a0040c80c0c941044210502c949d0a00c141601e649880b030013075100b00d0b4020702074000500204a02035104140e0180032224890705400c0c000700c1c0801080c0c0c105500000715160b0300115002d007540d1440c907e03203100c88c58000d00c8a0303030030f1200748006010030101a880c58807500007450006440c03c2c01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 800452212 1250 800450962 800450971
    0x9150127090305031f0f051e130912090e0f0402030a0b0901020a020d080c0702060310030609050c0109080a15271101020c010c030f030c0c05060702151503250e 70
    0x21001d0b02ca0400301240c4c002c90b1070203501562017020301d039070402284840b1403000b0100c520481d000c141c882c2d02c840300d00444c01741c140003480d40216840d022030441d05103039014215080c02440c0b2440c40c0354407044242d4100c031481c060840c407805807100055509606083c1568058406400e50303101e564181d860800c001c005645458040c0d402041c0030342c070a0ba0400c42c51306180380500d02590203090204042d402441080c0f8064051500000080c2c40460010700c144001d5174484810003401510341002900c84903a880c40c1400100c0110000440a5000516a0000e41c002c0405c0c0c08507011080f21000030142072805c0e122150f0070600c03501d250303948200c0c1d0800e95801b40540c03441000c50381000a0a0a0a4285075818001c1401d1a0008645d210400d8803000f5031508001402e202005800c1e41c51030180200142a0b110303042c2000b48160340451403c1240001140781c01060301c03402c030320360101c10000040d950564081010040b80000300d0905030818140c800c08009102d0b02c548904a062108030f4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 800453462 1250 800452212 800452217
    0x628020a110607090308190504150507050d08010311040b030c030111090a08030a0c030e030102042c07030b180c0c03130816061209050f010c02010c08091501270903 72
    0x101c05050702420702c09a40e001c020341c60544070444c199925885c16006010707407018030100c086000e4503050300540854000d803007002c2e84400744640c8400c0003400c5520180e0120b40700d0190048400c81c1a000e00001410f036540300725540704030842c210a104c01810006101035140c4a0302c03042e45941d85080c495803d03498542128150395001103000c0c00340d070303507a181d110820300c0d03100300580f0380310035031004400b4505030f03252500412041584000901900803a00103241e5041050442907040041580e00d03455118041003542941d5903400094040b07441c48044503400604e0185a100e056140c0507480764403650300000c01d8200404021010b165412280359036103200c00c1100c043c03010100401807030303100e00312100c40f201c000303400d1880081441d05103c0c181030003592102c100b041000f105004042c99250381900070403005044e218028040d0100c0c5c0351480105824001080d014500490725003440100001561101c1c4d01e0b04d002480c1500c0b03200f0703092006000007155802505007070302884012034020b0f07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 800454712 1250 800453462 800453477
    0x70b0f0d050f010509070f2322240912050c1309020f040c2705010f05070203060609070c050a08030a110721030e010f02040609170628020a 61
    0x108400c044520140c070400702071038101d0040006030f9581500e45e40c804082c1c5440d0b03001c50f603860400d03a90103800150f00c11211002c0c11408100c006404043c0c40d4400364035010100009144851441d11415405451081d829080300d15240ca060070301a2aa00840c81c03810f00318507641c2d00380c0440032105540303044840340c0044103a51000d03d80701041c1c03820070a020b1400c1000e01007680c0010441c5086082c4540035945910004594500501c0709a811039594001440d861048045a0042c45c5540c000c2d2404100704a140003d1144101c082d0ba21b0164003400600351034544004005c241c500040aa10070001007260f14400140c05001c0304800d0b80c402c3e508180c80b030802107025004d45003003550a64000b00b06000100c0031a200810107400011126200406403c000c03e00b20060a80703040c00003490f40c203003403000b03060000300d80c000c000f21012075035255207a6031075200300c1100c0c41442a0b42c02480c2c0c00100400c200c003000d941124015048200b01c2e60428050741c0001d02a0707004040d2240c0412000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 800455962 1250 800454712 800454727
    0x503220f05010b03030a1b02040902030114040506010b07020a140607020d03021f09050c041a0301230f0103230c0a080604060501080304062f070312021b090c0903070b0f 74
    0xf4080c00c4580c9400324040c0d81007540ca90802170802203100c3e030112029800400a50954603242d12109060381c0240080c81145048500b4005015081d02e085030680309481c0005039041c0746400b6900e44950040034801c7c120b207000e004810b60f102d4803a1569100c0000c102200050b601c414004102030300c250081c0005012141c03040301c0d1100208800e41240303042000c1040003c2c0301041440306004121400a45449503100d861b02d440f13030345044560550320b0641e607950f00c1c20200f00c0030004055030b200d100d1096034135109050803041c402c0c44001c01c2013401109240c101804509e0305546132a017941224810852500000e03604130681c3d1101c0d10079000442031205211319401a01d01410001004526040c07070041c004001d1f00304540c00e4001c1c44e404480400c07841c8144114440c5211907001118030107622400c152008030900345252025105206050011210a5182c0404040010302000b031070fa0741c0c9108904943c3c0800340d059410700070384801240d40c04024014007086001510020b484219 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 800457212 1250 800455962 800455973
    0x3070b041805060d115a0913050a050604030e030105070918090201090b0403080a3b040212070206071b05060a02070215031f0e040c060503220f 63
    0x200508124041c10042131600b002c11441c9118080130442038a1003c410000d9028000e0f03030740c0c4046031b0154600b07544a03030a2840c06050380c094095104c0504045a10f10501d84d040102050050080d03820038a21400100c2000188807010784460051082e180385000f0703a0f43e0a428450122012008a4620a02c0c00c0003810309108a50380009182000100740b41450802d050132442c44080321422900c07040306c401164410400d520007040c1440400f03455503142e290082a5802c60404100094129025262070aa88003158001240d10702110084a110001007106050003110042e070060b4080001000282014030201e2103080d00b50701030300301810611802020a10305071807900c0c4900c540d031039840200720301068450b08401c480b0070050740d5000074404512901c00b0156101303c0c02c1c5002c01009104214006a44201d5200300c0d1504c00da16140d501c004022901594058a880c0701c0700e5080c42428050310085402241c02c1c3d000703800d01500c1ca4481d4002094440c01201d204413450090800c125 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 800458462 1250 800457212 800457221
    0x60d080a030213120b0c0d1d01022d07060b01050f07061d011103010e04030903020604090212100305031204062415050901020d03090f2a0506042303070b0418 69
    0x2410056050f0a090107450300f850641e406014244041000507c2103a01c511640c002e40300c00c860542c2211540c418440c25078002e40041e980c82070306010701c40803900071021142c140c4940d4500c007041a070a044658490780d00a000008981d41030200802c00c0d0300b20042110040c048180c404c071408580111811480c0c500c032658414200d03116810400081020000c04065030705442c60301961501c65951802c3c101c0d40c802c1c20381d002070740024002078003007030848150f0000c000c4c07000d400d0942c07516900e43c0000c14180083d94070000e001d40c1c0007449014501c03e2102c1c41c03990041d00424000c2544d100d04140c0412740c0ca605240024158600f110410140d4070300c21340022960118149030b400c268003540041d4442e5002d2440c1001c040d50b901704c0d40100140450140d03440343e04807032407100392100c5c83c1d09034440140080300ca00808500c0e050010321840d0031000c40d000e5034144074120760b0500c0ca0410345003600401045441e0725001e500008103d411280f0041e0000382068981030324044000b806960466 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 800459712 1250 800458462 800458469
    0x20307140316031a09040302060916031709040902060a0c020405090604020a15120216060f0c23070b0703050601171608190510050a08010b1503060d080a030213 70
    0x10024000c00c44924507500c0028802e40d200c2c00d02040340e007100d603c400c1490007405000c5611407500804d0106040e80001c08511840b4044112800c05011084100884032107100c01892a29000c0e401c0292030990350181112010140c00840c000c0130079400244680c01c0894032000007015158035000750b150501445800180940c0075090b41e04058000c02d10881060103203548665004460198044c8107100c8032070440d8104400b10340703807480d00320070300110300d005031055500508007045011410341034400c084013410a40c50710104200000d4078a1803e0041030140d501c1c0c1a018001400811204480d107407041595035800911840d0000015000b506004096501d04c2140400c00210130355058001d00c1202650074000044e640d200d062a8580c0250700544c03101c44e0a11090240c6d0005409454041d0754003250410103498880d1003031070803240c10142c1c00b40d014400c44941c0b000b1582c0c1200850308020043d101c1801c42485071281c0350223900554940c000030f640050f242c920707452401e091601a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 800460962 1250 800459712 800459747
    0x10201060b1804180c030b0105010e01050a080106110c060f03010317030f0103030333052106061e030a1103011407020d120605030709050103060c0203090a3006020307 73
    0x4049a428070158403101d0040d002d4050741d039030b130502c030310810858030800c9140e036102c800c400d6900d07103e107016024a4400c1c070485011503020700301c4a0f100e40c00749054920300c00b0b56607a00b8440d0303840e02100301c45440f284c0044504070300800e042d00c034003511a00002e250101142c0b503500d07542d500d180f80000c503c1e20719003078101501c0d0341441401a0056081c0b400c030704582e0107280120700d03464003580503e540c1c0303180d03004108942d2141c8101043d580841c0c0906040b40c80c211989440003041c3e00529400345001c0c40068215002000001c03568540307100c64104890020034120104841800031034074005240c6400e5403034050341c10280505240074011108d080342912100f050a08200780c0107956041e01160b03010500511030081c1c1c214162a81c03080c40108002004c44400507612480e5000410081c00300742c44090908000d00300300c2d40000221110888050112410385d49480c00080105a0942d501500c91201038490416079940b0004940014060350f00140d59041183c40540b10b9200b1000d0f0044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 800462212 1250 800460962 800460967
    0x504140103150e06040f0615080f1608131407081207080301140f0907030f0f1b0503040611031e070c0b01090b0a080307050d1409090a18020307060806010201060b 71
    0xc1e260040c200203400c541d50889004491340341c00c00050003504000044580007440c00380c0c0010744400d40a195018116191039082d8541c80c1c526a61544050844048502d0310500301041010341c410400c2c603030b1082203030480c621580075558030043c0851544030780c4045944040d40a00c8800320030711100c2c00e01d1240c44a041d24111003940c9242603800148500d801c000d9080c048403240e40c49a15141e15070714402000d90b070041c6000a40607008010307a41d0451841e5241c40071a15850035107200ea15031900e17204004556200769a80b044680b07501c018070450b4165105c8258052b29581000607500070f00c000101030401c0907408050540c8100002c021804001441d15444007007110400d601c2c0c1036038080d4601250400942010a1401c281070f4452505ea110000c3c0070000d1081c049030079071501846030751f08070740c0681400f80e03907405c0e008942d280c991210402001c1107400042c0c0c2d02c1820388140c6030f01d9501e01c00c00e2940029051807240d503c48401301d02d114080180c00d603420b104010140250040b10390 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 800463462 1250 800462212 800462231
    0xc090902190804140a0c17120403020904020111061e09031c0c020102070f0b040b0f0f06060703030e100905191a04020a0509420d02150403030504140103 67
    0x701d0304044030a014204011901340310f403950031484000300201c2101d00c10b8910780f4120640609a10582041100300c1e217610f5014000490100e00e1124a40c4403513061900750b1702048003030b40b00503000324140701c68201c00a01212060088900c1580e139402e4003003240701c0e0420702d240c010000410903610341e0001c11000400f404045241403a0340c801c0c0800090240c42c0c40c00690082c424003101511803200c41c4489820030007101030080c4182d11a0f030110f401910b603482c0c1c007003640c901503e000190b4025000040d8450414401030b100d4103020307150124640140c00a860b0800b070941903445411070f1038400b0f52062000421044040d0079209a07124003448154807103802c5050301544c3c441160100c0c50115095503907003000702c0e01808008104030078905042050f031018440780104c2007503048440082c11221072501e0480f4048034010b520262008900703a04010500080b104100c3e400710041c0043c1080c8004d080103000914420349a01e6034507420102080301100441c42441d04060400c0c102c0c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 800464712 1250 800463462 800463487
    0x609060e0609011e02210301170a020102100905010f02030a09020a050108090a061508160303090803090906100903140304140f1f030e0d0c02040b042c0a0b09010c090902 74
    0xd420f4443c124440e4031101c103403040100e05061540c01c6c00150020f8240c440140800c3c2d445c000d41c100e030901d0541055600989080a407542121003001e40960001c003c011806c500380d410040f08103200d000006228a4140c50740412038006865142c039280d52100c1d00411802c02a81c4000a4002402d2440c00d03440d014483c656281207140c402810320742c81e0004828568541c0002001a001c00c2040e2440c0c2e501421208401c400300b8481a4006140d91100040001c00801260400c140242c0902601d81c0d5a20a2151003901d5040200400400000000115a40803e1010460709810203150381c3c51410000d865203003a4422898820961a89007107126074a900b10348a21401c0c100342c88843c1c2c0301c0c100044e002001240d5100c242401409504001158800103050113188200c40c100401104c0400b4442110394a142040758513042281603000e2050030400e0080c6054180202c1c0c901d00c01e19501c0045019059800d980c0e10ba4541c980780b10306075040b141d0403001d40b5084904504100704001d41 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 800465962 1250 800464712 800464727
    0x1c09090513020f010507050c0406410f010c060609051f120308101e090c0e010e01030e03072102061f030f020a03050d21022817010609060e060901 64
    0xf02030601c8000201c010070800b09000305170b0707881c0c00101304001d201d96403d0070001081802e42c1503101d62100b540c0c14514000310b03070b10490320301118008405142407840140030b2518550b08146043c420188601c0d40010340e1070144e500039050480d40401e090a041381c1b003d070280703000181e540003003500b00c109004e069034403541c0c040ca4942506c1d265035135896107414480f0300071258000c00f03c03812004603482040b81d0300070b4080d41101c1c01103e08020510740301004482002120780d000c3d000445141b1140c116620a8200760039200101e010380e407414002d036441b422030f08414808440f1100201d10186c0b0859010b005843d4040207603080d2140d01c8040800b804c040c001540002001c0c0d80b90b40c0044001e546410052901441d841021103041b009902009080e003036144400a021282c84101c032504182d450003502c070960808001c1c01d90307002101d284c281000f54509075000801180041003180344d0845210180200440d8980d005507900345030004050903004400680624000c03c00010240d900490 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 800467212 1250 800465962 800465989
    0x609180a0902060309060402010806093d03060e0c03070308040e07030f0c0201020c0d020c012a0206070b0f0c030408030f090c0402041707081209010f021c0909051302 73
    0x955001940e542000e0800500721040c010390045800300400800714800244e4038080ca000341c0710ba0b045a601d60040040744001110201d0454070f895242c10800000013180301248801c0a800d030b85402d0310200f103424440b1060b403040c0c1f0256155904074407403030014030aa100e1504154040c194290039a00c6d4201544100e110b01680072041707a00180c021031203a4084641c400916009205252410100a010b9003118a81220790300a64248042c261f00005e400c507190001a181c0c078841d04e00e1101c1c0144100d14402c12814041107001c0340000683e5803000804089100d01d0b105841824044520281d2a0000b0980c6d0310665040091101085013442540d60182101e4107095040d900c0e90712107414541d142c0c2c0391070b4002e8004500801c40c40500d6080700d0901c0c0d00c4800310340480380d58a03816940c80c080171041103080b020402400e1500d5104290a9440c9800c500490314054100244801010402c1e201d2038001040c026062104115501807550014286400c002b03030076006400260b5500070041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 800468462 1250 800467212 800467249
    0x70e0402060d0b15091c05100906140c1902030408031803030909040c29030114030a12030c1b0b0f0601031112071b050c1903150e0c0609 60
    0x16000c0345080c09500f010f0880781e400713050b500411908658007a5960403942886120b0307074903010640303030443d10482240740454001004003038005400140c50b000700040316060700c01a48030240c04000700f4405145901490a058400e9540c00c00004403103038004260090ba0215042003004024800001042d500c8c48031780781105004030160803001030b107944981003403107801c100080d081100340117211508504681a8015404000c06010044500300000040140300d0b201c060006001820b400c1340394814082e00a070031180a1003481d1110440f0318080d005040c0002d407114031140d8072690040398040158011100700000d9401c0d0740c0e070712540030070040900c40c8180c180c0000500c01d87c4243c01c07100c500442c4541d42c46ea1002800b10f0103008041c11181d24021801e90412003540c40b01f40e0030041c2040e03802002078209608480b04200e000002e0a041d03c80304443c3e41008808910a1a4401c41c00d6500702d00c0001c40e0701e200401141481420454544603020521010140d0740f28903050802d01064503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 800469712 1250 800468462 800468467
    0xf060108030f030709090c0e040b0f0109031407031e02042304170d0914150103020307030b0406020d1d0d05030106020d111219080901020306010f0c0f02030d050703030509070e040206 80
    0x444211050711044d0706c0000d000d4100740d40740810f41e070000711416205509490600c000d114150500c03284807510002a400512400020408107849040c083c28007180303441030360a80d40e640e40300c120003910b002c182074840c684682650001c5103098422441100d02a8100d1034048a03240301030840480010005003c403540c2e1004442c0d10006901181c0c920301c01c4200400020440341043d40c500c504004160740c05100c1d4a10210810440144181c103c1e54001c0c0108001070555662900c9000b003e801103403034030740901036282a42110300412802144190292040b400b01d001307800d1038800340c61403940921200300018450305602007030890b01d41c50542490b1640c052000c410354075002c80742080710fa01a001241121030094501030301c082c01c002e1540c814210f038640003841c0e0300b01c2c44182c4480707002c540582c108a021030700982e514100f66015230344011070105141c0119007000035000031040011000913411003019010700c1103d8120310300718001c091950502400030721350354000d00003a1040c90007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 800470962 1250 800469712 800469721
    0x6030f10031506032307210b180606040908030a0903091d100603060605191b032601120308091002041203030f020909040311030d14090f060108030f03 66
    0x5102808000c41c0d00c000801d150307029000304200101240d01003283c45c03049500f5903859810810720540b0031501d4480c003506941c0d190901e02e04160f4405204e1142c42c403811801032000c10141c030703101c40c896240110305d811894402c1400350700b4403400802c03151040b8075009104010403c0d290a6136072003c54401d0004241c3d030030341070544a80c0c03e1035010109000712a0500b16000c0c0c1d00c0b88016001b60381810010b00303880c0e01c88009400b03544481c000e010008409008034824001180c1081d11000100d040103040443d400c01c0210441c188403c054000c65036540106201ea00410301002094024200820241d410854002d031a500d0341e21000d4101312030207020400740003003408a800401a1074404640d11686c40310340c40d0030300342074180c1600800d280c0000b0400041890084a101c0c042c0188428110703515683c0980f1704d142e001130300300b400d0322089c00010800720842c814808114003075440311131107203000b0452601c1c0c08182c00107110070b03401003801040403590010507103d0640740e00032019102d030344 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 800472212 1250 800470962 800470981
    0x70801051c080c030a0305100605030406020a03270201090b120109020c0c0901030f0c0906031101030f0e030412021207030201050a030e01020d11070b01080c0105160f1712010509040206030f 83
    0x1050a015050b03500c0051614403c0300e001009040c64881c90700c050000303680d01040c8030020716841c49004d0101740108005400110160300500410300c2d9401d0001d850305000c070400682a840d800306008401880c07203000203540c0c000e188517009000301c40d0f000c1d20f05a042220080044010700c1344002481e00480c5a80c200041804403403104800a0100e24496030360703061403140390032840004c0d209088040c40102c0c0040550041c402901e80210051516482a01c01100141105414260700e0f82c0e031600d18141200b0240000d2004054251810364031074180d00411508020300701c034122040c3c3c00a9030410051340c0060035540303824440e081c0014407182d0808024064400d68951b12441d80c0340c44000424881c0e104080c01d1800e009403c00004d503030701c0c1c4010590b14140d4041560102d001407180b81094210360110640491040c00399070045a40b40e5940e80341e1115403000c1004503800841d42c92285d448000189004001c01c840c560954149a00807500c2c0d031101600d400784801c1c207030740050340c0d404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 800473462 1250 800472212 800472259
    0x30c02040f09200402132d3314030421080108060601030e07181e05061009032f031e070f05090a0c020f010c030b150307080105 56
    0x180e80c0c000034000000280341c224280c030030340c1e640c54440e010b001e64501c443c1d003003c0c4290382940f400072030010400303814402881041422181c801d0f00d051034041c140d16074601081c0c046001000d00004003080c0c0800915006103000401c000148a800c5041080c800030760701c0f0300d0f9072840e41c00d000b500c560359442d40e092902c2a0700c040c842d02c41c208110440b89040c00c6074408481412182030f001070758800e03203a83e001107040c0d400342d4060362080e501580040c490190f0341022170001d102c131618000340102c40405a03c21190000707203100c030350f165164100b0406007420f00c1400d542c0d02c5245415605282155121040c42c02e644200400e078254000d804208032066a0031241e0401c001411240d84034441c007049614140604e240c0d072038500030380c0c1e40041c070844002110001c1d02d038000c06449040da079440c900b000800f0443d41e000c045114000140a00400c02e114940b4001c10f25980400e0b540c6c1d4050510804c001084d41c0110400c804208005289901c00c0c04581507400031925150011503e0700c0300000b62 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 800474712 1250 800473462 800473481
    0x2003160203030c04170a1a070e0d020f01030c0e0a03050a0c150f05032706060f0d0317090c09011706071b061e021c1103130303020309120703020d0e1903030c0204 71
    0x8901c5498583e01f0544070220b80e44511884e940b06142240030505000100510a400075007000c9022140715082d8040d40050405400e00e2809407200c030a1007001841075415a4010790b02038206420500038041400c0c01480a030582882060000c030b20104001e240c80200042042041004000b00d07101100720903c03007080a492043e6000b80b00c2210403c1c03500e804c41903894510486d84550800500d05103001c81e00b16003901500e0f8901004240040340302030032001010056240542c9502002c103a0341d41d01070a010301259006030f824030751b100701e81611301a405007240c0140031326024840c254000805620518660000001c5428443d0810810700302d20301c2c44c200080c2c1c2e40086030102c034403900c22001e2041c01024101c00e000740c407a1103500301644c0c0b1099030360000711151000881d000c02c1c040e400448e002480081101c00e18041c510b900645d58211807812001070f00205144081303140e2201051112400459019050841d20141c181061059100040034002c4800c2031030b055580c1d581c0022601c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 800475962 1250 800474712 800474723
    0xc0e1f0b0306040c020706090b130306090317061e0d151803021203010608070c1718041b020c130e07030602070b070201020406212003160203030c04170a 67
    0x4552203080186458000b210781034022890700c000c04106500c000b800d0011564207854000f00c607814440c03240c0c3c42d64080c5420554140c402400000080e92502c18450801e00980c2e0b003a9014119082c0c0800201024042d640f00b00c134211525401071441c005661074408003114251850225480e1295101a62542030f4810f039140c0a00c000a0000155007240418480d50a560340780313010300705052040c0400e01035540019030840002d04218080e202100c0190700424940864507101c1c601e10145030310482c14800c80100020311002141441e008010b14031041018a140569240d1402556800d10381c03a07540c0f1030103000105040f0042143c1c02201c8615220098071001c42c0c49090020103540100c008590a001020008a04074170600c02e540c1078407030640c1d41d251240b039071600300d0b0b400b01c00c81c013103124000303903140d001e80c403c40929200c00070b0103502c1320601900c9240601c1c84003500200c0c03202c02c1055407c10010810207079803110458003580c04100c494000d9820f00040c8902d00344102400800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 800477212 1250 800475962 800476021
    0x1002010905070b09130c03092123041e0b0a02070923071413030b0f0c0307050313021f0903021908122503080f18151504090609060f090c0e 61
    0x2614045050384d044648043c0c070f070030000d40c9000031000580302b00c0e008a400900018802480050581681401c001048024014106807188206880341e40301c900c003d0b0140e071080104010340b80050140004484580a291290004640c4d00f00480d043c02850781c0204000a403154100c0b9035403000350349241546240d03070701101d41c40e4905401090015a2000e140c0042900020f003200c101d102160b00c114090307a2901c0c00d54603140c205c0d41104003044c038102d9104014410100c1c600c0d2010759440090300c126619458400c0ca0340c01400030a03808201290500381d1849800e102e51000040e290684224240b2065920010030005003400703c149215400f401d900311f440c7c81c0030306074442240340c080c15200c60301c002140c0b04c4411520307001c000c0318a10407258000b400420140124205556031102c42c0c06a0040340c0300082d800942203c58020013156107940c1c2d203240300c06004061007100039210341c11004126055482d10f8102e0350516070b00c201d20f81d4400304030011b980722614280c1000079a84e1100c0d085c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 800478462 1250 800477212 800477243
    0xb0109170307050c03161512020c0c040f05060d0813030b010321020601050d1202070e09070f05090f06060703050d14060f0a06050a11010b1002010905070b09130c0309 73
    0x64690b440142c0648242c42030240f640514540450f40c0c0742a03040c80000303004070500e0508000c400107902005001070056469000d50110320a0000303040c00410000038242c01710035003040000300d807000610302d05141d241004100791034540304a8240e100750011b80c180c3c1c85491460403400c400400d9080200f103040301400000403c02c1041500d60342960034100c0208140b1400d5003240d8500003482034640c0070903500410700114020111101c0c20800501c1603980c0561100c88c010f800003000e4480d04000e91142008000200c070001c1c690028200c2250302900300e040c1900d118030b044201418061142200250720004c0500440031551505040001481400304100c8420a02c02007100d40c0ca0103034103005e02e2981c0c0c6242c0310026000740c86080e12014217014954808540803e42400c854091750341c3c0300c0e00d0411540d24043c42c84607c84c1a580041080b103038600d0f20504203071203680b00c100a08400d00080d03074140c2d502c5a003041d02109032000000c001074101c00403070140c002c02c540503105090300094074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 800479712 1250 800478462 800478509
    0x30b030a2a09090b15010507021005040602070801020f07140a1707020f2e030b030a050703032003040e070c02120a050c012a020a03020901080c1903020607060b0109 72
    0xd00a480781c450344256055039800d035101038461100006000d030148030300140801312444440d41da246018940141003003035950200d55040700300c14400c00810404501042695810000c1030040d05002c4000d5081c502d6200396120140103454009205460002100241120812a201843d0b800046144080d0001c0d40011340c594020701d03059000380300d4840c1c09049030503c111480310741c40450b8510b03003100000c1205244103001d84807034030003090f031240e845803502d6808120744044039000d00d0182c00c91174514500507000400c01c165480e401040034040c402c2c02e80000c0107030b408460007403202034403556984400704c42c1c4070201c15000394065407105405003012000260500b0a610070307811034a014003600011b40d2050781903d00e201180851701d03800c103540c0700b01c004002031107440503000068003511385c0d0016900303103000d800559480d401100d80701c0b6280b0b04840c070b401349282c10800c081092802c680108030107105505010b420311b038a84140341540c0c0d1282c2c9420000702481c100100714080001c0310f4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 800480962 1250 800479712 800479763
    0x1d0903190908011a030c13020f0d0f050f060a03030c051912030f2f04080109140114040c0e060a03080d0605011d0f0126010312260601030b030a 63
    0x1040d005600c0c1c240c6040c04902d00001300d440083d8010018282045550100000990303c2c1402c207500c1c54007404000010491000600218803d0900c04240050001c0e4804211080102102c040004410034880c881c4caa070003c400a4980600d440e201804207810308610701051103e83c40842c440c11601d100c00d00401c41c0c8900d074901015a0248480860200d108083c1c8050396110021007542c50070040d290901c1b14841000c440701060311310f0a01307984604030350840f140840251680400300c103100015400a04c02e44d5184c0340c4a246c865030600341a100e13289108090b014650821030342c40b02055a6664420801c0001c551005a1550b40d6696100c2c60b8054440ca10800d4040389038101107170740384444032203225180b4201401c0302c001040c04200440b04030f1084000e00d82d035a69131501128450001c603a299028500495028a014040440c000c0160f140310503014100140d0312031841c40030a00c50390854103c05c3c24a0040f85050040c40003c1c1860089440207106440940051204800388503d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 800482212 1250 800480962 800480969
    0xe0615040f180548121f03030c0f060e0f030c07060e061e1c061511060f100503150901110f030c070602040306020a0c0213061d09031909 60
    0x8240000e4880c00008401801078907a1a8803070700903142040000c0810b01c1e50b400082412204910004d907400c0318801d0250700c000c462485400340e071810800b44014220407000380c080c0e4040500c40c12407441c0c03401040f0541c0301d1001403145500c801c452080c0866030b00003020010014041d0b400407006050210364079448110078015501891034005880781c090211441108405480641703410901500f40303810090101640f540d881c418803101c2c0e05a0b0411011800e840701014000032442d050000000c50004805021810048000e0a08100c0b1303001062142e0052a01c1e0030a03c180d1b1a0b0400350300c100b40564000680510072114a0a441240b140d01c25020b002c0c0403000300030000300300c0341385241807041c4543d828082800300081802c80d900000103102c00b034007030400141090345030790b140f40983c1d00c80d010400c00100441030744425403402d00c040c0c003507402c500c4008210513840c055507110399041c2c1100d00088560b080740000c051340000e0040316001e85044040c810729040030480544036510601 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 800483462 1250 800482212 800482259
    0x312060f1f0f020d09120204020c01060e0c0903010b040926090303070503090405180a08031015050d060509151302090306070207060905010f0e0402070f06021c050906010e0615040f 79
    0x104d07514003500801c810b1060703d135900c1d0110f01040c29502070001039442110714805079035170b030301000400004400420b0301034003601c40e13071990341e20007802003609493b946112940f02e41c0c0780c0614580040c00c0e41112141890452406200c4181d0b0030142d81110b000b505900364150000090710410001d02000404c01c3d44001c44041016131039215480c85c12415121000810f60711008060000c40ca035400038540c0b04035101e000c0383c11541c4402e080151028041a000d010035000318519007600b005000c0c4101401056903891a540b4005e414407114030902d505c0140140e00c504d048460a00c0c075a0103c44403110060111001410000307002035440d051481100c1c00074142e1480800d941d0b20948419071100750304d0707440c0f603491101103003000700030361161a0884900111105506c0003454500140000d151480c4201d0310000042c44070700180c46000f003599066400250051000c1d15200d021a41c2010054508514010035110700624a1240350040c0b030100111407800503a40509815000c04400034a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 800484712 1250 800483462 800483473
    0x81204090e010b0d030503041b0b03071b0201020d0e032409060f07091512060303020102090103061a18010909111804090b0c0306042003180312060f1f0f02 68
    0x1180502d088464000d09107503c442510080d802107445003010b150090300422250320940070700101800c000350300b503000307005245c1d01204004815801c1103481c1c03075840400554600c40600c07640000d4443c08840d48003401e00003200114101610100661000e5440200e0f13080b0108802d030100100042088032060820f1158400141e8442e1106221600a00661b02ea1101c4c0c0c40c03e11307403032145102c5081030301420000c4005e20365600d000c550144400850198000503a5030604000040548680d6000ba0350960002d40842199124204c1225400d44070721055080500790880102c600c1400d60344900750141c10012607071011400f060040041e507030b1032020210a00d20b40d105000a17602089005049220418000381a0040003001590300950060002840e5401d84041d40091034030800b02c01ca200c140442082103402101c18000e20401c00c3c00019410300a84c440c2201c200c0c800106005c0c01010031942d40c80382500d800c071008000041d48284240b1010301e41c040146008140d40582c001840354 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 800485962 1250 800484712 800484731
    0x80a050d021906020304030c0803041a0c090112020a1107090c02100b061801030f0c1e09081207060f0203070203070204050114010207030b040c0510081b032e08120409 73
    0x41c2801200d1102003110680b00c1a501d40800035000104107900f400700d00154000001e000b00029846148101b0280c40c2c0304004804074005400001c004020741c4904110801190380c00088041c01c0d0b03c040b100250351080303c0d80c42143c5246000c1c02c210050311514030041103c02003900814249041c0341e003240c60130b2508079524800d4940d1504990b41180c0c2c01c00c00b5262541d43d40300643c002c0101810045070b03040c0031070408412500c1852880001452540510741002e17860000c4130441000c40c9095448642410461900ca848a0010b20b2a01800040c84402c1286903040b600d0081700b00d400031500c81c900799102944a6204c5070f02280301e18504000410b0381d01a011101418030341c181c1c000c200c01411a80c81101c0030350701410555100c500384078001200c0d50343e4504401c07a4074142d581d8464038108030840188005400000c10f074180070a10410410800c508029200301301f06140803084544541c56854411407a60042241e0303024141610201c034607400700900c00c0310744001007000729400e03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 800487212 1250 800485962 800485967
    0x1c1e0905010c020f0103090b100501080609070e1c0206030a0e0c040e030d11040b04090204170a030c1e060609050702070f030c0e04080f16060c0806010906050f040e01080a050d 77
    0x90a02400340032403294041e00e4054204440342d050880303010706001410030250b844810804d14121204030f81100101814402540c1c0f0903500781c0c000340141c59806803404c2048001d401058503000300c40c052092204006810a158000c40c004540c01400d8243d80f8107103a80281d000d03100f038801400447c82005188007040c140b91165204100f03003180035500f0403035070a10340710203081011440715800744184008a214100c05008000910341d8000c016a00d40c6424804403003060303241d1490070aa0041c442200103c4d4215803c5105503901c406c5042c90000a010030540c1105940d00c00761280340707030190108000c020b0b54441801441c55808a0700724a50350100c080d101ba20500000304908480a410045142c0180c07500380c10034810006542080001541403030b50b60002145070503007070881c81011040c40080e20811402c1d000394230f8258070920f0b140002801d078030458810703541040070000701c4100d0089603100365005407050303507407428155070748000050f40d503443c8800c00c0c0e505000c0d010712000310310b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 800488462 1250 800487212 800487227
    0xf0f090303090607120b13051b071203090618113c0402120903030718230102010209030f030d0507030507090915092d06180504051c1e 59
    0x82d60000809407035640c0744089820040707800481c5900307030721a0f0f1042d20555620341801280b1101000001d154500384520030804d45040c60429100702c010003d000215125644e00a0b4028103403e000c81d07403503400c1c80d0a000410342e0301e03d0840c10006070b42c004810030070803d181c3c405007039013100d010003103640e05410240e1010400303c9280c05500351030121004503407170fa1045c2d10705003001400103040444052801160f59000c0307071144580d4000100b00300807a900818005110320448810040c01c0382417031513146100c5001c492002c0c1d2045804071880702a8401d4046582000003d419140e08243c0c1d451040e40d01d81005800c0719480b420040064242c0748a0f01c02d49210b484035030343d1aa6194900a400d00040ca81c2250301c2c10900d030010400f240281c0903000e845440340d0140700118000f40308420108024507401e25070701340941802810051140c2c0c0006424200c605d0040000311a2202c1c507044e031400e1118440300001e0b03642880d4101603640c0000c40f06032500704a4120b10300c0142d00c24011503192 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 800489712 1250 800488462 800488471
    0xc0d0503070512090c030d0504060909020a080c0328020901080a020a02070510030f020a0f0e10050343090f030c0306020714061005120102030c040e040309030b0f0f090303 75
    0x41c5050200c100302d509203c0da250741001c0824140c0314103c0341000840d042c1544402800042000000c0403c013442d80446040c0c0100b00c00c0717108609206031400010841c00003d4200e80b1448008000706400d4003000b006104d40784020050038401200110006020790000b040b01804204440001110b42c040d5008892201c80e20717038054080349050030100311035031b01b01102c03850030181e40c2c6042c00b0070340c03c061008025a18440d2500ea0308840b20b000c00400520094442a00807265030020400c5150007605507504403c82c04544408001c42800c80340300030080d0120b06842040703960240802506041111a504141e90794030340f4020f0310b800e4030200340d1481d44030041804500460800c040743c6582c1c05000303c24030600c10150386000f0500c0d6580b80607000d481c003200f0031880d2502000070b0301c1d107200c01604004038013001f94154600015080e850340582e2240c0c900021046d400542010310417182c0c1d101640d4080e07036610342c505050071400001001110b03d00c0082e0702d44c4000c1101c900c0000300341ea114 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 800490962 1250 800489712 800489717
    0x30305012c06090c2106210d081b3c070f02012606030d03110405060901020c0901030c1a070f20030a05010e0c010c03021207260c0d050307 61
    0x881d2103400621039048030041c80303184e50715003d00c2440580c1d01504140c4500c09075400e025001401d00300100902e48602c4814032081300c3d101e0fa120000740c400402e100007610f200b81840c181c2503440381304401c0f50000d40b40c440082d0440006604c5090a04103440013285485210038044540c000c240d14034803124a402c0038580e81d4010b21039400050110f08100207160302c10b00d0722141e62400c4512030301904501e080e40c541007200c00c00170008a800c0400154501c52a41c3c0b41c107200b182004043c40c0d449100700d0044a010700310000314940c81764000c108410820802900020003580d403030800c640d41d49a03034040e5035402c0d848580210180301c0b602060710000c0350820340969880807a41c0c2c03180084c2d0303200821035440d048100041c400341d075810312031104160b01410000c16050740b41d81d0668100341a8201d0316040c800c81c0c42c10070380820303030002e41005c440036401270302680c0300a541419150044420442510152840da0913008600b880000c0d01a00c604601185c140348401401507070310380003c4481800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 800492212 1250 800490962 800491049
    0xe0904060207030507020901030f120e0a0b0702060f161e0309051306180e07151707050f04030c170c0f04091e05010c020f0f0d270303030501 62
    0x454415401002c80034480d052640c5010f0940e400b080400c00c00340c1c0107442c02119850400203016020f1801ca41c1d10300c041c946501010040350000307041e4400c2d406002c10383e28000c1440030440d04c40c3e8003203403a19007030b10800c43e84840c080845d01d0300b10300752910b080710151102c02e1400380c882801c13500003035120b500d41c81d407120f1a4102028014500d0014501e91002c903180d030f10004001602103500ca582501d942408a40c5900348511a4036008030755101ca0f14103206131211a10b00c3e54401080d280b0980c02e0071040c42140c4034180200d41c0303401b4442c1c034042c0904000600008100d2940005000c0303580c04150705500c01c52031690b554840386200182d070f400c0801900c4ca85024501984100001d52041500701e504aa1078030501071055201da00031101a996141d0210390b00c1e804004007a500032411008102c02001d4034905512189000728820900009021141400c00c901d0b50000050310301201402100d583c83c20000e010348800c0c402e0284003584400a402480c0300b4425041406540b03001e40780 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 800493462 1250 800492212 800492221
    0x10030c05040e070c06050f0a240608090312070e01031409100e0109060908040f050a24030b1c140109020618180c040305011109091501021009030306080105070e09 71
    0x3040480060080f0b081000c03120031280000c5041c800c10b806803101610b5034190340380452506e011610011541a007000240d00301d10612150200300105880c07035494800f42507150424010f2a5014240014003400404800c100010f9070004015030404403d1f6400d06c140385010118481001060350030200701e80000300c110a8500300b90b000102e808032100000145d0b0030070b64546204650a0410498481c0d40c0050108406030b03a10b040d100c0a00760440700c904005142100c4410094500400c0c6840d0041c00a0282d142600a911450742551b02418818180c04040ea64100c0d621b60f04c00e00b200c0e0400a043d485074010340520079100c40340c0c0e002c0c03c01494590b002400808002c074074a580c0f17a028074110281821095180c01483c0142006030352140c940341589041402c2d2802c2180c0000c0400b001c0c03010300513542c1d410f9400344c0c0103b507200c1c010400051060040f17041038400e2021010803400c0c15440e804140e4568040c034216034000d8001c0100f038446640407202c1c48000d0070003c1e0300002c20030116 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 800494712 1250 800493462 800493479
    0x301080a02150c010e010504060e0d080f09120a050c060108010e070302210313030b0105011b020f0d0b31020108010e0a02130312080f250c1a0610030c0504 68
    0x801e020400c0d460940c1801c1d10f62500d18255004a5050702c1c13641d44440038003040250354020f00c2c418080300c2d400303404141c50200f0002d020f103030010007107150f50b00940b0204070049400d100c00c660080b445101a42e58068102d0050b02a40c05525004903911440b03000240420062160382281c01e0b150b0050b051081c515020000082400510400c1c81c1540d4248642090b004000030001e84002d40d500900030752541c00c000d01c009130164001418003d450800c03044001104034240300700707581103c5032102d0044000110b600c1840b41d000c02049801c0041c14000c0c050542482e2034078083c4500d1034626401104207241200090003007000f40400c4000005201c60501041d00641c4581008130050414040380c108008000712940306a401c245544151102a0b5200e084103a02c01c900c840084440c4c00e104003011080c1071028a42c00d4031002d0b1400c0c425240b449081c0e5464245d820480080c0754940e07004010a42c10b0041c0c900511500c403031400d42ca03515000340200760051096841c3c0c58202445c041c4007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 800495962 1250 800494712 800494729
    0xb250f02010608070f18020c0325051e101803030c180905070f0206090703020f041805010209090f07020a03140904150905060a0b09100c080711150301080a02 69
    0x45815552111000314440704108612002841d0424481d80c44034030b0850034a01e010801d081d40c0c400140100040100c0c01b000104a80f4a2071100c1480039030054420840c820900203000c00a11074040d94060300c00e1800f14141d0b0990710381224007a502403000c1c02e00248201d07006000320b40229914000d5181c003007806940300c9035610a007810000d81c0c1510440035032800108a4200980740d070344d1501440542544445000034010190006054a040600320507a403000c10303100003445034071821040482500d85800481c3d045039942d50a20f0388c10301d0f52911502039003010350258003444840c000030f50801d0b4003d103200e02900031500074080656040d10211200c40c02c034003400241000070411501c05031158450400742c0b003030b4890000703d044e05280e80502944d2024007014841d01ca641c03828010000e000080341d503c10303003c035080b4000182c0d101013524042c09464010749008400715407101800458404008405811508602c1d10456030082031000c2c0020301070140543d2000c0030034001410841e00c0e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 800497212 1250 800495962 800495987
    0x60609141503040305030f1b071209090906022206080a0c0228020102010c0f20070302031c0806041e2c011401080d020c1323040b25 58
    0x41001e0307803046070008a0341c1d1003900c044000031300c00001c00c4051305404600d281c00000c101040319946804002401aa002c0c1c1c10014120740107070084000300901410b008001030080150070700c41c0d18058244030000703400440c0c029506400004480042e64940c124001c291403541d118548162038032040040105030000070320043d13108020015554a540c100000204103803002d0010004140d440020b080d0303031402840e24148103118454070803407900210041034503148150500c46503107403404154a0304040764000303034250041c040ca0780d6542d00c01c080d010200352031548441c03000e40c4400c070030b00044402c0410055043c400312411240c0704c440d15088040c0c0300d400004200c0088003410701c256a20031005500240d0b60b0740d074001321303074040c0308401d400703401042e001020b402e00503020000603480b82003120b2441c0c440d4001c1201c42580f0b40c0640d01042c401c02c914020b040c1d5001045c0811201144142c07001c0d030b100300481000807103000c48840504555101d00c81074114030b540008090300d120b0400d80e0b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 800498462 1250 800497212 800497219
    0x8010e0106050f071704260d140a17180f06090a03050d1d0c0f0d02060702040513060e15090a0c030204020d110c0c15180d060603060c030606021006060914 68
    0x4800c405c80c01400f405003002e8407410340440e0725858a503003940107052a1079a5507a00d60003503e03074400041c4d00501e42c0424841d2400000d40d889400042c01ca86031080b02e203152001046070750500c00034280c010303401203641490508880200074010191aa180b40c1102c2e502241d60140001000092164016041890420002003400135810301c400d0043c01c82c500c1c844000b64008003060714285010000e1507841402511000110405900031850038801c040002c0d01039078583c004168507140c0503a005400039006002040200c4031161815102c6c607098110700c0c40c1c4020741c008a001850041140f0750705981c0305000c013200700c2c90b560030b103c00f94100d86100300c6600d99401000c0d01004241006201c500710440142210aa0180c01c022101c801d0b080d803612940d0041c03080c00c90700320500201680918046480714001045807a04002034040b50300002e0425003440030b141041b40c4c154200c6402d690380c1e80c007514500443c0440010845000d4428040000d0400208102c61090916440c1d18030390b018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 800499712 1250 800498462 800498483
    0x20a09170c041a1f0e0406230a0b13030c051005030f0603011506030902150705100f0f02071a0a1509020304060b09010e0103030908030405090a0e0114070e0108010e0106050f07 77
    0x2500004c40254080034244031135182c49454000190b8000030b18042c0c1c0104072410003400781440e40303100140080814000300da0f540c021819031960b55992052005010440c004c03559041442c1c26482c100d103107407204541e00e00407040042001d141c600c4821080400c907907101c0382103585642d0059500d0340080c01c616055503a8280d240b0004c070520380c12102401d41030300d01280281d4184103000b947d0072000030441c4080800d0001c900054000b0418480e5400c04d403202080f600032215a000040c458001500380c0c41d4070000340501000b80300d0100030000c550384c3c14030741a585d94100b42081a5803418121810302c021803007040c00349000d150f015580150180750001115602380303000c01c0101c1020303000103400c0800030b0010010143c1c014044005003c5130f4000c1d5050626240c042440b440e005000c03e0103071030b101c0e0341040b142c4900b544840804190706100a070541003500000e070008584078502400241c44100200352803601c00f045a0407580c00e039543e5498025a22080e0203690048502201c43c200d10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 800500962 1250 800499712 800499761
    0x3030c0809121e100c09052b201009150905040203070305220210030c110109080d0c020c030c010818100f06060c032001060f0801020a09170c04 63
    0x81251803030a20300c0c07000c00c000d01c000f001d056510788400e250880900c0350400014179007142c0e00c4002d02044400c180c40c3c0820103001005101e100e001d1202c0085010080b805010041c4588411440c103801110706900740440d056909212943e403000340180c02003103001100b002005010400080d1803001c518013a21480d45400004d0300380e92050f240000065291070601c804158003000840f10100901006017002340740d5408150640700c13940c0402c080c10750358404030389064081c4071300442d0011150020080c404240ca0104034640116141a4490749084034060406000282d20041d485000f401042941110300044544030300003088040c980b150286584000036041040c9080141d20761f0000c102c041209680c00201c030200d034015420000419484000302c0d4020041c0c80410b08005008810003824105403405001d41d94400c0c04004a07055002492980642c00341c205441d450f628080c482c3e03954900b400e4080e805c083d80d144c064101c01c0d443d541074586030b40b00344101c819031601411a50320 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 800502212 1250 800500962 800500999
    0x601020c041104030b0903031315021c050114240f07140721080d27030c0c0f2706121a01090c020a0f140610090507050403030c0809 58
    0x10400c0307000c400d50b601040038000c10032107012043c0e000040c40010360031460103580300d618540d6044009000d4a035400060306a000c203030b40440e4404070301c20a00f1500001035040326401404240b160213035070410b11251001038075181c0580c0e50307505883e82c0002104100709412480c1a40841c0051900c94420000500003850500070f1403605800d840103801500e25094641148491511a0310070701d00002c08004001401704058640c0e44605c240e00003540d4100196440c1e00e440d00c1d46408414150141d210420543d000e01614030381441607c0250039140da440c01e81e40c650304030340108003201d06040e54050702103001e100c070240c01010582c0c000c02e0540e074620740151045000d000c00e031010303000800140d10384164030003404e004000c030354410054501040030003503c51200e000c0080024440105000500907860401c5001c0f255040035120303203040c048110881f6050724420300071800d09060020344082d0164007501c3c200ca4140c1c0b2000440c00190f0b40f090210780c0001d188547c046c081c0d0a0440c0c910b02e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 800503462 1250 800502212 800502221
    0xe0705041d060109091e0c0314010e1624140d0605091e072003040608010312080f01050402070f0606090f060e1b032208040501080105090403170601020c04 68
    0x401e10007550710041c0c074840d0040c0c10501c058016840c601e04141d04d050010700f44554141105000c0d403070803c00d061052031700c0101c010141e0310140411603101529012514107606c08855200142c0403141d10300e64214818408900520510401ca01594541100c0d0f4045440312480c11603035103400803600c500344041c6043c41d00240903039214999513140911450070300003604c0303400081407030690406003010703c05000c0807a0000c0100b0100103c2860b0a03489107220301e8070901d0a0300c0c100c00e50f500c03691501401007004500344010396040350081c60400910b400f84502d140286542c044c0f401c0031f0380c00d11081c0300195000c5101100c00311980d560660101d8403c0c4100006407103101004250001d28503020001d9803003036080789600311114001d110f030400710307002010700d0000c6000c2099165503031a500101c0c1403025a0704055504203c04180007000300c0d0b00010720660b1801d807030300c14250344c81c0d02c00d00c0328001301154000d01094515103419600c000f21980c1710b03802101441114140c031b01c07403c081810b49 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 800504712 1250 800503462 800503481
    0x1b061902031009110d061e090209130509010c26072609010b01080a1404020906010c0c030c030203120309101d07120c0603020c102705061902090d060e070504 69
    0x3000c0201da00a00d045032030241b500101a0706050142c3c50303806415208035403615104011401d6070015000019440e0041d014440ca142880200b10f00e240160000d030182401003117900000f1400c040401c210001024101008030803440030a402e552030240c00d85003112a611120152121024290114041c001d91284581a890b0012810405880001d002d80c0d0000d070942244508014454614506c00080945d100f0f80488030312085844000c0140d442c5080f4071310240481c500c216001c0140b00c41115440102c074425404c882010340d0002e01b01000f07000a60b4000c2c0e01d80c000c00030147e0203248030f40004402410100b51450003194103d101884c16a050784005d420100300303040030003440b680da03464100801040c14154a85a480101d25855030080415520110b55a966008a03100500c0200b084031985100401c0000010300340340342e4076a4101c1c3c01803051140c0c0c2e03461044d08810b03030098851010008c2c0c02d0b054000e29595503100580311103103000e090303407056000004691b0303a14007540d00340 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 800505962 1250 800504712 800504741
    0xc0f030c12020315010f1d04020906121303020c0904020918010e030a201605011b240b0f030d050f130303090509011e05120a15021b061902031009 64
    0x201310000001611041c503d03200001407042c0b076000484a118070b0303200e8801501d800c030f90042ea500c1541e0f0028505005442c21b04241c000e02c1c10400003101310300150081d00364003a070203c1c0c056226803001c11860f2502103030300a4000012001190030340040e2481e1900c403402c4e0f00c1c00030890303920074400689190801c1100d48005808040030300380322807038140d03843c08414810018004c4400f1848242e2001c2020b4800d26041040a00103200d016400401c1041301c140c0c0400c041c180b20a1303152480b0010904150042e116500d800034940442c81c0c0100d40c0c032a800c401501034a8075560980040d20260002445503200700750801007541c1c45920101c040700590300c02c4e01c904626905110500044000c160002940f07050300f508a1605140c2150803841250400c44004450180300c0005a06181c00b081d0028010400e81850000c1a011034000c0c0004007000c110314140e0030301004030103546d49402e50702600e24031061515400310041039001903a00260b0103407880840c1d0b03a94042101180d1460604259 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 800507212 1250 800505962 800505991
    0x30a060f060f0f0f060c0f05010c02100605120a020112090212070602060708010b190c0b0709090506180414010b1906020709050c12101d04050d02010c0f030c120203 72
    0x2201d030b039000068010b84680d0302c0d50582c0508007030f01c105002034903009040a0010030540802040f02c032540209100d940f1100a101c030b800d03103030b0f0040e5076816002d040c10762a070f04145000c1058101300740307101440c01614004203440d40c959001940c81030740c50001100225200c40e50302015072038500130042d0303104044005001c0c15180241c001d05100d4003509c41d0007080758400040062040c88801c0c1d400201d510107100b1181c9110718015580ca031500100103099080c80c03020030603d039803c00e955a040361a001302c1800f441d5541e40801942c650380b02402c074203540203100820042051091881c070900f440c917000250034514140000c581c1d4551112903501c41c081f160007403100700d40c1401a8401041c84220600082c1401c09081003a40105a903448141401400040050000e8031691006200802c0c2c0c07540728170001c000f10140100c04440039500780c46400801300b24984140f01d0890010501e81d10035041d90300000c02117024140c040740036010864007841001000d2000d100541c01070720001c0a049 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 800508462 1250 800507212 800507219
    0x70915020a1b0303080103030e0103060e0708060a0e0c040e04020f121f090f02220f1d0d1e0e04050c0304021207030201050307030f02040b04060e0901090504051506030a060f06 77
    0x6070041900304881a02c00c1e04100e003000002e0300542054191307903042c142109070343c60001c0100d00400b404e500c004000c940001c1801a490303007003902e050080409a6904540301d8890075100040281614004031180c41000708010543d804600300390071620080c80c403c000340c290400981d54141c40b000b400c505801c03072420440c0181210455440e100d0100c20140028191500d811700f1103e03116002078010080c1204815201c58514034806180044540c00c0200f540c90007441e03c0140603448860105040c07000b02103454890000d0402c461603004d5403151034400b41071006000040002034860240302005142d01a6907a0382c0c041c461180d215101c0c0d1f1904c915082c0104a0861103076604285a60005c207000e01c00750340d2180c00c40b68081014200415034401564030034000f4440e907480039040000128010501c154809094166102c045800c610fa80c0d13211000307001103030000c3c0ca00421035408142c0380c410f0142c90f125010303807020004060b00c022140315141ca00a40d41d100c480f1a50265842d0f1051 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 800509712 1250 800508462 800508473
    0x1140d051212100303020a080705030c1e0d05040e04030e01140d1a09040308040206130807120615082121010e0c0c0a0b040507050a091a010e0303030a05070915020a 72
    0x101d030b100f034400f00070840310313851a00d0207911070890000c080d104c80d500107550700a1081c204100c07a8a210300504942200c83d000c50040040b81c40e243c400c0d2030600032140304454462194041d203082d01d2031900580300640760b5903030617100c1181c0741886e08d040c000810150407030756210f103020b40300c0c1800c55100480d2105e4032100c81c034490300c6141041485014000180008a5803060103075900507419500b03d55500700c003032030020003001a42c3c440385040c4180c003000710f032040300f0a21218405100340800e01503010050155668001107014107000c0790301034030301c1e082d04015000c0041c84d030b40b908000c032620700448400c990382c02c445c0526088803120030400040291a80c20611280e000c83c540506a081200031294152500030a100150407052900049070370704c9003d000440c0209002402d0504082e91400f81e00090148140025500043d103014441d85502505021b810384100030050b51541c0d03a503102310b400412001e41510100100c0300030120b07421442d00a12120462140c0040005481c0761030305 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 800510962 1250 800509712 800509747
    0x25110712051c1e1b02040e030f0408010906140f0c0f0d1b1706010c0f0503120405070801050106081b130302030d020705090a1119020a0b0a05190504080301140d0512 72
    0x203220800192001c0d010300c40b004138901d400030700d0341101c0c0803d26405051072540303140515400c10010385000500081c40c007605501240f486403050505000194003062801c981607000c450b03152100344041c00140d40a0140c0c0014007903102c0304150281018000f0012404841c012a1844140800c0700503103c0c50742d41088015a0080150880040c1d82c40e02c2000200248203008004054008003010b410402c0000c1c800c0d103407840e0303d00c10280001d240a09000d99112010302c116441540380c80c002040d004e200300f40c0c1c18450601030b460201003469206d081c104580c01313400020f903074444000010005940034820b10024900c41c5d4010300d0128108000c00480501c044c04d46404145003202d400034800410701070712080f0b84803003521601c0100303881c016800d1070b690f1400206900d0410b0104044040c9651005010f6102c11800c1c909130031044092000301c40069501929a40d01480101302d0081403400145c0e041c44050040784a48819a03034446c41d005025401e901911400701c3c00b28801c1040b600d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 800512212 1250 800510962 800511017
    0xd0c0816032d020d05090409050118200d020607030c050703080d0b0f03370b070311090d1211032a2e02090925110712051c 54
    0x342e003420b802001954520b01182000c05008011510000544c1c407030380316254260300880240110b8040401d2000d20b1681f1381400c80d0313288140c1c20800084112814510340300200982101011741d0700790200141c81e04484c5045040002100d03a4200155041c04034100039441441903584030702c21020410305881c25400e07298007800f0201e200445941c2d0008101800145051240c4d5110030441c2007500c55220750300140c3c800712034486500c0100201913070071500c1082c01740d408111070483d40d0b5500d400c91241000451b401806100c0317201c00314801d0390700d40303803020680d040585c074010a0040307680c00d581080020007104104059100081c00c884c0715040124202c1001400c445011001030300f140541c0c02c4001074640451200c003651140190341140c02411000340101c80c1481c03e403004800380110003160990403809500081d645034040c0721209110f55414014203049414286c0f80d0016000707040c020358603482100d0351041d40c140b8000940b09428003568807020319045601703100344104c281c200c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 800513462 1250 800512212 800512277
    0x40e2e0b13090501111803060f01060c02040506011b20060a02150c0f070b190b0a0605070602090d03080f0903031e100f060c110409050d0c081603 64
    0x15010140c0799150040c10310382107112000081d4800290404500502e1880300312484008005400007910b00070081c1c034080540102d040320415511045282c2d4108028825140482c10312407462005103050380082d98408410714010f54044041c080c0c500c01b1401e10b600c295010104465500742e200ea000008480241058620b24605009490001d6482e0f00300100b0420200c0203030003060852440008031545c1c0c00c1845221512403426060100c000355041e100030b800c2e501414030490f0025601d00907a001040f00a107003120261800c8400e84040c5d03c020011074030346501700284562560b0320b43c4141204c40c003940d50043d4a141c41c04451405e280094502541d6900c04d000700b00e104a120021811540340e83c100346015510703500e89908510341307140c0180365a0b0418001c00321f43c05a020001500203401140d0101c80b0618100c00c1c8001c8a0301e0703680240007600b0000c41c03104590b018010300703190903204d134494500d48008071444403048103240e102100000d04081150801221451401130ba4400c000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 800514712 1250 800513462 800513471
    0xe0d05040f1a250209010b1207020703050c0d02010c0812060901060518010e01112b0c2001140703020109060c030212180f010f090309170a11040e2e 65
    0x201c0c840b50260154290344030500944610404402c041e04541e08203035a4050200c0205503140c03402108103400c691100010369824000040c0000c1c800140081102e070484e014203035440c8201d003031104200121038264188601c8035810000190120000c20f2001070300040e80d021400c00c5001c00c201020f040c2c5c422010490280f180c0e502cae442425031008143c442c2424030303000f12009000186c4044600f10481c0c00c01d070007546010f000e03140711080c04050a0780080b070b154a0846003104262015642c41d0303005454800c5400301801a0100ca11400088501c1414150030501a811140c14542d10a040860050351554440010410503005452400506003000d42c104240c81c0704200e6040c0c001854942c0010b0810388025003a5130900c085a8001d0041000344a13040d082c0080c013003d008050001c4001854007100098280790840c10713000f207070204a015100920607078503140c1900100d0004a40c0c840da4039500014104010048a07106200c070004213024414018164202120800484a55075040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 800515962 1250 800514712 800514749
    0x70506070c080d152112050f0d111b0a050c09010302100c030e040c18050103050115050d060b1c060b0309030403231f0c0f08010302040207060e0d05040f 67
    0x110025914002c584180004450340c25210352130840c2c0d038951050a19580c04c401c003480c0850401c400f000594001c00c2107824548001d40110b42034829a42c0c00d048006051082800088458002d4400300c2c0048110509001c0160f0384035140303200c408040b24490f03120070404410030030705100e000556138088641d000c03550302d150049000d1468980d80a0108882e149043c0100b5018621003807018001900400c40d10100100151010b0074008510703c00791683d07680000c0941c8603001c2c46041c2da00241c0e0651446001000a5800c1d400c4251a901420f44651000c1075580300b5002410102c91403075103a032080c08014200104882d01a00600071016040042204045000049804882d409001c42c520100243e81451040e0080031104000b130041c0100b000400c0b14007000d82c0c0000001000402c024801e01c042a241c9203003502024000c9410b00c401040585055030142c034489000700030100c5c001c02114419400c011186c0000d2001c0340000c02c0c180010424852944094040700035410203484a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 800517212 1250 800515962 800515973
    0x90c04030803041703090a0201090509070c0b040f15050610021c0e040e01060f0302120313031101021e01270b0c071b180b01080412052b02070506070c 66
    0x8500015110400c0040810f00700444000c2074500300d030003903a1040d12801e008a1543c0c0b1000d94207010f03400169140f502052074a00302800380c0c0248003940720320101e41c0c801e540d4844404401072040c2d03424404850303940d0114043c4245401001b050800014607440c2c07400c10403400740318030540f02c011980004684010b401c8154107040496002e810f118a08070b814000180c0a030040c43e8130180203509000e0b000850306035240e40030b81a20701c01c40d1211064810031400b10764901580d019400c2c0c61010780c20400100d03d041101c0c1d80f0f84030061040d00d0300040c00b0812a41140151500418180c4d52545164002d000b1044040b06104112020f0302d10034450362900e400f24140500007680101001a00c1c0e8200584c042c0c00c02d84000804000880003641c500c45003041c148020881e049643c10560080c0b103540c420301446214652001e1601c0550040320b10440d2160411000c4011120840000840e96000c608100c0c09600c0154409681c9100d20b141c81c40c24004041c1600090140c070034580e90002d030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 800518462 1250 800517212 800517217
    0x7030c080402180c04031502180d080f030c07050105150906031f18020d06090201031518090302010204080111031b0c030301181e05090d1407110a1e0f05090c 69
    0x2143c2d001800e058a03036080652491046600080400d88803420070304603901941c000e0415081024010700081445000780a0340c4040901c004207280c02c1000448110a00d01000e180c000d4181d04031103090124650310507007181d50a403403a900c0322014035200c0d4403920302684c2156000105401401d103c50a0070a254900c1d801c036610050300d0380c0c99920106814503070f80041d030303940c80e00140203103044040c604200c8000c0003c540b040e4002030400c02e001c50100c0070145404101e43e0a0120700c0c042010703141e14040101822003048045540812000548140074000c61442c0443c503010aa501e05041c1e00c44000e14410007606004242c080c44030315841031001c001d0305d044816290800c000e2240c00c1c0c0150004284040d040743c021340602032550200b00c81588803500c200c007a8030448140f44d40044050300c84100614000b22090320410100002680d0704480719003d040c00340000103180c0e11469000390300e8000d080078804c400503c00301040040040080040206000d4070810207900f0442807041c92171 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 800519712 1250 800518462 800518489
    0x608011a10050a0804110907111603080a0507060b060301140910030f0b2509030201300b0d050607030b2d1017040c06030e011a221407030c080402 64
    0x2d10040060700340051800b41d803003d50307002441c1030700529140c00080e00409101901405a02c81e820ac94802114101850000e5030703003008003541840704000c02180c42d075101c40011190281c43d52202c84c810b44400300a5400b0700b0001c5021500b0904900c180004440010303c10074600800140810102e60b0111203903207499003104180589aa07200041005030b10303400261059103079140b103041e540690008410003920703c01d99481c0c4012089540707a1242e038640c0da120421020034088403117242c0a09600417160301201070105041007003e520342a061060440e20580841e84641c1070240a140c029403800484861001a81440e240309521003168011402003034081c5090b0111000124095444440c0310504180c591540d49011b04d8500e00000a61003654086820b284140d0341240b018000c0943c038410000c48107107115503113410001c1c04c201203481c01802c00c1407603154854a05040c02828020801d03e00b03503600754140814018201ca030000901010029800103010040e41c0300f102c44d80d00c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 800520962 1250 800519712 800519717
    0xf07030f0920191514040303020d110d020d030b040b03030301090504110907020303011a07020405040312050a021606020a030e0d080411060a020613170a200a080406050d0605040608011a10050a 84
    0x6414061041c1e400344c003145c00054104001060002c1010b81c0011030015545031980c13200010302c030701000650f48403800d2806c6805600110003901009120358440b0500c10741c0144040340501029021908540c800c0e000078980b87d44070800c20080c010f02400c11020311500b030346c0e426000e01c0c110b8002034607808180144080e03c81d9080039100100010010b980c00399400420400c41401d00340f4010300402091007596000b5800c050005030118800d10a46075070440414142e84000b02943d546c00081d4042c0c900401850307a14107100105c14030401c9613802006140d220440785003441d00300100024184040b00740724100030807072419695408a0b07003980007000b82c4e00d05541640b56240c641040002c004040726580404902901d0f06a0312002000d03a82440c5503d182010040d60314164640b4050b00000c3c00211003004100710148c41803004142d1044250000141d044c1c4920006080e50000c1d448a903860b0b460768168403154020040c1c881c001c8004030340c40015280105409040e034021040c1303010a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 800522212 1250 800520962 800520989
    0x90c120705030d0c0c030b15060d020c2802090604022b0b060319090606050913200315090309030a230105010f05040903090b0309030301081c02060f07030f092019 71
    0x2140d0b41c2340c030481c611000100304607211a580c0c41c04400942050480c40c2c4180b003a402c0305c0c1403940301d02c4000c103155403c4404200341154180c0138004554006403030035811641c00c000007107c512071000d1150740d030007103042503021154001c0d01c40c0c8143c0e40c0c0c1211980c8903007420800c0c481c0c02e805c4021903511510700044045002d14860402000420703040d40310a4100c5800000c00c100c02c424002107204891207280e20080250592041410700800c04140d170350103906c1a01c801550000300c941c42d41e800500c00d402c4900d0080d1301c1b0301203030902c2d45a5204480751081d84180b0348100030441c3c41d4401d139040000c000c000941c50241415000c494078410103000d41d41d140540070906101d0f80c45203014000c4141010360700d06241c07024542d0396100348900d02d0140151391011000d0100300000030314440c00c6074010901c58440300420031114401801d00020b140e40d07038042e074100716458060a0002c40c0264518003080380ea400c80c41c412140b01c1d20f50b2034425560250031510400030740c2c01907001d0781c01500342c61070b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 800523462 1250 800522212 800522221
    0x11d01020f0901200a050607170c1206030a0f0804061d2b08340302030316030e0d0201140105150d0b0604031703040c050d0201080f090c120705030d0c0c030b 69
    0x80281c0f00981300c1d1605024400807001400000180940244016a00c2a4812200406810f450103040d43e94a01d440d4041107000103203d00c1200d510380001008060303403d2802140c1d1000010041c46d00e0480d2490400b250802003280c0086e02241318140e402803003010014071000140c8810340140142d04d81c40c0d1200c1071204090200b9040c0401540d100034803035130754000308544c2d10000044112001b00c00380c0c0d9014206100351211100648103515070029402c40d01e0f101804907120310b46090140801d56103050203403555408000002d06184240c00024090394219070401d0103400580015003e2013604ca13800340300700304000c211101c110711580001111492030001440031b04c201c1d4406450020844192151099480021030042d440340c002c103625165510203001500c1c48414010740030030741640000c0c0d0100182022030b5405881c000644013400301c0f00c40003541c05443c250001480384d00c84102400796003000c001c0c0503201e040c1400c1c0110300e00f1086c0d81d0000e010505000003460889401e0205 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 800524712 1250 800523462 800523497
    0x110a03080c1c060f08010b0d0b0603120301030f050c0a051518030d0906090e0606030a0b1305070e01091e1a0c0109061415090106050c030912011d01020f0901 69
    0x48400700c20040360021011041128040030f0030090042400000e00c200c80007880708014403c0d0010801d0207090440803410b0b64645408940c40240745036054050030755100701c120540320086001c1c521600a0201124050170490300e0445403240c25405046196014400c42d03580010000c80304401030a0f69a6481c1c180f00c210b4141e1007168141c94045c0f05e00201d400e0140e420803045402d440c01680d5000311195244001c0407105000d603501d0b81c12078010404607403400c0305c5800090750300c10042e100340031000290030150304403082110303182300088803400104604d692008980000344941c1c4221304080c0d40c54511040e941071140b00369000200103070210510066580c06031005d84848400030000302d4020b08052000d46032101c084e14820b1641c0d0700140b00004bd642c4071111506000c0c00e00d10b026800d21000342c4055100c2c500004580c4018000748002d5510303403401c58a843c1841d000400d00c00c0e400c58032041c0741d400ca10034059559006109061900504005a400441007460100132294945021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 800525962 1250 800524712 800524717
    0x50604090f090605040b2505070f1b0b0c012d020901090308030a05071e090e0a14160e0909061f380c03030103020d020a1d07020c01110a03080c 63
    0x820080c04d0400b004244a80350100c280718072003044480840c0403200d0101d40010040d101b42c3d401141d42030010f180801c0350042883e189030302c250b80503c40c202d01710003505c00100d4154000c0c94032400002d400a050308081c040c803d00754008107880400c040c00d150200311780e072081200280580d0340c0443c585c3c8080e0310030380078a4020340d00b20030755595078108011548058001241c034440803e0b4480c1d50900c0240e130046090110320515590b02100300c1c00d0821369907031058080c005401807521500300c044031852000744280110441034030090042211040584004031001c142c51140344070704100107030840d0105400b0340c45103030401141c1d000b40d4011131500461551307400a40d215885985440090580100c601c1c034440000e8100800d082110818a400c5124001c0c0840c111f0304184010801070611940101f80320f4401006581c2e0301e900d407190312300307200301700341020b0001100c8609001c0c29940500c440c1d80f8220080c030b01000720a92038600d41d07a981c840c07144004c0422030000d0008110391441e10a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 800527212 1250 800525962 800525981
    0x203120408030901090f0509042a18060b0f3004060b011d10081504020a021501052403060409060c090519140904140a06140a06050604090f 61
    0x19140d4031241ca94010300d9494001201441c0492840000403c8001d1102c0003882190740080c04100c181c2e80d81e645010381911a40311a1101001c1c080448100718010040d52000e80f000e41140e4482c1d01180182100390342d12075010b403c84090410088240c4100082201c0610200d000401440d489550101040101030820f542c4a44c42e81d9007440104480c6400c03521640909980c2c0701e280c0c22024000c602c055010f80200c40e444140d4011a00f41a8007a01c006a4407202ca40d20301c403400f41c0340b50f0216040e80d010b82030300c6005800801c0d8a420003000f00d007000b409008250341d1000d02d00e82d810f050009100203446c0d0a0349040d0048002841503079540c00090250380c0c8510148428074805602900020f22401828495203642003c000790159440c03070041110316001b1010580b104e0340e010322042c0c00300980b0948502c0c81c80340030005409030070403035a0b015034070500f000910121141d941c00e9000402a101e40910741c24080b0800a07941c91109440c20340702c00f90700008121040b42c1018005054141 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 800528462 1250 800527212 800527243
    0x1d0306070507050f151f050108062b0503040305060a02090303070b1f0f051201020c060403030b0114030405062202130c0504030501230903160b1026070803090109120203 74
    0x1504030a0240510f817055008a040b000d500d003c25a90403146e904039269400b400c2e0020322000300043c49854070341d95460701001041025010381c6c000f40105131049840a10546090740005410000c0003405c02c8420b80c04205a00708504042c520701c000381d2644220b103c00f4040e402414003040c10003071524a14124200e9220b03061210540d0740d903503820400c24500c20580300e2454920b00c030b01c0c80b90060084888000c02c800281c2543d98580c0c0c0d00f40c000b400c1c82c005083c1040783c603189554460203203c00450255026400405070361911004003a01c000d01d880703c4490480c11000c40c000141c881510340041031400300740104181f0310911013180c050181e5170003d0565800e0541d503114014200b025035200429941c20b888890745c2e0555103039a203205d052500d4048408402c44ca001080c101500181c00070300d0b070840300c41003a40c1c03003100c000c03803000108000c80b041ea07000002401000c420400b51000304100009141020071000020f00700c42001d2040e6008090945074a9007156814000d03040d0284400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 800529712 1250 800528462 800528473
    0x806090a0f0509010621030903020909070509040b2d18120d051603050903070807230c0f010306060e13020904110d0501120f02040207060902090c09011d0306070507050f 74
    0x1c0c407807501030140c0344a004000054844411078940c403544441d060140c00d51100002140f2710350034041d4044008180c883c05026819011806a5403803c4013070155000380d950a019060505402c01c020034035200006400c0c015010001070b1407501111603502481000b00c01f0307810312805161134200700d040c0d4481c0052901c00101c007401200a0b61005021b82d1b0884c0e503580207120101c6003135003280c105444182841d44103102103400106240020031640c0e2140c000030b8502c03440c2d274217040c00380040c80c0c2001c101c50b0083c0020700d2440c00c24501d00c00c0581801d203014042c00c1c1c500540034116120b078503001801007035006042c4401400507011a114444044e00c00c101101224080740502d400150f095404a030800d800003503c0d40c84501d5084010340c0180300722500c4000c641c01c00c00258440c8800b124002c0c0c0791403940000da07640b800d516103d004000c960310fa40e15801e0000520305429100c624180c074180601a0fa495100060941d5010410382400c80d601c0405080080c9403440010010f1058440c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 800530962 1250 800529712 800529721
    0x209210114070c11030721030c02060412030305090133080d050909071d09130212060a0b1f0c020d150f0605010201181b0806040609030e01020d0806090a0f05 69
    0x3c02c104107006802144441600480c1408060703d5142c2c92003030391501c104160400494171340b01808040c105101713080081102d11640d0100350030b0f030020f03801261420702c021f0b5060207058144c00346a41c40994074008000781030140d130000c844d144408054403001c030714482c1d107038040b5000d080e07101000e014440300b155014070b2581d1005046a101108080c00b5139018800704507050300550f091144840c02210459800d0419000c0c04801f8000170036580000c0f800f80f01800c0540ca0301c91010030000042800380c085803509000c1c60301580d01420341036000d098800300c400107481c00080211259403482c0b81460a54140c3c0c00041c001442d51100640a03403c404184000200742d948102c0c1c04021022051200d69600c4005a088407010440c484038080c0d19641d803030018020202e100c41d18400b90f0740359019640c032000454500007044404480c0a9641e050300c600703040d0849100d40341c03020700348001c0c52021046000145240380c060904da00800001012411030800c1d50018801e4101200b8100300b503240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 800532212 1250 800530962 800530967
    0xa060204090b060703020d0f27030b010b07050601050409080c060f010305120408030d05070908012301080c13020c0a0f0f0c06050f1c2c10020921011407 67
    0x10034420041c5041c0390440704903140c1010001d481a0b40d8050700540070a5440800a4038100140c00c5007804102c5d4440414400f403c64080c0307045460030307400040c0c83d02810f51600c0d442014040c0c114100480f028000d01e0001000000c00c28150b40301500e02040d00d0185240802c01d41c0542c04003d0418041c040802510105d2502824100e90140f001c840505162800c41205482203000e00002600208902e1043c88020b411640c2c0090403440c02c000300d5075071041d0040c21205000300d402074424a00b164085a000855504c030b0141102601030b003041c1c00c1c1d4000180030714100c26060080a0340206150f205101c041c00f521024682010160401070700b64584511503102490f4112480081d80e600416080c0c400d2040c4c9009281c52806c03289001080444540e00d8800402c812842c01d48a0140346011034032041c200f20090400d284511a035245a2032050030400d0410102107910b10502030040c6595544400814450300007030728200008100440e80c0c09400390140c5151700340c154a05011207181d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 800533462 1250 800532212 800532217
    0x1b030c080a120e01080f100812040515041508130c061e020a0b010b0904112d09130207060b041103060a050d0c1e2705090a03080411120a0602 62
    0x5205103000c0c020311502c85001c0d294465690b801d00c0c0040d201c20001140d000350452003980100d00b0f03122103050740e69680d807140d1400b040842071400320107022804220500b400c41c403c42d030a6013102a0350741443d04256161100120300c2c0504402c1040d20030100b00d800c6101c180702c00300d10343c015120400d410b46078000580700b41c403400140302a5136400d41909170054400300c0c2d02d243d026031101c0c0c00d05490740791544165240d040380c2031595105c0d80d2220000316800c05407000f007480994001985d4008a000e030704030300c441c04c616001c5c43d0b1040b4080110070350a6650065884881c410840016201c07410b5041a0008004020780c4d0364010380340c00c0c200c1100c07a07000000f80d485240219682c0700f5407030b110000c0c0083c2410945005050040e85501404010100030000106140c0e6004080f502903442c070520780d410016450a0205140716601110369203054012603610489010050601c0e41a50b6030040200000510242803c10103105203106540c0c0d00380c0c10401110b45108032141070515091070002507 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 800534712 1250 800533462 800533483
    0x161b0f15021309050c0d0509060601090e0f0a0c12020c150a11040e2518270b030708011a040509060c182202030403020c030c0d1b030c08 60
    0x4000180d464410100ca40220b54003004184502a070203850000c100000d44405410300c0240402800103107280780720b901c1114840c100e80402000d0760b00382040050442802a0044030114511000b08a0354400c800406a00321181e03081c00039186503c28003c0f600902c00700006d501c464000190700303020160000b55105404801c4440034255156044140122050715101c000754000500080004d004810071340c950000e6030b40ba402d0b52003641d40c03000034580304030300403c0d10100703000900507441c094071034103100c020305100c076541c4041d60400c0c80d1515000002d1100c3d05030260303d030808400581c4081c0802c074000c08140c0002d001c100305e501d940c14003407135841010501071454400001c19108001034a01e0181200c040303800c0c50124035034103a010500142d1041601714100061040381071090700340341e410410b00c5c2c84c801600da00b080d25000341030811103c0c900d8440d03031140c800b40503143c1d82e5501411440d41c1c005002102c0f250b00c000020f0314070115a102500e1560165400601e445000c984100706 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 800535962 1250 800534712 800534723
    0xd0b0a050f33031501080a060501141303020301060b040e160e0d0201030921110a02090402090c0c2b0228110307060507031202040e010e09031209070501030c17161b0f 73
    0x6d9640d9001a0085aa00c0e11807680050000300c004c101100c07009004000b61400c0d00b8040000e6a01c82c1c002c2404e4407590b0b031000c0b0314280000703420411143c000810306d4000c1c032240d00b4102c40c1340b12004004c21800c040c4520510580c100700340380085a00036400040159800343c41c02908104e42014140e40f00e15a0184a005c603484450700c0c05c002c42e0204100000c0d950080600c0c9440e06d031074082c03040100b00180200d503070034400c10042c103a510003049580380c0c40c100c807036603480300c803251400c0300380907001c01c00c00c890070741d4402c1308030162080350701802070741e00030f01c414800130301c80c00d242092070700f811000c4400b54150265120103e55998450010b050240c0607407680301c01803410000340805c07845030b03216442090000740018400150007002090b042007941c4c04490800355401d40f0f00324800c100b90303814040c541c4a0340341000349580501501b00044883d0a00400c0c07040c1040c4040c60744400107091109040406084080540c0182e9042c0e2140b101c01c2c0403980c044245181c0114400e4605605031207 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 800537212 1250 800535962 800535977
    0x3032c071401050708030106050309100218011d0a17030405120f0114011401050a0504030203010f150f08060f090a080a0f080105090106020a11150d0b0a050f33031501 73
    0x9594041c40442c0c0044c2d50010880345141c1c41d00c102203075540c01c09004201da40c003510400c0785107000e80e80040c041d514000a01a407001c40751000151480c180219504500c80101d070300356031507580741c60f802400c5800101c0a04140071000120380e04501c110340102d0703400405402d02c0c090300c035000281e610386080d4500080000402203465000071110911a4211208003580401c00551044025200308185070030b01a04081e281c1c0d002a0a403001c002e810403145070360340320102c0103400c401c0d105001003014001c1040402c0c01c00c0081c640301c07070005240d2240d42d02400d01007024400100001d0040c1a0000ba0703003911180c05e118014a54001c04084000140f004000171607a03203030400300c9504a07841c40d00100303103c0d07840703994408a40303040d4228290301850a44100d0b41180c1402c0040c80b000c00030801c0050410203900801c004182c194000310300134544503007484601d1325040022680c100f5601c0e680c0806040c5001508500c018101c0c41007030503000031040c0f182440c10b0180f448900d8600362901d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 800538462 1250 800537212 800537249
    0x20705030c040e06040809150a050a200717070509010b03040b010f0f2705070c030215101206020415030c030c0c21020c030a050607170f010303032c07 66
    0x242c03880100c01020135041030b404540050074000091240310800303855030314100c5010b0480c403241d81017078040e0301c00300b0b03000552020459400481c4802046001101501981420400c40c0d9a000c090142000030402c5240b0a8040300c000c00900c002864020314680342d03580c48080151043d081075404840c000b15940000c140d0030507064091080c1c502c205010712085107800e20804991a11000403030440f0703080e100a43c811045401818402d25560310741e08058000380c50001e1400c03c2c11a1f0550003400c40c0d130705010020340c8244101084030036030066040184404d041450003403055030b124405122460034035210654140d000040c00c1902500c0402400d800300038207035900e0480c9803008106880100d8015602602080380e4441143d19104542083ca241e101092a00044000642c2c1d182c1c403034403c0101d69540107031029100c01004482c109141041451080b444406000040906880e040010000c505048440e0800d01100b001030703e191103280640740c3c95010500a40e0b440071030028801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 800539568 1106 800538462 800538469
    0x1b1215030b09072103360e0a05040b0406020d20120907030f06050a0b0405040b071103070f060e070b07110a0603230c09060a020705030c 60
    0x28009802c00c070300054a058000d50000c00c000d10722045140501c0340c0382050000d05640750402c940c030a006020f0005088040300002a10659541e81c107200e0b81d40c0e111840b80403540700750342c00c4c00360382c03108901c50041d128222001f07003a070016840824001031090740102402c10480f02e00140c000c02e03171071003403003c001921101e1540032030105050316440c0003214010707040024080140006441c0d59a5400321101e2a000908040d9442c000030710601c010f5003040a07020b4004004114034038240c60503060406041ea098000280c1e580350701c0c500d4020000803540460b0708960104c186030030941e0b84202070896203a081189024100d070020301401400080c01c1e06511070305a44410481440a10520418941c085c0c3d0405040c1030002c0020590340703002164208140d2005c0d02696a814030305503c40c03080740186500240b0006034903c1c0e859010445c50180c0b881281920008414003041 = true := by decide +kernel

theorem cover : BRFrame.Cov 800359712 800539568 := by
  have h0 := BRFrame.cov_init 800359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 800359712 ≤ n) (h2 : n < 800539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
