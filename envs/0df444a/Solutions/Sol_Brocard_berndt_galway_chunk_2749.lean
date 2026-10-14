-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2749
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:37:57.635149+00:00
-- url     : https://prove2.me/submissions/81bea8fb-545a-4965-89bc-93f2fdc4616c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 494244604 ≤ n < 494424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 494245854 1250 494244604 494244613
    0x8190216020108061801091a0405040203070513060909060e0d0f0909200705010204172109130c0918060806040f03110d0e0108010b0c120d0905010203010b030a0506060a02 75
    0x4001d03501c82e1800c00e07440007014102100c20007002c0c0141c011400c00b40c0c007000c0c81540300c4100500d10030418003041101402684e0030301103804d25a00280e160049d5000e40d5008020380d81e0211503040ca1030b0000c80040c07800e07440410511483c1c2c1488006030404e213060f0700c035901c03402d11841003d030302c51110030022031b103255141c1d001319040a40080280c14414034004500c3c030301890100842c0d0310f4400815000d48100c00041e680c40c9082c80316100743c4c070012a5800250490025a501510070020700c0660003401c01c941e5079502560300004654854004110340041d01d0b0488501589400580800503a00045811107540703c0402000303003070764401e0140a881c0e400c00008640007851565490141d5407080c100141c13000b40c2d4451061903d040034a650340010220701c484a29541c010747c40ca4050040c400032240303802c00d1070803c50750301d801140071425a804d001900011898003940300500d41e5034403000030b644e25690785101001b1908240c070768145491078040400c9d41c0303160030021595540314039006003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 494247104 1250 494245854 494245897
    0x30b0924060904080906040306240501170a0b1819050604020c1902031f0203150105030c07030c081c02031807031a13080307050c0c0a050f060705031306081902 70
    0x20343c501c2d00018850791b0050024000440040e0050060803404d003080d11500c8200d10788403288600142d825844941070114031040080c10480d405102680b0662041c0040b40b542c1042021074511103154201544400c6103005020364982440010301080111440c10b1081c0e48981c0b082204a114990161890b80c0c005036800c40310f0490b580746404554002410b80c0c10b441401d9010400e41007807000302110f800d50000400565038410313018201207240070b103002c9003580741c8040401d20f05c0c0f0600c60084c0a0244e0041e03000104104601142c582e103606a4100510411413481d10b40a0740017076401851310b450310001c14800c200001802e208aa400491074002a8801904090000c1e00a02201c008810010101c0041541100194000c17034040c1c1d502691242080c0c034503820100c01ca03411503c203500707c9030104020b40c4c0301128506011411504540e44603218a009441d51085440c42c00d0260080c1c0c0c030000d00316420008a03403142071002c40150038114014030900407440790003000c800c0040203080a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 494248354 1250 494247104 494247113
    0xf0a02060711250f1701050f010e04241802010e030a020604151209030504090b0d080f0a120e0a020111030a02100f0914030310350304030b0924060904 66
    0xca03001401c0500c1403c50250b11204a03a4144203250401c00204007002c080700c6004400348561a801019510511203c0d4103045403410880d0004e80040e03c3e00c92610143d202c0b034076040b103280f1458019014100300c0500300c1000e180c040c24107020160b0108da880d00c0040e0280c1004200c1640a690007001c65144c1810041060384481800c5910300801c46104030500c0441c00c0b1b07201d001d070894000e1f20384c1134031186042d0780001a40c843c40000b9000307094202c4490300048032007080d2600a055650314684659041780101c80c040304ea900805c07100d908145407505020b001003400d1084034002e988045298185034100b40e50b0744111203d1000582c04250400381c04152503201420310340c0c061a02040300781c02c646a6544a40d484d0f80700e034295400000620903001690240000200540600c0c0101032805000b8810000003403003e003139159100c0006800c0000c01070084402842d8850841c2800b4202280e45564176a40d0303909036110000221600d81007507070301a60503482524000d1010b010740e0360b107a44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 494249604 1250 494248354 494248393
    0xe031203011a1b0f100c02010c0207031205130312451e080708011802040b011e0905100903120e03071d04060c0305040203060a0b0d080f0a02060711 65
    0xf44a020f60640380c0400740e5200080c00f1a0300006540300c000c0414030422201e080454140d5100c03401960714090090f0f41c10b44d00400c600c000c0f2504030001165982240205442e94400c0a9805081944203600401000344c45550203031401d069994a4243c00c08503071803021042c00f1900140c41080200e541c007010b0040118001c1e00007814100c40c0c0c41002e40d00e02c0000c03e0b401500c009120fa01616400a0001c09000c000c0e4070014801e00b40203112a103a6030b11220544144d00c5000b9004948810825085900400000001e28540002d400101d24503002c0102003034843c0c000d03181309401001000d203026100e81d004506581d000031481e0742080150f0b100b030310030102c000f8000341c0500135071300000b0b2116091120f186480d83c150903101e51a241030700e40315013100c08489206007414070301010311001d42c60001b48070394810540e1000003104d524010024428001e506001810110300041c50019105044040d024100c8950200d42c2d403900e03807540c10744d4400d403503280014182d840030503100c805804844 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 494250854 1250 494249604 494249617
    0x60c02070812120718120f060c0e011706060a0e150c0718050609070309032106060e09151504050a0b2710050706020909130b0903180f03011404030e031203011a 70
    0x70b03602158247c1030350305d070b1066030002c0d514200403440011140c050303560008174242001003040000300103840c06000060300ac0c0140501d540030030000d06c0158141e40c5a0300c24010441c01e080300d03440d444500c580c0900f0346c2c072003040c0075141d001141c0c03121004a150090003002d02624000740547e20310398440200314001e01140d5016030400001004074840780030003041e0b22903410741031440451541d04040000c1d100c040000003c0340200006400c00c0795050407104507442e81d8104032181469840e5820301000d2600907074008c0c550040c0140e80008010541600400f45201d5040c0106890060b49640d40080a40200b6041c1c00c900c46082c1140700a210324001c010746803041c040142410f0411001c64001e4108440c1e520904901d0308191007440b0900780b40c154829201ca0082d460100d182084a1454841d82501401303000c0c04411a07090341d50039080a1407144808804034403620302810020a1550441da8240c0240500307200702510308082000c0303a05030f50000075100e4000a1040c8800c0c0286e0001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 494252104 1250 494250854 494250863
    0x1306050a0c06090b01052e0c052109040b01050903060103062003100501031524032403120c03021b0609031014071b060c0207081212071812 61
    0x140000700015440e1140c1c03030020f805140541300702e42c10709050107610001061540340010003030024220ba0b054824504455100360f00d0301d40c1c2094031629045291125654801071501458002075100722141030240801540840742888103a20b500c00540701031062050103030b0107420200050020070295045501e452407050030f882c05100040000d1503443e04140d40d10a600003403000d08000b15031307260282940311807542c0508910b40349065840228038404403091542281d06a030440075032802540b010105205010002020007020107542107c03480342d02085808500e03921480d04018810303c042801c035503061b0014224086400c140e141ea04030305c8190168009400c000005264a00744120104400c00b640c0218844080c5c92101d52140c100900e99410050485c0768000c410454000c01c184151f08040d00183c01c801420080781804020340044a8910400b022941d40c074442e2030040202405c1100b1203006919135440443e41d90031060840280f8001414040c80000c80180c03445100074400d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 494253354 1250 494252104 494252117
    0xe181608060f190c030221010e010909020103020f0a030b0a090c09090b030c1c11090f01030206090406030b1005091b0405060d0e1006181e020c0712081309021306050a 73
    0xf40c40420180c1d030500e81618000398000c504100891881110740241c1c0b00030b0300240701158102121544102c1c0148181c507403c9850b164102e0139640240d044805c1d12130440801ea50300c401905000d000307000c4041c61140180c1c1d03402000201140c0714402c0082c104181d03503503210068680302110001e001c4451180ba458000c1c4448035010355207030342c0c4072210380642c064882081c18150400510010004042038000c43c0b0210400000c4040d4540850640c1c0c1e044401d03648601c0301c20302050041c0700942008060b010b040060007568400071000400310f40c0212548052503032400e240780f8501ca0f005880030846a0240014402ca2500740d0103081c413807860300e034001100901101d0740381c03070900e06074a1026441d949440521643c003044a40c3c8070103448100003071111041c3c8030601d03c880c0361810101032606038086a11040d03c9001d02882d030003003078008034241d00c0c649203081400d03043d444083c0070481c200c140c0100103146c0040e402030703d01c056078002e10300c4520b42c17a11074191201d501c141138113410001d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 494254604 1250 494253354 494253391
    0x6090b0f010f02031b1006060314070c030c171204031116030c050f031513060e061902162a0806090c150c16050901091a040b01090e181608060f 63
    0x1a07c2110700410f1b841e640428020310410407001070f580060192001c008007240000c010a03081219458803d034040c20103d00f68181030404a44d80c02905c207843c1054030110300344000e0580c00540c5c010300d91523020644408071030300400d125032100c0c2c5220003083c06540b007608111524003400c103000c03080f9000d425551180d014144680d06041c0031900f2204c2d04482c403840e0018804144160f084840c0610001e0a09040040c181800351045801c4c405010380c000440083c1159401c0c2e9003004154880036510400300510010b03551000450f5400c0300000900354000344001c00024000d0203400c442d005040505800c00500404903c3c1606200c03001c0c00404c207001600c0400c002c2d0071904a90f00c0c0e0700c14010350400b81040300400040e40f00da0032039400d00058002201c02c122000446030402c80d4005010419000141e80001075903112030100c04950040200150818a0080a0118400c26601040709603504103584001600600c4a40d030300030703c0028400351503140c1c541d41003120040800100034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 494255854 1250 494254604 494254633
    0x60311130e07030501061526060f300102030105061c1808030402011404050109050d0204060e0c0304050d0503010e0601030c02120309030a020c030601050d200406090b0f010f02031b 79
    0x80c2c4692007141c0c03582d9610001c000800b41c1000084c03401809180071072080404c1c035016001a0080300960a40c161040c01246140e03440b00744560310718501074600f088000741d15003403446000c41308201e4034080e401043d01001d014018800c0724180c600040c0050b0914003002c2403441ca5000070200824000c0d40ca4a1341d48407034101844011002c0c0c46805032a0340e9180500c001008401c20f02c40c0070346040390604c420300c6071b6038000e08010141c800c1554001d54400741400040c0240c01980d00006d07000c3d82c07100a102c106001c003401148254040c0c4200c0c1c0c4080c0748aa070454092100744507003441d501804012074075640c480e4002e040104542d00c110342001050200310303a0320754002c5e20f404545600001d00321404a0301072085140300d00003100600341c150b140c2004907001d90300015006000203c840c0075075060211002d2a2070f11400040c108200c107686505d04d000040c900001654030070b1011030342c1d9079642e47c0301312103441e0103a004e17501845c1040c0c07040c3c11810345c5100040c1c0200140c0100c1000c00c4229 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 494257104 1250 494255854 494255863
    0x51903030b1905010e011d062d030402011403010612020304050f011409241303020f0709060603050604051b0c03041a1909060f1407050d030606080604060311130e 71
    0x1a0584200750301c030714a8a00017401d0640b8041c10380d030610100c0704030051a101d6041184519040940702c65542c1c009044520521144581c1e207a204505070100c0800403100b1403016520844c400e032907519040b80034880d81d6016010902c0744000090f03100030080e15083c4181c01441d0040d200c0c1c0100c8026081d042c00d0310703095a034194281c2850546190403c90b500008120901240c0482c4124404c00b07039141c110100180e10051a41000c0d0502d040a442054801c120f4254000300c21802c0c0c8000c20f031142c00e00805090240310780c0300081d08100c00701e4034600c0c041c880c00b400342d000d0110003003048143d0f12010200d904814100c01c501d000c240000111442c0c6d4030009601c000040c2c0706142e5552600801712102050003903003c0070004100420300116402c400074011601d030a05003030500d07841c120903142e818481c40c10010318038016401c0751103400f5099004581070b00c90710740b90569142d69a50510044401e140300c0601040e500030814105820004140c0d180c05011040c0800c05c5a10765079400e240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 494258354 1250 494257104 494257129
    0x7050723060411040204050a0b130e01060809060703050f041101140a08090f0111122715010e0702030406050d06030804180e0c0a0915080105070525051903030b 70
    0x59811107000c02003040901c0c40a070300c510100311400c50415041c9030125040030524000e100c0e0505000a101c101980380b5400103005042501d118202507841c2c03072000301901d0080e40c07000c49910420002c41c0c0154005c0c0034081c459018680b505106075581e446100b020030200b441c10341032040c042d09407600c2c90030307410060050f5215922402c4250900380d1a851404c5280300d016406c40c1d00d058138800c4804c1150040b100c034416100038411854a80780310b0506011841c146400644403c180d940c04298004a1804406950300c009010030340c4e6556103000200204482000050300100300c03c0c091240140080d201d04031100f20001221a226078030100242d010381c00c03405092900204042400c20705004100744e10b80c034034000c2d0640d16108004110a02003d0042007880340d00e61500d1300e0303e030b481c2c1c4003e0402009407000921840c1000d24018285a0100c41906030384080d854012240003800c3d0b1a414481303901000a0000d44040b680c40041000b030340400301e040507100c0300c041d08580d484040c1c080d00d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 494259604 1250 494258354 494258423
    0x50c12151f090503070f03020105030c030c040b04031505070309030504050d05010f05071e05070b180a0614060f030f06010b1e0d061d040506010512010e01140f060315070507 76
    0x2110b0741000105031511880c1e41c010041151203000078001070f6400010790742c002c14020031003038403616940410009030045402c181c440d4500802c00000b44604480956480e2241c044204410388034514110191030500c10080d0102e50204010001400c000c8240d80203140210700004412000703080b008143d80b810303564032000444a1000000d003c890314100c040000d030f00d00700a8078124156540e040c00f07440c002d00c20450301c145c415000401d60300500c044403101d03905ca81d0030446000c0b000680f610300354080d036006008048800c8030000c2801c0c000392180020400350f0040c10981e103408412030591341701b46400c041c0000440307440d120050864001c0c050300749407020041201c03418010071641220303044402c0c0e14484540b405102c0801c3d0045485415100151202c1c0f804500c011941409001400b034281c00319841c02c189403c8800c80c000900c0d0182000310031170401074403080708240d83c85010200d06c0a1003494a00031072187d900038801054641d00c640b6000202107600d050050041100e44101e11 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 494260854 1250 494259604 494259617
    0x60a0812030402090106091a070201030608060f04060e0a02091816090608060c18102307020909030a0203030a0e0a0c09021810090302010509130504050a06050c12151f 73
    0xc114a404a01e51780034200d40e00e400c80c0581d03d4014602e100ca030825102c00f01e078080c000394000659100340c00c01c1001c0c1c49054101c0d10a4113200b107891201a20072a801d9030403d240015544030f02c0e00102d614050705400421150040d10f0b9845402e440c0e080d54030900406100303c184580c0c5103010200c0b114000c051507000041c0311842d00d21200c0c01c02c54001d120004040d01042107000307500e2403084200440f941502d0f44203500c1c0d80c4c0082940e40824001e010500b900040c24042c02d040b8100c8020042c55200f500c0038501c03900c4800703c180d0b1320b0142d404d801015800034000502001c1c81a0321181104094a084516182080e11000440123241c0c00c21303903d1603000540c80036600d140500322013125100f521342220034500d0b000c005000611070b0000034100320001540070183d030f4500c549010100c0c0c0e0341d10104210f09080c60300707a9541800d200c003221005d040c20b0000702c0d080c1d11386081c1e5980181103c10002e85965840189400c240707640081030b80300c41d800b842101e40d0070303549015071100c000d07070388a80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 494262104 1250 494260854 494260861
    0x3050d020d020606030a0f031d1f030605030304030f02060a12050c0706180305190203040305031605101a0904060e060108160f15030b010203190c030908010b1008060a081203 76
    0x3400d18000404c2203000e5130010700420b001802802002800c6601407801c02140344507104039026007803240d810950702c032944583c00c200b86c0001400d00300405036542c80c1003110076502c8003450f0316401284005803024110b0442d140250030480000d000d00e1f01e00e07213000d030b500c90040010765041750790a4550400c119408600501006028410300d240341c84a4100c03c01506d019913001002803041c40c80011f80e2004280460030814020420f40d4040c2d5404801c0d0313900c40104185945d16080d403d50309980d10311442860041c03117402c600c1404c0c05400c82e0b441c8020002590410300000040c054030458199982e010010150710050092902034001c000103015031028030b00c002c0f013820300385420000c00000841c0d405c101080c0c041140801205050a0214028440b072005070b05500070180c07508116811801081481c42e4020074500845119845428580d07450303807601400c941c501004a038103c41d92200303101e4400c0c01141090703440380c00280003080542d201c9101d00e007020f040c81010403481c0c6011050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 494263354 1250 494262104 494262107
    0xd0504060b01020a0506070323040602222d0b03090105010f05010f080a09020609030a1a070509010c2406032003010e07120314040b030603070603051501050c030403050d020d 76
    0x4048034100d0910040407000250346445d41c40b413102901c58010b00d9518030b0031380110007202440304c5400a0342c02051849150a0910101035030050f90002d86011000d69007000002e0010b49c21403d86142004c81000c076002c80d41803030a100e8603c03c690426152039540011803451030300003188525443d40011509500d044c01408003c0b4a5400c8681405003400d0000440ca03030005810fa80701c1e10b50706010401000c14008242d42d032180c0e40c0b1881e0580500320794503003844005002d0304501c01461104030160f079105103084405024441c240e5000072141a182004034020104404680c400c403d00d91300c02d050b100c250042141d03090750044034100061603003130154008641c1d03280c024034401d6000b400413441d400d0300e150700c0d0b41035409200f5a0460f50415103060610900028100c1c10340200030300d54643d202c219140c8550011581580b0922511078013141c141c2c8a80640341c0500c20343c1c045004004c05400041d00c59070803030034a21034148418000000803c00c00c011003800005903401501038842003480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 494264604 1250 494263354 494263361
    0xb0d0f1b110d052511060703110d020c0d151113050117060907140d0504060605120a0c09110f04030303060303091a0a080c070609030f18050303070f020a0b0d050406 72
    0x4044090050501c02da112501485944150460701640b2113401e1864524012840404042041d81c01c1701c004a40242016040100100b000323041c0002c541c0034155018040f070b0b41c3c2d140c96080c640c01103282003014000800c41d102020740d00720b00c00380106c1c181c0e603100764414464120f40a0074041400d500e03410070841d600819049290b100551800d481440c20070045100c450016100204110030b180d51a00c00417880340c165004040c541c02d041c0541e061a06015025100034066180300300010900b40055250004000100c1c507408602c80308220320300071030710005007240e400c010740c112810888800d090000e10010301c0034510a8800040007421420002c06101050b005841401c000c2d0017007650001042051380d0307a0700c1d890700c0d01d01c8060b9281122050a401048801849903061100760400c05030003070000c5c0010405695103607074500808590f1151103282348680d0340c041d00204040c4002c12000c64198410f00c0c00645005620b0390358102411160b031094060800241c2d0f80e900780010080b5502 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 494265854 1250 494264604 494264623
    0x60204061101020c030a180b0f12010b0a0c0b1003080d05070f0507051908040504020a021b2b020102010e0f010501030302011d150621150105010305010b0d0f1b11 71
    0x1d000310304040103040c8240c0c0e03902c1024642801e004120783d4044500d0051240400500521102c1c00d4a4184054640d07810340c010135032110491b4828000425100040010356803401999540e0488922185d21100c2c1c0e88040504154001c4c0c0203107a001c0701107020300d4000e180103100c3c0c90f000030351498502c2d0000c01c040101d08811080050800809010404c00180035200c10340720451200310300d03298940350600e8032580e844070790041e0000c41d42040c104e40209002c1c0c0101c494000340700307418415004106214045c0074499450020f0f46090204400c103034110300340503d2045c00000f500780c02c2c150320b00d85003203c5c41c3e0000316160344620040c010141d0a0040d14000d82042e420741010910341401151111000b0090202414407240018065903c92805d040026072040c555a0600c9070340c1203d0b911640203903050400400d0640002505522a10495040304c1c8583c803c24101040f0200110180441c503d004400e5503c80744020f01000f0b41104600c2c1c02032039929040e13800748050321194107004800b0b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 494267104 1250 494265854 494265887
    0xb0a2336041214070b0907030210080402010f211d19111801060c0f080a021b06030403080c130f0e0105011115010b1b010f0209190b0d0902041806020406 67
    0x19002c2d07035101c928030f8003603680b86039024507202c00a07a01c01c80018900402903102940c040700c1c86422404990300269114040d80c003c2e42c6000000214060540f04920540a0412155160000c0007982c3c006580401d040c00c01c0c17202a1403a42041c2600640741651640f01442a843c8101181040040300c0039007580c95981a03624a40503c50480100100da4051082d541032244050b500c0007089840c6c90380c20903881e4060350441e00d91001440003903603940007808d6020130203180108030159141c40b1040d688070f00c0d810307940c0c605c1580d5041000b915a400516110000380d184403c00318400004001c0c1138083c000080361080d4075850200010800c800a01d0b0440040d04002c14000c0e00c1c1e44016081d9041d500c0600810365241d10400d00425490200b520b4546c00f5403910103190034a10300c2d6001855a450102c40000d940f803c0c5480030741e8031412500c281c0d0303040d00040006100c9000d45401c194031450004000056000111884104801e03103484111000d0744d0000301880240d4100f020400c542401b03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 494268354 1250 494267104 494267117
    0xa060f02060114061603030606030b0607020d080a0c0b0103030503040b06100e010509062110051c110d02040e0105061201060303090308031f0305010b0a23360412 71
    0x18904003944814060003410344800d03400b20703142d40d541c0343c960803503402c010403140c0e46100b9521820002c0c010002030013050000781c02d06607a1100c0e1302d080c2c000c0c2e4915580003000401e008a15a88a15260340000e4008081c0a907001118002c5111851210300a50080d143c1c1c0d952881c061500c3d4240980c0200120710880c402d00c00c80091030381c480110032160a003801d03c0ba9888030b070b010005c0d01c580a401b4103030b4103203040d002c24841504408410240160f030243c80386404a51a00e04224610681044d04000d10441c49403030404114001910b49440c0380203445001d00d00000e4004c20306952a16100c0a0141e45070300611402d42401003401c94081400002040501d066540082010050b84005444010003001052402c01d0400d00030b8024407219600005080d605c0c41d006002c1c0040042e240d1088505480c0050302c21105180403501d007101c1018445001c880c50200100c400c3c0c3c852582c0340000010030780e1106840c10a16001145d20b80502100d01c5142601c3e209922040c3c001064040000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 494269604 1250 494268354 494268377
    0xc09010b120c0d0905010603050f0a0b0f1b041d090607120209030c0d0c06110102090a23062113081911060c0c0606120c040e0304120c050a06 62
    0x25150a079a00008039661452960311481c0e5404150700a02408228051400b42d10004200055100b0400c480c86481070b1031581943e20102c41d10f5142c0c4a5024110f2500c15001801405103030075000d0b4032815880c46648032070101c1500004030381040d045615100750b075000a010038000d84600b141d000d40440c0003032080f031500d5413005128507220920810070b190003241d440b082d903a0500c1910b07205032029003040c040d1540d504252002903042d200f4034000c0740542891100c00384041c021585c0c515000340122252a1a055140c88107982c503806401110342c10080c1c0541c40c1c2d58038401040c00e1000c000074016040c0c3d11040648441502074401c0d400711030f0300060500040c0b400c03001d8802600318030314035100c8442d10440540381081240d0040b0410f000f00e03000c101070840d0300d1025101441e0303680110780d83c0380c1c1c480040c00b40c01d01e0103407240d00c8650300408040000346003903000309140c4101542503905259a0b0000003110701a4003c0c215042424101e05211600300b8a45600042440b8a00300c510b800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 494270854 1250 494269604 494269619
    0x70f171e121807050d2102030712020f0c0108060303070c2d03020312160c03030309030f171b0408010f0603020306060a0e04080304030504180c02010c0207060918060f03060e0c0901 79
    0x210b07100f06406a500c0ca490301041c08103c06c4034009403a03c079940c03090031440014000b9160741c07054400701c4481213503c2401d800d8510000d041c0400750030060062180c0d0b995a001507502030350040c4a20b90610040021500103805110a400100000440402e840f2031400a003640c00404035124017086048100c20400350790f0001c0c07090611200040450303a11071030010500c100c0300403c0409007100b203148600004156150b40701c0c00d410350107541d03182452000c0310740c02c49030103284016403404041c46c10003003403100001d04401040c800c2810b95240c502540c03100c205080d5600c91004005940d034070801001035041c18800c0c19845401151044042c5060042c864208407028001030706451303022000600f0140104100d8001d00030560010741c12504444c09a006404104604001542406a0614902e00004000c002e8441c41c1c1c4440c8001410b21a0950700444000e480a01c450344a403000202c00c02c003030046102442c05240d001c00c1d6000300d5030b811882c0500c407001c005d00a5400000400000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 494272104 1250 494270854 494270863
    0xf0302090604090203010c48030c0c03030e0f040b010f0e0109050a030c08100506010f050a0e090a0516140d0509013e0405011b021918060506070f171e1218 68
    0x2304a212440410501401e0031280410f05240c0103019a0b03114401205041d04054800032100d8115503400f02580e081041c8000d03103a64031a00c0e400304075443c01c1140220302400848030b0071035048c0b51006800740e0b030300e00103030107154154010744107403500e240d007840104802d00000a0555240c1024012410500c00003005d803d0f1405007002000008541c0404803031107588540b000c181e005000d4001810300043d400300178603040e1003440681e01c5071124050114060324003c1c80c2145400351107400c21814041110142200410f0401203545c0c800c031810b4100307030001d480c6401c0e01b00e18901000034034140744810440040c40092000d0100280000c0006aa1128002c01d020000c105090680d072101e10200b0b04100b00c10aa40321500c0c0c51120201e122580c09100c081c04d803000403401d0100b42c2d903d83c20310070180b1030040007411100d10010b03200c021840c164000c0c605040b036035400503d032103801c42c2070412007528000ca65404010018245040008000c0c03a6a0080500d82a1402805c5000921640d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 494273354 1250 494272104 494272217
    0x20105100f050d0611030c030a14010e1306020f040305251a1b0f030d0b06030606160503070503030c040302150a120b04020904060e100605040f0302090604090203010c 73
    0x3030030752407554404002c4250030100d586440a20740c2500c1c0c0c14403442c9181032390000c07240700d45054075140307556210040b482d218604940c80008003d40360340b90441c0c0030035003042001c0281e07021034080295040d240b000000400085002da070140280d10f02d4003041d015040030740b100403400040000c4083c040c0c03403294490003914009900800380e48586004001e00b440c0d1020100352094000c0303903182d11107010040001d11020f41444401c1040100c0312040004a0009481c2c1c95040071003800b015580c0468100800084c500510880b420311074155100e500e99841220703c07451407040454100300b1410f0200c0c900a103440e1440c03a5034103007809484014409000d0040701100e01c0e4075000441c8440e15150f04485020b000a401072294030303100c880305100c00c08c00340c0b074141c60010f00d46030000c2d840e4412400e490540d211032005428a500d103800b00a65600050300e90340d441651808150f006039804d01c0f130381090baa41c540f2050046c14800100e00344005c6010300c00780003032400e103403100446004a07a51914 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 494274604 1250 494273354 494273359
    0xf01020a08011508130204180b0403140a02030304060c090302090c0c0c040203040f1104240e10030f080906040f090c0e0301050c070f050c040c020f0d09030206090103020d0902041a01020105100f05 86
    0x205d00f540e80c000540a01440d8441205594805200c10180040d001c0b009104500944a147c0c2880460402129904c06c1075030280042e0010700110b40010010303003015040300c101c3d00d0b08054460b201d03000548000d82c10707074200e04010030001d02010072010a10607003a0140b4104c50450641c03901751951080521001c2c00144000080d5450f880550f486601142c04680c1100e800c82120038844120984418a405452240e000900008408584904041d01a250701018240a00c0400d40d80c1c4101c40d0440c103046070740b0840501c000b191220700c2e012070100401140102040001c4000c0c17000d00040c0d080501c085c0030703906000030466201d107001c0c1143c0c0d00c998041d01c5e09100c20340ca0b050090400b06079240d2190b016040188104104d540042c980308124004400c0d03450744100a0070654030303111288002900302000f030019821a46c026030117880d6141c42c80d4400b00b0341e018950b0028045445001c41c80a80000208501c1d0895034240715855100c0f07a096440b040560400c44e00248416040c401c1c0b40c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 494275854 1250 494274604 494274631
    0xb041104031122022512051804020307050403150c050415020309030a050d0801080c010906080c19031b05041823040b07080916090b040e0f01020a08011508 68
    0x119107607070f01000e0f440c5441070600b008007402142c0b5180650f201112690702c5209403030380960fa44403440540100b20313902031003d6001200c003060541e41030308007820903d031340c1c24006009105507c80e40001d5128203110b80c1c4a0317076654110302d04450154040300310240d001c0e01d130201c0c40481d280c100301160103841070041e4081c07862140e824100e01c1e6100f401e28060700750040030a9030080060009503040d01e02c01a031100c031843c3c0e883c1c10300c1d130741d90b10061002d090000d1210031080000e98091401c00d5045007440a04034500042109142a4695189403000000741d440c107149c2000341c5244503c03501240b140c80c8c814a010300d09820607902d0030781078409e500304a698403c003445610300301e40444c0b06038400304160356051400d400c01555240b81280c20b50042342102000071b40c0c101c404988009558140c56203550000e080c114990005e20102c2e607029000760b50340e04400c2d0325030010030004c8501e44e4864000359540f0349510004004c1d420692081d1205000f04107400d03985a0040ca138581e00c00320882c00074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 494277104 1250 494275854 494275883
    0x10c1722080c01110d020c15090316061d1c09030f080a03060e0108060405070603020c10050403051e0d1a24042304050906072021040305010b04110403 66
    0x1a00411400c414440e00000014070a80c005d0010b0f0080e0151079194820742d075441071400c1d001c03030592000b03d40400168004112040700c12101150001c0214001e0000141c01040310210350400450400201d84030790041240540105401240c00b059124521705081058510760302c1c4180d2940c500c000030101000400c040010030322941c002d8008103070760000d903002541c0d601c2880b42c80300c000743c500f40c4080c060a0301c0400c0301030080c021182c48440140041154281801d0f0b004004c140150003203040000c20000e01d80b440c42203115541d0240501d00d515540d0b8021801a03000312240c00032071800b120041e001c024115a0f07180c903039a4940c90718611540d020b16201d030344c4980324447c80c2c10102401d40c034892003410452280a0314800004203403006c10298462442c001c0c1e030340c2000c0300c001002440c004031845003249441181c0468103170302d40807105071034510a40f41050001a1010003071480e008901001480400d0107030841140c4240c5040104813554081c1c0710080c40340c0e000c041e000c01c5915405 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 494278354 1250 494277104 494277127
    0x20c04020304060e0a080a030e010b0906091305010e010b03010b030f0a031b0c060e0f1f0507060f0203070806130608030414011b060c12050907060c020111010c172208 73
    0x24244940c200f800e40c5c01d00c007003910f00901150007076a80710700020728000060700101c13014451100b400340d0091510343c0e980c0e107981c20000d0424004100c00d0140340c03001c40341e0000440134001d12000031100d0b0004106422000140b500711400050940d01c80c1e401100100501c40011801007403083d0145001581d00d441101d030407201d041c40110080104a0307414000928a038444441c5c050848200c0700002a050a90104600d400c08404445c41c007100d13038800c0c0300d0014040d4000b0050f151040b10302196620f040038050f0304a070000c4564002144000081001030b1401000107800e103086500104035841c10302d50340aa0b01d0140c1e000c0c0c0296071400202e45102c0d68000c5240400701800d40d180c41840300b031503180c000054025041c800f0042014951601c0ca410305900502e442061120020801a4902081141d00d01c2c2c99a0b811b0703050046916040544200c03c2c055400e180f510381c0ca9480c032910800c84800c80c4442c0083c00403880030940008201c00c034094610307080089400800c0c1c261505041c616 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 494279604 1250 494278354 494278361
    0x170d05240d0b060f0a0e010e040c060c020f01031e020c03030402011418100e040c02010f0b01020721030905060403120f26181f0c0309030903240c02100501060f020c0402030406 77
    0x1b2840b124100c2400006c0c8031240300d42c14900c26445184450b2031186e031140140c0d409428120000d5100b150300013072100301e5110380d10517030039041c0c0380000d0002091a4010002240d200325016143c0c1c2e0000070402c000d40d40c03c0500c1120501c18865400e26258101d2004d80b21285241c01360381c03280040881c1106a580301e88070340d003d0b142c0e00400c1000b4056290001034024444100041d029506210000c0c2c030720360010800c00708940c4030700100c103d5401406207402035644040030450500920020101c1c071a01c40d84c000e0400b47d407241c2c203c801b4210110300b000d46600c1003480701404200c00d60180006036030600705001c1e8055002c640488441c0c03200d80210300e8600943d24440f810744690b8104c1320082c0ca4484640400d41c010300020856006d0144040b0140d414488003c1c0125051500800004490704840fa021010072a040180c3c140125001403e4a00d0704c08118016404035061911100c094820180107000c0ca00b41009808140308001e51660302421003288155804000101848210382 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 494280854 1250 494279604 494279609
    0x115030f020a030b0901060824060403120203030a060e011d07020c03030c1506030601030b0c0a032a180302090a09030509031212010b0313170d05240d0b060f0a 70
    0x200c066403640d400010080060003100c000c6031285c41c114000003803090156440074040c00e4000043c504a54811a0800c1100c40007420799401c00703c01c103c000003144110b10f07298040d204550103190b8a0808a041000740c580d940c000c1c0c3d03c040342c002c0041140003018110038043d60840800f41803590340d103000513400c040c0101034036501030000007250119801d01080c0f404072100350141c0e10505440d0b02c000c0c1540c80b202400010031080e1680c000c0b40b040302c4601c020b401c03400c1451402181150b1654a0402268041240342d1000e1aa6101d1292980d4000c8840b29485241946100000d859070700010303194030005e0308440010399a1420242814403c1d4200c0c2c0b80302601608840810002d11003106981d44682007808058aa002c008a45690040c00b102e0140340d0480980180c00595102d4000303185045c00c1c20f0081e0503041042581228032070182512604001100d0004501504500d40402012541c4244242010040c0c04005241c0501454005ca419900c85260340300040c00315a02c02900e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 494282104 1250 494280854 494280881
    0x5031509210c1e0d0305040f060207030201021b0102070c0b03060621010305061f030b062805040b06040501090b09040b1c03020c0f03030306042414031b09011503 71
    0x6000000c41c0701c0e07050042c0703941c14038002160414480b000841d9015021242e8100064200b080c00c00081446504142d400c54041d098204080da81680c0e0310040340d102d1081180941d4010403c4142d1107858140d0307680c49280e1070300030340c075000d80d9540b0030b882c940d4140603074002800d01001042c01d5071103e000356454610131046003120392001401c0801042002d00c02240c1c540b0400d00025402700c501c1d00403040a110301c03400e04041c542580d030745c0b0a504500501454110400c4c04402c4c004a402e81070705481c2e0409d10310800b10f114244010701c0309448030040754600a201c100400c001699000003100200c82c460340c00321762107442d2500004e025240c4800503641c013100c081d8103440e181c02c1c00b10714014002e209030220b50b6024480d40c240701400082d14099603050300140300141950400b6007010040c1b25a040d6007440002d20b030320382c01c40c0c00035190308620845840f41c40840e031213044c100001403003810707174500c00070402c02d21500040c4110014007621050941244907400c0660080e0040703901030600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 494283354 1250 494282104 494282143
    0x1008010204090f0b010507120e010c02100804050c0a1d090102160803070e09010e04060506120601080d0305010f082808030a09202808060112051605031509 68
    0x1103600110190220240441c8982d01c4c21035504030a40c011000c0b02ca4150303100d014101d10489450041c0d0f50840e10009030390600c00400403400060360791030000c1c81450320a0311010a6800c1c241807503842c29004001990050b9500342c030500c4050441e5508a039260520221466503685490030103001e4000d80701c0c1089000d41450710300040040000265100700c0307050303a510692500b21030400c00381c84401c2c45400202580300d4082070203c1d07000d4200310360103803015020081c100700071044a403920000768030011094025081b04210f81e64180a418018410340c02a01e1686041c10b1445840c2c1400d01414001c0303520240b2070040884100c004503032600d4200494589074500703030030404041c00741c1c0e17802141e00307000748408078010012602e46408000b4000d00916002d082d46001c0c0e030720601100142e0082035801d40400100b02000304601e6010b0f00c2912802050070850385401440c040c1c168414101d2240080c03001d02c80d548001030075050100651041c00c0302503e515030124103212000c0c50101e00101e2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 494284604 1250 494283354 494283359
    0x1602060a110d06080c01020f07030b0a050a090507091b091a0a120c230c070e10030f121b1e080d05070908070b07021f05041509080d090305060f1008010204 68
    0x5012520b01485c0d58207030207558452101c5000d03691950000d000c003c0c03001040401160000b02a503010030790150225400181d20340c100e03194117140210030390000203166101d42200300c80038194201d108407844d05091404115050090807a0782c106144407107040701801007400c100e1148a13224443c0820302101d410450741441440090000c11088050003581007090900c075011390f4810101c40a80c0c1c02140070b0b01e1500d040030124242100050551081d0412716000400400c3c00140881d055512420040c1800d002343c00028111801c0c6003018034101141660800114030501c101d030b0300c482c10210082d00c90001318070300032031580581d0100080380c520b403104010921307030481c4081082d41d416000300d4070160317a40d0202c10340520800d20004e4105042c607032200d04a045204040c0b0940c484c030b04000d03043c140c40f0342c0303840e400d1a000901940040d4201030100030400050146204055071450300889041c15a02c4980c0c1d14680a88200016458940061102d080c030840e507002030201c03a80207544c0c856 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 494285854 1250 494284604 494284619
    0x1d0714132606370c081003030e0d030e030313090501080313031202100e0c180c040302120c1005040f0b1e0c0c0a090f0b120a0f050705040906060e1602060a110d06 71
    0x21915011404a00170801190840100d0f0000d1001c490313140c0d59110102c07100300c1c00c0c0600764042c403004070103105a0a410740130a640600203044880111041c5500040c90030001c2400c0e50810390054541d50000c001c03066030a04100145010780790003c95004c10b04241d10b0341245404025560030352014902100284440c1c40801e0300084036170211004140418079072b148080b001d0040e41c0280d41140308110400c01410701c8181c0030307c41590070003a603800d803901d400443c0702c41c013410072142e0000710006020712060708003000c1c03400500b60380000c00c1c0c14202103110080340b014141c540c1c20144c3c100807078003840840e8200700160180902401303005e80c0981c0c40040d000507180e070a82d4550384505180080c111070415081101c9035090f0031009107a062074503203c10a201c43c0303052044d21240600d0102081e240c03624050300c0b00a501c601400a0450300c0c3c4860071422500103000e69060056522001003800e50004045030001032422000079000084039400d02c05101c2c1c04100b951103418002c0c002405c0c2c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 494287104 1250 494285854 494285861
    0x70509010305060906010f0c150e01050612070f06030218040c050c1509100903110a05030a48051212010509011d071413260637 56
    0xa04080c0c809100c6901d9a004100c00c80f0b00480343c5c1030001c0c1e110090728039010700c17441001140740e0103001110700b01400d100054099640088140e2001d80d100c00500806040c9450140080b91020001e88851400c2c0380a1001800c82c51042108040c0c0200707048100744118041c3c4440071350000d20801c145044410f016065402070305105070140618000045070020280f1905e205031001005030402024114500000301120201541041415058500b41e4a000c02141285a00440c01140c40c0c200c800c03402001e440034070f601d0a510301036002e94286c0943c4a11504410102c03850403580070074000d0421000210490400600640b04403e5802c0c2841032050080c601c000b1030240e902d50582e251001d00c00a0642885500e643c007500b845044c8203501c12941180d003250441c50400004011600c400302240c002e802c10000c039048051080040346411040066220102094080ea15202c00e112940710003000304440900102c0381406007004140d0070050081c5c11049800e8018940701c890450f004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 494288354 1250 494287104 494287117
    0x8063d110606220207030e09150310020c010608070b04030b01061e030902030c0604030602030105041526010605090403050a03140606041206060308070b0a0e062e0305010e101d0706080711060705 85
    0x200c600e0230104800300c990042205100e070300174005202c0c004443c1c1c0e400700258018507003500155a1000d02280c4960148000001801500702c503546a90440c03c1c041160681a84800240401e0314134901b00349556902c8d20f603560080303040000d0138582d58000b0a0400416000c0c80d68064400a400303c1048603650103103060f00c609880800100d00340c074414111401d042c0c05214044205291100c40b100b5642e041c82c0e115020190001ca2042e1391030011480000303055608501069021807080e45090f0f1500c129101100101080d030340e00c0c2020004514284904c0c01184500103441d4209420320040d6000440110f034421a42030390345030a414040d090711001d03100c5189240c103000c0d8104403107100140180c05100040304001c3c0c0041c4189007480810060300159400740e118100000c0880c0c0e003885010070741e01200029144501402c00001c045614008080086a044144d1210000700020f040001d81d080750500212a85803804c0548041c4101c19082003d44546001c200001d540000038042 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 494289604 1250 494288354 494288359
    0x9051608070504050601140309120415020f070506040b070602040506030a0e060c030609060402160f1401060506120c360108061e0108063d110606220207030e 69
    0x251039119000c02064801c19175805000400c1c440110701b09005400003150880c2c83e0004484418109407408a041d401c43c4d841610100088031005e500ca035014070451480c2e503100d001420641d030402002420501603402110000300020400804020340303641100c0292030020002500c80ca46544000d0150400172481449402642c3c0420a81c0c110002038138000c0303000410403905a0ba50106210003500090f208102e503000c101e000c0c4001c00c0f10b44050107140c60240703941d0003a1b600c0e41d19a49082d55807551005000350313410801803850055000760305821800303824072a6a01e44400c03203155003200f481c2c2820313019241102002c2c400d0204100c440d007480f00d02a221040550b840070100070401d02503405581d000a4401c00304990356124804d05c590259004140b502d40c00781e25680304242d8240b840c005418142d0240d00054002c06540240c001d028207480c2c4606001004464280c032644041c02007400b6004245e000e03072114101100e000c52002c0700340000c40d00c0f45200c2c10014280c408400c4105e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 494290854 1250 494289604 494289613
    0x70f031703010e06010c0606330e1c02030a240b06030403050a0c06021b010203040c0b03060a090b010c0602191d06070f0809060301060518010f0804030e01020109051608 74
    0x410380050001541d040362080269518035a0781e031401075807046a15a01220011350300c04004c42c0c0c503140e0300d0801c181840c444104042c0c1421100c108102d00c65a10740d04410320000852100c160760b2105d0360b81c121341482561100c075134000d62012a203440c8030050024010070303540303070250f1120b00020099482e4010460301800710785000c0050201510040c0c07001f0340000d0301000a800d00300d000c1c010742c3e04424030601c8014948402c840044803104070340d005450080e500003061106006007100b003940680000c0740300f5451030825000150007280f580c818410f485031030740c00c42d50075680184c4991074102d80180080d0f540b01100001c1c84030078060400c05002207888482d100010710090705c001d15403c000035164a00c3c00595446110000f070b0784c001c084070110401c2003801140d03103621026500038100c94540d030b0703101c2c21400c5460b014036550b0401141000900540000404c0c1d0002c1a1070f002030f01070800d0850a100400100d000d8108000080c2c8123104111b4003c101c07000200d081c0040707070741304400d44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 494292104 1250 494290854 494290883
    0x501090f1e08071b0f140a0902181201060e100e180303010b2203030903020306220201080402060705010905071802070b0708060a03060f0c0306050303130b090d05070f03 74
    0x804000c52440040c1c0210001d00c140b400244c440c8400c822401c0c0c400008014030750340c504040c049601540c1203200c1e03000070350020340c41c1c5003444584034001d8107034410154201200028850301411a24612a02c03030201e200701c540d4480d1084d40440041d00d011040c6101030301e4900d1000d5581009031288030300c0d2101103000601a20740111a00ba4000c06002c003852859103400b001042c0c64100b540d914548003802844110396071017150b50304004511070b8641282c0d081c03079801014184a00201810751180e12a8240380b444028880d4181100c1e90909121059484900104096004500e0008d100750b285c201150b043c0540010450101c3d4403200700e41e032205001d0501c10050303018407440100054150000309000da806000e40990040c0080c05c28160103690f034070342400355802c4240c3e04018507030f1134000e100100c5d810702075103000d00750a034015442d000309420707051b15140c3c4501c1203451802002c00c54000b1543d88039041da100c075420500b02c610186c0c4480c3c10007466a254842258442c2126940c0e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 494293354 1250 494292104 494292143
    0x906160f11030c090c0a11060f010311010c080a0c030e09040c140f180402030c060304030f081e040605060103180311060a050601081f03060c030209032802060702030304030501090f 79
    0x2043e48140000c1c2649815072a800c18620301034004041c000d05104003c1c203000c98443c0100300e0581704520310540742c0199451414100310752400028124100400e100805011801c01401c8034540340030f0740380400381c10801d170a080320b2104210704400da20555010601c8144000911250b068a81504a886084002400308480800c0c0c3c2c00629400c204428040b080103509004c201d9445400a01665002c4030000c00103581903108032801c50229a50b6030f50301074000d0303004240c2e0358030425280444420118600c011260380c60000c000a141c036881d10009440742e40302e41c10102c840d00d90401c0d084078001031840c0140800c180003035280510700c111000107403802c80c503009844c0034910685603000d15494105141e0602407080b8030b008485401080004001103443c8162002d604285c2d4005844820fa0783c105820508403140100c103000c00319841e0040181d5040781d11407190760480340c0b241d88034403610221741180038070351016099504c1e00c40510207200b91f43e281c0300c0c00d1610501c2516009411840c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 494294604 1250 494293354 494293363
    0x506010f050d020f0d0605070f0e10120f1508030c0606060909060d06090b0a0b0f012307050c060f0301031a010308070b04020d140c0a06030203010b0f0906160f1103 72
    0x5042d502020000c2c10340003500f04004601c0c0c002c20040c01107112105540c507040191501611742d180041c00040403e062268010119034003080111001581c0e07003a41700c1d0044c1041105821200500c4d035070142c420a4240681c40280c00a6082084440e081e40c1c03243c4141e00d0790000404044180119000903541d482e0a0044408070803004090b032049880356014420407e40c2c00700c0454206544090f0480450740e5483c0c48c6120710b00d9003902044040f5002c050116040c45800e101d0b06020011441c0b4240d07501140c4201000140b801815403954041d040141c42c140e060010709030404000a0740c40b0440c28800001c5050303e0003002050043e15500040e485c00090074800a8038410b02400078100080c40300200c4c070380040c0000c0c0274240b1483d01c0e80320030cc0d10016115000038140d0148001d27015509160415100801883c1001c509640c5001c200940f18402ca03850f0344d40c4074900241300791099440300151109550f100d20504e1003c00540f6080030040300c140005e0b20030700500301000b041c9240000303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 494295854 1250 494294604 494294609
    0x302180307080319170a02030117010c12110d050f01090e2e0915060302030d0306031106030a060e070c02032a011404120b060901120b010626090102070506010f 70
    0x110318144c401d0f00c104444a41c84500da4042001184a180c2807041c007000b414001c0c0d0340c6440040c2d413545450105d0b10440c100003206569641010806442c082d0840e19010f5145040100070418180846042d082881104944031005207890240a9141a10032106068400b03268007040f0740b802c0c0d00c400998400f800600c00c040c140744c24070036110b4440f078800030500000303240d0340124204010766960b440e001c0d5881130043c48240d07078007810030070352a00b049051010452810100031082c15038460040110340303c41e101d030264000201041c0d11015942c04100244043d00e180007141c242043e0040220a030914160310a1045040610001c45521004900c0c50607602e12040b507084900c0064691410485581d024008180720010b8a500391030300300744119100e4604c050a900e01442009103603e81070304036840444101003440002000f41c040b06064422030308018503003803050a11802c0d51001004401b486204000a0111016054001e401c24520800c1034403484d81c2ca0381c01c0d00031100500d2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 494297104 1250 494295854 494295869
    0xc0804060504021f051e190e06040504020706020705010b01031506030902030a0212070305060c030c04090c020a0c120c090c0207030209040602130312030e0f0616050705030403031809020313030305250302180307 92
    0x74041f02540c42c0130b00408121030b080a0061820956a40d00040c100c0c0c01c41c5006640c0e60350006814020424288079403042c4c00c84c02d007403c0026903c6120710802c0f070041401942c0605603201440025075a04000325602194010030780429660094a955102c0f005888101c0d014451840441c51300388507417040e2841602c041004900380b070f141c4200c100140584051507425030180c1c0000d034020848084048000d003900700030400c0c426116103041643c0f1011584040216850540451784155000c503001d41240c2d0100c84e001800e8071107050000c000d206030340021a080040c0c1000004110244203012041085500c04102e008031a420161300c424001e050000c241e006400003401403155110f42c01000303001c0307140c000e00f4021682ea135146143d0068100303a000c94035400301c40f41e100314000c00c900003402081d4011350560505d4020a544240064002030505460320000766400c03242e03c0100c40544005020402c482044440140080d03100c00188a011002c4001e0003100e070800013200c0b4201c1e00c50 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 494298354 1250 494297104 494297137
    0x711040614121911101407033e07050609090f060a1706071706012709180210020a03020c15120406050a2409020a0201060b0406020f100c0804060504021f051e 69
    0xf1560304a44480840d00c44050360f240d0b00400e5100d100d000d00c8150301c03000c9c0d401c40c050541402641010310b0705425501041c440d0328100841d060700d4540d01c0c11280c005050400c4410b06441c0c50703001811620b060f4012010300c2802842803200c9000000d009030041d02c29071514003415038101c00b5074210182c103e4030b1a01294416000d20000328103605801900d580282c804c105940c1c80e1800c92b020b807155028841441ca991049074010b5240200c1303031041c203002074001004501e0b00303644c0c065100c2c40785e414000d114a051480f4031503080308d244201da02440302c0305c603110018a8185059001050306444403610149816034a04400c0d0308050810201031401c101c00c03e1052030588410041e40c007042e103000865403100070000b9030341c800703002803c00f500e041d401411326521240d000b030703281150307030b042640340c05060075103544c0502d4010000c16003060300100041103070760f100d00224a0a80e05056074403030440c080420507680c1d0368894060803111032030a0b480510344d43c403c03026250500910400c903003461803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 494299604 1250 494298354 494298367
    0x20a06060e0c0a082d010302090106170c0c07051f120209031b0307091404051002090a18060803041715010602030a1107120807110406141219111014 65
    0x80c160715503110305d00035141c801920a400c0c41c0404400c422215100500c6864010300c11071074a1000280903201a1400f489078804c1060b04482e100d070003900400d14100c00142c3c0880800b401c1c00040050017002d040d02d594071800c2c20fa0321103581c80390f904003400035800c14012000c00f02c8034000c9402c28540240105401440b89081c010418829528940e0512606d0000103040350b00e03000b1406804540d10301d180b81498103007002420f00e40d400602002c02841000943e500740e03100450201950f400100d1841140705d844024801000c03140c100420507c0003090004400c0d0795148441001441c800548504048046c60412607140c01e00501026070014001c60424510a480003926040c944084801c0d03c0d1b40d9020b07510081c5000d09040d112401c001a084040c4516681c608001c2c040984040102c5458010541c50042c091a4407900c544240204890010130410180c0d403041100d00d21481d55400f603207423000f08803082616080c068101c0d102c0310340b80b950052600c50002c50040205618080c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 494300854 1250 494299604 494299607
    0x106050d150602030d0b132a0905090408160c0b0d14011d1b0a08071106070807080901111831020901110105091e0a0c260a03020a06060e0c0a 62
    0x1b82c400c40e40c41d00515040604210580c090082542040900004a01c21501002c264805903280b07585d80040c0b210310001000b060710b940c10241d80c89500182400c0c0c90303421040d6140355a5151420140c8210302800f00401c032442004000c06460140020801c1b56a01001407521100402d100380e54859400102c640200c16101100c50f07444245003c0300840000d4100d644603e58004130f207030303400080d140000c100d41d031030f0816400140707503051034010080c6150407540208a5800140100108205040400c03c030400c2504516001c1c5145004252a000032070707400140c030107502d40312600c20505400f4401040740d0499051301d020705941003999040003440b201d800650321201d20181042034036503605541950a220b0140a0a00b40014202e11102c2d144203040e10407a5603004483c0c1d03005610800001140000410111007045245841c013400da44a45850608120882111743c0185c580d01d004040c1c2c0410380c4c095561290b0810821140c4076580c4200c035010885400c19004410003590341e059 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 494302104 1250 494300854 494300861
    0x5060a050a02070206030109050123100f02072105070e070207031209050a1707050301060602030a08150a29030c1605010f0f02040f1d0402100908060106050d150602030d 74
    0x14281d42400340c40d10800358040703603da0744240d10100503141c0d94001485042c444c0d03542041542c001058000c201c0284c0000540d550421181003804d10914080c0100769074000d11445000f000d8103582c0c0503c03030071243c0700103203900c81030002100c1d40d000701c100c0400d40b0360592590f18000d46c51540102003160441c0e503901c006007070014024050211402c000907a5030b40c1c22000c80094915100c24041d0f107a180280c4070f2501036607810451183e4100001402020380c000181c4003660356600e026a11502c0303410f04008040f40c205074040d00980c0d044008601402c100103807070392121100384280e846820250003c2c2482c08199140040b45400704180c01e500701036200bc494959004400000d980060420800201c1d03050380308074035945030040381c100070410b456001000100400d040328114092601e80c481041c1e41e009100030704c1042600789641005200b8865403000e05003000440d07901e0b584481002c1c00795000700b800580d8807420f2515140b420051110464211441074000354181a090884600074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 494303354 1250 494302104 494302111
    0x20705060706090803100501110a200607060e011407020d08160203090306240f0603010e0c0d02030a0f050601020312071101021629010305150a090213050609060d05060a05 75
    0x82ca468900c01c5002c12441d000950141c44c46c243e000c48020b24120000d0100c03800c80c800b403030081c1c01103403101020864103601c0c004081a00074041c1007800d68100000c840c1c0c017402c000906030038a480d0000b4004c2005500601b101c1682d0007851461b90f40720001266200e0540c00d2050026000001107402007600d030018242e044214010341341001a59000700b440c145d01120301c0001c251001450808190b082c4440126440c0165024921007400c0e00104020303100600c1003500c0800220001403109100e04251044005e4a1006545c3d9040940c03181010380b815504c030b0001c003072500000c9002d940c00081100c10120031020b00d4401030784c51010598154036144005103683d5020004840d000d801840981401c6101e580030a00280c01094221040f5041c1c03000c4a8841c04440010b00100d040060352804034040070f40400540d42d2507900b4080640400540250440080c0c6c02545440c0507a0708028860b51080d120300c40c035641d4440030004424190304016083e608400c02013401e150840d04015403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 494304604 1250 494303354 494303363
    0x2010f0306090c08010905160206040f020f030d09051005070f030804020a0b0a0903150c050d05040507180f1a010c110a08031201151416170f1b0307030207050607 71
    0x184582d03140b080c1d80a44800604443c00101c5201c0144038003203691064a820821101000014440144001c1d549410160014150742440c030a030b0002c550305e0300030741100b5020240a89000b22240038014140f07100d0750140d64814518907074110241c81c03203a001c0d100f1140c1c112000d40d800c4145610240c50608004d0026070b00324403c0c2d0004034a0740240b60090458010655800c041e403455404c040a4002d044510b881c5880e09000d001006603038480c00342c0d4000768841d800050540c44614259150030740d164042503000300b41c2030042d8611541d036032082112859905062120300c3d00d4030024145400b1402c4190701180b80182881d021856402c810745a461000d803002c1c6056407500388080c50340c1c00c422406021008a8001030110544024580001880c82c0c204150003090400c180402c41c0282130003d01c1003d01c0a0a04090003190000400c0707848850311b01c1c0344d0f528482d4090b40304580c0308100e40b40d18600504a20440b0320000400c540302d4a415034082c00d01c144c14a4104401ea80c001c140640d0b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 494305854 1250 494304604 494304611
    0xd1b03320c07140904111815040506120718061e08060906010f0b160206070524060d060c03180302030301080c1f051c0212010302010906050307020c0f0a0914010918030c02010f03 78
    0x803582d0034410960095840c0c00c00c0b40c00708e0020000f004180c0318000c240c0d46c081c8811401c0071141c180005140002e465000030340008010a04a0340d40c000d100c80d5120105c110596405000c0b0f50506012a2095030710b900180c58507a522000c034603035141c42c280b0440070710f9590f400080282d0710f01301c4c1c00f800503941451904406402c00d0b030001401034020303034425030312a008011801d06071a00110106008404002c031202c06d03203040701c0003d0075510f030420043c028649910481c24603a00c03c3d84191401e41c04400ca0032800301403070074029540d0f0000d010368450340c425130640c22204d00d0509501080c10a0868640040310064002120b40e030b0805900ca101c032040285424258a0550014018500351209800c4031503241d40001014080c0070303444102808030070020720034559800b090f440e000da00207035002210400648007041c092511540890542441c003180e0012841c0c82030b10180c121205902c05008001c80003104054041c0f103610020040380c2200c280700015405000b000050185504000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 494307104 1250 494305854 494305879
    0x2011505010e0a0509010e060f0d0b04060c1e0c050c060f040b09060f190306091109090403051902010501090c020f060103030c2102030a020d1b03320c0714090411 71
    0x380702d910003070700150070071428207080107543e0030a000c89e1002300008540094000c002a00c546d2110071380a48041c14032500c450782401410300441c0e1100c50f1080f800315520400c90011790040260020000c01c49480c003440d05090071038607001d4241c440054071400a50314040c0340c20b0324511940d00407414550805020301c6141704100203040500280d0811a4150b091070481030030080480c1c02d25080100440e1820108ca05584045400d1340c1c1522002e030f9034440f41c1d848604003502d05000b102d5414030841d140e04644c0c06090b6042d08400d040764800782c42030180c0b640181d0700342d07181c4030700c011161003960190004002203840340e01c1c030700c0103e80a4034a1a0428648a41c01924200400c039440d01580c40028207102c0d45178100706829103c003c40c034010380a40410384480c0310010100b080034041081d4031941c0d05403203804010020301c1002c0f00980000301c05510035110003642000c640102e4030b02a40000282040c020310131018030b814001e00e078514980d100d44d0307000400400700300b01581002000100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 494308354 1250 494307104 494307109
    0x50301061413110f0d0b2d01030e01020d0218060c031e070827040e06060d0512040303020d09090203100605070303090b0f0624030f07020a0b010f0501090602011505010e0a05 76
    0x2030940c1000d0226083c5d40f11075030250706003500c0110303078541e00421014071691006040c03003c2213105046000c40f900d0040000b80d0040b4007821002401030034035440015040801c10035940101192006841030140003020300040240500170011590225002080f1110030202030414107c910385d03100780f110741071802c25111b804650f04451200c00d4a8040d410043c5504a4109615041030a040724240450040705144980f02c45000c0d040038000c60030017441e03008201d01440008400c544040080c0d40780c903604d082c002e6956502050700f0300411050781d401f0034000aa0300071a07115a411400481c2c2c80c0f450302c0c10032601588842d006070b040503a201c000000140c04540321901813043e61669442c0c038148501048885982d280440f805074904000fa04105000c0405517640042800302c103e000b0b55603010107900300540712400804903a208000445c0007080803100740190ba0307081e03079400b01040c1c07210020790890b94508814101620103440030400c561046009411940d00608000c48a6030366102 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 494309604 1250 494308354 494308357
    0x60120030c15010801050402030a12020c04090c0302040513080915040801020a11010606020304060903020d030c08040b070611090d12110d020714012a06020412080a0905030106141311 80
    0x21415040c0c201400001d02c040240c00514050040c51000304100e0070258000f036a05c0c01c050000609281352542c0760000d0b00d0090200f8010700f14007410502483d600d910300781e0102490783c08100d10941c641400b08040c601c0214000203c2c81d030000c80c0500e0318140f0010807408901c80c8900d241c018104020200e5101003c0c0040e2400b05c415480d000ca00f5500c2c854070760309541d10b6410260465006000400c48140d100340310004890701691a40070300c90450404903031582d12410040c1c8080c6000900058290078200100740b114002c11080185402440c0d201499211700c142c096482880320070241c0c0494003d408a015000d441d08090b40324900c071201650400405d07141c0000980c0114800704020014140003091403102481c6c221120984c8421040c0840c02c41103940140164100c03031641000700340e50444003c1e1901083c3d80741489040e1800d000c3c180e01a008141c001078803d10005807508050248600340e8050007d501e851140b138209110364200c1c0d004000006503252040250385240341d50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 494310854 1250 494309604 494309617
    0xb06040f0903050c0f06070f0e0f0d03021005070504030f020121050a061703040b04180e03120411030105010f21140303010e070905060d0b190603020d0e010e030306012003 75
    0x2103d441e2510f040003102e50514522950442c0f0700d40101d0308000c4801e0340001c048500313110700d052010300003407940049100c0002e6500142d40011041e020307182030540000d8660068200500c0c24441a41c4400741198130b03004612004003013804428120700107600820001c00d410450f0210402d402c910015120143e0f80103071801098140c0d034003070a00c84400d010070ba0110807275064004519251401c0003105803840349105440c03154041e1800c030101e105458000c901d01d10080340403681c4440d10984600341d042000d403000c4030b82c450340d052142c08904060007800d040b03500c11188496450310307101305070399108450f01d1042e0520b02e040c1e50241c0040c10071402c070251144090001c42e2258100282004041000303490b0030140035041a080100e6560181201c0c00310305440f0011901040300c01c04900034540a03001c3c60309a004000e40411001d6256015211000c9100020b0000100b0540c843d401c0360f2401c0b0110265800c1007000840d65405031642c0c405c2c1d80c4800742d01d0a10039944441d000d04541110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 494312104 1250 494310854 494310857
    0x3180b03010609170307110d0b15040b0f0919020c100c02060606070b010612020c150402040c0311270303070f021e1804051e0a0204180b040b06040f0903 67
    0x44010301c00b10340d0010090010b81800240c3c0940303002c60350303013060b42d90003002d100912131003036014510710030b4803598281115940d11010100c13403414520326000181c1402c40510340118034007588090b10385010a0032495108015026100f2900c0c1c0c050320394880c00e141d42628065540800c8003d5031081e080001311540d1428441c005a00c040c100305c028205040a4080c074420309085c80803201142c500354416044844078108850b91001243d2002e01901071034507440e205004226100c443c0c000c0d05002c080c443c2d407088500b001141d41003071060b0202c41c4182c0905030200c9052124040d080b118543c9200c03c810300c4009062154078410009140d94844c840c101c03819903001c8128011420b21041d400e82e910501e5010608035581040410303441c4290205030340d5030300d424001040a211341484034079142c643e90002100404d4102a1a9944c0c1a02c264128005c2d4903004201d40f4908030076440d59000d0781e11800d0004152a40c0e21003134084000608496401595030350084144211031068003270b8144039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 494313354 1250 494312104 494312107
    0xc01060905060a0305030307050a0311030a0c0801080d0e010e0f0406080304090605090112030302090117181006062001110a0c020f040507141315020708100b0f0402030403180b 77
    0x10040c1100c25030300c01802c6a4000c4001190500000340080b0079203078003100503d0310707940307a0311002d408034007500e03180443c07c01c101000010f102985103181c018a011644640b120b05060f40d990107055038070f509540060000a00600540c0c00b150b200c1c010134042c1d100002e2034000300c400010300150481e5010f9000580e95800084c0800c03001c20305000b078800405040341e5a880c3c0d5850405452500700d420035005003055400200c1130701583c02091070003040350429480340c4552500311212051003090070b078103103068031070140c211115107003070b0142c01c4c2603410307555070480042203407a95009519120080728600d07540b01c51800700200301c01c0c005400807221903500c2d02214201e5006120102e0101e13120b290141d03040c0030402418036044100500320302c0c0051201c60307441d00c0042d0340a1401c0740c00e420140e00d51803400004d20041e98001446000e44482d04183c90f090318074101b40004595510081c5508139824003c0c2015138035060380a1030340701380203051440c040f003035914a8650444243c0c20400c1d59260 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 494314604 1250 494313354 494313359
    0xf0c0c15110d0f0801030b04060e10020d110c0d08182b021c0e03010e01050a02030411090114060d1b020f12180904052a090c03270c060c0106 62
    0x100910305110155003403403201d43c8507211006100d2501400081e00c417899050108080000d16403121002c3c0031500180c402d403c40d2000c00002075031000c0070f1380001c18200507481c0541e9900100301c1d0340c0681c081000f82003000c17041c10141c800c601c0043c144491007180c59040404080140f00000800c0d001d0800307a1640c44007415055a0b150602d0381580440d48074008007034803103150505440440317409061441001c003041d00001c0c09040c41b50004134195003020140b008404507a0040c40c0500e00c50341941c2d4180c1040030901411010900c125041100001401540346c2058401801602802c6001281d501c50036000d41614120031a200d00059205050795140380005009081640c4c0448008500e0800e0031071400c0e91844a00e101d55101e00b500c43e001c2030802104000010510301e00c0d04040c2c104010396a00c0620a000425080d4041c0034003000007050140c03504100c91144c410030103070f4020007698545105c02c010a100c0e40103001d100b0300680034a10ba0702d04010781695030b2080c0c0085152170 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 494315854 1250 494314604 494314637
    0x12020105090901090b01140a050d2406120f050c0a08040201180806040303110406020a02040b0d02030618071203080f130b09010e010b091005010507080f07080a0e010f0f0c0c15 77
    0x141d400485c200002c028420361031420b2703000007140e415009000000c59071090481c15803880c0b0b4051f0312009510750039001c0006030076030444a28a901400c1c02001c00c880d4110000c0001560022075029004060400c1400302982c05603000c40c0c0c00a0061500f1036214680011542c1d802c0c8464100c024158400d038200408c00d40d0502801c100b8400102c0c81c103041c1480c0c104040d40d500d14015009204649401842101e900c0e5419040100d58008003159101e0a2080070f800394200042c2c0745807424020110082041001a008165140d42c5962841881d07039a00c1c142c3c4185c030030041e090070301e0290002d40010100d00c89400050141d07214200016100c84000ca00034211340440f403155019400110070800c080100340b21003011244203013002d5594000520706403075944152410018200c00200c0d0040600113008043c10046445031100c1c00c0f50402d4400558100040c0100c0d440010080100380c41140d21844295038160310904150544a4541d14224170445401c000359001070703c44224095110b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 494317104 1250 494315854 494315867
    0xb101e03120906020705060702150d090c080c060702061b01050c13090608190302030d0204060c020a0e04020f040f0f0e031e070f1b08150603010c0504050a12020105090901090b01 78
    0x1038554105184000e141c0b10f400b81d1a80b02c13900c22103104920105402c400d40d10740e040e40c0a0840840030155170b8810a0008c110020a0124070588810f6060000490905400156460b130190300411090030080e656003045403076030010510410003040c8038024403100000340600c0740034006400800d270300c5100042d28400d1044c402d50000007203904004d0100b281690101d82c1d074508100c1d060054450b03071f038241020f91961049801c191045807002a00083c8294401a90102e2500c200c3d418840b195456409582200081d68003a51082e4408400c1e1298034042d80803041d402c242c050080b030480c1c00102c0890446140f181118444d403c0015602079003240704440d8138a0f950900c140c41e040901a455a001621172920014600000c4a20741454820004210f03030040c11003d08030f400d15224460940392014090b034129001e5030900d07091510460040056600703694000c1c0079952424a400854205502030090a0707050201c100690310050b21035214460180041c10b80c00304045049a00043c6103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 494318354 1250 494317104 494317133
    0x30304150b0a06090306090f0f030807021b09070c05010b100315050306091b030c0a03030c0c051212090f04020c0304080606030c010504090b0112020a020d0e04020a0801030b101e03 79
    0x140d10120090202c20313003003c841c0040e280c008400094030803091400c41014800241d02806c031035801004801096409800144500e5003903094895a008080e6418250501103103003690099000000400d41e6201d11004c2c041d082c010f500109035590b482000c0307146450100b0420b00000d4962110000000d05c110210000b404250001c01d0940381100607a0340360b50210024920304209414840f03500d40d010410304401d02c01c02440d02c801aa640c1ca00600340c1d1880c41d104464480d000390300010030345459200c4694592802c0044c02088910070100c9180798001302c03100e607101814132041c4d01203849500c080c143c23266404d8002c580d12401c00640c0b5240c15030003490755101e17510900c10000145d0303104060340d08031840180042044094080141e405007001da5069410a101103056a2060307400500b182c0048100d4030b441565030664410b000691194518810200d00101c00410000c0c80d01189a1740c42400403044178101d0f510343d103a20003c800d00200e00c04a80341c03c40001d0040c0b140d4100321040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 494319604 1250 494318354 494318359
    0x20c030c0915091b030f0712050603060a02070602270a2c0402010201020c010e0606040e0c09160c08040e0f010b09030c1c230618060109050601030e030304150b 70
    0x54038035102d001d02400c1140c1d9403407030b4000d81800c400700383c1d90038031201c2c00c1081001303000303507543c486c9042c82461031201c104803050030010305a00e5100700341034030a00c03c05000301006030240c05030341e5864244101a6020603070071201c0507420405490142c04441806100c2e0741c90701c0d42d22891078000d4040048203204d54000d6240c41501d82500d10030012100569000e54a403c2001106075a0360b00050340280101141da0042d5400c110b0f0762184010301207582c51050718111007c000660025258550b80c03000b80b103106030800c140c50701096100384018402d4410340c115151000c2e1114681c2e030703038071016005130b8064200903e0300300178040103c01201480d03001d018a0300f0080d050042d9840025952151454801c0c007500c007040120518050412102c5a065003007041710005200f80820791701301c0c01310085d044500c0e001c0d040100301210a04001007419200030001002e02e031b42070202c10001814041e03c12814142d40d81c40010500e20148051446075000344070b420100c01c1c0d0101007005032656403440c2c83c07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 494320854 1250 494319604 494319619
    0x2208070302070b1201060318060c03050a0f0209090c0306040908130e0112030507060b0123040e130213150323010f0e030a0c1106121806070c080a1707020c030c 70
    0x8484c040c81c0744400f811900d161034040350006110003103440b000c000344000b0741a80c2c20b00000c0d200094050b0807450040d4101c40e010071280c0c01000c0248100c0c001c0d40c903610343c469806404129900c141e10040d43d000a001440000e85c07071056a00c04909a01801d100d069010910400300160b0103070144082c0140040320701e07215006510381d0010b1052040007001002c41e581e81040c44030b02c0e44206010a1441607039200a9514004611600a5a042403007180c40d000111000250004400d90020800681c05041440500c902480d81d0025007201c7c01884c0e00c50112000c0080410809040e81c1d502885070404440a015106203440c00e4940f440094484117050a003494120000002140c2180ac120310f44240396120502d0004440200c2c403a291354851804600381c0f00c4c100500440c4e50040c100d03503c94915100d42e13518556103c20003210707004c0105030054008000308030f80a000b40800c0328285484404600401c50b07440e9204000d0b2440d800603400010411440e080c104505141c5100c121040c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 494322104 1250 494320854 494320867
    0x15041a09190209150301020a0306030b06100c14250806090d0f0f0207051e030601140303040603020a211a1e010f0203070b010801091e1a2208070302070b 67
    0xe4408209074000030700462040d8000b0740001d800304038042801c1e00040c000d42d540c2218610007406000c81d8041583c1592145000c25020318110b18000d0003038441da02c40c01c1d410b800c01d48407555801038880c2140414050381c15054001c2c480c4604000c0a141c4603e09041868208101c05140140040c003169096001c43c009030304060700050b0170b1610500d1403030034894420b01c42600328108503003548050341010014030303e10501660280031492500041c2c00b00c404907070b601d01c08a89446000710110303806401c20070041c01210710a1b0000c0000980a00b0010b080000265488109000c4060720508407603030350054840c288413121071030605c418219a8022286200071004000c03050201c0c00c1814400c000760303901d600034001c0c400c3d64200c98001d400300c05503617501d2100e18080c0c9004003040b00c031581c0c0c01c1c100381600c2c1c9000103460001900946046031880c003014121000c2c000191141310307610856550000c00a0880d6400c0003013900c2003a00035140c44840c170b0040e1411089821403140b822090040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 494323354 1250 494322104 494322133
    0x1805010908131d04080a09030803010e071806091e0302090a0c02010c03020a120c0c14210406270b04080109060c030504022b0b010603051506090105070f0515041a09 72
    0x403150816041700c00940d5410328124161030091066200800d00c0700080000074100c01208550b0740f00d500f01c0c0e110700081c10360b833900056660342e982c0200d0000c5202c1385810b0001e011285210381c6900d80c9031140a03122620794000429106003240c101010342d07203e0809c5000380b0350a0150310041d410b24101541030800740c0d0005000c0a040c3c600b422085641e40d082d00d8040c5101d80761603c074041d00032148110018020f0321540d16060400061220011040e403c504902480c038100c50407a01c00350750340c0c0c10707881d0703031a0150b0050035078001c1c1d58005180106c008218101f10000600062440e4000003c40f0030031850070740c05984000b188501490720384020007000d602c81c0003143d81215200305801c80c110144401c846006106601c3c0640486584800403901641552056014504c8022001d40c1e040000b4100031242c422404d0482c0003510500402001070b454810f040002446001621100203017011090b90003002220142c03003006400e602d807005d1031000b0910321341189100c0013a000c0e14840e01326 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 494324604 1250 494323354 494323409
    0x1f0f060e09040203120c100509162d08030a030f0e0a1e0b130b060415090e0304030b0c040509130314070201030b0414061003020c070603180501090813 66
    0x1424041c45a410019003190b070b05000d985540c07080c8500040d01c4080c0500780a541d200320010b0071014074903010115908200000f10010003502d101102c480e52400d1828117520203907000074462501c907054540714040746000c51503c0252403803d004689030852002e0090660b44807055910940d450030007400109903001c10340700041f90b0003500d800394005800358015070780c03148084043c000d01260b80034020142901c500890100e0302480c1141c1264550f40104000c80b02d40012183c10800d40c0541084240d09982100050100c0407003520300f0300750b498680100302e00b4104d8200c0103008000500344010320700404025000000c07220a40d903006900e5078003030001c0041e0b01140300c0240f40400c0c0700d0116807094014049042c000303441808100f24280c1c1d04102c4160a4607424812007400310419a050320070303c05d8a041c0c071500341c01018550b04e000000d0700240f0007100b080103a0500c1128020200300240504070449104803141c1355580842e0b00811048949030304000030516544820104c0f060340480e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 494325854 1250 494324604 494324627
    0xc1c1806080c121e04081b0613120e04060305030c010e120409020d0605100e01031b020616141909060806030a0b090c100806031b130207030311031f0f06 67
    0x81a10581d034840b800300ca4502141028013101c011400400c2008011640e0050901200a90002c80040000134203007500d994040700d100341c0300750380f410100020540c0c4407503005204201e81010204c40c4001004681a1080c580050354030741d000140c0e02c001c400b03003481000421001c03000030f8051845110400703a4548113500c502d0300d0301500400c4494682916520040081c03c1c018403a10020300c02c0440944800d917800711050100c0c2ca00700490300c400100c0c210540400300558094201035039469041c4220908051421041203242901e502c010030941c802048280d40900c3e110f168400a210028110030a54125504020445044c4680342d1030003d003080303e096224560b46031540c1c0b21040d031490302c0140c0141c21b500802c070741c0200c00400d80009142c1e020f4ac00541c141d6608010a1807d101c0803508031301195000b031402103845141215660142040da8864500426442c0c00c09091070111380054070f40900100c5108001c424074104181d9010040812500282d2400d01d40b00d4050403421286 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 494327104 1250 494325854 494325877
    0x50307060503070516120306060e1822030c050c010306031a0a090203011127091b093006060310020c12070c050a0e010506030c0c1c1806080c 62
    0x480800c0c0b183d4001c2041c1d4402e6103103c1c084c50f808208505110f8402c100d120b036454042442c081021403050f1241000c03500009014009400014006032a45035403400142a0500407030344405043c0c0d190a80581c903600316003c0d542d00c000b0002142811801e0078942c0051a060518041c401c0001500c1d5048690490030b12450994040d0f070343d407a04002506002c08029455460301c03040c04050008100580b180c00c1c0c01c1030751140c80c04d01d200f41c02066542c1d502c2101d503102c04942c0008206002c0d2440782a100c0750003940c410b04101d450000705504841140e072416018094075003840a14402d140352001c1503400100501e081d0516501182e120503046d10704442e0542c0000354107900d03560030040d2107640b00062403450b40c1c602145c1007410301f040301750290a107d17180591000466601c12110301c0d041e00c070000c3c1824910344031040100419444041195000c0c05140444841d101e07410a04000c201d040751180c1c040c0d2142c20001c41e2200c002c3c1d4000c0c005201c011002e0000c010f0480c02503e500c03c1e0304 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 494328354 1250 494327104 494327107
    0x1b08090c0a0905150a08030a12090b010308030408160605010611032107020307150542040b041406040c0f051c020f0304141c4409160503070605 63
    0x89013030301c1a05249800001d500407170490000101380034000010410309605030740d003000300034040d40d09805603100d085019150b0040761005001103041c16004541084c03050658a2400400c0011110004403081c0c080da01b4943e00c0300104031894218056881e10711045000c3c3d45080e480d00014a4656048040c10340d0303144a600004100e0760081040345c0f034075900129a90f101d12500c442c104007801040b00c41c58111b45134030710800c0802500381e81e0060030042c0d030680c01e12051103600c3e8114042001600c0c10358003c2d11135140c1c05041d1074038030688640303945a400c248030b503240c0348081c401a02c1c0000581805c103c44001d5210354070f5401030643d035600240401c0035060280e44a0301d50043d0081104009401100106200c00c0150002a2401c0b500590040e0340c4031422131010354410004409403100440c0c00c1c00720000c0002e6401d89500003010110f0103001d0034008001011085d0403002c4040a58510070b0001e0184d2100c082081c0864182c58120044005080801080e156107807880b844051150 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 494329604 1250 494328354 494328361
    0x1703191e0c05010e150108070603060f0e0601020c0d11041508030703030e100e0a03090b040b0d020c0a0b01090614030c0d02130e0a03080411010c23101b08090c0a0905 73
    0x20f401414848207131900310351008101c200b5500c00c4550070300c261502e40c45001000a8441c3c041c2c00303100c0031625450011320b41d0510b03081c21403a0580000b00703d82e04502a10f080440140c2c0d403000404800c0e40250349035007089542c5030500044507c01c510354110700700a624200100c142c0082100c05141d490714002c101000b46103401460549900000d44403d400e068290032540e03000255000c010b0700941c1c407107140513a00c1010038002d10950242e03801c0303900e080040b0380f400e14958005000d2072911408503090160107882d503100d43c50081c0c00600c1482d8540380100108800e851000d840558100c014150782c02140703000410030f228030030000340100c0c09a1040c03a0000c2469100105a80c0001c0c1502c2603003444d441c1c01401c04404072001c4410f001c00c02c0f0b9003861717540300319107451809610003480c601000c06400c60780072004c44070108600500c9681c001c1c3d04c00d0211800b580708545000100c08075040d02851000e824010b0050a05145521000010310581d03030b130351861412145c1d5a43c0014090302c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 494330854 1250 494329604 494329613
    0x90804050d06110705030304022706010509180709051e031b1305090a0b1302030a1704050a0305281502070f080c06011e0303050d05101703191e0c 64
    0x962405550004800814844d050190200081d44914421501e030484001c0d0015408a84c03c4503105a900c0035010400103059540200700a000f80c03500282580040c03008000710101c004800c40e0104001505007000b00000d0070074404400d0b20041e03964030f4125191724040400da82e107502601e0381481102c00601c9408680f24401c06000601c1012070a10a901d0030150241d0307541000071088408402c03c100180c4010781013014611100c1d4000c003d030540050503200c0c0c40e042c0e04001401481000200000078842d40d4400480000f944900d01a00b005081040c0044070004c07603044a4041415218480d800543c0503120180413940c003040c016210b4075103041418107000204002002c02c0c200048002c2d41810005071141200c0c2000c1c0221803144203c401d07a00c106045100003008100c1c20b200423090800c0c0f5800403503026600d05000e10740035966894040c07100c080da084511040e080012a0744900001903585102da02c03050501d0705d40044000408800a40446c58010801515015034000c02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 494332104 1250 494330854 494330861
    0x1b050a0e100512040f110603070206042a0e0405100615030e031303060203040b0c0a0e01050304020d020306010303111b061b011d03090307080109051c02150115080a090804050d06 78
    0x442154894511a203420b240902490076000e2050340c00500c45144041b4a00d0300704222803081c82c20383d010b020142c565a45031402403821164041d16a2114120b6a51045801201e58000d00070560310740000c1c2000d042c91810000d5104070131003820f0038641c09000c0402c02040080340000b10f850009800e0943c3d0f0419400c5001c1d100800c003001861604c000180f00ea5600518010340c01030a140c24640c451260b01d4107140300d04002d21010070b02805d100c01123580541c0c09150f0140c00030700b00f1703448540030fa40000d0806000740c000314082184080c40800c3e108081084450b812030707480d00d146024150f0b1001031518050079840f156070114611840f075114500707410040b080c0d20b08402d080209645c1d9240a610794100700d0000340280700e80d510000d040c40e0140644008039070441c010b8131101d81604088130b80c0520102926041d84588940b10851054550a5070700034080744039100c00304044000001d10849000d0034034200341d400c0c801c0d5240890700e01e50890f41141c04c01c6906120f003082c0e40c0f508a000c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 494333354 1250 494332104 494332117
    0x3100302150424022e0f0501050108070e041508160e010e010909050f0607020309030d0201061d071106150108010b0a0f030c09030807050d0906170402040209011b061b050a0e1005 78
    0x2001c040d08103000d03480000d04031710301c003240d0400403e00c1030501c02c1c2d003020b003110001d00c075850000354a040410121402160740c0820b18102030404910050882c1d00c407810240c42d070f4069007681c0e0224080d0880b0704141441c245c058020594070340c0c030b10351501009119850042c080c1402003640e80c0005410480c0c02c12038016400c3d07040c0d065074104e160140c0c000c1d40301e0b04080b288501030300400100c40701851041c850b020030344461240c2280d08030394036240420f2040c0000d01c41024041c07030002c0d58025803c20030002c1e00c0340c4425000ca03c10303844007800041c01d00c0b406a000500d5030009010700303906150080030076480e401c2c8500e0000380447d10300030219881070b150760010b880c03480002080c5040c05401f0070203060801c90303503d56581d104d0f5142d0381142c020b05a168200401d070044808600185055001001e42d4001494850130960241c04104008824840c5c21135400c4c0d540d200015008020702c419190880f141c2c2403841c148005000040e089040722290588605112064174104601650540e6103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 494334604 1250 494333354 494333383
    0x30304120303151205161a0d0c05070f06020304060f021206040f0b13050a180507031407030c090203040309080d171f03030f02070b0708090105030a0e01020310030215042402 76
    0x2050035003800d0258842a242c20040c51010301c801001c80c403402250b9006a102e40ba21f54094601907201050b00e009040030700744681005000c0140030041010800080081d0740101401a600d0030149010400c8a8020040d2034400340140824581c6401000210360300c260141c5010034030116030000d1100502502001a41c40403410702c0d60040b01f405c991149108528140d000c00075410301d51118120030b01d20510090580c2d001c4034040c00010791880c0340820303410038241103c199a4481e622100540c10301d41141403140d90100c00c201c02c1c5030344000100000d14140b070250009610347c032001001c029080c3c03d090100c030b4040380410540702c80d5401e00e8481c50203140c400c001c03090b140c4c13900400c00e501900b07d80c0014810f00710042100c82100c0e040300d070015441080b01740341c6480d00005441d0364100821100c101035448180c0c2884a0003030001314420b5003000d0f20705d80001c1c11841000050701ea00280000c010308280300502001d0110840d1480d5030f10200d51001c00d100900c1c2c02207141c1383c905404000d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 494335854 1250 494334604 494334629
    0x41a04110a090c02190503040315020903030415021506011b21020706090e01230f04092a0f090b21010b090c0a0806010e0406030204020f031503030412030315 69
    0x10301e041c0300d0340f1114514030103070b00351088812803814170000d64011801c080c01d1a00100400c2000800d108851207000c10362410250404c507030080024190b07002507004a0781d001008074469982036040c04581c0780390300003c886103c0d50400800003482d1070208042000454501e651082c14032011a105c1c50300588200741c188840f0f111504000d481d000741c0c4c071425011a0306108081420302c0300342ea106050b80d128968000007200c118410a500c4a160300d0810340140324080680d1160b00c680c0a280c0000340034503c1c1d118804200e10072540f640a07141110005080995424013500e442203108408581c4d066102085400c1c3c100d0003e008a03040c0b0704880c42c90840240340044101c010b40020000120131030340180f00340e0b21070100780a184115001400010740901c00076a981d07001c0c410074011003002410000b0030341e4807540880d0403a80000401806001e0200800142c030004090071204c03d10140c0c055070030240361007814400f8611400c001824561a070441d005100956102680102450000356 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 494337104 1250 494335854 494335859
    0x4030b010b04171207060513050609160b090102030d0b0117190c050a0203070303091401090312050105030109080301090504170711040b0108090d0c0f210e010305041a04110a 76
    0x44129406842007403101c10401c0103940c41500c010440c890031004a55201c0d2a11103d9546c0f440103200080181864030507032100c16011503802c214007846292000000c16100c8142c601030800c041d00303548032540b40c81042020fa03220340d0740441503034451214000089810075942d001070b589401681d0b02c50030702c0500c1e001000031440940e884051070b500e0b104410407052140382c1080b901403060307200d00000359004106500002c0d200360720000d062802160030700081060038004509559840c10194002095143e401c51a030341c40c0c2c4566401004101c000300b01c6414540e850311880c0c0014428044020303074882c001010312000b80c51400d5030000d003400a980d9904c08d80b52035410070114196060040d8500380402c0310383d5004200b01405030403224010b010f4040c03c20001c8440105143c4100c40d491000031a1000003044240d00e18808841c0251000b0a401d4400c001021105100411410181030600384004202400f407002c00d03511000c020684103035a6401c04032842c891030b250f0f0541100112500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 494338354 1250 494337104 494337119
    0x50f090a14280207112707020a0c0f050d080a02010603020406060c0b060103140606180d111507080a080405010e100209210c040203180f0c0424061404030b01 69
    0x2420204441001c0c41d0b156240c10315108901600c08028100200700040076400d240501904800070910f403a10540301301e01061603520700800f41c9100001d80d0011001404003c922481c08019000040c0d800413502e1900340020b280100002d00540803c500162040f142c03403003074212002650300980280b207050743e01c4400030180c510b2410151010502c06003c40c03c5980310340503213a9103104180c1c00752003580310a420080390380d100d10380c2e01d80d4202498404044c1c036250b220000442ca806681d451804031043d0b01800309500804040ca0011102040000005603054081d91803081403440e211789140e850740751250040251000d24222072184c040c10005400342c507002895200000c0c1e03145008407007040d110803914480c00c070302d9080d40e81100c0c40d8070000b41065400785500c00f1400b180c1551117103011200a040c01c03041004200d1030340000340400340c2070600d80200c042c07808034030441c05000035554162521880c0342d40910010400c80300c041c089481c60040940b0003070758002580c003c040d60f40e55030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 494339604 1250 494338354 494338381
    0x619020703021504150b0d0f080307090e0c030403020105091212060114130609080a0308010e07230a02010510030f03080709090204081e0303010614070f141b0a050f090a14 75
    0x2455000b800c090140046d41004180580390f0b541c0040900c070f06620311390758000c080d04000e081030100490a000082c3c408080807169001e0390424400c0d17940c03814a420001d081d180b009103801b15030741c00301d40825203a102500c1224498400c4a40ccc030511034403a01c0c01202c0c03240109007880e950840224034071541c900d4902207130088407071075104c0201403a40c40c84425240c1c00056006408140214010804e102c109990b0b150700c61004d1030100d01d5003d218401c1c4c40c0701e00c12075161a0307a0b84004110600f520b074091140703640140040c1d4014001c2071465440403080303046c00400500308483c83c40400c00c0305000f1208500a00310b840d40c19512240c859019661b203204440300104c041401280c0a81c8810000c41100e040c0c2d074441e40d51741040300e50b0850018441e80940d8080f50111402c1c840328011900c044c80c1e074441414000040c03ca00d5000b108800c04c02c2c2c03c02a4030b0340c422507104038204144c0d0340c0e100c0e00721101d84054840c000140c0d00c20112000070f01d00a083e048082e0000b400b0003818144034107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 494340854 1250 494339604 494339633
    0xb03090c030c2709250303020d0302090d0809042901090e0103030e1005040b2709090601050f060c01090804050a0609050303030109020912010c05090406080619020703021504 76
    0x604850a110140342048100050341c04180c100748000c1656000001d620504141d008031100211200a170000840480441c0700250786400c00324901e40500030160305001e11600202d1900c4e00b542049508000a1840d0080c1d00c4010148074001070403210a4445402410400c404800e1031262072801c484001c2c1c202300d524410b0b50000d40400004175105003084602c0341a41d0300760b92020625101ca9040c0003a50394515420f1040c0300c801d000c0040d4400d00e51004140341030314a0900d20301840b82c40c2d100c03006c1c5090047d14500c26030f190401c02540c5040018424112003048070707441301030340704d40b40411070710301c40d09041909650802d150360061000d448000c1c07003203c0003690030641c100c0d40c1701c004454011090150350740c15013041004010030045a000703402e20300703c001c1c0b440c64000c041c191b01e50b0860b040600c281010900110f10074031103242501c10f034002490740b60301600403485c10081c1580e403500d00c002100305c083c0d070100c2c100d01030510030030800d03020b0b99020750344001e00d00300b0303003800c2107100c0100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 494342104 1250 494340854 494340859
    0x100503010e01090b06042004080c120c0d1704030803040c060219030f08040305041508040627140102090a03061b030b013f0f06050609010c08130b03090c 67
    0x2590090700301c20520030041e2054100c42840307965141e035020071001c0d00365846102e03090100c1c1d20320035214a2604000b08010a405001090710340c0d44c2ca0300703000701c00643d402031101640000603052259211110b04804d11035000b11040b00c1038403814446c08071401180c002410b0150b01004100401800000d22401d4030065000c495002a5a1950000c075990003030004000840507444c505c00b03d402130341504d4006119040003030409403a51007600016031200111000100c20400303201c1445030f1341c411080d03880ba4a4866004e82d4441c05005040403040000080180440e070091400644080d03042d40c214850003802000000d5807814071002402d250a9000318074400780c0600b40202e80280315001c0d0031101038480f85d00c401401e400c280d2580d01d0004c0b0303403201e040d400c50240441a9003010703001410520f18070000b03031f942000104a0210f032501c0d0003480c000d480c108811106a170b00041001e2400303500810503070340c80c2e4181400750358030307403d0703501940030800088144500d11301c003c110028601020b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 494343354 1250 494342104 494342111
    0x406020a0b0c0c030d0506030a020d0f02090105040c090b03090a0b01031b0503060114060702010e092a03220510020a03020d0b0307060e010f14070605013b1e10050301 73
    0x42642e86240781c4629191a80907074400c21001d84084869040154007803c01015104c0d1204541c000c41c10355111346d88112180c100301c8101800318601950b00c0c9015180a4804000310700010a006c2c1485a60340941c141c0040c0200015020782c0b8200000d0341e1580e44000916030f076596901e058004900d0854280042041e0702c1408191802c002800504030388610141050030000c0409000d500d501c00c03101a03041214403040b5061395280c1001d02402542d00c8045d106040307400c050310a02d0392079214100f07003c41c1c40810038440d4844c481e08031204004585030410140c41d00c80d2034010b14050052501c031602600101340c907822035401d07901070402030740110001c0c0700c014100010141c8602c1c80e8001c072004100c2071902080154442e880400c054589400e213a0340680e0000c200e0701c000d400c001c1c4200c3d407141c1c840c801030028541c0c400103410303445c842c07009071040400c50140080b0391460360303c1c90314a0741034807a00184040140c1001c0c150791a070380b100385102c0340c01d041d010944010000d01405009609 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 494344604 1250 494343354 494343361
    0x5041e09020d2c060a0b2805181b162a0b070f0308100b0304060507230307052a0a031409013f0b0102010506180a050a0e030406020a0b 59
    0xc0d40903110214054032000741070710369222410080140110455660411210100d1803010f413406500e251f004025546040b6129150070100711080d0640d490440c203400c01e00c824454045110707a520070309c0300901104180c0707031a140302c0b080c0090002444068010b405071305070345400c10041c00c4030000e103041040586120688403542c04240d03110380000241180c40c908140301c040b910850701c0d60b0300300705000c0d54030a0760782d41c84a528903d50010744058030302aa0364002c1c0b01c02c2d103070802c0d4000c802d0760008540c1441603064000205407400010808400e0082c006080101e00c031100e400c4403803000000f0486190682400c2e203580c0d0303842d0048001c402186600d80752004d82100f038402d942000d141603441c0280d8211031004400d009000c10f0748080401407503202189012117120301800e00c0e4196440018020005000090a4600261155014000030714a2518404150402583c41004402c010444d0303190b0881180c0101310942080000b8000441c2c042200c503404208003a40c180a00b001c44540c0c0c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 494345854 1250 494344604 494344661
    0x30c050111060a0c0203090a09061712041e05040608060a3c020d06060c150501030b060103020a18090905061b04060804081c020c011b05041e09020d 65
    0x3541d080d61044590301510004103542895007012501c9590b61056900304110341d0049001c510040d0440000c02c0c2d00c403a82400480c3d19042c445d000304038164018041420103a11690580c40f46000e0074a102d40459100e20b142803c4000c000001c0070051b00c20040c4698039501561a160103583e1000050f0a01d000404c0f61403035200100341008600c039061802d02c4c81044210115200c1101c4d00c403030640c0a005d8022045801d200300d0005200350303150a450f00d00580342420710a001c088004460034503010040c0045018443c030241e00100038280180e58020b2100c2c1a150740c61001d00c5013a103544042c030042803000c6190864210140b00d4402c0791480d4994484030446c0202d070100c103c0316a0340501080101c0c522070000c50342c009004078582e925042e5a8100b55904961141c45103102c180c0025004500e10400d100301c40b083d0000c8581c1008402c0d5481009080d84500d1185100000c0c1c2c001c0b2220062036070400e080c005101e60350045585507030481904000d400651a107107030030702401e43e982000ca03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 494347104 1250 494345854 494345867
    0x1030b030a1e15051f06170f040204021b010c0f03090b06150f0d1d03091f0201020c0a05010902100513061d061606060902040b0403020d031413030c0501 67
    0x101d921014407202d0074016101802c10700003100040d505600507030049009480c5500c901c83c0629a024804078145855030b1020701c800304a50b029104004009080012060046080c6c07600118006844c50345c03504c1e2400028081d000d50710740d003940d1000c07101d844840404c0551040c504115540c48040512a04842c243c04481024501506c0100520300044042c50582e052858076010035000c1410000081c110003c2500b12000841415555040f82040c0300f00e0405003041c80040c0c3c0c8001c40c506260203010981c40c2031404050080710b81440d04401000d8001c0d0162041c107694003044030440c030170300d04149020782100700701607000382d410650703440c3c00a200310101e840004805805081c100d2030305008942c0301c800c0b0581c080219080c84195001542c03440001c0201c100c008450008603403050600c401102d10f15441003080c1403040104100040744402030713800720b80c2c0487d40c0da0070740c1d01d49060590303e08000080d44440c448001035020b01c020140700c410002c0d03d000b400402c0005484100641e01c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 494348354 1250 494347104 494347123
    0x1e050f04022106130e1b03011d0d02010f0501051c02120102070b0a0e030702091f03020901180506060a0e01141204050a030306060f0801030f140706050418150519120605040201030b03 80
    0x540101c0c0c141c0c00c450751000102036450f0386c0940001a4401e10004010030310b20307240d0010586030806031040840c50f609000304031a0048401c01044154504800614a0480001d03220110b084100b600030075552100150350071900c00c1b40c0295511480b82ca0030170b250f518100c401c400010f141044198032a4000400c0e14142a4090040c041c0b030b84508402c8544c200042400b581c403890740340741c0400142c42d141200c5000741004030380070001e954603e600d40203036400200958024401440b040e820250302005c0e50f8600e54084c20801f804e4407202d090752090b48a8081008030800f52003081c8020803c0000303084030060300030b0b90100b1a440e103d1000b2030b0181040e50158001400354001840401c0240724030343d015174403480f61995140e03940c1b10840e040c600e860344207001181c000314003000b83d00c6d1800c940b21500d4030b0300c000401c58641810500d0344903103003074090389028142c014071911003011048810005030580031170076040d0460504d04280a408225000c030700017070901c9010f542c24240041d000300c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 494349604 1250 494348354 494348381
    0x2011b08070b1317070501050708040804052101051312020a0807060b0414040b0a1a03030706020906160809010f08061f140705070503071e050f0402210613 68
    0x7414015482d0300391442e030094880d02c0760341420007510000608070850440d6461821003100e132181380906015003112001032422003407001020420000810450407601074681c103c842004034012007862004106443d1003d032041e6180c00240440d0005041076001e43c10720603e0600300305918071004a031900e1b003246004100b10010f110010004105400190101c8000b40c00018040c20b0202100e8190303c081e68299826801d0034140000c841680c0242c2000c00a0300b03030340c10b44040804000c283c0d2849900b1020700b0361507000c110840e1316529002280d404070314135091480002d40ca41408041079200d03000c2c1a0101c1e044100d0840c03814020707070440c5d2181200a04901320840d01c60412881c80000b00d05073300411800055442c0d00c5d00020000c1c24015009000810351581041c060500d0003820383c001645d51100080c14400b0070882c00d01d0207058030810740d440e10b11180c4420100d000b0740503955032018071441000c8031400c81c5c403001480b07900c1aa0119101105401c14180c03400868000706039068 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 494350854 1250 494349604 494349607
    0x1d15091c0518040e0a031d0303040b120405010b060a030213061418040b0604080c0406090209060a1805090c180402040807032006040f091b0f080402010201140c0702011b08 75
    0x3600350b0200c00c0c09021244000d80045001d000382c4031310600700340752200220b000c141241410000622140d0380c1da0fa0400d030503070040d4030b41400c0118125282c0110059510880b54410018080002c00c1d0080061008064091911560304d041c001c0c0180d044000300d04550103612100242c001d105600c44000901645201032030000c0488401c0321001040300c1040c0c2050300d03004607900c903440c2c00000344020700d400c002034210300c4009420081580d15940c441d4060900505c01c20003965620011607a0040145c1827801c070700c0c0581e082c40c52041c1c625520803584964014104541115124014060311040140111031541c0c1d00c1d08110403401140200f12413a40170b4030301440014140300d4601d000028014501c8031246142001401c2c0d940160000071588040c00e208100001d0785008a0003d035046119140407050507082c001c00d80100040e103101040f54102c04103045d64000e500c00c00304844807606000a0340740510700740069520100e400c0b070001e45480b0809054003602500d2464080e4441c1509 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 494352104 1250 494350854 494350867
    0x6090501030c020c03060c0405010215010303051b0709021b1c02060a0209221506032d0b040c11101116020310060e010e090307020a06031d15091c05 65
    0x4500074a02c01e010b5405510070036207440d20b107a5040007100e01c03811100c0001a6502d0410000904144058090342d03c85e26240300140000390700101903031280041c001c110b03200c00300b00e00c2e0100e1804140b54054103134280300207540280d502448100c040c4903800381d4121103c1204800701d90f6010200b02c489800140c01c01c90102c1c40c0160f40d50000c200c0c0450080050024441d180c411a8809150016000c4000d507680b8510100d5a0310130102802041d00d810104079400500d8110406c0c02c0c0584008002450010411003218000390301101040001400400c03482c1004075000d801c0b543ca43d1800c4420740300754444c7d0080f00f01140102e1518011030740c6843c1c204020301c12012455844e01d40200d903d4060301c2c94007200301c030081c0304101c02004521001099549800c040c1e0022010103452860a90002c100b44005600d5100e4a101204c03054034000a440b4130700c808002200c0c61404021504d0701541e1940000b0424004030303107020701e03a050252041c10201c0c050001e50540040c070304602003101403215 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 494353354 1250 494352104 494352107
    0x6020c010e010e04110c060f060a030f030804030c0609060905060105190e091e0607140427060b07080309010c0e01170a1b020f0c03010c021b03070b0c1507080106090501 74
    0x2803c03c140409480414110101d40290b1070329003001c20741c030030240e100000b00035480054610250304000c0980740325005e94119150052150084c0f8405000d02c201c5070086000c02d44135500b80004d00b50031480c1003083d403040307203040782c09041c0d00c0ea01580c86118490022405e440d01003810302d08003294a641c200c005140002e25100700c82d004007000c04a000300443e600781c490036103200c005480c02041c0640501e2400b100c0250810006040c160309841c0180410b024100040103040706103200c0280c84407041c031414203010b010f00041d4001031118400880c2301030420204901848c0201c084100a0000011a110840300d0500c01da5050b400200d0104580c036000580e509030769080b01c1200c00104d010130312401100e20468010400340016441155400c1c025107060042540d8050210000c1c0490141404000c0d0340e0f0b030b10190710000340c6543e0b40d1400c420340c6e8100092801403011165081d100c023100c0b150a61220304110b00074440451801c0001c40072841303015010f040c0c3d000741d1540500181007070300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 494354604 1250 494353354 494353367
    0x130c05180d120c0b13020d06051317130b03040203030f03070507050a120807031b030b0414090d12090201021f0216120f050412020d020a121b06020c010e01 68
    0x68a50004207200504022406451000b550021543c80d030042c0c0c0301c03071440c00646000c0c0040000007000600e0f160500180d848075a0b041240e60080744c08101c40c1c44264108400d445111001000507280c001901c0c858180070f40030303201c20100501a00416940d5025514046c441214003d60540041114070700c00c007010805560060081c1c50302c035080400c0d0380d94240ca00920075600b650306845644900e003015902c440100d5000806241c113110905a5825051101c0303801c510034400d040d1907400740405a05d441c0d00000416202241408041c20488032054540c00810041c10001e044072031300c0b0000f0100b40c011072030f94503411f90043c00d036124481d48503080c840040d00b0b48510142c00300801280306900702c542d40042d90054800750002c400d40940600103005441c068003e01c5402e100411040064259058403650151908030a00c1001c0c40000c00c0c5010a4000000c4030702c0604600c01800300d03030010a2420f00d4444241c8030000d4852600340d07600c00380c400400e8001a0304c0301e07115645503c10007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 494355854 1250 494354604 494354647
    0xa21081006050f040b0f0913020c0c10111006170a0c0b0717070b0604050702010b03060103110111062503060b160813080307021807051902101a130c05 66
    0x1203641001c2d20b0700f40b44005030b406282e80d00c6c402c035001f1508002a1811094075031501895042c21403518110f01ca04540345d00710220220f00c00c411084007958410f01460011400c480b4a00035a0708000b000800320700102058003804080c0ea07451001c01071003c4000445444094001c0c046c20502c0d0318195451040c0d510074581150703000048071315003243c054943c02a245852081c1c24460240c6002010b20045580c0103214004681c1090524980b0341c40110b01f1605680e006510f03409072429810058840e116000c0041904e80b10794010030800501000711410303a010b807100144035081420380200d0681d861400f030b2100741d1030200a950480b24100350381300d042920429140b400c012860145240302c03c0181e118420701d0300005030300400c52a00030806070341d290411004091078106080300400d18050300703081041e607200e107609901c5190300170015852020410f6005100202421802d00003031016025071034000c99a80a901c0075030a030b030780100394030403070b071580c445007050b08014541030b0107200721 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 494357104 1250 494355854 494355877
    0x10e010c080f0409090302010c080c030112060905011b09061202040f05091918060f0501030503120709080105070e04051b03060f0d080d02030f090109051c030e0a2108100605 76
    0x104400203124444c3c1c007070b00790154000e800000d4101e0b42c0c0d11015140c3c09000700941c107000d90400040c0041340c1c40004081d0040c2d004040080c030700010f032803c1030041a82e0058030400079404400120556484000710741a141d480d540c2402c00800030840c40240c0c0114000c10841e111711950600c41405d18440301c941c07248076061641200c03030501c100301d803c0382c520494648505100362503071304c10300c1858050f020300010703d0541045950b145440d407580701c0c0070300386040c62000342c003101040c400c1d845084a600500b290400820182c00c01041c003800301903076204038a00481c100030000308004a011301804000e2900c00341946103541d0141005890000784450365031142e0869043d03400f0a02c01c07809850915601100107030f580c21310717078948001c03100020610001c80e0b060400500c000355000c209100030b441c103200d95610814004500746d01419018200080324480e80c288003090014412200115807005c03d1040307900c0b54600e004452034042207544048d8580c2485040004910500081c0005c1d10b02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 494358354 1250 494357104 494357107
    0x507060305220f02040603060209040c020f03030406020a090b04060906030c080f041b090203090f010605030a0f06090204020403140a0b011a04150e03030403030315090b2124010e06010e010c080f 85
    0x43e6030000f400c072502c1e60000d035052035010031402841d041a02c65a0141c0c0d025000502e01440950941c0e03a0b00d20009100910b080c0e00881cbd510f90a034040e5030040013810508841680701d50303e03001c0080c1715034000e200b01400241050640a445409600325070300400e0075480c44c0035a641c8a888422141902d54035041052103008400508101c261001e180a1014140504a0120b9881c03100342503601c1c40c6c1002e84250068620900010281c03044141c14544c001000310f001146400004c0090141d6031014061010140107002065804600360b40d85500c9943d902e011641c0f150309425000b103400100201020040006006030010f18200c0407074281c40385410901e101502e400709003140c00c140d104a002ca80c94200d500d02c0451a00407000c0541543d007010044400e100c0000740307103040710300b0098590146481c00d00d003100c2018070040d04001005004601a1444454901500c4800b403044c00c24003c00c0602003002d83d0310031840ba0726030120503035600c3da800085803190106a030210140905e5140d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 494359604 1250 494358354 494358383
    0x306040c1202040e1006020d0807030b04020409050a02030609010e06100509030a0f080d0c020313150e030d0c0b06040209180a0b090a09120e13091518050706030522 72
    0x101c0c0c0c0003c0016003078504500c01c0078144050401c0907000701e03400c0385056400c106028101c0715440a0559409182c070300e00401d9000b0040003080c001c0c81660481020b06003080200a03214120350004c500420041c0c5581001d41e98840003c02c84000030b45001d54070002030112105103921520180a480a0050644080042c1a9a0184400216402200d03501004a20b03040601c5181c40303080d0041c0400d0010b145082c403d0404400d428042d0300440c00c5c1812081101741e18144919214440842d0290031150001f08003000501088103204080701e024851000042090519009031800c03608050940f04020818030900940314800030070030701c0301981d590061b81255542d161098040c8030b42d00e500103060140c5052030703044461140c80391410310445039072510840e11844d40340211442101070000d03462581e89882d4038a4a207005e0742007840360820320341a41e074010b0303a000c00307c00c0c0344141d040300e08140da030701800e405650080fa044c2c41240d80e9820b0a45204001d45403207003c1501c900c0c0c806171030b4403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 494360854 1250 494359604 494359637
    0x1140904050412020d1d131d0714010e0f01050702060c06070c0204060e1e150d0c050103061d0109020708120f0403020c060c0709021e071208010b040b0306040c 70
    0x10002c03a82030315072080302101003090603018840d1100b03801c261300d000e40104203101018142c01c40340f402283d016400700c840c205007030b01c0c1c181c0c45415140d04800003481c01c5100c41007801ea44001c5801403854031219030f0070307006c2c1b158080e4910524a05004c2c001c25510640c0e04019242c0c0d0f00089001c0e80c001d0010000300590020910015100c0d84c100e0f02d446030740794050f0051104035043c54101149180240c018011184000e25200040002150000c041662501c820040400510251903080000340b03040b041004500401603003a150281d9003000b0950381d03226800303122002480c10004100e890320060040c00c019070000e1a01c6402a0303034a80c681103055400c507041c018101d4440403007502600500c410540d0511071080788283c225115800c21407800e60082c3c5500f0303d0b02c1035402a549c001010b0030200d1b03c00d01c403004000c508403174054462045081100303040d6407585403580000c26080020030030100540948064030585010301e03040d0b40d11482848010252241c0580620103908420203050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 494362104 1250 494360854 494360861
    0x30509030d050a030605041e0506010509040e06160207050108150f0901061707030203011d090a0803040c0f0e01030f08030604060e09010b0906030114132109060e12070501140904 78
    0x140180c0c0d0b603550312101e00c58014111811900024441d40c2401c642e518000c0119800c02c6032118120350002c0e4136102d4400587e110300c5180c2440d600305081c0201645110008901d0354451882041951318040e4a031f0812a1205480d000381c13400300383d10303601203400304038007110061350114090302c400d00501006001400c40b180c240e01010006c0c0d40c19111201d44200008581d4201020341019030841d4180450880c3d1150507941d000c4801200c3c6001904654040107488a020741141040b40d80b0304040c10010ed1100541c004d014a40120080004480900d450424103c940040340c00c0c407044515540ca6250781d00103804e0950083d00d40c0400b180c1a2005881d20b40522010f400005008001106005407010b0051540340301341d141a5400325107007101040658410b082280d00c0504601c00e151040800500c50880010140400c40184216800c00b41020940b0071989881043c100c2c503d0070001c4e004450301101d10203401140d4200300790b500408401d100c04480d41001030a005050340450100c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 494363354 1250 494362104 494362123
    0xf01052a0403060f09061d031e0f04080102070b011703120a0b12030c01140f2205010e1e1606110106030f06140606030c04052202070c06201903050903 66
    0x6036075149408000c1100c1b5100d0183c134209401c0312206007000c140c0009480e4000c0116104036103244000010050b004030702100c0d284210116401d4813039447e40e1030385000b13402c100011a404000c1e00c0011509102006c1d0000381d01000c60700548c61311500510300729807c1005040460495140c500405d410f50302d0300c0307080c125030100400460f1110030400da46400d4038000059841316507060002e200c1c0052030780c0c1c0c9040d4001c2000c03072020943d644040140300015207002c0054050351030201800b6001001054010080c0800e4015a62140c009030000c0c0d1144d9451030b24400d00180341404100b0a4040d1010b156140c0c0c0c503600006d80d459490710342075240241c001086462558480041d8001d01d5041190354002e03505407545425403400f10000802c0c0c2c440c0b80502c81c8180031840300e88019004544684070382088880040d0b4580d029460309650750181801480c010642000f01c103c2d01d800d201000c03000d00c420443c0184205049603a0707900c143c40c00341c0001c1d800c22a0420240c1c00646042059452 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 494364604 1250 494363354 494363381
    0x1203050a1e02061b1815043b062d06040602071d01051809011509020d1103070903031d0301020a090602010f020708040302042406020c030f01052a040306 67
    0x261500c60b41c45030550724031214845a044d000d02c0160500d000d00c1c43c100340c02c4402a5203005114401c0d0010000354011603102026031000781c0301403601c1d9942211f00b0b1041c001030815100e68405050064a5002021201150403121000c061442542554002040319518001892103409030001081a690281e002800940e1108504004090111a40d1854810080028562035050400281042403480c00a40c00072174104080744140800703500452010f50410740c814002c65031035074980040e4000c020059030151900d4001001205001c04aa105802ca5900c0c1010241035680944101c80c24070402ca100b045201c8075020180c0f0309100408450440351600e2008a142074402401d40d080941c0b240380c3e07940140110000101802c058038140e070760468000c0349c840b000d001c5c036440c2800381d2540750004510485000407501d801241040d003030181035090f0b500d10880f4101250070784a0545d40d9220121850035017002c150600707a0021745c2d4104406d00c1c5894907503039460341d0b000d0702c0000d0b40603031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 494365854 1250 494364604 494364613
    0x2090a030c0605090f0f030d050d140412030c090b0306060d0204031506030c0b0403020d08090303091009061d09070e010c0503030f010e010e15190e0a090c0f1203050a1e02 75
    0xd40318038220a021240240444074440d101d40000d007c6502c4000070100c04007071040c00704883c0d998110300c2e00300320466100814500031520f0142000460b95000c101080d010a10b41095403902e42d01c40d091000c00c0d100261240352940c0c4648042c07181c60307446803003401e0000d5402e100100000f5a04000074440007031540000c11802d007141414013034400c040c0d1082c442214208030400040e2940c40c0c0b4030208030b0b00011b25644038002100400d0444c070400070156840f01e010104c2c2104e03160482e9001c400e9400c1c6654007409051b03081e028903155240b00d00700e80c0e071040b01c0c400010081071107084200c440c2070040c54288401c4c1ca29503505441c580058400400f2900003100500543c21305004c442e0041c103445c14034442a0420325a0001c40720400f410190040c403001010b501c1c0e0098415018008142e100e801405030f29141c48154000c01c0301603012039000b20401400594880400c2e0718105690100a80d0103045d51155803c3d28950b1106641a082c40700b201d0003016401280c004540030b0701c4060b0060b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 494367104 1250 494365854 494365867
    0xc02270a0218030304080d0e0d0b04060f0b0102160306020a03021b0105070806040b0105070605040c0f0906090507030b13090f020442330c0507080304120602090a030c0605 75
    0x49540d502d1001c00c041c040d500070b10040001420028400c010380041e0700301401c020f1b55010105943c128404e03406004c0c81c0688040c003003003011591141a00440b96841003014040c0d0074012601c90070014000750300002441b20901c00701d6000d0f4010403414065060041c03030046080303040800c42c20141c3e1501e0b0140d541e1410080d055400501003584010102c800300510440c41001030614010321602800c91030f40c078400039040000000b0343c00c02518058059102c140d07546d011044c09000b0502400410340c1c103140100d00c0e10381c0280a0380c62000001400e800500e650194020024040300b001600c80040b085444805611580f00705403c28220982090700c07006456055032005040304a281c100740e2480300c1d00007009c03c6d907440c007406881c1401072810584404140e00c480381c0e08921f01d64010004088095280b0a4002510000e01807040d01681d220079910a101c0703450b03009a100300c0c0d07040000100100009499030f80140050600180002d01c07090f01d949690f400a21203810440100d00002443c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 494368354 1250 494367104 494367127
    0x3080a0210050606040b0307090302031b1215040b1003060c0309120c05030a050702012a02090906040507151107090c030e06220c090c02070603050a0203070c02270a02 73
    0x2581c296204150050115040403030204a0b507106078804c0e0600c800c1c0c080003068a2603c0b0f010000010354006044400d00700c0714015882100b1900b201c010b02c01c003010303c401d08101ca00881e04021081d181021001e041e51240c4a600b1790070401812103094505015000c00010080c0c403c1c441c48200756540001d4050540c80c00d548240701e68070011080c051001145800110700104403101442586802d40e101c541600c01a1079000641e101f005807444022060b80031a5103244a29181500031078158503c0c2d280d02d914542c4440301078801070001d8004490a0060030b180c0e03092030351520070b10714044880300d4030714410360b00300305441e0080d021140d1654030f14a02507030705015660700000c00c00041d081034100300386190352800f490f901003030014804008880c04d1041c0005910028801e8541c04c0c0280c181b0004005c1d100c603000c0c043c1002203890100400c0803c0e849200b981d1142d040d50721141c0d030401d910340030003290f83c80b5007021f003409020f14107940f0301801c1000c1c03416005211003035016850b89414013a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 494369604 1250 494368354 494368363
    0x215010602030a0809012918010909020f01080403091a0705010504050c0f0a0602061f03050303043e0f0604211a0906070804051218030124270603080a02 67
    0x1d00419681043c1c0118840300e10b601208420510004420707d480054902246102081105865040e950080005114030286d0840841903200700c688000541000005407403d182c01c2d01d0150005040701810301c16845034842401816403a40d88aa0404207076540d160f081d00c1c404ca030200c9498004840401c3c40f814440400a110b0804a81e812103090425800a650f6500202047c2c0d05034007100722040d0a0402da440c0101440d003240542e1303580e182034100004006001d80e1020000d20111400010060610301028050b217812119070308141003444c00c0010602c0c02e00440ba0748201c003000f00044104010f10003c0c07261b464420141072085440c00c000790050004901c003d20301d00c1000401403407035000304a0369480210780c1403000e407a4840b4200076103070009001c040c6002c034500150010702650302414000700d00320121b0081c01088450507501221650b0409000520000d008041c44264058410701c040d000b00420306d020047d4955264800740c0da5a98410759801c3d0000400d501312542c140f1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 494370854 1250 494369604 494369611
    0x140f0723070b030705120c0421150902103605031626010906051e090a020102060c0c15151503010b03010317070b0a0e07090911010c030215010602030a08 67
    0xb281800d614000102415910a0680d1050400320f40c00028a0700c010306001e8038041d00006581003100700388d80c01d281030885e10501c810f4a140c81c2100d414008402c842c0150b0000d264040d0030300d0f0b02c50024820658015000b5402c0c210b11203459204035100c83d860407801e8002c420400d1010034200d20740340905092428110716030300c80c1021081d0034416018100d00146001c2405520564440c14040d4040e00500c1e01030b10041100307003070109100c0c0c904480314002540031101d6240e4042501c80034005650b801c0c401c3c9000b80940c20000000300a2409000178010101509054450140f84200840fa49a10841d44c4640403040000c0d80802030074a442940000444810058515418050358407168001480300034407000340002c1c4040424000002e95641c80ea0010034000355007862030000c1e010380a203da011501d480383d5180003d108040e030103000d05581e0422501c0c1241e6902d00d00440350ba0307170016000d505500c00c2481031480d184000c103403d4020401640555120488054028141700024 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 494372104 1250 494370854 494370869
    0xe100905010c0f0810381207030e1b12030c061e1312111506120d0522050307090902100908060601030c0212070f02030705040606140f072307 62
    0x200c04201103284606001802d0310b42d0010030000344041006e03803080c00300d041402a200001e0b811006030500070340c24080c0400718000d150806240e0380f0f002e0200c0868a0b050803040d01e56001500b000703000c112194400062140140006008144603c046407940c1d00c1441d813070040342e000c4010031882c4c0d106000c0740d402d801c4244034941a217080600b9400d40c1c000e0105000344c6150849a000754a980c0a804000c103041100f0042d0ba88401002100c001c5d2a00115905801115003500301100080c01268144100159880c1c10f8142401d010711901e403c00c1542e502030000050001c0420aa6800c1141c840145003c16020804501a1060009200010b5540c00c2880403400c42802448804a92564814003c0c6800144e4140a0350200e103801c20400c8445e000d041e000032203e0520240ca0b0003103800d01d000f501101c202c0c580e0f40c0103002c02c40f0b01d54444c000000b12030801103404610648000d00900c52480159401c0107007507100c1ca010705000410300d054a07100f5202e100f81441082c030010000b410780 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 494373354 1250 494372104 494372117
    0x3050405031005061f020a0c08012c031210030203060c0301090b09040809061612020d03111918031a010504180201050d09032304080f0604150e100905010c0f 69
    0x81011170181008410244202040c00ca0303061041ca10030041c00c9207407900b109003004965520064507001380240c0da9110303400000322111001340e082d01109803074070001101c010b514000c0d4140401c411824080c1800e00c1da1150f006000000d0381e001c2040b10300070080b90585950360352400500320102c807144d19409000750110410840400c52400c261220700d10240c40e020358aa40b031400f01041074240380c0001341701c03d044074a4040100e80c0010034452608051302c0410040554000141c0c00d40186d400902c8814405042c8020725403040c0303801655040206901540c240e16a661807151300d0380c071b0900301d030b2015030078004125502d0300380500d031122000c0200d1407100e20314076000200395105162150b100b41d40c807007618108240c459005c00b0b100c880101c0101644100174035a251045d030080c0302e443c800d0311503a4030140c5c40c90030105505002d40ea10081c2803202000000f0030f08081d1000240982c40c41c0290500e55400f51420b01642d11018450800040e0070f582080004d08660040242d10081208 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 494374604 1250 494373354 494373361
    0x20010c0206130b040807110a03030f0e09010e0103030c0503070c09092d02090c21150a0806011806080d030e0f010c0c06020705250911030403081503120703050405031005 74
    0x1d40c6503400341c025170402c1c04999201d095041c030340403c15100c901c80b030b0060180c2c1c00001c03d26a00600d06241c208065554211a644510400034002000c0c060b40180100c51401000024010900c40b4442c40c0b01c3d1060780d0800c64140c54001081c0c169500800e2100d469003c901c042226503441e590480003403c45042c64601059211040000d40580080c003030842c40c4c0110b204001c940f0281e888001030080d00b81c1c5404110302c805010843d0a5401303020440d1420348003241740c604144110144c1d5041c0300149500d078603280c03c1d40842032002c11000c1c00583d4030755011500d21020700200241400a0b1000704140d00e405405929104c0040030b143c040c1d9250112181079558049100047c56410401c0562a5044c40c03c0903070800300050030b044041000136642c0e4469281c290700b03031411501101400c10502c0c034440f044107014402214001c00140c030351800100702d03207820325040a20010103402c50f064150810b44081550780a0b9905602080e00442d08106030700e01040524542c1d200010203124074103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 494375854 1250 494374604 494374613
    0x1b080f07030e0c0409030c0b060405090a0f02060d050103080c0d030507050f07081909090e010b010c0b040c0803040b0c06150312030703230402101d1020010c020613 72
    0x10040c0c900000c0544600403244075010410007203403115001002003044240514024090b070340c03825000c40340240d000002030254900340c030038580300702e0824014124001c0e06139240000d1007418201264044010b0110503007101961007424041e51103003d6203543c0700103640c0b030300e464901c058181c5410542000100089268003509407480c03911400382042e00d0301c02501d45480240100030b003010101e07080081c0c0003422540324035181c00325641c5450420251154484150030303540b000903c030380403804580700480000e8081c400c0e02d0340306014040007034082d91a06201e07400d41e4000d6000006001000ca40200142c00511126802884031300000d580311880002084d101c40d942d006401d03c28002100081c01e4902a07080154031050881d1140008a2202040d09040e441a98107070301680c00089032140283c0100390005031200c5200c000c03404906240104212013100400d0324081050140138202c00b101000c500f010112010030003c59401087c00e8000e1400400819980360300b0106203132900400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 494377104 1250 494375854 494375881
    0x80c090709050d232103010503030306061b0d0203030712270c09090f15200c010e03070b01030506161707051611040b0109030b130501110d1b08 63
    0x590095030b1203510f8800d5070a011100361414030072065907581e0809508242480482c40c1c03040742600b500402d810714400380e50083c1c117010174015160154000c1010550901e0140054030700c00302000741c0700503209499803100c0d0500c070180a103100903900102c10721080c3c5402203d454094600074208012080c100c42650b420700003882030b0178034140d460300040740c1800720f840d040e0f2000d0050072405022000781441d24800864011000380e420410080071403250b031100780622004110100174450200825240f440c8880d03001010340c00c2607660758104024054024400b0b000c0c06401400f00041c1d0358510304245082910051080005004d50b0100300c20081c1c11040c00350320000740300c00d1400182e0710494181c0e0b40f07200e0260b00e400c40c6a44207150f01c04010302410882c2c0c281e0700a403000c2c0710b00f01032500152030254003404000d22a441110001e081119610000c00c010750040c000441d5072190281d01c200c49510034180021b216882d001281400382d04003039520b14000252410700c005141442000111 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 494378354 1250 494377104 494377109
    0x15140609010c0f060e0708030901090e0106200c1504050f1804030503070e090a1b03110a0302030a02070605040506040506250f1202040803130519061b0b070306080c090709 75
    0xc812000c0c800040c0700c2c0d0345e486130914448076021120402e8032001d40c1e55694105103410750028180c040c01040c005800240725040b541c054407410389070940e000d03600c50041c80c070b0b03000c000c81c0340701d40c0c400c1c40b802c1e07942c0184000c40ca1200c8007500c1c0d6034506140a2040340c85c0300c4d50415000385501900c40e0443c0381c1c2100d201c2e501c1505490210748070340314038204542c82403242c0c4500b41d2040460f0180b01d00ca0100c2d0b4405d00c0e402105c90000d2004e071840b508150700303840c0600303080407060400b40801e0031440d01076001160f006103060f900518040c0c0c181d45d4002264005d443c16901c5612003410801005020012103400c07604907012041003c0360340ea0040c0700005004150020440d68180c40c4074030310301a00e000c3c0d10340e8041035401e540301d03529100e4141d9203030403810080ca00010300b001c0c0029241083d40d00c40151028000d14a09002d042c003509480054101618103d100415540c24011441520000b0300500035590041041450540d00c1450100c4541010b80b007113481c0030503c1011078002031300004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 494379604 1250 494378354 494378363
    0x3060b0a05011b211d0306060108061306171f050112020607060209031209190b04260a030c1727060f0712021c0f0305040204020d15140609010c 63
    0x10343c41c1e654600148982c10603072101d0f20000c0310424040c840780c0c1045412072078060108541412400010406666820a4070a94042284400071985a051084005e603080703a0a41020507516aa01508110781c030705081061003941141101c900c0e0420014082d015603c3c0700303201072110f54180380c0c1d003c1d85440c01101c000c2c481c0034002180d800300401ca03015681c0400717008050740d000c0c0050241040143e80b02220051103200c80814400f1510b265070b22002c10345180041c03c91c202400c001240c2410b070076040307d00440301d91801100b21844020002d40003032510aa4503159804414504400c10309250314060303a42c25424020b1002c242034481000150304540148420560085400b00300144030b210400c0018000010341c0c0c030140110a80d8001d81031074150301301c07007880300201c0c80c84a00604000c0c09a00089965041b400e03100d07c2034001603000780c0001c00043c9048801c0d03058008892544581807520204a03800304031044a00744003441101d016184c180c40c10b402e0800081141485400050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 494380854 1250 494379604 494379647
    0x8060a091505180c1005030402120c151207030e03160c090617060109110301030b0c09041a0a0807060e010507170f03180307030c24051003060b0a0501 66
    0x80c0059500000d807440c1840004014030f0424002e82c4400e64650205881140f10b0460304460500b8080d43d25031980c4000c0c0d40d02e5045440f6982003001c40007503a0030f0711805100300f104401c1941d0310b04500c49084a10601c034035a54800d03a440e11851140000d001c0c0c030030b2515020310f40e040313880e011088070441c118068030000310402c2c5144c0b03c3e52a8034030b80c1004161034034201010880003000014900d9003140d1200300d800fa81e9a030a82a0142c40c0e40007241c070300303489003480108002183d41c5891074000c0380348040740381030825010115003220241848075800d10801c469030350b81800c240504102403c04480506411802d20300040d144c504002080e90400c407000800c84240202c04d400000c0a0494682484c2c2c1e6000f4502080314a810035582c0380c00f40745244540c0c401d0b01d54000116901c407a07264407540e898a000781c0360081d544180140c0c14140082030002075055500b107100740b40c401e4000300c698480c0701d8258189041190505800d00d802100d642409100f070b682c00c082400c0d103030003a000160 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 494382104 1250 494380854 494380871
    0x20a0c060e01060b220b0a1101050907140d0311160501030b092401020118080403030212030907030f0807050706260108030d0e0a06050403030606030e031606050601034208060a 77
    0x920000e1598401c00d11803a0100c0c87d040656404068805881000b0000344001d480380c042c010340300c031000d1040866a804410114603241404032040300d0f814003a0800c44903442d50258511306041c0596004013900c1081401800b242d07800d8480c0d0040c000302641c0b0f000c094909804100c11100c074131074241c40c5c0b10f12401c51480c140d030b100350058403071660008014891494207207031032100364029000480140c0695042c45104030300c00360560b44118040c0300101061455502c803100c00381c102d100b003564044000c111013004103404014060007400d150b1355001080d880fa48003081c1100049880c6844906c20400420052400100342c41c1031405044000542c443c0042d00e2514010704507000401d014148001c100c14503406a006c10225129600c0501854006182c2107450784210752510552150410420000c201d0603030007298840018100080c44c0b00c95488448144039640c4001440400e0b214104210b1045004050a0b4074040301e00b00003040c1d0901c1c0e6060b4035080300074080d58100382e68840a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 494383354 1250 494382104 494382157
    0x3090b0601030b0a180c090b0307090302040c050909160305070c05060a1a090411040c1b0f030306090e01020c15010501020a030c0501110a030b1e010207050d0501090204020a0c060e01060b 82
    0x903401082052400d280d8170580150707400c098484e0004a4010440501d0000346c02d80441c0f04991288040795900c084d11401d42c1d08201c02003024000584c10080c0034814000310f0389510528600649501c07145054040920000906403503009103110700300034560404500141c0c0008015030040459032002c202d41220030104100c00341049801c0d540400300409000900244241140c086a400c1e0307410320140d8501802900c2189001131070f0138241c500815410b02250507044c003105c441e0300c68540400d45d42e076a44150402c1d190144003840703c5941c0000c1c6100074000c1040380e141107048060702118a036150100107500c07917040e400058180700e1034020714810004203601002012401d541c800b070310b81200541c0140100440083d00340141e1400401c00880c160754081c241035180305a0040504c03030304010500640c4504048200d40c15900d648003500140c0d124005440350524560f260106480d0f18286501560b00c042080e07002031740b40c90024801040e424003201c03030703521900400302e154800c8107a6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 494384604 1250 494383354 494383369
    0x7060b060f2a0607050301060806180a1d070824090a02150904150e1e150307080312100902030603030708180d05030408160e130c0902031e010603090b0601030b 70
    0x2c10181c06014104280240c01c07001650513520070f562020541d668480500010003a101c0d208038240032a07000240358074139107802080252001c6045d080f80c4404400c0403602d88034058010850395000347c44694408200280d010303414450200d807103409414081009912030110400103030003416070350841203040c0d05d648101d170103449014004012000c050062141003540c20702402c0d4516080601161202a80741403203011900b050340f00300030907140d0004170407071215001c07405600360040303c00c0011081000e002902d2f642a0140d5120782901d03000f0b61005510a5681200905610510621070640c0f400426284142c2c1d000d440155650301c58110346449103400c80540789e0002040c860181000400304c080c1049407402d1084070b69803080081000e001550742e00903110184a12400100b00580302e905151145008203c40c81d8000d454031a04401c3c0d0740300716402e0b0001c0d440720b900f0201e414000c1c281e06005081c2c1e8903040114008a698803800303004082d20740e604058071344410401d10746c0c440721b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 494385854 1250 494384604 494384677
    0x103050405070e0f0a050106030504150c02070906140114040e070f051c06090506061611060f0a030507020c010f020303061203192706080403080408040b0c0307060b060f 74
    0x10761a0b0402e02d4214041342c5030307182c11034840e40840c0c205000059024013078091140030b80c2e441014240050480c924200040100003403d0085105821000501c4512440b0741d20207081038044803000c1081c1c000c005800400b4400701101a10020401000707002140400580c00404900c2c1003541042680130458140c001c620f0f41f01c0d6004000000410107a0855003c0700c00c507a40316070140520361b0749404000d8140610000e042840c100361900c40001525490380002c0741c0d100800c00c2e810b1220080040d0b0b45600800745990101747e854080c441010b40400414040e900300b460060840a41a10025220300000c0c2c22140a450041c0d0070100d007440910640f04031442c00e0070301840500740d03620000d0501074829039a144030005c002303c866030007044400c1001914144c0d117842585441d1030742c0848850400403c1a0b80d01c0707600344400314580718800010052005070301c0c01140c80c1c900034141102100c91219046102d00020000188900c4114080d11071214081118079400f10b03405690701d84101724038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 494387104 1250 494385854 494385869
    0x207150309060e030c010c1110020306180f0711120f0a0e040509030403140105010311130e0d120e07050a060c0206300109060806040605130203060403020714030307020609010305040507 81
    0xd5482c03d8091000400307042c00c04002002480042032070f01e420340f00c44071041d412140c19040201c0d030001c150410b030001c40c1c1141e006058070000d0405080b07004014202901c1d0804100100d100b8044869482030200a0000c411409045026114103145209214041c0e00452003480400c250440900407a420200d500015005115a240c5820615100d5000307000444251102d802e800c1b0b030a0030144203c0e41030341c1d880100d41081c00520410090009080300b8082080764440900d00c201c05401d000e00312501c001601c0c2c24240440c9030360080150b070440e5048044690200c80c0400103640d603500c0c4402121150700b00000b4801c1c240c00400c500c0c3c480e0710b24000811104a02d0040d0104921144c548640003110282d03101d1390b2240c2900c8240e03803a5200e244450382c00800420013098880e4441600910701c106401d201c012543c1c042420304600b00d80940141e0018503040188800e044c0750758003140011070103140303044080d900140720343c040c02c0380e03160400d030342e03400041c04200b4104111405441007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 494388354 1250 494387104 494387111
    0x1006210e060a181a1003051c17040f03050901050c03040b22181a0d0506220203030304080a0908030301080307031b02010c0609020f130b041407020715030906 69
    0x203019155651405071104001d4603e030141c0c242e2a090b11281d106100e42c2d00040c000c42c0103541300789801c040c9070042c040d0b210303403240a40d0010011358204003c0c41040000040524042d003c240080e0603842080014a2031070071180802000a00a01c4062841a454180ba64940c2c0c40480100c519000d6504106024440000c02207106030000c2e01a00b00b80b00f9030060f03040211058280d644403400c040c03141c0c1001d000d00540b10008034140c0c2e0442c164040a402c403542e8991a200009040c4205900055406802010034099503200750391010307408108902d0ba90594249681c0400c0e501e1100500113010458080b4034054120301c2244194000c4c0f8408080b26125611104400d45980c80b108084003c600740d010003031290741150440c0888642c058590740d0941021b41c0b2400058151100104e0f404024004007440b40d0341c811410f200302c0c013103c400000304068079100b0300040f101b40100c001401070b440e104101c44140d0014801064980c994105207c40110010a501401c00024000d00140c00c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 494389604 1250 494388354 494388371
    0x604140a050406021c0506030c100207060c15050429010f1a090a080706030c0207060807051e1c180206190c1703041b0609271a0315100621 61
    0x3254100c180030301c00841c140c4807817110009c2040003030201c485090001d40c00048041083c00d014402c4124400c0c0a5203414007400b00c42e905a1302114001c0300c044498801c0c0e859411111007064980030100c80d0329050f000525410100110028940d610a002508007500302c121907111101c0b043e0369959030040e10154007280c40c1c2c45015114030580c0a440c000900d055020b034450f030710004210088a0039038a03071440e6501e0b841c908440c0c0e580022844a004a103812008800d814440c004040d1164440c2600ba0110440000d234415654014140504903016400420141e0f40c3c18007105d07400c116042c81440c0f680070721a0155448001400c02419014498608400102a13a0000d52003148550741010082502d000004140111401031100140623140140000300401d4240c040c01c8003003240305203103000c021840c4401d540c0800d07626040b0032820300e9000000d04003002007405039602e05c070909549207440c504039117420540307202d441c08118002c94a14040140701c01e100c109141c2c40c800074800f014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 494390854 1250 494389604 494389657
    0x7050a05030714010b1c03020114090c0f0102010b030606040e120c03090a0509040302071a0f040f0608060a03032703050a030201090314070f150e0f0c0103050604140a05040602 77
    0x1c2081c501a10003c84408800a540344188100100d2040040000070043c6010390041008100c21100300c080d59665030080580c040000c20b0b445c451420903004000300c0784400c007404640d0b007691021605685c141000c049031503401141455120741c040c0d500040d0360800702c86182c03a0409119140615103000a0384042541c000f0000780703245c0c01c00b03175100c10f10725580c0c00900907400d03021a405401070300b00c0c0c081800183c00c29180b907800d590103000c005081c9500201e60b5449640194044481044c800788104006030300030038a640d001c5000c4801c1a0b0355441c60302c018001c1900400c028400c0060110840c0b00303000e050060b100919081002c44000600c1441c001e4000d000501054000c682c1e81c49040d1000c10540342140c1034264090002c0c449041241d0700c900d0f24201c402c01c03c1481c00d850350082c82202e10100048042405407000178075030092110005421a50301425080c0142d05020b0a50440101760322210b0b040140602c0001e03a80da41d504003e0024001e183c150703100108141502403115 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 494392104 1250 494390854 494390857
    0x708160c0f030305031b0418110405100c050f0114042d061505100e04020714151b160f02010c02040f0c03050a1512030e060f0d0f09020303030c0d0207050a0503 70
    0x910380703c040d07841031b9200d038001c0e044e01b40641e10071351015011030906001001c0041e08190000d013410101542881e071607000091031034082090f02e60000d1081c0d00b0240c1845030400ca864054007801d0300070013200000505a10050300001d1020701051111411038204110b228182c05c003803294600109070814a51a041c0003919680040071254141010046968a41600a156200c00d6a00c40002d1084e025043c0002794100c40c500384c0b109200c408450042c40303018030080b80b02000141c10710103a460310440c00c0080b80c0000301708008680c01030000d0050010461900300306c00d508890425465805480100c50203000c2510080d001428001c0008000f001c91700025036403099a1414400c40c0e036120444021a00d0b82d20001c42d00600c10f850810014a9000300580058000e15202410101300404203516500140442e608801c0c0090031400c8292a0301c100c0c1c180c407550003824081340526400183d90b074080a00740820421000034414251004d6a0480d001541d101040da00100243c0c10810b03120b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 494393354 1250 494392104 494392111
    0x20c0d0f050426210d0e0c06030f090f0d05030708091f061a2122050309010306080f1203280c02011410090209060d0207050a11060708160c0f03030503 66
    0x5105035180390119151242c03407040004c2c424851503050861141441d00909a10082c020b001c0c0506034030800303103443d004001c500c10200b40416200c6400c001056624102001002018541201e18400a207683c4102100e410246a2410200c16241e401c000f03410400000c5501c2001600e90941c545051007079013060342207074050301128103044c00c0d0b01034402462095481c1d2034940318032088400d604030942d515843d0041e4210721022014400c07414034001c41e0300a180f007941d03580c0c00403c80303000540e858061507016001d01d80180007114604504c46640d4060a42e102c5c2c8480c0f00800080e100e0b140c0ca94404c0c04501900b02080640c480d0581d0050040c1400e0b00c1d440015400e04000290b02c810240141d0300600080d90480040da1403d08140000e4015100e0341e50300050402c0b01d158030300003074000307000d01d1030082e0060000344d22203103000030911040d800400e014400500980c00841ca245055071403901d81c1c50b00140d00a4002c1c640501d080b0081e80215800795140d000c040241a8014040d510 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 494394604 1250 494393354 494393429
    0x80402030607020c0102070302060f19032a020c01080a111201090c050703121107020a03080909070201330504060e070219020607020d0201030603080a0302070501050a020c0d0f0504 79
    0x20191074401d012a01d407284d041c0703074030b01581c00348504100609212006092244200b0701503418248100d20086145007000000b02c006030b2a05240d000740d89804032241f040707035043d100d0000a144070070000381d250552010a14180326610300040c0001d011900100d0b0170240c6d01228680ea401c04440c0070303071040000c0c020701c9915850001580341160140040340c004580507101e002c1204511944500a84403e2031400000b070014400903006031511203445028500c10f00000b80c5540181c07082c45182c080c010461011607040c45506106401c40b000b8502042031005074820030280b0b42010300d032040d419a070100d80c01c54606100010020182c80e552405440310358280c030544910708110743e03a64401100080d5201208000203001860181c4c074199120384103040c046081d45d0391f5204c031307102500b09824220200c1c0e00010b8003000c03c1020b20810380d10100103201181030520701381034144e8a140ca02410740921075400d408c0c03c041030041042da4000e0460010308040f004807003808001c8402070351220751 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 494395854 1250 494394604 494394613
    0xd090c050409031704110a2706140f0a15030b010f0c0206340507050a06140d09080c0102040f1401050a120203060d02030106080606011106040308040b040311010c08040203 75
    0x40c4501c0e1038010b1003160350301039a0f03640392000400c5a064000301c02800480c1c0303010800150090f540c031082d0800d4020141c1c404294454415400781341c00301401981039003005803038a0828044c296504ca008101d802c020b50307010340c140500b1004503800403080d400022800c62440d05a02c2d100c1c0d855048103d1032042030340c3c4c128120101c1c4005917000180114000d6000c0c0c030a000d4107034400140c800d13440001e8915142c0c05410504040c082c5402c2186141c1a40c1d02e410010050180b420304000c0c1c280106154901248100710b041841c3d40e460156803071100d8820b0300c41d400764081c03103140400c2c0c0b88002c505800071562265218190102c00340c1a110700340b6181171640c0b010340690301038010386010b0711141d141c2c8088004041261002588000c0003140e00059170030310140541c40034481e42000e490100024006070038030340d0000d41103021100422015038407a41c00c200c00030758010000c0c0c0c1c1255100d40003076002e4032149416604100e00510002103580307800288e0481c258440724907800707240240d0644 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 494397104 1250 494395854 494395859
    0x160609020f060f030a02070c0b070606093b03091201051b0f071407080d031e0209010918020d020c060a0b10020a11300c060307080a05090705060d090c 66
    0x2c00c06010f02c400308211800d092000511405d1301b81c006240c3e86114640c02080180c81e011820007a8015000940b01d41d5030b95a0280300402252191003580815114010680803c2d045400f42d150051640410100c4408400b200e15500402c2600c902da50010184030b00c0026921a140c0241022245070203041c025841010401503c0700403240341401c00c0960302d1030f0551341d8482d03900c0301c0714181e80500c5034454600001400030060245500702c890558003c2641581e8080038a200c000399110301c031a4a01c100145d01c0103a812035408400c56081d00200c40c3c281400c800c0d47c1000740111601c2004090002800b09001240403c500d403103588004c204101c410380e244140010034442e00d0303901000d6444640c3c80070100b94200d400a911207030040c0f003510108c0d0340000c01044040107052409140418500d0400130240c20700070910310440079240c403801c51500350802005c4410141000000b01e60b01d001088c04d00005200031000350034081c00095071401001c1080e0010404075030191445104031380007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 494398354 1250 494397104 494397109
    0x10b130605040b120402010c080f1308190b280209010314040803010b0c01020c030a0c0201091d06010e0316030803180601080703020f0105070c1e06020c011e0203160609020f 76
    0x1500c042c1d5a2050401d404c03c0c1200740481c41451016100b40e06000034a804100010a1380c8018009000c180010980703c800c50502280c000102d41c00c80000d50704007082c5a4200c1c402c1101c896003c6811942a84036034a50740000600b03071403190700da0480724213003001c160081e1441da002414091000e0360b0420101034041c85505c0d04900c1940e005003440d00400c010400000e10130050205440c00340001843c00f0784bc4c843c154035641c0300c501c0181c003050145400f041503680110b0744000800b028005504802d8074628010a5227400902c1031341880301ca0490f0302901d4404001042440340d84000b07a0000319100c2c1031102060308115029100156594621000103d02260060490318441c000b04519421a0300b000002c40e5502c124604104040c0400d402186010108800810144400c00c168a1a8003d002c24100e8990000425940b140c031101c8400e9a20030900e032075441c01304940f600710180340ba00072829445205084440984058051418070095501059100e0b10840d0034810f89000d8609 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 494399604 1250 494398354 494398357
    0x105030a0309060f20010c080c0304050c1905030615100e06090603060f060d0c030536030d0f05180601031a040c032009180c0d051005010b130605 64
    0x100038002841c002c0200070090065500f00900390b01d509000c060400800706103842c10038900d00046960303442d20030311510117400241c2c03507800001146c2d100d8039524250321903c0e034903201983c4041c0960194031105496030300c2d142c034020161034014141d89445c141401d610010400c40308050344540b800e422100301e030f80d020b04a2810318110283c140c0d801c003150003040100c2904001c0940303070020354075400c650441e0b03179640003441c0040142000241648400b04020101e50740141b01340712003d211000b0740b00005502c09040c00310154400b60b8504140c040030042d08600641405d0312480742001007070001440d20307402c410300c0b6504101200420001c1c1d480b085607078100a201c050b0a02c00c0c45150f18441180d03a03904154003501510003c0c1000d0b589030b0380c10038030100303210848016a103200020000c03883e000d00c005810440c803003d09640f81f010500a07940703500b07501c20b41c284038017540d010f6001008410711018001c2e45030140b0030006583d448008110b660710804118a114100c0d2070003141c03a038000d50 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 494400854 1250 494399604 494399623
    0x211217060a05130513021011010606050f030115030f0e1506091e040c15080123010519030e0a03170903180402090616060605030c010908191704080312010503 69
    0xa10901c251800c43c03e0000040001501340e01d000501c0d4042840075844104070920209819654408610b4040c403129007126040d400210400c4001c000385003080b1a41c1d0140da055603200b4074601404405204160010300d481c0441c1704e4541d0402580c40d8000c0303804644002d02c1c1d81ca007501c81c81075558110800119240880e6509580d240c2d641c440d405204407080c0301c0d0f511034400c080c2600115240c1446181c004200054600041c00705401801070000311020ba105000d200c000d401001840007001074084e010342d00748410313409904507c20350054842c0d04110207000c200c2d0291400204203040c010144c3c80b04014091540203005d001c6442688000100d0700c141281d0b240088001c0011010800a940308049160f849801449000e59800c0b0501901802a02c02c003000150645404189802c3c540b2030b04007541130004a0400f0000100c01064150640b1290f01c0c2100050419140c614880b1034052054880890b0218010a0907900000181004044924143700b607030798940400d5a40d14030394 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 494402104 1250 494400854 494400859
    0x2707230a0303030e1204241706100c021c121b021323041b0f1802120c0304150507020a02100201020c0109060f0b0303070c211217060a05 60
    0x21003080010920a50001314034500d524291040003030003240084041e0016000004200228002c0e0109040c99030071054032503ea81c00c0500d9528038140341e6003070000c0c00900d00c2e800354500520b03c0c64840d11030f0340a03100d0340b0b03401000c3c00c0300340940d0520002400038070a0115a60030490364201d0729140100d50703d40c4104074403003000100c40380f19401d04c903660000c40c9001101c00d072501000102a45405080544030300148040359981c81c0ca404d10014080c8040e021881000c141c08080c002d84052055103000e8405040300301c07512000307803000303540284142c0c000e954400359508184100100c12038021800740b805450420a00c4c83e02e1450340301103440540740d06002da4000c441c06801802e09044492a000090000509041c0950040c909560710068101c1e8660f58519142e040340c1801d10a044c02080103070011402c0c810715995484088110340509000f403256440c00c1500700341e031941c40c9032043e94054040c8107800c00c4a40d010340f4401981e1604180501c45900050310b600f08500c1020803078000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 494403354 1250 494402104 494402119
    0x8150907090902040b0a060c170f040b0c070503010603050d080606250f061d0f01050c0f0d150b180301090308062407031110091109270723 61
    0x780308002008200c48103089801544507520703210381da40e0b0b05441000914050312000400f2a0a03e80881c0094800d41c2c0301d08502c45c148048d14203924890140c5003500c1c04242085d03030b201160007a83c2d2034882154022a4507600b00a800300c01c0050110b182480860035484103456601c400c420080c20303000d0000c0900b075611031040c14082d05a860280c0d059000e00540e4030442244403038440e4800d590000f0707528410311904940c5001b15600c00c214442000c2c060303100030899800c00c070061080c2c80c8114400c611103c1404540040300405d540e002d43c5140da8062030114005507514501540c680042d41710341c20000c0002a0700d0040d040601560517803940c940e888114981e2508100440d0b0455030325048003460041582c11000c0d00e00400802625000c0d07100c0c24061b900642c00c4500d0b02032400350908180e424000741000184404c1b80d40b183c25502210030500139036681280d28040340705036021604543c2554400f6200040102d08803060700e400d6038040c0349400807101c3d0003598034060100c85412456 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 494404604 1250 494403354 494403359
    0x40501050304110d0203060c032715040212060f04030909022113050106091d0f1c050c0d030906060602010209011403060d02061902011b1d0f0d0c08150907 68
    0x255580b0f000009001840c0141d0384016402007486c0100807a06184400800001d021074041d0a54001c1803515440c4138124143c00f84501140d284c455685001081c0103030140030808568a000051030003031882801c40700a0b24181c0d064441044059a05802007081c000011440d004035008a41c2003a09070381032000310700b01e0403040c0310217460001d054480c8007041180782c900054080c0203800080c1440400850f1410071060b41211080c80014036807103661101145440c401c0e0041805482ea502c4508002c0359025001c0040e2a544154860465107000f02154030002c950980c0c040c0c05c00038081d070000c129194450800340e01300c0c4140d880441c007242c52414074101017032611005552204001d030200c00c4e81c2d03100da4042401d42d0480040588948118245040340c50760901c5500003d1602d9604249500b41ca81c602400c407062603d01300c4c120050301180c8441e40e450781c506002015102030104842d4640e1410010070b41e4110380184507481c01605410300740741c1c08200710a03000c4c81030000600341551 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 494405854 1250 494404604 494404613
    0xd080103121d010c08130e0a0f0903021005040206040515030901050c0a02121308060f190203010302130506010e0913051203061807170f01080d0c21090503010203011410020102040501050304 83
    0x60302c11130840e40d5035400c10240c080d41d4549001003004008404c0c2000c0d903402c02c40c14401c207540d6121300d01c4030300b14641004a004a5800a884c0420355018000010291558008030340b4510481d0003494000b0706030500a4559035500f4015481045180001c0115407500d0a180e03105116498402005901144500c1d40c1101d010008041c048031840f02c2c01c44207a500c00c0e845040000444a00c81c030000e000d810450b1400000004500c00f103c003031000c51940d8110f40c0054041c45600f9202501250368100003032045e409141038800c02400182510600c3c50050414144d600c02c3d1441225540280181014024040c0e02664040c82005152011591900d1060190128024603c80801800640c1c0000c15503001440070b002d0325040b44106a198107021919180a8245421000704050151028007050302c007140305c000f02201c82c803002070300c00165030f04481f200f1154001130385c154800000003408000780c0c0301c03440556105444001444410b4003050313080b4012440b400d40401d604000040009 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 494407104 1250 494405854 494405867
    0xd0207080715211b05120109020913140a14040b0103060225050a0b0915010306020f04081209030d020703084005040b0f030307140f0d080103121d01 65
    0x29040e2070b08160445070401001110001c09008000f030f0355961800f038040d0120002c11303080d103a0413420510b2405034050f0092046174014451003083c1c9501043c252066a40c0000b1701c0708050070403a00b40607020b84905283d007102c40070703210280700303e1500118544600c0c0c9242511310030ba030441500c0045038a16100c3c00d004e0340c0941d142800d0750054140509482941c90200c3c51014041c8008000503145441d00698206000d840040c01d6802540c1100501040c04601e50549600800c09610f44ca204c940302040b6016580103d500b5003d1040d142900d05520406040d0208045080f20180f40740010b081e0b032500000c0c0000781562074200454440b03507090103440d002e250b6800084d005000b01540d28198420b2241a5403c030440030280e0402a61410f4003600c20030b80070480342e07540c09280e1a000250b881c450802c0080c8160050041d003020050305012080002a0180555038608111030700102b00d60400d00003102c0480c06187c0d090004c0b03118070090400a00c2d002d03001904480120300648a1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 494408354 1250 494407104 494407139
    0x20906090c1201030f2906240d020d230406090f08190305010603060815040203030f0309070608011a04061d0604080115090b0a03021009080a0305070201020d02070807 73
    0x7100310401200c4903031104903440a00950098040108403a03681c070746002c40703e44245210301301076044410302812000d82c40c4019001503040726825941610b54a03c0c3e49100c2c10070604400f5034401040440042000d071700284001e070001881000310920303008041400044205c512041e11020400150009001f6400754202c2805001c00601e00c90050395a82440d9010095998680381c1c2c1540860340c02e50103025a50240000342030900049003011201559001131541c1220200b40100116065440c10b20403280c602182c1e0001d21343e40d107440c0a1003907490070140701e001c00154244000084034807444003d031480005a8100520b044c1c80c02008031200d071140c87d41107518062030940b011207541c0e203000602c010b04182c0300119481d104070b100d08031100103035440f1990090810003400f03076a03502c9109002c103495048a000810007203000c4210f80010a81c1c208100c94480d1081c0f0760f092603003142c05061483d00c01d03801c98100032145d0304102e0321100a80300e441e807698003d1000b400082c2c6030b180c40202 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 494409604 1250 494408354 494408371
    0x20c030f0a02010516170703020616140d062309070905010518040b040c0f03140405070e18030a122913090503040f1703040f09050714070c090b040902090609 69
    0xd4107035068403484070100c6c1300c88030020780c1880028000c0425405004982d8450aa00007a5181d01d111485c00f406880d40343d69000c58400001640821081c40d81d4400c6000d419820b901c2c2404c800a20a0780c0904244228428810a1020700140343d141c4540103690503200103075201424611002422800e109200a02310340c8907403038014410254589100e24518203185030385d102900c00300150058102c420b42c840003800c080c42e1208010129400007074890858800c40244030a0395552050703001c50304240c40380d0250600000a80b80341c1254803510034101e0754090802004440c8200b003811402d40d800d07152468005000c10b03080e942914069401d88441e108454000c919a01281e540c0c44c219030290b0041c00380c514a081303041c4a400046406040c5c0302200d60021464a410900c2e120200360390b0348078803039140342c4800002c1d866910506041d08403031001d807810340d1500440c0c0b0b84104d403c0c8141c080c05410710b1920312040f00360314280c01040442500581607240a07190300040c0020290003c15998 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 494410854 1250 494409604 494409637
    0x2a080f03040b07030c02100804060f0204032f03030a050307020c1c060f0f110715050f04121202040303050306040e031305190f060207140604360f020901020c030f0a020105 75
    0xb80580c60300d1490b01f864240c10359400c03803149468a45001100c0010302d10b09003c13071060105000181c44000400c0383c10400102242e07112011356511903820761454032454240c04007164088100d81c00c10055405060182c003a141c00c10f18000c1800758503400c100c507501d0720440400190002c01c0e141d5000b8601d00341000400b0856a0560f40a003007994110b04200740b41080010b0902c9c01d01c490600104a2107160500c240b10300e041c080302000e10007038003030006014416000710b00307080c460046e0102030714080110802c1d51070346d41e24180907105810880d031060107182000b20500140b007021045604100702c90341c2c2c0c1c00d0040c1c10107042c801c0c402c030f0b03400318011104810840800c9200c8485c2c01a0010103180d4000d098035801e10050b0f40d10094085100c42c01142c05002c03d0021300300c000401110300ca460407114116a080302481c8002100541c4c1c1b800300140b0b040c03255044214150020001c816080e001c81b040c0014200c1403598441580540c020540c021b95200801980309000030580e101c1854003d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 494412104 1250 494410854 494410877
    0xd230612100c02070806340e150403140708071a282d030e1905010b010f020a0c0e1b0a0c03110115030305090d2a080f03040b0703 57
    0x41c04a41c824112100913900200b4200300c800c3d002c00c6101d602525001c100e481038026071006544003d14000b104c0c0b40d015502014400d0381d4402c600b9410041d9004029210000022402e45560350003400141c0d90050940c441c142d2a01c8006086c0b000c4920340720007840102e00c1c211405211907800a841000b0380790400600c0301608045446a030007519040c801105035100f071001503da103510100e24441c500000000b07155a90608400f080d08801505011a11004c031500352414220301c400005140700307500c0381d02000c0c02015400400c0b6861b003a203400009800702c210030781c0d8800710500018021818000e050060412003079030190405c0151483d600b080f0300c80c1501440726089550b0050000b440300840b0020306034021800110511803d00030054a050300c1c2503c00f10001c64003015040c803000154548854441044000160790484d44140b003111092082d01d5001c04105c103c0c0759480c150510108e000c58001c1064040048600020b41c03900d4039001003814150003005c81a01032201c003004a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 494413354 1250 494412104 494412133
    0xa020a080d060f09060f05030d0203070303110f12061e090604090c0e040308091b0105030a050c04051206061002030a021c0201140903090109060504140603061507080d230612 76
    0x10010740004d15002c40d01c1c0341804001104144d240c1d010601c6580031007d1100220340210803600007030b03094640481d000d6841d0841d40308600c662a15911030484c0010088204074500c60100c0c05003c049a58000307641c100207400c5400ca028501d0164031817001c401280151800f5031005180f240300380c4a243c2159030710300781510700400c102c6041d4046280c49080003a208820700245000c0c2c00314211422038941e220000800c5030100412405280d55202c020403000d100b600c055400230440208006499150840c6003034440105883c0c05001d88111007000200d83d00100503100c45880560061031000480380d0300440b5441003000200a55507500c44642120480802c8140300308580e02c000c40e501ea021000040c0f076140907a01c1001080342c180400c1c00203c8140811403088a001c5400a889072143e100140c0c0382c050001e42810074800002e00d4808102001d03011704041604440200a001c131101b070b004030350344500203000c0101d040c0c0900060151a00400503451a1010380c121142d03001c91001c2c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 494414604 1250 494413354 494413379
    0x272d050d02010b18060a0b0304050f060105060f2b110703120612120509040501060e0108090601150507110303040306151e0303030507020102090307530a0f0804090f020a020a080d06 79
    0x1010740cac0603007003000e441008103003c00016004020660b9840e01d030250044840101340100b1a034807044411211070b40d80a2910b1401c4006d000f8014142040321003040c14000311151702061302107001c9841060781c600e1020301d6106501c1210314080002d0366440301682e440c442c0c000c0303a000b41c0d0305100c4140b11140003034071076108403406425180c88008800742608000f4141000003003031000190701083c018460f01d4a01441080464001c0c14000d4a42506180c2850501c5480883e0740d01803102240c000140704051f0007485208525203100308003640c803421070034000c0c1203200c00b0910304841c6400801c000703071007903100310f0384050385100050070007502000007401c05400e988a402d114602082c11614815034400d0807c500003c61a00080e0b040c1426003140f000b0080d51034600c09002011322801d01d40c6080c8810000d20340d00210500d40c2c40c02d50325004400f80c00900402c09400d01d00035011031641118800c84641d05016002007041070010b540320350031903006940800f0120703207407500080e20090501 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 494415854 1250 494414604 494414611
    0x31803043b0a05011809020a090e03040b03090606010306050307030314370e01050c070513021315090b0c0c0f130f09110103272d050d02010b18060a0b03 67
    0xc0c0460194500304d803542808081041790008a0b02d4450b883c00182da4580f0040c04a42810b40049101c2180001d000d046000d154454008054004100891150b0100d191449818240c030100051307516541410742d02c0f42c4a02008010801845481a191181201400e160802d003025550f0480a03000540ba09103800310307114000e40d8100e4214015681c2128801c6c81070318080c60268244040045210b9544416201d103e0003104545c403803072040b155a404541c8040d01340e003020b90382c030365a0352400d091030000c2e40318030340010720341007804120207602c14100d07012002e1079002000902072090400500f507040e500b149a00414a1043c170f85605000d0240a01100108100040b1685903007885c8640190b10380f4410b0400d4603004040c22042c80002c4807000341080a049401c400206103802d9181004900034440c465101c0c24104c5800020207424851041c032800c01e440312603540e014142e0070784002d6842a42d0102c0d02d0026a11803030008141c031907100c01c00030211a8265558074cd1020b050344180c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 494417104 1250 494415854 494415871
    0x303040906080a0203060708130b0c070209070c1101020a03080a0509010f050c0a09080c03030417010f09081c110901030c0210060f0e0702061506070f1403031803043b 73
    0x4403c080c00303500c2d0602000354444071508003881d4618100c6841091141000d03001401c4140c0702e070210300000c90300800d941410b80d019104100c80d06090401030084220007004a51081e4004003091007944003040c207040450741074031510426101e90340ca04026100040204030699130b036544c049214a1075019281c010107103c4409543e41c40740000090030f01240d44c2020946920071b031a108443c0d180082204c08481e0084a08284004803000d12409002d105d080c140c1600d05041c011000d02a000008042800d4200c0c0c6108990001d2071000050310a10f00420300182824801b91301c07254083e0704505400c03130241c0f0644e481c0c0d4130310990b079008031000c581042c800320210b000184905030004200d960007034124001000203140916100c40400c0003c0900d9000d0000486c00d00100700c170512680c02c0080d4010041011203460300d20199a94004840021a032180446030000003500441280c0070381c1c0c1202102c944d84019040c00c01050401100801c214601c2c41004184034581845074a000340000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 494418354 1250 494417104 494417113
    0xb1210080c060d09051006230303040e0a05041a160e0d0308070f031e0209041103130f21020c1009061b03021516021204060c110105090d050703050d0503040f0b06030304090608 77
    0x4008108c01e4401d42510443c000d5004000074404194070590444d4080e800c0d800100319596146004040700d05070800582d0810115810b003c014034064081041b40c08290395000d6100c846030040000d03401d01c0c804041c1c08a011000440d801601c9600311000c0280217040100e050400c107140303a2108183e0720056900c150380496082520310749070141e500a40c2201605d0303030540c01c01d11848050501c00010080082c0c61085503d01000311585101c07030480a9084407000c000201c80d4060b40314504100305c20300c04e48071411420400e50050f03031540299200d44e034405080665403d00c40810760801d900c1502907125655440003910252120207100c3c0b20f03141e5100c54985c2000a01034580b074843e0a0b0942022002d0000740701c2141d002032040345c8990862400c0c2507180d00280183c83c240304240503103400118400e035290078008002505070480e88624201e618100702c101d0101c1c0c890100303880c018540c01a01d00c1c541d000c5940702c1608c51704401c00600b503d207803d9a40700190100c40c502e0340300408a410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 494419604 1250 494418354 494418389
    0x161112120f0a05010b27060408060712020a0905152209050106030c0e0f010c08160209131e1407091a03072d0b1210080c060d09051006 59
    0x4001400340e0300701070180ba041c882035040c04900813203030003807001341c18a00c004c03098403c41e84650002c403142d142d0400340040c0e0340c1c0c549446c1d20b03d0312007804455070004071340255100440c00010f4422035140c107105507a08046541810f0812198402c14110260b02040c10302500050b18010050b43c5000c1100b1541410460302d84007000040d101c050f41310500741843d04900c0b4007420f401a0070351100702000c882403130743c010f502d90059544c0390010001400b03808010400c4a0800102043c000244e80225840c074842c0d80d6031040001c80140c070303100040070b40074103001d0200c0c8200e8a4040c1014144200314400c03150044007400e03458542c1c142e008aa040380c54100c000b100354003040315544504015000b4002141c109052441099002c4103070000001c40100d035400c2c004621036007403020301140402559160f040b00380443e01c10f401920f42101c003441c100320011b9090780004852381d00000103070046081c4110710011800405a403c415912402007071a1001c200d00c152184402a01400341a45101c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 494420854 1250 494419604 494419621
    0x40902060f1b06220f1b060e090c071e06090b040b1305070314071e0e0127020d0b03340503060114010302130f06080f16111212 56
    0xa0454000c8560f504807409028a10700000621414501d43c6070b4910300d05416450000c0b4503051201c0041d0030120b105044001c80e60258604400700c45182d690860601408010401d16250580f0041035a00e01000260b0001d480c41e0340050b44440d05c7c154a09070000d558440100765100504211488040c0d08100701c02c0010103005240c02449064041201007807940d5216510a0030b800041d2440508428000d141081000030303401601842e42e028245031305201c0c00740002007541c0950031511035004008205065110b4001d0000d9a034054450070350442c10003503030000d41c0442005490240c4810503200c4a8800700301001013840202040180100081d49504c4030301c0c50303000b801c0040d00e02c0e18400c00140d940042c20a054072940002c0701c4102002c0030050b0002e114403014102c1054148000154046489401204440741c940f14010260344003814441541d100b110107400e182c4000b0442d4070114480d400180c81d090b88101216442000c03000b5030700d443c2d000008007640f0030341e07a030703040003d2403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 494422104 1250 494420854 494420887
    0xa0b061b07031b0b07060e0f19050d080c0f0d0b180a06090b01020d0e040b0a0b040315021e03150a09021b06042102030706020d0f180201050d020702040902060f 70
    0x800040044009060074180950602c0c0f24681024040d01d13102d01000d05060005c0c0000e01150040c942110070880e11601c4c500349ca60500c1d00165550f00554250550b9075006648461040808440244c9402224480002150064418000400d980f480b64254586030216a29a254440900c188a82c80d042e031560b4141c03001501301080c130b02c0c149144082240d0b00014140d4001189041180c3d050a013040840d00502003200303120781c0160043c00c0058050a04002002924056401d0300031080d448903101c4183c0c45104101110003034800100ca560b500d014010b560400c01c00303148141c010780b9040c00580540b141da040080324513400240c0c03000644404a0040300081d0302006450245043d4540d0400b156408610302071100c020500030180301c1c800e0085540031035104c4821516164a034941d03100038804480c00c41140340c5040003101700400510070601e201039051390303a40c0c0b40054902e0104081c0d00055812038001391a229070800503500e110142164610501c89940c45403403a1190302d034203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 494423354 1250 494422104 494422133
    0x50d0204081b1c0201020c1c06020406030504032a0204020f0903010905010c121a0d1e030e0a060c12030f11180a0f12240513050d0f05030a0b061b0703 66
    0x26449080700500050741c000c201c445000c7c0c402c64044142c140410004403881c41d8080000300114800500490f02d25050f6000380c0c0514043da550702004085d00c0c00540c407003140d4605140c4407a84095081005181070740050121100000c00b0714180756000c40840c0c25079050f0a4116810394440820f400025400700203150901c144602c184501070220341d6a00a240200c007c860088014008810a02c0480d100c0300e0942284601c501110b0007c6060003844031468180541c8110340038100003d07424410800622080d810002d410000b200d0b0400a500800c41c0070084040030761281038082542c0212006003042c15501012082e24248040c104903d510b0240c000c0c3d140601c4950b0706200303580c91082552003040d444220480c1045120004584408808466554407401d040c100000121031804258140d840388080b80c41005949100751482d0300032414440004005000140f42d10241d45c100305c034500f5015200702d14051542e1008080b0b0004010f400c07690740d211240030020071050008a010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 494424460 1106 494423354 494423389
    0x9030318080c070b0c030a03050421020604060e06010308070602070602040f0b0c010b1f0305060d05030703180f05090f04020a090c091809050d050d0204081b 69
    0x590b4014080c00280b030052220003d601c1943d02c00751039002d034410707002d1414009040400c40080000500642e1901100c90700c601c0b4001c002d004035500d96155a0240c490ad2905003080c03805d4030005007076a00158010001000841d42400c203507070000d6800399015969000d0b40c1000800780c0541d8100303440980740c000b00041c00716040c00040c501550704e031000707210724100d11040003442c41e03040400e1003485c1076060130807050134401d50020707a01210080121448504580b42c583c0b6540101000303c1c04643c0306c0b00c4010208070309070f9016008080400140030310609183c041421000007a1100103d200150081001c650b240f054032230241c404401c0421a0505442c0d006020004520486407100f06030303080308640e4202d500800080079080b400510000d45014000c644c281d1120f032880b080b00c0d5092101284e98a001c1c82192091407120300c1400b000c03c0c02008110859190200300003 = true := by decide +kernel

theorem cover : BRFrame.Cov 494244604 494424460 := by
  have h0 := BRFrame.cov_init 494244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 494244604 ≤ n) (h2 : n < 494424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
