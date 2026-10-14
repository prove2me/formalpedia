-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2324
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:21:26.538596+00:00
-- url     : https://prove2.me/submissions/63a4b2b0-4ff8-4dbc-b2e7-fcee40fb1100

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 417805755 ≤ n < 417985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 417807005 1250 417805755 417805757
    0x2030606340b040c060f08060f01030905060915060306010311040207060204030623010b0f04090b03070305030d020a02010b0d021c0201111207110109051807090f06110705012105040f060507 83
    0x102d149424035080a0b44190342d00910208040384040940c0c0c1d41e00a0340b4150003241c100c0e442d034101600000101e028002040009042e030141005000c280e01001134a8580e4014007040083d1070740d03030101459501e080910010b8006c18042030842854103041d40102011030040b14054a41030b160f03203800041e500300182d0040300000e4044180740e58071201c0b1042e409060f544044c1e07850028a220794400c507004a001d6a01d425030340f003800003215a001c100f80070041d9402015203442e0381c86411410700030341150b00c40001550030280b04490500d0101b510f6450302d54010095046000014a112040314514008034140810700e000c44192040030844036100d45002c02046036a03000390719200f03407541160000715050004104090100e80d86c0d1a58954084d20140d40c441055581c5400860b0040015030051242e068444401b08107140d12901c0b0a01c4640920200d80e401c99450004648081190185c5c0d07000013078448103082000d1240d004541c1160213130385074200d20a104d45806046804c25944e00c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 417808255 1250 417807005 417807023
    0x90c0905012403020a050906031012080a080f010518131b030204200415020a022115010e060d02030f030c0c09090a0b19180c050102010e010203060634 66
    0x75845102e001ea01561090300c40c90b0950519241d940b02034401d0240d03600c40307407003204003000180c40304002408001c000c24a45010b1412440c050414481c0d60748100a4030000501c1e5000040040d0102d840003130484070046c0c458140300f60822078420034450041e00182000710300c0f00240c008200c900d07080c1075110f008071380800780b040e155204000c05c803105011500305a0310084200301107525004140c40850703199446000c101c3c90006422410182c60440080d80403098070007240301990f0038038035409502081c100b10b4041044440110030f800009200b580814844c032030024030346042c80c0c0100801c841c4003038102c2e0340c5107180141d16400c41d042a14483c0c001d6000c41c4040e19241342c03407442a6040401c1c540603085020ba0390312901807009000708031040c010719007142c0082094166000c04030300178144800303003559181807920382100300040c41080d0043d800c042244580e0760040c070072640201d41c000e040c0c600d402c0002001d104180581340f40c10002d4903040800c159290741800c040064188901010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 417809505 1250 417808255 417808289
    0xa0b0a1a03010e070506031e01091401080a020a05240301090e0c0a030b16051b070608060628110f01091703090c010e032e0b100c06090c090501 63
    0x21644400c10840107119a0403c074440010200c0490072405a80c001d48030141d5aa031100031840c1420b5803000d10340b5090f14513100005000840341d10141c5d00c06641c080c526103990741d80100750759401070b0810207940038402800400c103500c3c15200c0415180401c00d0950340d0040c07010b8004074550401d0f03001c044842e450b208280039200c000d025180c0f00c074400b16440020a400c64845803401c2400900c0a500f0345650000112072038041c0e020713203444030608045032004c01060180280ca6005610602d004580c109000c54254500f21080c0e07200010000005041030f20303041440d0354502c2c0110940014000340f0b404c004117400d014044c000d01d2040110002c07540701158503005184801e00e50040003008014000d0100ba07100c0403d1143c1d44000919200100007911000039003060340c41c1c0e42034804084003c150410081500180c0341c00a45001c03c01c0020030f0b01d16062000d0200f400307084000003500d1202d208000307500e541c04805030701e0041360903a43c80c90b119840c590455600b80c009040750701c80c011107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 417810755 1250 417809505 417809531
    0x330c030b040b190603020c010f06120203120c1009020409020d0c0314070b09010e01140d09110301020c19050304120f0b09150c1b03030c090909060c16050a0b0a 70
    0x2410080401c1500c41c03800d143d82e2002c45125892080c000c4904050300080c1c0e03034001070002d40103801e91031f00c11a001c03c24a80d49001040c0c000307105a47c100c0c001c1c01a03071803086026000740b064070000003e01000e0078207550841510002400c3c03810089901c2580c59214a015880f0700c0d9103400310610501d080300515043d414070501031440d403e40704140b90722402c801e000c0c1c07202c0c4070283c9200501c22b09207004618078060040c5c82119410f001440d403000c0110b511030700071110760000703c902d40c00303040d049034244034660506090344a00c0c100301110b83c1c0308004010705580b913088500d803841c4c061070036a4100794654011115103850801c080d9515800c0c100100244a6011121034100f070703107000103061064914803100c905801c010100150f0103004200020101e50000303960b03c406180c00c091b00d6982c501140815915080035418500511203417000405401c4001001e0340100000800b40b401d040300c1c00e250480d15071203860211403a002c0c1c1500a800145090025409542d1000000c43c4103505111 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 417812005 1250 417810755 417810761
    0x1012141902090109060e061c0204061b080307080c04030605090c09130f11040e01051f0608090c13060b071103191a270109030909020403330c030b04 65
    0xa040c00d80034410014201203a802c10030101c111441418201c0030000f1840000e01140552039194140c004010002c0e81008d00d00c0c1c0c028815540c064651251030843c40311040e800c07040c0d4081c001d000840400c00315000b1170181d204240d10290340088945015100d680b10b406550b01502c14810760383c0290303050601490100c030f4a175403200c4529140d80c4a2a02d940b1005040003081c440034100c0310041c555840103480b141c100400100e99107001780b090b410302c0c0c45403c190101249030400700a682a00200e28140f04586803802900604000c00300c00d0743d0b0f5420040c10030500e90f00000900d90350080041c80041c3c0d54064440f0a014952082e0b138808021305250a015010446054503d5203262540011310701071351400080100e484540950741c0c0d803400900ba8011404541103c2071540c0d44165000e80d03054006840541c8a96903d10000361348030030410036401103002c001c21700b02a0620f600032802500308008007800f9010810313502518107000c0c40c42260021503aa000180d1105100d05450034180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 417813255 1250 417812005 417812041
    0x2205030a05012c0d03050705160c050f10050a030c03140a05100b030c040b0705010b0301051003120f0c02062118010506060a0e130e070b0403060c1409101214 69
    0x200c00b0001207450a03d044c0c41ea626600070350241559980403a0085200707400b0740364061300300400303e1601c01d4103040041ca620041e200d9148619401d252010590402c0c003c00f10b0f8254254a408e0b08003542c941c0d007500075040d0b4414143c105940c40300030092003070301000d11500415130041c002460341440e50a40300154415000381514000c1003050100d03440038542150100d4000d244525211140d528041d0b0251182d010301d154958204420701c09080c6600b40b03000d0442c0d00c41d41c448000303100000002d46e00c0244004030200411014035003c000740c106500240760000303182500c000c0c8802d240e116028000701c140d403102c0c101d80342c004149028410074071170300390081021140e40f420240c0c1c0c0c01c030080c01c90502544590041440300810401523402c0c0e040500040361503010740c2d100c15242d10343c070000c40c0c1152105907011818110480780d4540514801221001d41948040c54107a940d000d001386501c0c061003400c100581c0205104103002c00d131003682c0790840c1400000401d82404810005081c14030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 417814505 1250 417813255 417813311
    0x11d030307120210060807090b040902090702030c0d030506010816021005090601050f0102010203011202010c0f0c090203060a060e031c090906080313050901060503040b130807060c080108070b2205030a0501 90
    0x110140000c00d1b000500c0f6081301c4a01d40b01045849120011901401000000a400c490544244071031190084080c018910728241107569050ac100800c900f503540540f501408160000c020400009819802d080d6a01050040b1a403c45422001710100d603c00c954a03402c1743c01040c014065171400c3c940300c01c0004001d1000754155418030792941001e45141c0301c000d05000010100204200062050044c0241c01201c51000e1175030302c07100600030354030880b0014460b2032010008035030b2601420f845076205001030000d22500740210748220b201d6491014010038004038100c001492011801040c014002c07100203103031218003030f52101940f07103a15006075200b00100001846240d910206496126800c0146080b180c1c0b11111008070b0480c0040c00680f080b00b00140707c100b441400c1e04405d03007990702c81e80e410520340e9855041e10f403600d00c3ca02440080030410800d0034511890700440d01e0b503244180c9150710500b507440300000c1c50528407901c200c80d203035180c103510307900e8400e8100290010380700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 417815755 1250 417814505 417814511
    0x50d0309030f03230403091502010b0112060602100b0307120c0e01090e03031909060c0302070506090c03121806130e060f1003150306051503101802011d030307120210 73
    0x501c034401d400c013803e001000c6502640b0008061511903c2d2150080c00c203041c542c80941c04180000307010300348030400c66003c62040380f510364801542d4403c1204842466000e441041207085222010b00660311606a00d07200700000810190f40d840a11426603200e80d002c1c0140c94606882d031114441d05a2024041034134004c41407007140300c04022240d12964207445c000d40082d450036540e00804203841c0160003e80740c0461350448a0f0194020480c035070048084400945e0340fa00d84683d50000c040f540364060b00079048a20300e02c80b2030030281c1035080e40d90402c0480701c81c5640204503260002c5480d0111089900c00802400c7ca032000ca1a803c04000d841c07404003024014003054000c442142c51204040d940d00c038820b42e025114651001666005005100c04e041a441c0c0c190750050302840b90303229015100030008a201c66219010005c988411840c2d64403902c0d4006403510081f01504184a0022148401300f550302403009040c6248298820a035071048600300030300c1d0141d031301c1e280480ca910b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 417817005 1250 417815755 417815771
    0x91e060a020d02151017070902191806051602060f0d050420010504030311010b03010903050d0b040207020a030210170f010f060807090e09030c070b040e10150516050d0309030f03 78
    0x18505402506c2c155851900e180340d50070302c010b24040882d4031000c81540301060760388142c0d0240d101d036103521089550303270104d0780802600c0101045040c415500814020032441e81440100300ca1030052500041000381403000203184021183d00103600d9445c030300d940d0310820040282c52580201c10081e41440f0700c0c600f240400010f0218840c074000a4103000c90102c0025000c102500311002c0b204014000740002000303031801405513003014110451840c1003050380c0c1d2550425200351402250018240c0d6074561541d000e12480b03c0400300403504000300340000000410f0030040e150f000305000185900c2561501d420141544155000801041071340c10034804440c0c2c0c45080719040c1e41e4480350140030340e2103050409286201c1c10100070800d0040d00380004122610714050421500101021250f51b42c038110710000410b018080da03698442840d5518903110703c260b000e40000d08104030600c003040300d80d031541031402c040d1030600c0c00040d446440721002c00da800001c418048489090a1017520 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 417818255 1250 417817005 417817021
    0xe01050a060f1a030f13020d1104111c180b0403050403150b061c0b15030a06060804031b060908072108090316050a020a0807080d0504030305091e060a020d0215 70
    0x2100190040641703100c3c410209000ca418119444005079000740020608001d0b0b140404013442c0020700c0c1c03442076182462640040448104a0742091100d40d10583c507242821003010040c010401d00c02044036804244000144003559440e00890083e101d05032200d10710302e0700ca0190130003541c807402a1410440d0710203098032500f003503400340042d101018130034941d41c094810082500b50b844540c441c91904071502c00c1c17a03441e0300a5015502028050120580b030701420b80d8844800c0c0c60007000500750002441000071034500030b00d4840d20501c40415001070036200c507041c81e0001441501e100011641c41c0c54402c803101d04002c0a014527050200440c03070f2032841079440c0d02410121110889051080104021060000c00f0440703a000b071190302c0d09500c1c0d800651b507501c09030150081501c0b030480303900c646d540103c0035102166030583c1c03000d1600300340c0010301409584020820003002501c030500e044e2652000c018100302c40250f0300070644601c0d40c1400a02d0b044d84a04031440b2100d40d43c1c00e008800c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 417819505 1250 417818255 417818257
    0x210408071a0a030b1909090203010501050d0b0601050a050409091410060302010503130510091220061803070f05160f0e010e180609070f0504020307080a0f0e01050a060f1a 75
    0x458520b0600240c2100104c0c0428001c8219141030508110701c820081030020a5a10130f2000c0760090740200040c0ea00e0750700b480241c1701c2c1c1c80d00251081c04d410000569542c8200000c1050507050b14015081603030b83c130751680643e142c2600880300204680c1c0e414400490804c4440d14a4055003020310616186400280c00c3e4400a4a120407034074008410905000701048061012400882c042000b800c10382031040c002e0f444144510002141c001001d00c20908040c1000c0c0b003915080c01804043d1520b060700c4080311401e00c038a0b607480c001031041d80f002c03c3c40300403200d02c51401040503002ca08c00890603c44a0364154003d962891000942404048268203030241510100c80d028541c0e40c40b0210222103e000b09122581c05102c2da00400c901000c000c58000f00300c03008544180b88454540e8200000e0b03010480b0715400240118000460904294211507204202642c00003143d5590948640c01e40300704880a1070420340f00c403410000324103c1019080208219060810055150500c541c0300d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 417820755 1250 417819505 417819517
    0x806010804120c05120d060614030a09020a1518060f0914060403080412050106120302150705090409030e10090807030303091118071403010620210408071a 68
    0x1c000c012a80b80702c0705070150701500311060b0020100c5c0c0b004520915980d559a101c0c250150b012810100e00003100b0780980844240c040e107004032103055035100043d80d001030049400699100c0541d01000030b85154400d80100402d8036075442100208100c454124086100d51004040004618a21f4101503209600d0b1050701e62a050350684440f83c1d4002560500940d040030b0303d05080080c00045e100903842c035030020035205400910005035504000b06003a83d800d2005000f60300511300131000c50b00708810311540208103060041c20020500086030807145010360450100d641c1d04c115003000d10782101e05040503001d0380351123200103082c845040d4542d001c0c1e22008050585410202d003c1009071500407062900c090071450b641d240440400400803016100c0b40d011a060b1001003190100321003c590603150705844100d0b0844803144030f00b2403e00100080e0841d8000d082e000c0c1d078034410600700e08828821b208982521a403c4c000000d00704041c60303014809074085001409039042d070710303010707285 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 417822005 1250 417820755 417820763
    0x605100f0c11030f07172a180901020c0f070305030715020f0a2a0803070c11040501080a0c08010204080d0e060c010e01230c0403080a05041d0403030c0806010804 71
    0x44140c071441d02c0240160380052555040c0a0030f10b05500140b0001001022a404103a01d410008035192000d80c440c21402107407206198010b079404030080d1520440404484050701c03540d84080e428106c0c1854070829501314010340d400050b0341e05064410010f1440a024407800b504400d0b2841d03641c0780e928410180c006082800004400600541c235505030b4190302c00c108001c1c2c6e6a0070b0b85600007442c40780ba0302d000c3d92610348400d01e100d840c00c030701d1858021401e92004409207952914203040e2021500c021040360000d0072488840703c0ca40b900c1c01914000d00808005140306480e0745401120340485411060041c0c0c03061000b000074200000b41814004480d00b0003078008807a00b004500107219401c0c200d0800d600300b0b00b050101c45030560014042c0480b1100618580c024102a0744040400b600c1c820b442e5041071001340041800e1200900003000c2c00d05250b444c01b507480640b00681c5031020941c1d8888100301003000300b8590980141c0008000619044045161070000680028070140c0060 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 417823255 1250 417822005 417822017
    0x4061d040f02150a080a06091a060d150311030c100f030b011101050405100b01090b030a050c13030605040b070e100e031f090c06020703020a030b06030307080d0207060605100f 77
    0x1100b5501e641d4415070982e106040c0c2c03295542e00380c010251050b001610300101ca5450100d000442c1c07285403040c2c0c0110240c2a007907220601c100003c0020540040c410080310b20fa85400c44d031001940c12010b54002e620502c0ba14010030803c4040508180d01c0034160f03401003c10a24211141d940040040d00c1000581000100c40c00020012149107036500d0342021250710345000d00c820b00c180010001346000c0e4400c030501c61110150011113400000348111a034840041c0301141c1010030a40160350f0000c5d1106056041c80291041588000311650068544503900e030180320500c0b003405009903008481d400c015500309000008a2503920a180d600410410311212880b41980d05000f00c0720682950f501d94148866494a01002000d00040c1110269403441d000500d503800400c2740403c4a40047c00d45d21040e10310f4841d080f1100e0020400c2d90305000c10042f200000b001c101c090441c445081c00011303118100b0740740500483e040e40d0022403140307450500842403d54030200a2214219a00e044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 417824505 1250 417823255 417823283
    0x30c040902070f06020f070501110c2107230c04060f050906010c05030a020d120510152c2e050901050702040c051c02030c0d09050309030a03080604061d04 68
    0x45140e480c0030a40201300500020b4101404070003140548075031800760000300b0546520003481481031003056100d4409421500b21360b03a0480184000c2c20f00181403441c11441c281e059940d24110344544400380511807628541c086038444c0420410004403000c1e0340c02c102050403c1015070024070203200385c52049013042c0014040d6440f41400040c1c0e039600601303c94403400710440280d180c0f501d00d201000000e481d5198250762144e0350050501851031341c41020f64480c18214803140311f0125680ca08140084080da10099014000c4030301c80d0482c00b03034843d000c254403007000c200503e07031007a843c5806002240240000503815003820201042d0505244e50749205010040c4c07014050350b000a0752003441d022054500c0c9820800501d0944009496008401e204400c40800ca000c01e0f9240fa48103401071264140545856000d241036034015000c582c1030903c0e45000a10b42401888210b000564140601986041a008203405484030f0307440c1841002c0c184e04d10300030481c0c0c02080a440700d0004801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 417825755 1250 417824505 417824513
    0x80408030415020705130b01052208010f0513260c01020405090a0c0905190305070e0604050601050c070506160501020a1e0f122703020321090d0c030201060f080a02100302030c04090207 81
    0x102c2d0740d0b501d00000d0ad00603007107a18049025800c0c1c24420a0303125400c00000040e08803403489074900c2046419107032400250591030380c44501001e801030841140c1c030103403030b2140d4031401809810413a043d440096a12030030b04c0244040000007914140941c0d082031102f000194014071080e0503100143d80201310558050041d0030946125440038205028104001c40d00390145072026120ba0800e940c14402c64441c10b00455445c441c088107940c0d603401c0010140018605039008040314401045e10540303032880c6850b51070880c0e124408a9000c6072402c00d9108007031840d052180007031138443c24041e0714030f1a017420182030203120100141d001552600a1090080300300c804490030032048001c901541c00d1460040d5a940c00b0072a0074040540040c240e000080300704a00d54031414214000c1d0200000f819001c0d904810031410840c155501c40c940440d0070342c1001390070710060210b00002c0c081520240107000100d1505100307282014010800c200c400c440c641c00b20303003c88607c40001a41d84429080c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 417827005 1250 417825755 417825757
    0x8030105011704022d180609011205060a020304060b0405091609020a200703080c0313080102040f2606070f080f2a0f0a05041e031101110a080408030415020705130b0105 74
    0x4440d1ba000d2007034103444201e1807202c1b0352188500000e9504e21140c0e40c0390440c54111210000c0010113503408900001e16483d00c0c1d8015540051243e000401e03003030040c80000b800c0d40c01c115403000d502c1e4009014148668001203250004020140c0304600d05050f0100003420b103c1c60070307035240c500c00344600070f81d007400b90030401c0302c005580024580d0784948515040c50788070741c821401c2d40c906107441030300030404100620031a81200c074402c46201e00a86400003505c45d00403007214044240b1200144220780c54801d00c012032180842d9520703c0740c9001a0040a00320300005822007802901d203400300a403d00c252040300200e401c0034998141c070303c0c0820740002220701c41c42064141d040404561101c042d03400c24050420f1326400d06070440405003910074021040070622010700084002442148294003440c0040c100242060560703519800f951100c01c0c41d80d100ba4041d00b43e0317a000203010403a186024006504454440c806042c802d0b2900c400600e2003007110007484111607a0ba40311800a0380144 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 417828255 1250 417827005 417827089
    0xa020c220b0a03210810050603060d150c0906110606030c120f0d0302040906050904020307030b10030c1d060a080304090f0615030b030606010c0b010b0a030908070803010501170402 79
    0x1c81e89005540c0c40082c89144c0081c200054022460902c089403080341082c1600054030000b40203d4115501c180c10403501c101c4202e01541c204074408a4020b00c081c5a019174008000f494891107015850410002c040700071210703045d201e0303821090612072565001b00e1000b011500440c0c86c0c45802400c40011030810780401e203240060311400d440c2c9194160036802410440b80b005200f00000341d580d0f0244090a07100311002585a0404c020a10008000181c1d264001000c0d04000e014207490307980701c0301c020032560081c5d4441005021f100e4004441100b826030b2140043d6040452249031003c2595240120b002d80d500c0c294035401180c029a5103580728000400000b04030003511541210050010000030740114040c2c054600001c0165010b0b5991404230b40d803140560707006130310700381e0251580e4100400c01d40426881d20482000701d401d080242c41024041c1c02d210383d4a502d0400050003a0b0b40c0e03d0407001107410a04200000350b51540300c50f1100c40c040b0400f01c42008001d0f0044d040e408601 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 417829505 1250 417828255 417828263
    0x1e050a1524030203060f040302060f1504090302030301090f09021f0e1f02010f0204060c021315240207030b04080d140106030f110c030f0c07050904080a020c220b0a03 73
    0x40d034606849403410360120790440b8003e50949900780c50341c0c00409000c440403680600540d0111001c52135034145400500d501c8205030040c0c003260404140003805440290700240c0040c1d01c08401401500304501c541c03400c2a0f46540308009401d0140e020502c0401d100030590007510300004c80d43d401314080c41401d0340f02e038402019481150840d06d03903842040d003503000413401580b801409414140c110300c2110191036298039008650b180703e50820000038030311041c2004003502c032403e0206070001c000881c8040c1162070b0f215100c01e200382000301c6072801c415082e0000c643c0408805c101003404079640350341154200c1c140b6951204110384d9040904003140c90003a000c000340e030002402540c540d0001300c03100042807060000480541c00c174400e502400c078800086400030403410074008440710040900c83d81380b600380c0d0212540c580000760301d603000311400c0d16000e00000b410510b40b80d043c0038030034008108a800100a440d422000702e14401c50305ca8806c050f0303a481406e948a0b64900138000003c1d644 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 417830755 1250 417829505 417829541
    0x60f0504030203120304121d1201020c010e071502280f0506040303020c10051005010305180a0503042d0e07020703020d080a11030f032a161e050a15 65
    0x186011404c403a9200711015101080c00a4200c000c0c24841d910315120745401802e502c044030004410000403a61454200c3c24035075007040000d181c144280030b0822034070300c070101910905280880540781c64100984bc8000c42d00030072140d8050440a41d042d450100b103811581c07007440c0070b07460000d42c0020714000242c40d91003040100300c00c06034950000c241c2840c504003550080d102081c0610261032095a40744044001d11209014651103540100d41c814441014030380d03a050011883c1c2d050001c80d54082e40c16402c001018810040c11201601e11140001d00c9040c0405400a94000180c8140a05ca5808152030003049601b8400c003c5030005e10740041c00003180601519024196610401c00c0c240800c0c09000c585003500c10110944014100c5c924a2a1850b5244500d00140010a642c0b980303040c1032560706151b589403200301525680205a00d801c000c1c0415090001c8a03c0d01b0200c40c56442c1002c240c3c50001590114a0b0192550310988011089140e00202e41c068208900300e0304030075403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 417832005 1250 417830755 417830773
    0x8120705100903050d1a0109090c0c0b09030421020a0b0405030613020307080d1805030f0d030b210a030801050402160807112206150516242013060f0504030203 70
    0x2801d103100c101c04c0c0c40c09807100c0304842d60f10300e0390100307442b82030b030081d070200380c44500400202d41000d440315070102d4038105580ca4a61610303c002032242001c200b83c40524600f20811086003445900200502010001b00d03040070303d40381c0002d0782c8407070043c001d0f16050180c902d0402191410001040504141d000b84c5014003002a07000b4040c080308210a04906007441000806007000f10701502d5070500e88010706542c0030000415405000d406140641180e00c400d03500060b140e00c0c800c030350745003c4507030094104c45441c4d04006040401c180c0000348564410003141c0410311818014820150340a25000c2e11410710b414445500303002058030580100b2190300d900d203001c40010f41440c012a0102c000c22411b40c03180511003040c074608022001040c81080565908111003072000b2074103200303411900200d0024156519601074510b20304500765251040b07498880c8004001051060241103100d0800710410506200c5032441d206620505c920040c038110300c60700c02d108131005141c0282c225601c0070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 417833255 1250 417832005 417832031
    0x10c0204140a20070201050a11070e0a0509100b0f040e010b0d03320904050a02190206070f02150c09010c120206043e12011508120705100903050d 64
    0x2000c02d1038079201c00c203010354031640c0a6084009031044e50390107079903560500002c80403e4600e01c4102500c490070784151003001604d92412280c0300d03c94034440c00082400d041100c010303031820380f181f01055081ca0820240f080c80c0d450307030f186000310000116030209409044622a500400c15a500f907908151080b501405140d00702c40180368913078280716040401c0101192004403982c40c2c1c103a0b8102200d04210641c041c0c9845d070000c64004014410041c94a0341440da003d6243c01024045009600540d0030856215048041600380480c0c5001429480030142c443d4220008000c08c0e80a20b0701c0c01103810002a44180c0300c0c108440d6000443c94103841450601a564210880d81241d000340d0744125034040d4400c5403891b982d5021b007c42500d85004071480c044800d165803000380e64120001241100c0b050340240030383c00445075101c6155110508081540f801d1842c11007000d03035280c808003c0a800107000181011116100302c800180481084c82d088540c4d03c44e1000340e50f8400e040081c110842 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 417834505 1250 417833255 417833261
    0x1c180602030606280f0f050301031b0801291e090a110309011a10020c01030e120d060e01050d020603010909020303070c090510060f050a0302160f140f011a010c0204140a 74
    0x204503917480d8121500c00c11070040b140285107030009000200107000400c0040d01d00c2440d4401540d4000c0348004113601c680c0185d003190005814070000f8458140780ba2402d030a41e0b006c01d45002001d846410030003613a402c1400c4210b110003241409540e644d0000354140344641e21072604051090422a900e00700b600001c1c2c0030b003243c004043c0d4110132403598902c00c3d1400348c0d00441c0301ea2207034010700803082c462001900109425410101c80c0d000352912030005410510041100003c00b020000715103050414554403010160002401082600701c0d905c0940c0d5000103590441d002c2d010045403000503880464203500401100814251020401107403801c0e02d500020f20071418064241c100951300c080c04c403450740c4c40f00c90075008642e04000d10700740d191107500103115010040200341100c003055500c1510344040f050317080d41c6004640c11004143c00c4280a141040309981e4000d0015081031020b0380d00405803109040d041c05080c001090854546800002c10a5660303070201d00c0601c0c2a509035805 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 417835755 1250 417834505 417834577
    0x1915090605040b2203080c0a090503061003060b04021e0f04180501060f02060f0c0d0917041a0405060307080a0906050a0b10180506070c030507030302031c180602030606 74
    0x1403010f82d04d107031184200703003081c01040c090340642d104c2e200b684031580311000c203074041d69411042105440b4007080c075450401c60640108000c5220420a52540c01d140007217400050f440342c0710318010000c1c44040007001240d000382e8040c0311410b5944a00e5070021001030311807648250140c1d4101d4000b0082c242c0a640b03c00d040ba030a603140c902d00b055102e0f00c22601d41100711030b02900d004c3c620011401e4035690b84013070000c00070071150000e8947c0c2103486005c80100c81c0d40b0001c032000c000150900200d000c2c980030401c05110240328078100390411000441c0c50100901c4102041408030004409a0564102014641c1c00410420450078100035110240803c0d1240d14060404030081407042ca200e041602003400b0a40c1d5070005060601c4200010b5522150003a11548221400440441c0302802003000951194009642c1d0b0360400c0212070440c404940d1000b40b0a1904401007400d01021269000003a4016070060342ca64031240013031480e002d07002c09601d81001c1e6480300d0302402d690144603c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 417837005 1250 417835755 417835771
    0x360504030905040c030c12180c0801020d18120f0c140f1b010c29070e040f06030203030304030c03120617060a0605030a08090109031719021915090605040b 68
    0x130550090300c15811307103035800c03c0300c000a0340303d0038440c83d40c0c6503580c0728041d841d2089041c050824400c0d241ca1030101c4081d0860702107a540010b0868103440310b4400c04014403141170308140d07110f0180d168130700d00c0b140c0078200a080c001d100d400a51114803815240f45030950080c00341c0c0501c90701400c2c241e50b03841c061004500e1485001c0000d55100d501c9006c912403014140c0d20383c0ca07903084503900c00059082c903512945841070704460701d40e5480c1c00700402601c10041e0b81e94010009900c0700c1080142c8401070301c4d1f461300b50320b809424005a200801100d501c580c06040011424980c0d1800b1211700303040451100132140b8140e03011965501c030740e06000344104048111219902e5000b1004100c030b20798031941d94194028841c00000801c1140506199201414035800031075a03600e90782c0c50039040404c070400c801d0000170341d420070029404c212000114588010071911111504810580c2020900034001040b0b044814800301602d4000c040101d600100034043e506113481c144441c02e00541d0518 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 417838255 1250 417837005 417837011
    0x150103050705040b041202030f24060607120f2307030306091506110c03010f06030201021e10020903030f0f03040b010b0a08040210110d020c0a080736050403090504 72
    0x107424144650140c50558114082d0140b4007843c1111214040100d500c0890b003500680402c4030180c0c20510540c6a248541c000107040c2d0401c2c2d2400d10345441c4003c0645120b0201401f126004ca42e80c84680705810360b40703013809050344a10f44419170350b244200c030700e298008050741058510034841c1e0020301102c600c640c805000194880d50600141c42c0d10045015840c50100e8007049507034420b458406000400609079a0201d1809000ca801c1d00d0b8800800e00a00d500ca0f00d0070011541d041040200900501800c81c5030086482c05003501d0707092075841c8210494010504004c02c0d642407088880701150160b02d02e503241342e60b03442d084d85a00126426141c0e91881e0000151140300d072001c48a816000b43c1d503105c0b055070340303600301300d03001c50ba81581108114504101d501d220808100703648800c805c5030000d2900440340002c025003003a0a400003440361f084604108801c1d60600c900c1d61301542d404121900c03030f4000c0e00c00b60507245508080c000c0d41c2ca0500007440180741c2c120103450f040d40e60564081c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 417839505 1250 417838255 417838261
    0x1f110709020405130207030909090b0714030403120c1205040b0609160f120b030a0b0a0c030603030e0d080c060712060909081b0106080109060e0f060408070b0901110315010305 77
    0x10007203014601c505600300440c0c0000a0080b4801e900410f1a14480c0c1800a07a05031921181c00c205c0700b40f8501180c2c1c2d54080303018071101e1074000a007000400e003801129031451401e5078000344005a05020072102c030b03848440141181d40242101414000d005e1000c100a241605116a0060050750000e001d0282e00e004500c1e660005440d031400008161140b4007126404082210382d00b5450300350b0303011144d84444280300f46d5400e000014040d805091244000d0400c030180000f22482c00c0c50394400d2510f0700404000082c1c00c45804000500300f29007102c450038450a000340503106001465200c0d005000c10000c0042c4c0001207601300c6454030b0400c200d210380321f004c0c243c103c07005070501810b4810144850384401400021000100e001c0d071001180c42c0785e0f507000d41c5082d140707a00000c4a82d5a100c410070701c00147e0411007400030000790801440345041a4403025211310490101904409540d0b000601d131480940214243c410740c0c03c050703030b60307450482c443e111401c0108020a00181c200004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 417840755 1250 417839505 417839519
    0xa0c05011106041e021003020309011a150702030a140a0318063002030106020c0906030703170c03070f24050108060c09033f0c1207021f1107 62
    0x44100c05800e4000b04455101c5488041c00071607400b1264a11064801103800142c07503a207030302c0704004000e440c09612428940422825150080c1c203400008407160a50201d682d0380032450390a07031950000703060f0303982e034503002180c00e0619591020380304036503e0303c2e6415403400c00504484a68045c1e640e51780c0b036010640d50100700710194402c1e20005020540c1a6069141c07541039400e42202c40809040729110181c200da05a800c00da2080c005a04003c00402d101d0070a00d0585038004c00403030103040590300303641c0c41404429a0310010941d00b500030480041d542020001c44407000c1c6c12070304203200c580461800880564a482d0300c141004150000c60401070b2040c00380c941039440602c0580069502c107007a1030308517080313181061b0345072143d181c40e155145a201081c90005500c410103443c20700002000320741e0419600c0400301c00c4131040001c0c110068002c20360a540012100203299200c060b40001109600b02d01041c80c6400c0200b800c120b415900021980c05503980700d82600e60566440349 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 417842005 1250 417840755 417840767
    0x230a1b05180c04060f020a170a090506190e011814010f030b03280b0109020309070b03010b0a120608010c020604060e070321050c190501110906091e120a0c0501 70
    0x6655694242c050106001d030307a0182c4e09076142040680304403180f003040ca8881032445211850701d410001000a050030603190710602813006418180c03955032400603518540c6440382103101a150400c2400d1a0b0702c031103a8070a03004203511030054400144c03c0d0352114554484c002040c2c0720a070110f5181c030b42c45c403843c5000340251050108010054084021440d0844510342c0f081040f01540f4116200300ba4000752005c040c0e20b01030421004010384900d8071058091030b056203500b155100350380910040210b84c03c0e4004480b800005403034110032440042a40030058070142e04802015402d100812540580c0042c2840c0b1641c06a04180103501507440d4168444602e80000b030b01a40000c00c800c881c0b51501521180484c49600c0d100d454074450030541410421800b5039030503916001e5800505001c801d006d41a0b0b40810001c0b034078035107500301c00000c405104001000d4000d02000c440a03015030103c081c1c482c0011009051f14040802d4443c440f920784942907402c17101e940310342c04041060b504c100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 417843255 1250 417842005 417842011
    0xe06070503132c071e030516080103080409090314031504062705091504120210050106050315040e01330302010f05070f02030313090506030109230a1b0518 68
    0x6058094800160110300840040201a0428850b000400042028044100e170752191001c1d0341c0052030b8203120802c2071990000f099030004001c110401803010030905030840741121b16030f032400a5418210b28082e80c0140d01e10650800441d0080f007040f810344a44542d0080e070701d608032802c1101c1900c035110907a015030030f41c00c005030700c0191040311101a19254009904a54500110f49101c00b0010480030709041c1201d0450b80060141c00000714550100f041139600c6050200c244095810124018028000102200e18128007800c030b6203041c2d1241d0b4401d400540200000b84014002c4555900240f02d4200c0c3c4011074409030700c3c010313400801b8031880c18152907050392540508441c602d8200c03030701e8001d26010f60301e2011a1110310010b960400c005c0030091039400c50100451b261000308812508001c14241c000e034149810800080e0307002e041c1c0152080030740a07422003005400580b500d4088841310003041c80d1000303c072542c1c8100d61007034858111742003214030b8001804900c0000d41c1010080e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 417844505 1250 417843255 417843299
    0xb0603100c0816091701020408150702060622060b04061d0f04111b16061d060d0f05010323070e01090b06070812010801061403030d0b010e0607050313 66
    0x25101007510151005901d0f83d400f420307413a00e0428940c8520242909410500c41d000b00c03a0b40c0042c08001500c1e0a12140f143d40b207a2020b070290614140070f0280d11a000200b04600c1640d031304400f003015114050494042281003001003004640700c0010300c1d8668000e0241704081421750620b407500c00c0780d5010039030340a40c01416080c0440d5480007404054040c10b64200380c0e8038001e00140c0240c0008a5400f2580302c0000002d21542a4280d4003c404c0d071981e800000c1001080100603030840260038425030b03c0c0c10140c070b1042d59151040c0d058001840054000b41c60a424030000206004200b0032003802042c801400c0311240c0314040906039903d4071846540141a9001d0042180b044a0390004014070744c0a09024038258490744c0394240c80c0c2c4800080a0042c240c0340051060600c2441903101829403440294901002440080d07070703034043c0101080c080c5881c0e101100e0180d100310030174007402101030000d80d29280a403800984a8109100c8040001c0750014000b502a20403410090050b0103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 417845755 1250 417844505 417844517
    0x30c090803070804290c0a021e1e0118030c030c0603050f0705160f061a01030216060506030111161104060b0a0309060b09011805010509060a0e150a030b0603100c 71
    0x2500102c203141809100080e6030010103e85c1403a100b0200c60020f01c0813030140c3c0e004e001c0c8280c4520401c40f41451800c0603041ca140540b06e04640f548a0f450750340280781034034055070120700307140b00104c80c040304100703050084030108007002042090103640001504c1c4220a0000d5007503e4041c00c030100c9504403003140c80340c02110b0101d449103015200800139a4820f20b40b10a190b20300e61192410080d96401c00c40340360b5590410305412240c812040c1040010918082d0314143d5054940703c4201141c1901400e40d594070004214580d400b5805040304181032041191564120b813086e03044034214110540d041104464910300c0c40c5007501c150301c01e940c0c01d504068180141c41c43c04500038210000111880c3d41c3c2d80d08901042e65070065224000c2009501c4400018400d0343d0480c103072041a40240c0c0623140ca54188400ca5075050840d100341c0e640450710450664031105010042103020720300507041804a48044144a062850b191042e80c098045404003010043d0450031079040c3d04181c000151 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 417847005 1250 417845755 417845759
    0x705280b0702010608030301260706082202030109030302090109090603080409050718032307050a12050322060e12100b0105070204150f050901080c040c0c0b07030c090803070804 78
    0x88101458100c06a4030000a101c0c2d25075583e5803030356001780c00150449c004c500b5002c5400403103030300708480569110060890307549000700107800c00c90054618000c0007480700400c0141039003c0c0c0c0a40b05940c00a0080c0102010707800e003e03009500000e0b960380022081d41c00464258000c2c0240000c80e07034000451460180b421a09400031301c0c01600341d104210864008905419400741f001380a90f01902c2c28800b44401003001d0140141104a43e400301c0d000713102c040010383e40f40045003044401d58030204031111aa441c01908600c200b08408c0b1500145039034036000e08081000b01020307205141c45120f941d52000c010400d50350303c41400d1001c2ca0f8083d07070b40480310300c406030880b000030181810280c0c1003608550016094401803015810805a10381c410403d01c20f602c0a444010302c0165840710301541024286911512154000c07801241c5416000c044a0b114204003181f1a8210780c0b91710040c1011100140034110a40e0a9800075071180030100c4c4c0828044100c0d00c200342e028440e249014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 417848255 1250 417847005 417847013
    0x220b061c0c062d020705190f12030507170315040603050c0409031e03050915040c03110307181a060f09040e0f010e06070206011a03041b08030f070528 66
    0x1402801d05000c503180511601c000c0a059400c0d41c00c3c8142d65801400b8198201030030300c0382040c402014041404000003041124028445055040e6020b1884040b00e000f140d04054901d8410860001d1090b00000f80255203001c110003d907005a0480d61140320f00c0f03030303400c003000140c0e0340f2808040c120340c11801140d001403502c3e5000101c21442420010b00014112005040300d00c07188280d007011070384480c100001d81000f40034030582c0c1c90b0b8042c60104c035410300c3c1d120791090390900d010042c0640320043d81d181d40359034200180001480301200b144400c124158008018000000e85120a4003070790852200914007101610f544078000d11038503081005903410040600b50008020b04640109400398180010a00034029504d075080c0c001c2c2203a08150000a10b4018140d01810081c0003484000151711010001c5076041508070310280f550b49014070a8905124450f401004548800100400310b04c10600107070200501a01c140c610703992445150807c1d4420b662140b144800c01501d01500003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 417849505 1250 417848255 417848267
    0x318010902011407020f12030d050105030f0a0f030215070e3c0103021b010b1e0915010e1f0f080907030807050a06090c1505180603220b061c0c06 64
    0x20b9000030705a40c0c0e244204404201c7c0c41840c865a0003442e04000307508080f1301c0c0b440c0141401804280c000b0980d5140303528107244c42c0d450b03102c002000d48a103004402c05152080010b02d01c82d80170310100620302e0074441c8000c0c111503100340e00240104400600041c0d402d0045400395044a0180208207a403207200c0030140d985c0409840c2da0341419403e01c0f40c4296001032412000680469038000201805072008003d4118581007180703016101c034000f0082651150091182c2200c1c441d00c100080d1070710b01006031044210008010b030492510300307400e8000090440c111010140e036840381444030191207002c4030501811202516968440d07082000000c1c1ca00004202c00b40c040e00541c1c0810506d55618025600900c6040ea40031141c0e6506124480f02208445c80c16002810010303c1c048200c16070220184641c60103500c02c00c0c0100006031a2284000b800801790394408003119007110b90b10700342e00c14420580300f16000d2800794070089030380c0030b260a001d2070054100b031114000034a840012200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 417850755 1250 417849505 417849517
    0x1150b0d0e0a08091f0f180e0a050f010b0702010c20090108030901020d0806090a09110a031506080309031f0b0901060203070506070923150c0303180109020114 70
    0x300d95a03480310780c0d00c5209000c40089148148295940d0300000000c100301021038041036003120000d000044016030304012980705102181c103181910384c40c0c104111050103030a9104807140346804c0100320800d106903110038420402840000c034145d8036106010280d01070b181c4000d0101e0a064085030200c0c18070a607954100d001403c1e810803034161038001c5003501c3e070300ba4040300180e4000300d2050015a01407240010340c0b181c51422040c00d281800c002122194003900310070701d03103a41c3c5e103001d420311240f002640558007010b0081040180d41c1e10b03001e12403148072845240c4440c41c105000c20402d00120854104d2100200240f0f05407458403500c4201840d01900c15040503a2400c1022147d15050660703802041d03160055502e51400d4104030382058402811042048880b8070148000d00c49125500c001c0891100c1c603061340c4d07d500c1c2c0403646c0126884d00c40308150030041462015080c0c000001c52007405840c410142c0c401d100c1810500381c550b1048000d000c9aa20000415140d100d1006410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 417852005 1250 417850755 417850777
    0x241b060606041206110c1c2a060e0111180603040c0e091006090b0321030c0c0c1306061403040b13020429011d060304020114040f120c0801150b 63
    0x400300c1a4880c41005c942c0300031000d88072038000303030007820011400244911414800f403c04840403590540c0704e803980342e02580c485154154041c0d0110920049138400c11882c0300840003040300b800240c400a64030f0300000221491080074824004890510b203099900455220340c40c0d401140c241034030b03032a0341d44000701004c040d0322a83c080b1071551010360103040001c1410900008061a00c04181402c0c544da4950340307901101164041000204241c041300d83c46044003030f2064542134a60300d1141001d1031205c4d0395500205400f0840c006e510640d001d04216491a01d4444c4004611400050341c2d0004071405060071040c3c100048101e020142e03450101440100002443c00c410484010980d0303019880e00342441c00440d546e545540c110540124840c1c1c1d0204140d0350860300f40004403103101c0204000e0411003120b00072921403030290151406402007042074850140c9500500441d18400c100c03c0c2c50400d0000c00c0003820610610942c090761070641015004203081a08601c202d40c0040d691031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 417853255 1250 417852005 417852011
    0x10201060b18030f03220b090a0b130906090507080916120807020907030e07050a0b0d02070206120403050a02100b01021531050c040b030714241b060606041206 70
    0x2003240c81c3c04c0c0001c0c510310001c406c1c4c10452170514100307001c21500c1c1e9040a0b41904040180740079658500940d0012600c04001c2d4658545814207045191a000d5105e402900c1c01d0400100c2c1c49403194004510901e840d544601c0181c2d100a20f0b10758425103000d5240302d00560369014440d08030f805601d10006c901448030a031914582e0703800710300c0c9800e0480b5181c000075038400004a10040501800c0000c0c0400c032981c40402d800c01c0700d0b0150b1489240d809071070841e0300141000441d12124282c42142c0c6012500388414509402d018100c0c0e44141e020b003006000c0c0985803000a0402d00c24080304101c181c0c01003281e2504001d05001a802c040d20a440401d1343d1810f45048490b50300480e4074501c80c0021050721040f03a031502c3ea18010080e56400c0c03280d4206000318040c0d03280095400304486643c042514480c54500c04185402c00e80c240d07854486c01c0a01022408280a2008205014012041521a03010800e417151142001e8409990003001000108070303000002d82d450b90303040d015003000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 417854505 1250 417853255 417853273
    0x27060b0604032118052b06090311010f1112042f012d080a06030c030f020108100f120812010e10060206060f13140c0301080705010201060b1803 63
    0x1258400012400d02003000510030001d400c03d40c0104c3c0d02074183c042454030360340981450001000705086810360441880d405c00f080100004540c0f0078500f43d83c01c1507041004c004941130080ca0740000c1a0410b2803503003060b1119000502c0c52050241c17000310941c85508090b02060b00d4031041001800903a00850180110301d885103403d8464080050012624907217804520b0001d0180c00c0d90381da004015440c15400a2500d110040030544d0b00c1020f464100c0b919a0740d41c541c0c4000b07140b1500040d04503460030b02e000c410424074000000b1568000d8031004c00cd07075582130f02440e403d5254040da42ca00151664100501403400300c5881145229030172007401d200c124030a00c18200d034240c1c0908800321b110010f100c0344c18442c1e0380c1c66020b040d60744050121854050082190301030160030080c040c201038040d0030000c1145511150610800c60322807079290a11403401d18941d002030003a10018010300900081d55801403149a0480c1c002011300307424008160f410714a141e0144e50700d0b58242c0a8440c0e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 417855755 1250 417854505 417854513
    0x30b040923010c050f04142403010501030b06090a060509040f020706201905070807150c030606030e0601090e0c121507170a090501020417010f27060b060403 69
    0x2a81910a0001030001c0c00c45903078a0550a448501e1501c0042c03000400c420498014500110303400c0d65103021b03203108065202000b16840c2c1c950004031107070001d26440618403500d8007000460480d1001d0b44e00340180b04200701000150321500440b1a0311a592400030071500e40500c0203482c4908004000241e52480900e9001c280d90002000321041d40ea90250304240c1454402103000003900e50007140d051560200b07501103104030041851044c4070012401c10100705050b412034040b0355201c07500030303d090b10034014140a000f207500c600c03001c68100580800c2d614031a20851005151560042c9107503407808080000070300286001d6080c5018000c002c118684603d01d1000d20740c2a00d100034241060030090412a052000e41311004000c20b0000146900710b070420b0064010140c00000201140ca070301d4003030b00900c201d40c001c620780202010701c10607100c4198040041c0c0c04500d8030501c082d07844218070b1a03080a0107540f10030420400042d40011800651103000c40c10070180059140a887e921 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 417857005 1250 417855755 417855773
    0x21908120d5711120301080a0305030613020721021f0b0a030206030903030103030e040506010e0103051e130c091107140703050102040f080d030e1c021204030b010e0f090a0201030b0409 81
    0x201c0180410f010307600981850100700408181c40c44030000080c11541040340d41504c8070f12100000e130401c40c0100120300507941e0075036040c16920741e541c0c2c2103554626a1070000803605a451074220700e500b100241d0a0224008a5181152000c00188050004010094800508104d00038a4119103803140200051700c0e48401140510f10a0001b940c81e90f245182c003d0a04900e030701c50307d0140303081c41c090021698115480c1d07003203107209003008a66950340007641d4050392a002d5601d005005200140040c0c41810307580290018001d40d00b0101050703c5030003280c1990b540c11003207036100500b0440340d800300701d4000c2d010303002408000070744103034958a072503031030990b0859000b0428107010b80c48200316204e0200418a0f030780584d405d080c01651011040551680e40c040075248040d10319180b440404c501c00d1060140400d442800e00f41c42c1d603103d00349902c0300c903400d018640354848981d01080c1d034800c400040030b1240000400401810510b540110041d0070142140394000d900d031084d42c00000c078001303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 417858255 1250 417857005 417857171
    0x1e12010c391b06030908070210110a0b0712050108120c0a050303010b0319090507050913020301051609060c170a030b090711060106050a0804021908120d 67
    0xc00000460060004210001d0100d90043c02410715000c150b0380058600c070f0540740c41f00d40407201c403502040850415516081082481e850074042c0104071410058250b182074082c813840c3d501e00c4187c80810000900f100d50a0190b02c0c9585d10021401c58416a01001404940245801d6840b05040c0d03981e020b1441d0003c1e08243c0c40c05002200b0402d01031401400040c084011050900c10120b40b41c488035154500c50040034020498030340005c0c07103074074440380340c010701580038008010a07e0701d500701c42900d2000d102a000000d44044001800a01c654080621207800c600c004140411080341180c00350700108540e0241512a0300340d800e90754030b40403551b1041c0e071350b9216014001c45d035050150809505801c044180441070100d01400c0f94400303032565205505070307500d50702050100000108221207502c40c50140c8120741c101482002e0406c080c115a07050b0070390922200b03101404400d08516201c20a002da22248a9004000e03d10040b00303440041c050701c00381d00d00c6030755030034140b030b00a0b684 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 417859505 1250 417858255 417858263
    0xd080103030206060414180c13020304020a0b07050319120606050a111c140d05010b040e1506180109030c06021b0411040e07020c1e12010c39 62
    0x41001041415014000703960700c1042150100080030300704c003204200e0000602030b0a00380c0141400d840c10f00c03104200b084881c0c000148007a6891070a481c80c60044d5008035400c80c010441d00c8000111055034106603100e1680c440051400c084a0b5071800c049901754841d0301c001c00450f105290029101031203080094105a600e132542e800c100b0300050500304850f141600c041d841841c000190300d18002c1090345040705464048040202c1c5c20003542c1e24024030b460300d0043c80c6400000a5806040c400500803a003a03100c501d003442d5121002e07459600000000c554200d4003c00c02416090b01c001944000751805040c07010704141c0303945407041ca800303454005c039000d6032042414140118802c0d0202140d08022981802990ba81e44181a5140998400c0c3c0816044400201d07144500074400c1c011000006010364101b0403140c3c0a1000221001d03a41501940d2888060f050403c1d041c0206034034030415032a44100f000d115801c1401345122040c0d40d4000b00002d8515000e0baa20300481d2040c01401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 417860755 1250 417859505 417859517
    0x24040606090303020c0909060714040803040b0304170a020a030e030a0605042405010315230c180105032404091b0503060601090e07050a05040b160507090b060301030816050d 76
    0x31881c0185c81e00e21324090180c829080c807000c0021900000520701c3d030044291510003400c000e191000c03c684d0250360881d900f075007c08140480c201190101a51003180a51b002008140c1c540c1440742041c0300d28080d11b80140c0181490340c012900904982b40616405002c640d01c01100f61984000c0322000d0303400311036400e8054100c10700c125400b100c240e0100341c100002c0049500d941c1d11080b504480780e20310b00820361603546e0700042c5174021259081e0100d6005a070006c0345011440070a6951220500d1803441c440d090f0584159440f07981981e10552000c0d580410300341c0740c10590800800200d0030283c0c07003901d560700782000070040c561281c101154100c0c020412410b200400d41400001400241044140074007080744030641d2306040d4000145003001595926900303000c46880c46240c200a00c0340000066608180c101504160101800340302a04c14081d25656110b040d9240c0402c420340c0001c2c01d00c0180007050800000b490f41805a008402c4468056520750781000e0220004d81d0204034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 417862005 1250 417860755 417860759
    0xd080106120b0f12061801060828020a0b130f0503060403030e0115090b0901060c08030a050402010e1215070f0c03110114010f0e0c0a1e110106090e0c06070302062404060609 76
    0x6c0381940303051400903200092000ba0304140503207545403c0c2040b412058503214190b241842040300403482030340c0d000f03400c254106403100300e0550142c0c08840207010200c4400d01c0010588005071a041c00d858005025004549850300c0c120003070902408800155540c855000060381c86010042004010b103120200c1c000c1d60200c200824003205a20200c18030240c0b15900f030025a8000440e81d01070490b060008058032580012141c1070320020071141c0200f6011841c1c511041c0000380c000b4103949003040c076222591100e0f403c41e0305542c4150702001040720400c1c0c420001f0300031503104503105440400000d0400031b4807034004000c0342c284d01640740c5400d02242800040041c01c0d4a40d070280003072102d00d14080007104018240800c08010700e078501403184c564a00070744111600d52060081304028080301d42c0320800c103001090400f8810105116000e036104090a216094444413905600500007ea96142c072800b00d40844018200315099259083e48450f5554850326000d0402c95a94001c0c5d54 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 417863255 1250 417862005 417862021
    0x61113030507090209090f1b07061b0f0e01030c0201150f05031006182a02010507031802090f0c0d0e0d1209020d0201050903010f020414030d080106120b0f1206 70
    0x80c26500f060501d50300400508090340c58400b036003504990000e501980b60b070345540c01010b1042c1c05104101c420440000c0900c04d21001c3d411012106c1d1000941e00104001e885050301c40c2e030041161200807907203180540d01a90700a0f4030420301401c05000200f40c010320000b00220031000c507009008800c0c0340140500540c00d00f0440304e26001d8160300304101703c13820308802c0007805c409121074800715612004d481d885d50308440343c10380c0c5800030590004400200740030040d018180486400c00045c0c64501c00f85002220104009091900a0000f000ca5121441c08408a1030300500c1c010340d1410230800c90144c20054401d0348c9034564040040c241c05184044010070400c3c102502030030a07403e02c0710800240ea030700581704401c0c0751f090905559901005003c607001d0a0310b01074060701c1c03034400b0500094101c1c00c0840410101422010f42e06180c5003242c00303450b404028000e03d00012882c44038594540150b40c024007211000415640140115000140394003500704100c0d010742e0080340900c8514 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 417864505 1250 417863255 417863263
    0x408030403031d0a060b041107060605040b0406141c0b0103081c050402031e0c040204091a0306090d0e0112050c1b0f031608071b080c030a021c0611130305 68
    0x62a050014000703200c6081c010383d60703100c0b191440500303226038034103204059a03211b512450005a900682c1d03030b02d0741c5090030303c80010011f602c06c46000d03a0604140025620340f038890841582c40013941b0361409030000050166a1480340d000d440540e42e12407003900441c3c008a00e1b00d000314403445060b9955500f40d555000c0c0d10034980842d905081c144410f0100503a4041541c0d00b181d002d00042d81e04040c244c6401c0d07484e01010720707042a0414070028011034800481c2c4c01102000d1445482c248403c0001021301d992030b14101c605400355080210140078003486100d18141411301450180000400b800301401190811303035104450740310001e510081c41320b61680d0540c40394841409445088901800710fa168490300c580040483d21005a44040044c0c800595003000e801c00d82040369a61000c8a0701d0000b89140102222440b98200d445980d103400950002001d9020300a05034000d03a103051060032a131aa84201c600755140e9178801120b0010341701600e11403007114601c0a4540c5076042072420 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 417865755 1250 417864505 417864521
    0x20a03050f2406012d120e0d050714010609020a0f020c18151309060213090504050c040c0e0306040b01050f090103050c0d0206072915030a02010e0a0509040803040303 73
    0x82d180b005100b00044111045080f0307801002070030f00d656090001d641c1c6014000a10020000d050300c1d8850903101c942e071110703000c417619204a408004099000c54019910031071303684c0311340001d402004040c00040d0240001940070350304000201d82c99490b81c55100070ba80004e00504000b5000465000917039504012208403031006840071004848200d50803884000028005681d03a4845450840d80d500c40ac003c80a01510520003040781031003d1034007070080d52190106810410380740764089120030961292901507540200240003d0380d101c0c0500c070190281e01014824801d2111b81d14500761002c1c003c2902c1544203840582145d814401041a40b40030102c407140919449001400043c030700255540e41400125060f209925240c400580b51344a240401410484840054491024400e10486103a050003403a465195190212800b14400645200340c3c158005240100035501030505001c0888000d89006841034a80e00410643c0c001518200e0312003034008204000c0c16414480c0e513003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 417867005 1250 417865755 417865783
    0x40507080f0606090307181b020f2512140105130c12020307050a060503070914060d1505120c040e0a020a170a14100f0c1b06020403020a03050f 63
    0x30142080c0e0300110451a0082480d402203c00040c031002c9940c0c01c0110302e009104400210480c561820b1074803014000e0701d10100b83d110071004d0700300c58950021a01079080384141000349010311925005003c0c20000c01e10110b00615245004903202c0ba1145c0d4803407030503020f80440302000c046103110707a08403200100341e100c90807982100800014031785070f9020112040c00c11a50011070560000070309100c0a94442d590141d01c04500003600e40d00140514412034168a510204039a501080b26000c404080003503070103401048010303c0c0e030085510608405000d00320203640c554842c000b01c1d501c0d458483c0080383c10340c8454100345061816004280c4040d48640150501a101d0380c00b10b501401103000c1c01c0048140101108418802001040800343d0007039140c0320403a030400541e0351200b4000161200c1b0034200130001d40568080d000740c0c08002c42581e03403200718441a0342c0158080100e03040072641c01d0780070400000560340d02c20140e4051405071025002ca088208203252401425000c505 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 417868255 1250 417867005 417867017
    0x30081005010c0b100801021209010c09030201050301151e111e070b030702190b010e06030a081909180605090901090b0105010f0e0307170d1e030b01120f0b040507 71
    0x8000c030390303228900800480d4807400c0403581e926101450000359865030400711079507101050046400c0600c50341207016900300002000042071100e81241c01818030f000c080d010038010801003201090340c5081c00c091034050300e032156100c207019000441c241d00000e84100020b401102c1d04c94204030910401e80705045c880521180311a5030142103403901030f0b92140e582c0500000c00040c480078024131241c001c5001040f030380c00c0400414600013156900a004005540c900c01000921604000401da150b081c2c01004041c14800114500d0f070052484400c07071401c1144901c80040d8100b102100c08600100501c00032400d05e0521040c001070b680024103081e060b80c14518200045041d510701241900c5e42840e10445841e0b44803800e8a582e04d04410b040d0700751044803000144200004041081c04e0310715020750b00102d43c41c0d00110b8042100c10282820100300052a544441c00b80c0d0009000c01010f040459444940c004540201c030310300c81a03420125150350946c81ba910b0036116084c0e002806003015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 417869505 1250 417868255 417868259
    0x1101050103150203190e0601060f031514030f071706071803060b04230402090a020c1c0201060806090a11010c03020a11040b03030403080c0d080106050d09300810 71
    0x58401004809030300b00450707500001060703001d91180c51155645244110510840c1c2e0111103007030341c0d20b80034400e04002403205140803000e107200b8040e0303041d13030201000c0c060403060400034a0310381c1001c4442ca07584e0512810f03a040305241020301c103440007440d41c80c189003007409901e4040c40c188a4000d0100080108040d01d902545c04541c80c0071003502d0704500e0009408141002203001001c5a071000ca080a100e80488000311802e01107544c405c81c03082d5038501164940d44240b40581c0601521400542c00401c140c546080e04921040b402c00c0380c40c0b0001c20850384e242917803428003109484501741d0f500144004418440352000c000c6001d0028600003800181a8130000d454504042008010040c2c101c1c0742091a50b644d040542008801800c0d60b6590781c3ea031501d03042c50742c01303140c0c2d11810703000f11101402c1c0d0a00809a42c0d0495616480740d515140c0260321810080c42c1001d4110fa44098418101c0d000603500400b56201024401c0384a081d2040d0030301c041c041800c01000b01010758600101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 417870755 1250 417869505 417869513
    0x1180507050a0509280e0d030c03060f030201081306050106020706020d081902030a110d0606080a020a0203030402150c0706052701230405030d0c020a0b030f04021c021504061101050103 81
    0x391540101710f0350b81c0c0d0b000d106400f00813000404c0042903400800b070034541104c0c01c0b0500800c03203207500805c1c1d0710104507031520050f00758141e0380c00c2c3c410000342e95440c41040025500803c0c020b42c1c061070141d038440784450369664540c1119800e80000c2e0041c1c1c4031070400d00034150100041009442d90303084c022501d20301004694000340c3c0c0700e03039103060198000c00803a00800709500038580d09207840160980b940c0c1520000002401c251140800088482e404582201d0b000d04c210340d07400e001075000d5840c5555940030b00003e03e4070701502e8003210200300b0204210410a01c103400280845550304c0390741d00f600101d003103021720b8032408400140c00751200280c0c2d00e81c1c0040f210721405141c10f101c21840240781c4d500601a0241e503002540502403554508001a4408881c002d4140308444110079030f80c403042c2c0c401c440d01044640300741c114462008600075141648038036010f034003d0420015803c03407541c0440c00f05202112102039a08003c84c0512038684c02c020344043c401c41c043c008010f190300d5511 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 417872005 1250 417870755 417870769
    0x31b0c1e060316021e1006120209130c0f0b0324011713050708031e070b01060c0606120f05190302060c03071413051801030f111201180507050a05 64
    0x2108007004109280d50800f114000e01405400c5607010115506035013661032034a0701c5107281d01095416616200d8040781d48014000b101c605590040d080407880d90315120321029401380c0d581c080e01c0000e030086000400d5003c80c0c3e00900a0b082c803c1d203050f16401c1000b461f07104131208030640100d20000d00350046199900c140a01501c1905551040d102c0e111ba020300c17000c103041208054414014004041003203000080204144041601c2c481d005542d07000d0408440d00134080c0c01418120513400401030a8414280400f8617030084200080382940d8403040b01c031400044004840c1540580d00b032400740481485210070301107000200b5503404006d031750f0007034865200901130b640b440804004101024401c40055403405003210a01e5a1124001d440508600b041e12606200e0f888a0020481d45001018800e0481e9482400740302c03081010b80c0e465104500c0c6043c1c241c6c01c00d40200402001d103000740101d80704210052500303c04900141007150401e445900700d540241e0343c0318010860350b00c0e100c13 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 417873255 1250 417872005 417872011
    0x515072f0c120a111f0314060a06270f0e0a0b04050907120c0f0e01171c030e160b18030c03060c0c0a1a16032705031b0c1e0603 56
    0x11130149852286a00001c030310703009100c1080002d5102c40108a0642c2e05548a14000d003043d203e80041075885800f0440e03155054002c080005a85201c20200c0d0504008011140d1f8100504000388640358072409480c250035a012407401c00c179510500492040e40d2161a1500d14259800d21043c90f02e5900d4640e24143c510904400311041c0483d0020311520600d40009000d050342c44194035903403408400e00301e400038020a00c40d0300c42c11000c280013010001d4a042d50b031960015009010841107410b80003000001908034041c001d414001ca102c2e26880710710409082095541920340c4070600e01007900102d000ba0840c02544004a0081c4076540050010340c06400805400c3c0c2c0e44c07001030b100908203101043d00500039031000c1da4114000c03078070702d00171803003901042c44488460780d90040c2241a200d031a0010184007070202c5412654003181c00095900174090421a031070135240204207403094268070640b064580180308107800525200e40b4184c2d40400c141070140c803001078000051042e00c00a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 417874505 1250 417873255 417873263
    0x140711120f0702060403020306010801020a02060c0705070501080606121006030e0f0c091906030609030809010b0109090c020c030a060c031103040c0b0d0b100c02040510030515072f0c120a 82
    0x8102c4100715030fa030b01c0840700519070141c1628a5541d5400300c1c0c501030b40118840c1d0015024040003e0703084126030f801d8840c0160001c00520300189040019a20b025004d1320183e00200c04000c82201a0b0001c0311480c0108000e02d0070896580c6080340013812030701e0440d040304580c3c000c005040c2400c1000115800da04030304485444254444920f41d80a520185202c94030050400d0000028042580c1c400c60000c0e00a89804c0c40030790700d000c0351a08a40405070098007054400e0000c3c13004407950351040c01c8030540d900488000703100c1c501c00203162188005e8110380158450020803082507050060300c040f004000001c0f4154101030783c07014801140d07400b60691104d0085000c0d44141d071107400142c03501c04003420088124140c06001003111618840990103941041c3c04160507018850802d404c59800c040070f05140c0101208044525202610341010030080e6a8000b5a254007400029908100300c400c4050b1100104445414101100701c1030744208504251090b0031400840c800b030030f440e48 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 417875755 1250 417874505 417874507
    0x8330f040603020307120c09050402090f070e0d05030d0f020306011d0102070e04200108090c060313020a080d0f03020306100305070903170c0f03090f091801140711120f 74
    0x460003060040026600180d8544100c40300007500e1060310030100c070150300a0300303000301c49911910108103441040d10300940000d120300000b030030a1585882c00d50804124500791140c0c480300400039503024461a000d0fa4181c20010310103844080901c00c0004125104c0415411890220000303840b11058a80031202d030702103d41440402da1091000c00003a200115000b0300c2828542002d1800940007c0180d40590b20400109000c7d0700a02100f4400c01420005240c0e201082c2c050100d2604060115052014014071f805c1c01a074481601001820b2130000804541c8164800205042d008030a03086c180340c0b0420a10119071904184040300c51f6145c103020506440c2d0b004200e50010b096800500001d400300000c10150003000000d22824540c0d40c01ca03202160b1180c2416104e10411001941c0807080c1c580742c0c3c841e410030b01c05941d440062800200f80c117521a04005082d43c0e04d600c140ca003841c810038100503002c2e4100c03042c4d800300c680543c010040810a404501c12a00c520001001e440c54 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 417877005 1250 417875755 417875779
    0x5070e0702030d0f0c032301060e04020d0f020a18050a05060a110a050705101701090b0d0b040c060f0807080f0c07060218040b1519110d0833 62
    0x2000b0001c48824120010040086921811240700100b8840304a1800241440c04428644005034001e81c02410030b4001b0b101c5913480e1440950b40d8038281060203411a4081c0808007009030303588680d21000c1900c04002d0303500c0e680c00304018400124121070840385881d11600b482a0b8541d02e040d80e055170b50640780303555118100308058a80e20816245041d10f8401d00c2040d5003042408150013040b03400550b40d04002201c03450f8151100c02c1c082c1131000e680c400d601c004002c102119007101c917900b03102400420720a4000c1d2103c2d40419400c1700c0c1070b20119580381042181c0d99018100340101c0c2e84903e0705030301c41e0500440090004201901d00c00075011042e02042241803141c044400c185ea00520031591740a10241584c903500c02000361511882c0b40120905072400c107801c400c2d000130021030504e498039043c012607004910701030020b402084902454150601d804021410026015880c1ca0f02e5034038107903043c8110b100d6100814402c06d0f8008000340e040c00041d0000101c0b0800448050351002c2e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 417878255 1250 417877005 417877007
    0x1f170307020603100e09070608010602030901020c270f011401030204121b05120609010608070b070803040c05090c091f0c060b0d0b0106080106090603200a09030203010203010b0c010f050405070e07 86
    0x70444e6003215801c2d40d900c1e0b0038425010340000715030040750b04e07940359044142e0741c0b0f031004c0e622030090802c42d42c00358202c0d041c6c14160f442c04090040c80980c0f10740c0b0203101101c0182a05614000446900181ea91900c00600c003030301c241c9880c603c2d480824079003985450306004030781c4208010700e540280503141c048048001c404880c0858809801c01810141a181c40703d0009a035610040d280d01406501c0d0110215150002284a40645009048503480c0411647d103480c41c0c4e071f000034801e445150840e000031585550311400e950040d8824601503132101181410410aa4403030104107484100c40c0109000c1503401505e25140c03181c2041d00000d121107000d001c00c2011303c02420081074003250b1000070440603001800b442c1a11403c1d5290b101d0262544d10641c00c60f010040101c00310356070288020502c03404c210003000d40c5002d524102400a03a02c0d0b01003803c0e600300303030480302c450a00811000c040340e600748102c420000c0c07400e40078400c604103601c91700e454a0590148440c0d860741480015111 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 417879505 1250 417878255 417878281
    0x11040b040303111203070e01200d05070302030c0307080c0d0e0108150a1502010617160b0d0b0a0b03060f06090612130c1512021801110c03061f170307020603 69
    0x504c08240b030385540b4908181c0080000d9900c8070101c1c04184020b03420b0b02440b850b6075100b00e442901d40001c14201040500588030354101d42c0045085100400540020030010b00c060140360f8440e850036925481ca00c2020f030305062100707601c002003120003044100146e03440122150412a00200c0780140781c080700200f6807864640c0c02548802c14201c41201203258154071443c01c540d1044201e030501182d420055803141c40001d1080844180302001b8003882c8412070003400d9409a000740001d44248a6002c1204003c05520581e5840340c040100940d509202000000c00d12013200d4483c0350005000002d81180030b480040300e201c82c103d000094102884400d8171a00d9504049205c0b101d95940b614081c2d500000d18a0030001031503003010082d600c03018020368011030f040072001c2c1504081c01e0011545100041c00001051242800e141600d03102442600d00952240151084035207030943c00700f0440203a503000ca81101e248220f02c070604400801a5a011a41143d0f00d0703a41e5180c4503200301803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 417880755 1250 417879505 417879523
    0x1003030f0207030b0c03040507081b04052e09060602030901140a020c0d0602030a1103040206090d050319120605060a05030a09030e120d0206070504080c06031b030f090111040b04030311 81
    0x105948010510010b45d8900000d144581e11a80484401d9502c840311151510400c12840001c408950090299885c1c1a0020740e4071096101c00ca526a204a0414843c1c41001d0244101c48607420b500c140709a0806000300700107005035000031450000d1090008000003400800400742c2c40c00030a24009070752090041011081d4001c061580c0c00c10142001740c029401520f0707110240f807070710030020341034000c4809603449150010401d0782440000d000b4000e4200b00e4110446940c04100a00240b1a101420b41c8040d0041961750741074143c0c90520580803525907800c254403410040c0700404c40c03280c0c46411694490780111011501c24000c0c9000d4564010703284000341c0c804590001d510b052071001602c3d008002c5a6821203509840b110029a02d9103e54040c40d0003d4001500d01c00741030070180c00030b540101040440102d2a000c1d40e00c4442150402d80b030150b55070340320f1030501140c440c09000388001d5085240348146020b140c080ca900c600e01c198440102440300072607200c1c0070b9603400d0242000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 417882005 1250 417880755 417880763
    0xf01020301030804061d0622050915040e2e0b030706050c0c0103110306010c050a060c030519060e01052704152706020c0a1b0e070302031003030f020703 67
    0x34480d42c4928110740c0e40c0d0814000c1c00000743c016040c0545e80e10040c090441c030150050301c802d262140300000c4a03225803520b2901c03040351040c413000042c00e440d40c2403018442c80215406400b002d0b480030401055405a0404d01c40c20380c080c00708910204100711400d440d80031106894400b0000007070902000d480c03400303030340342d450b010302c0b1000152650000010040740303051000f980c4003494007400640c1220302c00503c1484880d001d20000f041b950090007081203031400707601155054402a0b4600064419400306840003940728000d01416820145105400c4034a905090050f182803c134400d622620500c1090f00c01c80d0b01e5401c40c803000001d654000c03070004030001c0c0e428661a00b414003c002c211401c03841d01800d850072444480c84034070f88a086580d80c1c407505c1d45e404500b440b81c032650081e401181c20309800e07004084c00300001590741d00c0300f001b007100e440d1300301c1005500e400420603865034000c01ca101070500410800a14000c02c5610401350f81c2d26042240c10081c034454100e140c410071340c01c014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 417883255 1250 417882005 417882007
    0x10e030903190219090504120c0c0302040209011812121b030c0c0305010504110f040c090510050405090702060916050d030f1e0e150a051804020d05040f0212010b0f120f0102 76
    0xb00d00510b85401c5a41310f54001c104a02d01d020042034111040027400b60050305020340258113000500e0181c0003040c50240501d03209803603e04180c1d2444942010394484c000d0440d030702403004200700340d071011000c00780424208901c07401141607940700340f00800c800013001c000324859584100440303c00f41c04007460f080780c020070061410345406c0c0144079064503070764413034005451405054601802404041000742e90340070107942c503040030b00054070741001c04801070101c02d1001089548641131247d204c2c00c0d440d4001e0415080c18020310341019451a121484403044030f00c14815a181c00080f0664180d16240010541c0c0c0121000c4074001444c22480100105c01442d0703039591903201011500380c1d40c00f11400d10001000041d0502e840c411081c61001080051092035002d5883c01203000c24220043c6c40580f03411040043e0708220b5401311070881d00300c82c6003225941581000740001c5c010f901400700030008103034400009040000100450b612906847d0643d10003210700b48402c10010404000035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 417884505 1250 417883255 417883259
    0x5130f05010f0e03030c07140c06070317010f2105010f05070c11060c0606092a03330f0102100606230f07060c051903020c010e030903190219 62
    0x51406400c150080d002c03100e0078070303c401002c0d030320100899019032582070b15a85400301c656114190030348244806e036043c0c0030746540c41900707495240c01171194621130741d101c020b202442c8080b400641c4043e00881890328010000f80041d2580955444841d04140d83c400d18480643c41c20134094000140c0c8446082c0c204024040e0b0749401444421040b0710800032424444049024048280180f515001c00707079111501007440d60924a80241c0c001c12215000c0360341410004c02800c00d401000d020a407007243c000b040101524040c80f80c01100f44003948040b050b00b84401940c0788264031003090503c10303406401c0d681d41982c0200030758003a400c06a003080c0319050740c40c00013a01c006918184170542180030081e2410003001d1100311184070700c50f910703a2805e10245880d02801001407442c017109104040116403045181303114441d241c007000360b0b40942c1d21030960460702d09403240c1844429003548184505e4541c0d5070003080c880301d81c80c0c0301e1520001c6000d00340002481e5540400d07655050f00f03007e400c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 417885755 1250 417884505 417884513
    0x412061d070f06080c0d0518030f0301050a08010b0102060606030a150305210a0813062301031202010618111c0506011704021c1506091b18030605130f 66
    0x820040701c40d91108241040d943d04802d42c0c5410342200d41d90304107201000b401c1c00c40c1c90349601042d007001c01c00400081c40542100c07928a140c0c044c00c06c09444000210042202d4500401440080c0420000130b102c59850100080d5503104094283da109400200010300c0c0c038450780e48070952411500c00095915550390620b140c44212011000c2d14500c025171040555080890407114180759030358031a10641d8496400c402011510072040701c8182e11441c001d0003100c80b4051200341c0080141049006514514054032180403100946040d64144038041004110220a04c00205510000410a2800c4804001c01031050008031010706940d161035140e4110309601481c8100c10a8a130402008918407400010301c1e001c8500a5114000c84140010207002d0f04212003054411100c1c42d500301c10403000003041e01c1c0383e504006062a03448011a0500300c0481d10901c0302c6805062500c00c4058000300d1060f184454000074080c940c0b0345000c6099142041c0e03400940d40e4101d10155981d6400b403038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 417887005 1250 417885755 417885763
    0x506121204030203060c04150809011508010c450305070b070b010e06090403050904270506010b0a05040302010518030307060e0d02010b0609011b1505070f020a080412061d 75
    0x3e9000303219060004e200d2552590844050380e098040c5082e1000030300e03808030765801d03004000300c81d80c1d529407003142c00702c05d601550400680b10413000400c8910ba5018000c0c0000b06500c00341020342d54000300264a000c512074404507000c102005c024055211a241c0001400180e00041c150721665000060300070320300c1c0107030642030300c2100070084690303a40b00018500d090640e44258080f8400c0003080c0001d0044000740b542c07000107000400c140c500c510014069104800e4400c000c0d05140c02034604000060007040d01500c80e04200c507060403030019000741103016038003009041c4400001e03180504070246c0c444c6820090020216a07940ba510324044018007a151005029440b072149482c922078018000d6400881010381041e06190543e03004640d0090044804840222207046004c08a0381d00b0003018280041200042001d0402000041a19090f58000411500324101100004500c00e0480e022100e00380c4090b40c218490b414001c0090007421492102000c1c03008602e80ca281e0045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 417888255 1250 417887005 417887009
    0x1d0103150e071707140307030c20070602010f0203040f1101020a081305010e01082a0c030f071a0403090b0304031716030f060302010801032006070501063003030506121204 75
    0x14403002c0b059110050181c0b0030003c0c140005c407000c08240300151147d4440c1d40101480d5080380352540303198141900300c8043c0a032503070002189400648050000c10380901a2901c3d0390030485c0d00310300d94589a21800340c86031640400509541100440c40300a80c8200b00006040d90070070841341c2c0e80d41c3c1707080318008059080d2107290301040c4101e03a040215801048040d102d21060240f90310320040401c102d40340d80c5400c0b40400c2c040d50342070201c1550040200058840300c0384410140b40d842c1218107041d00d002d41081460100861940700300000641d125014004985140358140e072662210b240c244c40ba544010791110303500008408020411980100301103001c60340d03850421140d4401d8190800380c41e80d40c000030303010604080040001400e5160144070314039103a105080b014100c140003504507441101d040d00da903034452505001c1c480c01b80d14000c1050080075075200344c40004003242c04945035070602c00b505040d41d035800105262150500c07040040100016a545000601c41c01c0205070018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 417889505 1250 417888255 417888287
    0x11030f090606011715060f0a1218030203160804033504080c060c0312040c090b0604260c060313030201050f01061e03140408030403030c1d0103150e07 66
    0x203140814010f5026484401082516482900b540e584554803c52144002e981c01ea4014004100c02a0a10544e1000e450344204035613848450821640c4400c0c01d03500e40040703803001d115a1842c440d0020787c0000407100e020030104d542111340d04641c01d0031030503401150310181100480d0041c0580c5040c24000001c40030170824188010714240c00700d1b028844c080c80c000e68103283e00103a03541419141c860060714001040c03000701d0340b604242650110801d001074078112040c0c01000420310500d44180144104404280d40d070398141071038110b03211440e140e40e50069020503030900041d8a8894140b200141514010300309990784e081c00401c03080d82200043d81900154640710200ba00e415601d280039040300c80301d984800740c5407092429460b6410080e81c8090606541d1554400f400c502048c46920541c02403021a44a02c0e083c02c015040c6c078030a5004400b008102c0781591800e41c0101c21030005c4080a1a001a480c0c08542d021000c8003040c1d040010002070480c00c201107913900c20080b034400302d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 417890755 1250 417889505 417889513
    0x90102190b01120212010c050a02190812060d200a1703090105031e130c0909020d06050901090602030a02070c05120a030318080706150b070506060d050111030f09 71
    0x314500c44000d03650080c0000e20682800c001040300b10310412049500e140001e00154481070306910403402c64141c0440ca50214802088142c02c4540620090824248020482d000c6c100301e07540c0d17a083c80c0700350120b12005e40b40010200f2280e032222940348181c540d100d2211a0190786441c0600320b00d914050f2600d2140100304000f00e43c0030540c5550211001d54000194108103501e001952a030b04001c24083e40c6140c40d0740841003c050229200b070280e10021100f41086527a42081c0388034208a40000d803441d81001243c0740140c4690740e40148441d00800300082544440b071082e4054045454013178003490010040c052040311a0b40100801c0d4880d1140520155480c8140a08603ea5030160462034215a001d00040307800ba03000fa80300318580c1d40e580c401c9042c4542e10344a150300481c0d82a00c1183c3e0300d03003102c81c2c0740044441d54400f0f00020003202c0e01349080350b031781c071640c1d030314001d007083c0c00380314050001402c100d0250020840c8400303c1e142d43d500c0e440d01000410031000100c4803000340b40f003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 417892005 1250 417890755 417890773
    0x60402090907080a060902040b0d0309050301060b041809061b11010605030105310206030c0c0f010204080d1d150c06061e0108150a06050405120c09040f080706020d02090102 76
    0x7500055a004540c0c03000007034012808591100c81c0106258007069030026143d0400d0034065540c13603940c0d001140700c1e03140c0c8092079013020185030071281d25030000020540100405c0c091303440101096207450000d02404500c1000764540400030b4050a045801c540a0201600080c59000b8010224464101008010442c0e940007011f01380c1313005075001500740303a1010181d0007440004c0d2016840940600d046a4543c105901080741d950049810408559001c00c024000003400e00407009a001e00e140254101810016941d0300e40841c00510814410410880e8186048581403142200801410000c1604a100d80c4604580c400d030388004150060b4800540035241188040c020400786040309009000140b0041d100c14901404030700356a81e801c4c03c0081030b03548000c4084040c0c00690364050b2502d1412003803199a01100c0d03c910002c2e00955071482c0540c80740045958801c0c2c000001da10702e0419400d01f046030340f05440740a01114000644907514088540007801d54038001e9007210101c01c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 417893255 1250 417892005 417892021
    0x3021b01051e0a060f03030c0203010509060c19031407030605271b0d091412070503030a1d0708011a010302120103031232010509071b030908010e06040209 68
    0x250100c0c1d6003401d150030b2040403180d8205000a5036400b10b0240da00050040d00c40201a48912981c0c0c812800a01070007154400c5003028003d6581140c084801003000c3d0510744101e103524002c0780400070720310009801e81400039200350014006443c411480c0030641c2004a8001c01600f003c1c000d45008104032941980051156010242c42101000d000c00e21034444480c04103020440780e0f2034400c000801e04c1103030645680c5100f0141003d01c1a40d1160082c8500300c50135041220220180f01c0202c000e21500300440c00100072203600801c90307400044d0b0f800f51000c030100d00c44d000000d000c0140c805c3c0c01d00803503070070300540c0300d003043d4040801100c0600414000440c02da2054400508084409500400000303004110180742980b2242021890240d402801c11007200a00c80c501c0800c20301407426031510842803e254050038060b11019014070303000c1000303849181c0c20001141b52104840042003403500c150901c0b805410894001c1c0b21498001c43d10315900c040555090744079242d1407002c29002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 417894505 1250 417893255 417893261
    0x9240304170f03190f020a03060e06030111030c0c0a0507030503040602100203090d030b040209190e070e0d0311030f1206090703061a070f0203010509030304060c08060108060609010311030703021b01 87
    0x346403084019455913075888618403107810526010284192030fa45040c0c0011004c0c0050a210b0700382c0da03070000e503035071900311311014010000c0c04550080c3d140121440c0c42d800703030740204d80d030110000e001ea542d48c110a4030807514005000202074483d0107007500c0841001008401401110002d81c2116107c0b440104032804910041e201400c0d00d60001c0315103d000303030081e00001c500f100c00810060500c0345c0d4401003000300200003140030010f401044140090145043c8468011000c0d2030103401010002e008290031070400c1ca009001d010302c0f1020240d240200b001141c4d0030303400d40400c00c1e880d00103105003013080345010780c0c1d51031140303e1580014503000c0c070a21880003242c440c102e16108020306482040c034581d02040055600c4040c003000d84000da02c00f401114010075003c0025a501c0c0b409050110448118607580e0b001c2102c248180525072382c0c80040250061070407074000359a2144000140c0c0140041c42150a02e0750300441000300c8290964050a075071a1400a29812485c007601c0250032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 417895755 1250 417894505 417894517
    0xc0f0d0c020d0302072301020601090504082b0912080f0606030c0c010204080f0f0714090402090a0b030106060f1106040507060305040c0806040b071d010206010b0924030417 76
    0x101440300ca14050300d020020b51400030700034010754519a40341e2106225500080c060140c40d054035505101c82568104900782c014119120b00f00854101655010194401c03660300a0841c000c8201034001300120542908201080070b10400040001d032514041d041d41c002100c401080b036000000384001440b40815205c0c0d500103001502c1c40d0f076840744000460300541c0350354000e59402e200100300040100881c82c1080130120051410070314060265280c003030302e074000145895440c00c002c84542c07242d84009800c1a03045400190302e0703550250a0b80100070f108080d80c0c0c190301b04200058030580061700f00c401c410940c1d4611140a0308440d90ba5620001510020021b40c050302c401c04c1058480d41c07103035401520130400d10340c1c040e070340b4080140f0b00803058800b654840b0000040c0201d0980044410000221205024144449040001c2c0d1103100500c01d00d01303003640020b6490300d07550300d414070b04000181c288180c17540c5000050000c0301a80003103070100d07030700d10807400782c45070092036442030b605 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 417897005 1250 417895755 417895757
    0x609030209250818061801200a0507150513210e0f0f120115150203091915020303011404020301080a030c030201020f0f0d060509060d0611040b0c030c0f0d 68
    0x6800c01c502c12595014000e21040c034044809040d1500d4800502040c1e000b202c640303aa03251000240c0c5074050841c0c0910402d4000c96000d41d04200b6074540400175200d1242682c2801e54444c02c0d0f0341811480c13503072899040700c0308500c0c00d402c00c442c0c00c00c0b16a5525503d030080500d140441480d40d6403801c00d00c0b21600342404580c069180b0641440d2802101264010180007803d60030b09a038045185121503164411751a511010050203074004480c8104c010003c40d44040724012110384041d4403485070a0300d081c003c09410316103109800740118a0700090111469050401001c4040203403070380c00a000d82e609540444200001c149000c0c020380b81030381c0310312020b400d1445032070f50141d940751036900c000c40955400f0300500b4460031820000d441001da240f16980e076034559201074030701151100e4000d50b03c1018504240002030f180d00b2989002c4a07030196000034400c1d0300910029080c0203035440145c0d9200c0010f5025203040004c0060305c040540700c01258960190409403030344800903c8a414 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 417898255 1250 417897005 417897061
    0x9080304050f09040f14070303262205160302041808030105060a020a020910031103010501140d0501090813030308090708030a030c03020d1b020f060c0a0c1703010609030209 76
    0x240c141c940000703c0c50b001846034440c2000d0311281d5481d24190804031042d1407032500b189108006042d00905064200f441448400c1d00381c5144d000d4101482c0c00c041e024808e420b521401e100c9144600e8070102502c140c1000440300c3d0ba00c2011041c1d0003528040c0400c038020f50802400c0f04041118101d0003400540c01410341c1c0c02c6a081c50203000158001d10102e03001c501c10b4421180160b11102090b5015441d5070710403000c124103605148071182c1400d401c0a00a0789008010071541e05200c04545100070107d5654010251a003082e41c00340c101e550014004038070001d6a1500c2003561680c40c02100c4c4a500c40c1d559654801184685890580c818400542c00400116040364072940c0000c011081c181401402e004150564004488918244003581e0300386842c1c0e8400d55804100c041c0c140341c00d510040c0201d151800d0f100b0800e0090f403002d0b5041c8000342c0d9034502007140c10b5000740c03150b05013020041e40365039561000624810032480140c0c0109440d0001c038803184100c41014818040c00c015107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 417899505 1250 417898255 417898279
    0xa05011508191e11030a06080a05100b01022a030106050316050108040213020a031e0c09030f0203010207081201090c1d0d051f0b120106050d0b0c04050a150908030405 73
    0x101c010701030022030f0031210360b4032494024011000784500b03041540300380c04040d00c3c1c2ca4040501c004844140d080910294014803080700041c0740002d2002029102501c0402d2181030300c00180d1400500400c82c0b8400e08044006000d480c4d140c45412060701000c80092120320b0341c03031040c940c69400c0d0b00101e84a0701a103030781c240003650003401415001407014240703405c000b0001c018081280c20440d44180000c1d12051601c0c40c01c1911007030411890782c4080d041150440c25070b0094800e0742544001002c1841d140c4d03600081d0f54081d030540d0101a004503660348c0d680c01300c8642881c100c00034041e01e940c091522400c8100c4510a4150398600f0a840402120042401d410001200c8a4400442c1c540c81600d52040c01c0204100345d10f90744001c54200410351440b40820410b00750003420211300c090b0726041c0c0800503aaaa0700307030b4100e559000612600503440b00b0407102010300c1940c0003e81c000a1400c0001000c5050482d030b1002d1240c9566402c805580302d080071512032241d40300d83ca610003806110 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 417900755 1250 417899505 417899551
    0x50f060f06030304030b07020a08040b0304111c15020c0a050d020d05122404020a031401300807170901020d0908120a05090301060b03010e010e06100309050a02090a05011508 76
    0x1b40e40d0300300000f40103d85800700241d54480259216410100402c24040144401c12160243c4561448803c9600750000c01e0b442e44400035800402801034440e80322207281803c0c42d40c00f03070304850111800c5000d40300c00038000e052250391040700101900c010b00c1110342ca915032600c5a004e55515110350400000d50703803605102c0070041d050030742c6604001015040041400e64841c401130410722545e4501003000ea4000c03401801c080016400007480f0740300c511740c17500c4400e14000700a103180c100440a03840345480341401d14050164280050015400c904900714090b00c01001d040c110307000b40e0840b04410030240c0d049800021510801b0407544c4801c6004642e00c10f004045c00c100f00300703441c0036401c041c1072400081c203480042d88071103100040040107000070249000c000780540b890484120481c20808040346442d0440001c00f420075a8a42031041046014040d00100540040ca10180760030641248001000701b8410b90f507010240d09156003144e402142644d10400010069040040481f0300b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 417902005 1250 417900755 417900773
    0x620070309050f061306020c100c11010f210b1e0d02120a0602040b04031a0103030e090c1209060601030b100203030f09030f040f090b010e061b0316050f060f0603030403 74
    0x3d66900c0300081c01416580100c11003c0f070014030241d4005d03c03007140c8010074403162035442e003500010403002c101840f0103da500c40d1b0303200605c1400c0c41c06200d080c2401d8400c84d03811b24142c2c10180c4404154080f00d444034000e0304460b00c0040201d8045048082d14032408078240b01980f440354004404a1500e0b0140c9080d60040c0300540c009010740d0100595651440c080340d10a42185014a50201d400c0c001c5c40f81c1050140b1000020f520318140303a5045480c06445400c14094440c03080c094040026561400d0f10f05580101c98118114040750a000785400e0321050110350160020385041041d45a62401000480809c1c2154000d986542c803000c585281d00100148007183e944010070081d6000000e840c0140010704c00040c8140380ba0381130030b01000503112079210030340c104840c8145001095540b0b004888911a809643c400c01d800c2c002181400e44c021510914516100403020074140000864800d0301c426001d02070b1078843c0c2e15001f4800308940203858894041d40184014000507608130 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 417903255 1250 417902005 417902029
    0x307030b04140601270905150306073002030109140906060a090f06030f05060a06080c09070e18150a080d0519142a0604081c1107062007030905 63
    0x14080c0c03160401e20502c84117501d0952250100960310000c10a0703001020b240d03034070251000c82c0a400c80b0305141000900842d481d800c407004080c0c0000003a500c1c202201980ca8003c00003403001d640341d40c2d50b4010000244102d01420641c1116000007419141010810340d00c0746400420543c1041d0801c4450070040c00014484031702195181d00100c04101d881c0c40750b1400e43d1040c001020540361480380141905c1180d80072941c55070000c1980300e000d41d211091640d10603000e18180340366484050028140c0b01100e1781c4100c03c01c1290050000803521245141d0550006482309400390b9680c21b0003e55840c0c99005100c00a007003801050301c80c0c5103d030000724206403280340c500707408501400c5c1d5000030391100d007003100e2030103040000250710b10100840d1024901d000303000e00558a02070b11075404a11480214080420400ca01280307182003680c0a841d80d40250501203443d00c0191501a004140d04405e421032455264003141241e400303101100c40311503041c1d03514051a454003040c4012180e9007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 417904505 1250 417903255 417903287
    0xe01030204090207080403030216120f02030a06050906060f0109080a141c0509100f020c121f0f060509010617071704030c120f08010b1812030307030b04140601 70
    0x208400500b442040c0060400c003030207040f80c1c0d82d86515510f0040d00d08207503081c0507540c007424036100b00410900940c00f8040981c008952900100d0107100003410f228100e10000c000c1c600d003d040c072011480015034203100300d00c00c0c0d80100c4894024001521000b00d00d21408900c1e074802e83c000c0c40001d0303080c410841481255800c907030f01064001507011807041c5050048001a40204140c0d50718a0450241e488071440c030304141541c00b601240007900ca00094442c540a004150680a02d11000704001c07859404040c0340c420a8082d1074010340c000e014024001c05c010390804c2801b017980e10313045002d60704030380264039a1071640615241c88090302d00010801c100317010086408450120b040c0e1215885030340300744e8940100c00003a16241e09000c0b0303502001010003400d00860428182c0100c0c803141980d0101000d00c0e20f4a42e5007000350402d200c140c0748150003940d140741e150445403000020318007481c100e4a00f48607050011060008860540310180151040c80002c10029402000d07001020258 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 417905755 1250 417904505 417904507
    0x12150612031b0c09160305010506090d060b030708010c170106020f1e01180303020304050f0d0e010e03070503070f0f0608070e011b0b1003050f0c010c0b090c0a061d0f060a0e010302 79
    0x42000560b00d50003115a0969112203c40c41c01706940e05110703081c09030004176101428a517015003c59035080c44d040d070007800199568100c07a51035600b0000c00000f004818000d110b06109c030080240790794400c00000c00041e820f00300200f8014000310703030204484449002000078030354140c106510794142e040a1a201c1d5a40c4006407807148860303540b03030f1840340680c40241c1d0f02e051608c5c2c001d203402e0300384000c82c446d500030b42c1801c09079035440308620405c40c0e401d19040c5006200840041d043c01c441e5440755030705106500000079880302200704002100c10706603021709040e69400041c3c690401c101c1c0c0200001f80d280000810660050800585003080b40b050548004244d40c0c074014141401c2d11110310340c0d5400c880070020420104105032340d440501014142e03811754280040c02641206000030402d4031301400040c0c0700d5a040003044443d5800030700740f1103141d94601d00074260042c2480e0b0400c1d251a0201106000d007007040c4408842c14020f0985440c20354001000c0f82e080d440710350124101a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 417907005 1250 417905755 417905773
    0x170c09210c090a0908040605041d06090601031a06211503030405013f0609060b04050907050c010c080411030303090a061805010603060e0105180709180212150612031b 73
    0x15000086d102420464840321b98550400305800d103013203a115440940d0912000400c0080c2d2607066004d0b410050a00340402c400c1c11103003102030a91020000260402c0002c0384940c100c026900140e00b2207801e1401c00c9409485034a40f03007845c25500032040350554030410041001d940302da89500006880c2a07200303601c9540840c144010000e4010302614001405000d0780301c00075052040d40700803c803820382040035030700c3c4c0001e054643c0034601c01d02d8801c51211002929050055040f601d1101c007500081160044100c1d002c0c004078801d590564070680c0c00b8004401a080c0002282c0c007075400d4400a02d40702e04141c0d502e001510120640c07181d2143e404003072200146090080d400614030600c4081500313036203511160700310380004220011780318410541140c00b1001007205000e8078078075200070500060000030f40701d10b4640b000000303401003440b82030109020008201c02c00d150080002c1980162110020401260440301c50100683c004000041d07085660400c0b5258140181d42a51841c1c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 417908255 1250 417907005 417907013
    0xc070305250b0709060f0206060f03070b03072d12050a0e030d06080c0d030f14040302061207030e03090612040f29100608010312170c09210c090a09 65
    0x4804641c2102d12416031400d02c001650889015400781c495441e00e800788030700d003400c001c1d9240300181102e40514503d0312500880d460901c070030000b42c00c844144503524101300c4401480113048e041e0701e02552240d01c058464201c000c200c2d40c610031095607640f803d42c02a00240e20010400545141e02d0030741e460007550560301007400a4600301800301c000052161a144805082103861a20944a401c0030b006c50400650072101c0504428840d107050130604c03581c0402400741d882150401f80d848100400c84039100700303620b102140f2461055809002900724020b00f00d5490240740c10f560b82c010801d201000d0b40450f600c0c02d0030fa000c0d01401c6a540280e445885010000611149001c1c1d03c084010303e00408400701d40280d50050b8000140115482c5464801480708906000080c9031803018540812031034171400c1247d03560b462500301c146007410103600c103c0d100d034080003000f030280f00190001407841120300400080b001111020b0074000605e9810084500001031040542954901c071000100b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 417909505 1250 417908255 417908317
    0x603020c0106170a0201030f050606030f071218110d0c17030f0c0105011d0402100e210c0102010b09010509010e060d3203133006020706140c070305 65
    0x60300751005088030944c01d000043c2a6440c0d0340250311440d0408040c4003891f244d1030704690384800c840c2e02540c001c4e1181c8030100c45a02111110000301c0d07081141400f200910b8821201e49a40700304100200400c508040c0801e43c40c000340d000e01284000d000420184001300c0d4103180701d014038011740e85800301c09a10022603030040e44540f01e41d60755070001130090601d4410702e4801c1101105040c2c880785890350001d4207110700072003c0010010742e440880b08589078803004110f41542e0034140001448440c00140d600c500b016a054019800c1202c0c0d1201070a00650040c142d4401902110090703080a40c070701c50f88070001d03040b181c000e58250a00c0001c142c188951040100134015403030240c03e0303414040e05c10a910f030354403520207810401c429146200c040b001c2904031071140b0000000c0110003e8090503018801180086060000c40c80d9810041c4580c004c113255407007010104200c0901d0b00c141d5103002c2e000c45500c4c074400700401c0080c021a0240d070107840b5a03502e01410181b1103000080420390 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 417910755 1250 417909505 417909539
    0xf0405130b0307120809011209021206070f0c032a0f1109281509060801020c06100b160f080a0302120c2d0f0a020a1703100603020c0106 60
    0x202999151502154030b018000703080281003030030420121051036180d00002d4070035070075240d0502464101c4104102d41a8000c1201e031074000f012104010301551502c0e8850300b0459001002038062148040d001d4001c0540102d07841d010765900c00c03810f002c0d0111100c0341121110298407001482030000001d405a4800e56419100703c06c0400c40a2030401440b00ea40800340800c861a4012039100307070008420410000721928000b408500c00d400f2520745081e081c4540c000505041c20610085645107054005100c1040c060085800315681d400314030020040e80e0295580b170500411200449101c040c6041c61107034054400c40b100d82c0916a070310004d40e48114007038804260089000015488410b40080d40801c05c00c0d446407a01c070840381003491908034100710fa1050810041d1600392480207100362010300100b2011503654840c8244041d69503001107808551400d00d85510309440c07014113041d217000d034000f81d8840d6503090400d041900650040320b002481596150f1300064172804240d00722038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 417912005 1250 417910755 417910789
    0x30905070f080304080c01090b070f02040603060c0207141009060f11010218031b061918030507051f0f0c050c090a0b0a0b090a0b1b0708030d14070e060f0405 69
    0x80e59038649071541b420004030080c12410300040781410000a07017280c080780ea0840c1c0c40003949962080c1440007070300411040d08064041894000740300f41c0103800103400001e89030020040f61880e0201420401c00300107000070300c0e0001c1c0031810200b045900030b0414001801481c1464075424403014107881c01c80c1c10100e910074840c3c10b01800c0140340d090038400d007079228984409882c02d0b8001800441d40f80d210310102049908008a031105000e44100f4101c5803845144641e041c00b190380b804d055a4034840ca004061040702a00d508210302500312003182c0e81044a901d84032000345182c1000e803009080000700391903d0040703902400c01c0303036141002c0601c210108039001601d00c07036803400d0103401c1445401c008140c036000c0040e2500780e540c141d62442210380005580d80c1d034007450301c3c0704510386540084200307080c851000301151064021000c3c03c0f2144103400f0070020701c3c000d80c071141c16002051f11924042801280a0a52424060006c2c08035001055205180c01da0b40c40c0400d451500104400e4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 417913255 1250 417912005 417912007
    0x5060a0b031905090f120d0b12010e060601111b010504150906030c020718050c09090109020a0338012307020f0f010504061803080c030901030609060f06030905070f0803 74
    0x50b16600755114150704044260002c0c140c10541e002c805954418000d2440c500303000114000c03424214580140342c1d41807001c4e1003103082c00341c0051101c0c00b03450b5030b02c186007281c01031034001003140d44905107140003032064030002d0041d441407441d0641c0034191740c0f4115041200801010a600c450301d25010f10086180c5d44011100e480c0040c0181100c41141c0c000d001c54010140400000c0400e009601000c1c2e03290000003016100c00f60f8002032807003107a11450700044802d000151809030b0764090311a0b845151028000312800310b25000f40111040b000028020390b04610301812003108203070b440c1d040d50605080c0a2107000f072001030380301b00340c90f1400007540500203002c0302181861910b004130a00151421501c44080400280260040303001c0e900400c025440821031082c41030480200847d0010905541c0310340d15803840e5100e522024130240824100500080c260b51244100422200b020748002c0250b41450400c50160001000c02e4820b4417400002080303100a40b01c0b00001005080011 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 417914505 1250 417913255 417913291
    0xe07020d09081204030b10050409140706030510060804060e0102190e0a0e160216031101110a03020304050103020a020c03070b0304031710181e06140f1305060a0b03 72
    0x80070000207070007002050300600050110250090305031000e80f43d00a011a078150b403521000c0044025039480301c0da010342004603400c00e202d07404100b803422074003102c16140f4940c1c89013010780a440c410b9550001c80f940d10071007044514480c07800203422902c02c80300810419840000c05099802020100030201c501034103c00341c0d50b41001c0520007018050303440f05880c0303140ca041e00a6402c8000c081c40d499000064001a0306882030098880148401d00e101c0303001e546a0410402100e103440703589010400300c0e04260303000880054944c095650584c000c49c641824880114080e400000d1100d0a500c1804d4001c5865981840900e018001d9091060784920305803c008018224101c034500d020000c4406004a000c87c01d00780c5026104102110701d0404e0318040c42030000e080b641c0350440c2d09a489101c40d621800700c1e8000408442c015241042da052840c1d00300507105e42288007203a070103103d4080b288540740d1650881c0d580715400500700b111c070f540e03241d203402c440342c1c4211107180440b014505c503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 417915755 1250 417914505 417914507
    0x30c08010b01020114010303030e0f1209040c030b150f070803010b03070216060c0321050718080c010c1e12030207060609060501050a08090304050301152301140703090e07020d 77
    0x8107109200248024041989002d26100c1c0030103042c0000380405480d680c2180d002007041020030010403841e41191107040e03d4001c0d18125400000d05e081c4130314242a10702d00d11601c40c1c05508050382d030081c00b0f1050707142c41800c000c0c1c256004114024801806000750307400328201801441c000d150010003183d8a2601400080c2040482030884000c684032840a000241c6e0080e0840d403250ba16048c21042000c000c03081c511403c1e0079050418400f4100f4041200e9242c0c425a000074504441805500aa89030001c0584423024014901d0010381c022003a0b00108078403240518100c841140507000b002020740b074090114190740d04590109070001200c1c402c2108070720a2a00503d52040c2c10040b040c109030000b00240300e01f1003100c0070010741c00041004c0f0002803003103c0040800400030030040c1e42c0341e90085203011a900ca644500c0e02841d0702c0350070800051207e40340e0003005030b551803010100c080040f9007d8000d12000d90401c4045034012400c01c001c10b0460b40606071070740003808207001c01a4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 417917005 1250 417915755 417915761
    0x90f0b0414040c03150b060a02150711030a05030a020408033403080408070c09150602071719031b0606031b350304061106011e05060a05070c030c0801 66
    0x11000040d610400300004a50344500f1001070300da11030400d1400a101c010301c5000703000c8a8160310b03440200090800000c980000d01d05d84a00300c074801503042940d98541c141c40e100c44181d03144075107400800a070a160742c8100021540880c103c00300504103902c4e286911f01c0e540040c10803180550321503116200300c1c54807141500b031910381030070204088600e035503005040304405440205036000c0072a4010420102d41d02c2d0a000d05185141001540c0e03200c908410416070501c6040c0241c06259000b24449020030090461215034400510460340d00ca060500c520071303483c01c29010001180040c40121b20300e0707480e1640d450b006a02c0450120300b142032900102c8a2921a114180703c504001c10280c40340b10390310a042c80c04c81ca017a07802a008032500b0b100c4c80c0000d5a00e07803c140800240801d1050300041e41d04030000640742141d041e070380c990200006c0c00b0f4030280c000c000211000c1c410000791501ca0700400070f0490614240d401c0032165030310440498601c2e0022503141c0a25081070046c1c2c60244 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 417918255 1250 417917005 417917021
    0x1103030c03071206030c030f0212060420010c3306091a0d020907140c030c03030a0e060c03060d0c05130b13062303010204170609070e07170a06090f0b04 67
    0x10783c104282c0e840c5582c0d440c1c0703400c5184001040c0e04100100c41040d95240d090300404918041c090380e02a240c1881d0282002e40301c0710500f0003d00d040340c8920899407241a04005555000c000302d0100d0500c00302100c03840114088030003a40b034130007000f000390601d04c0c00350200400340803d01190421895030a0010303010a08059805542d140c000b600250751a1000c050b04550642000f0000031503640e0f40c464a0311608141c01884c2c400012aa40c07038040000065105d11207401c82000841e21048280d5251368003070760700014914003400030801c149440b80340d5055180c414468000780f240e540700412541d042c000c2001020640d0381c8000c41a80c1400f0340462040103859404100260030007508001d4986504c1060300040740368804424161000d5040b00c0140120740f29504a84580500050361040100d601c81000d004080700041e8039005a003c5e10b0240701d640d250605800003000c100801c03542e0048c5445003064407650002003034000c912400641d0400c403c80031035400100d506000594500f4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 417919505 1250 417918255 417918287
    0x703030e09250c1e0b040b06091902090a15081e240a0e040807150b010e0f04110415020606030f070b0d06180f05070309021c031103030c0307 62
    0x28000803040000342020200b803000078189802c000702c150900065a200e40c20070f00303500c411440340380c80a10a040700d00c0b6118900c1040d115656070f88180c00d010322000b09403020212100b1107210780d81b0000250f0090b1060000c003603c1e130b1810341d66505441c003410105803032000100d1001c0061192200c440307030340b503103518890151030301550900100e4100310070340314807000c0505d00380c0c0c24038802142d69142a10b002044040144001814142044041035025800484040c5413a90700c1e89808076886c011200c6140c4140c44400c180f0540b081070021100d8070f51100743d802641d45480c0c40d5816203050280001e0003c021401043c98295440a841d145001d410607100354000325800e07138030b024001200c0058034508040c098a0346120800b24000d00002d400031642107030702600c40034107142d040e8071401203004090014070554136140300640407202506006034100c04860503051700d14020b0189201454401c0c541100d03802120b0968506542042d240241c40e05800014840c006511401808580401c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 417920755 1250 417919505 417919531
    0x60d0207063207021b130c0206011502160e1302090c0a0905010201151203110f0a03080109020924250204110406020a06110c0a110108011707090902030f0703030e09 72
    0x800f05000e541c0c2c000c00b5461102410505c1c0741003400383c58103020380c01600c1c0212000d1011001c42c55019441e50f00c0ad000340036400c0c08010000d403005c0d10001e140c442c0301c40741114104503030341000c007448101c200c006d0203500b004041425400043c0c5a054216106001100c4003940721400c04200410420f00b43d44114116810070a4480303140c14403410020840d40608000186e0780f060b894241c80c03034809554034890038018110801c508000c0461190748180c42581c4440e0300c3e0380c03a040702000b01c2c011490400e0300405a01d0900400600c04615020904200d92130b640c240001c41018005080030002901f01060601101c0b00450a09005180c6001200d103051410941000e000959910700e0940c080c08942d1928503100008414004503680300641006642d22a01a4100f5054000e00002500d00003054440001903600c0303880e1001c442c3d040c0003000b41004914045400010740103007102680c3c54040c820342c00000d90020001000158801e4443c5101c07588400d041080141b0004c06903048003030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 417922005 1250 417920755 417920761
    0x140d08150604082a0a0b0409051f0305210c06060127090207020901050406081507030b091602070503071a03221401050703090305251502041406070809060d02070632 72
    0x11240040c2d90036940b030080001f900b992042d2948010b202958429503400140503004002d20cc80898003c0502c400050030000b40c184100071555288181d0800c4000d0b5000900455010740c41403054400149604560403880c42e005a0904450a11688101c00380d6500007019400c5042122400e40141400c5800b04070704c2d03184c40f0099494074071840300c1a1145003c0000038a54601a600005c507030341000d00f840038940742000d44800c100c0d880081540142c8280c0c40d00007494500041c40800b6034400801c199001034a441c07000b45e00b504094420a0303c5040c540c450000040800d00c8010228000e80100c0d600740c0180e40400e0031100d001c0e2020f0101410314507004e02103030b003002c1200d500c2410510a10201600004402d10000e8851001000c481c0b0842d0000e01128040e00900180c2e554031841c2420a25100100200303031065000060641c10f00744610742503403400e100074142c9040544000b607c4c14190b603850703004544030300421741340c03440e50240b0712086402070003640c1c10544c10035031000340d40341 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 417923255 1250 417922005 417922019
    0x30403020a05100c0f05030c15040b160912060219020102130f0f03020906010c14010c030c0e09150310091b0605070c09050601110304030f140d08150604082a0a 70
    0x700c4c0300002808610f02d80425604000b410001c58034241d0030311055034003005021101c90300d0031100350741c25600940c1007808030350cd441454450707c4000005460300761740345160042907201d10817202d40c191400c0d81d0a201040c00c0340c1289a800d810240603a00050f40c4800401c2281040c1d201e903000b00d106400c0341c241c2401640d04030400134060341d404a603a805c890342c072400101c6400c003005a00074a40c48080140c8401c400054012800ca01d0058600340320811840302d003215080c101c1e00b60707241d0000844001c00c44916a886903c0907654014095070301207811803000e001541e00035031007114081d0385554542218640001c0301400340c03a030303072805502d0000c4030f494a0007440d07403902400c85d4495543c0f01103420745c0e008080c402c200d6034540c5d0583e80c442da40c2e8142502c40c8854840203455090707020409003442e20022030740c42c140102942f034020150302c40b201801c41c105900200e2a070411010800842e01c990100648178130391903006500d4030b820aa6000005101c42d40c2c2100303500070b10049000b48018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 417924505 1250 417923255 417923267
    0x1f0e070c0204020d09061d12120a0b01020c03030f040e01062111130f0e011401020604061a130509070504020c0c09061503040f140d09120201021509030403020a0510 72
    0x3a540458000d40c0314000f03681c040000b4548008003c01d0740e0318240b580c400c074010001100c1410200c0f6015144100e54080b4503003071610445c0070079945440003c0020ba00340d06c03642c2c80000040b406204a400c001e0107100428516030180700045000040414104a030380003501c0b015000d4040ca1406a2240d110641303080441903540d078a52490540302c810b940204c140400603540821000c8580083c1a82d441d41007204018660141c1e0032440e10000c00400c6042c0030003131a03080c1003810303402440340b99504d03110400144000100800ca14a088100180d250f58101c3c00c0c61606050180c0054103040c035130011850010300c0d500450240c2c0c0144029942c51001040000c410141039403400c1135a0356000025481380c03000350800e504140c000c02480144845140c40520051080d00d01c40c2076050083c04140d5203280e1465544001034403900c007448895451200344410520600440e4000305828210131156442258103c0490340045020420761408090803401400c056a0000305419601401814 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 417925755 1250 417924505 417924527
    0x1a060f0603010e07440112080a0203090312040501110c01050a0f0c060e030703200613030e030d020105060a0b1306030518010e07030311030316140706051f0e07 70
    0x440e51000380050f451a010300c928010981885490445d9410210341540034140900703603482d0040c00400e2040d10183c02c07109854140c6041c03800d018200300160745c61000c43d501c868681c5085020902544c075060701c080103030500c20709600806075241c50500000501458802207585c08035480320440800903600201180c0f000d100c14034001c504103c99840c25181179441500060219140404081c0f42100100140021a110b640d50500c2403548403985580c004c03c4552a20302a004580801e07112a4110403c1d1641803090519100c401e5500c0006803e00441840b0100540d44500c20081c0300c0c5402c00041d8003410300e6010f034a09244000d807c616041d00340d80900c40a05541d040404c40395249941c0b02c040680d007a000902c0002101f440700d0340c43d041944011000b0a41140040c8940340c0c003c405c4d1fa1060350749000f0100c2400e5072a13000c4581e644100c10580b0402c500f005110f020a07070307500507944640d00344028003a0300100005203018140c1103500090189104e04180301490350b100d00d401da8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 417927005 1250 417925755 417925769
    0x9030c0602090109050a0e0702070806090c360604050a15050d030203070f11030106050105070b060904030504051e030610030302060c0d060b04140a050109300507031a060f060301 78
    0x70b15400980e005840d460310a4101e0b507030105800c0c000042d415608015a803003203400e50300313842c442c03540d8510407a40c45100b81c49410844d00881c03580a41818040849500381d11054407204455040400c003158100e585030502c10282e01040812000d8182401030a0300219101030803c0119440e0510b034444025174000d062280340300e00c0b0f04805051007001031320b0483d5000b00740d1440d0854540780035040640c3c102d81480c0039500301a00041e00d0342c09101959a4140c000103407546540c1e03004100440540000e00480a2141c14000860035441d83d0540e4400c0429000540b0500ca00001c00c040c41d000e00100329603401c111004080c0002640071403044c2c0c00c554501c9406481d1403001c1e1540d0013401c0c058108035606100881c1c005039944500d04084031100041c1d51800c042905d440c011a012000b42c0102c00d40b0800c50000e03110741d4900c64140c5aa0302c00040000c030112046507a41038201111517100765140200a0f0400c058031182a06060700130100319440840c040003513020512a020521800c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 417928255 1250 417927005 417927007
    0x11103010b0d0e120f041a0906040b09150408030d18020a031401180605013f0602121303080a05010806040305030c0903060106020d030e0c0306010306110c19120309030c0602 76
    0x2129000100081d000c48944501340540300c00341415401c0c0560014817030b01610f0340891483d13410401c00c0004071004040d0240130303140303010305105c00c035110b0b84c1c403a03e003103a080070112950340301c80702e0540083d101030601e00c8040d660301d03501c40ca106020785400440e00310309205155500f0005070346086a40c03045030383c0000c040f0040f01e407081000b4014450b001d4500e200d00243c0c201d440400c600c550010781610341c4888001907040a05401c2801c2c0c811501c18080c01c02842e07041c11012011042c0004d4106216040140c90130380200110ac0c0303100c500356140c500f01c5202c4c20414003010741003820580d2040440e8410000b9604d82100390755100d8001c0d002900b4040c00101091100e03081008541c44c425000e01140c4555030740f003c0c025602c08581d1098000646050444030790010302184454807803000170010f00d00c80c2d0841d00c0d00b60041c504151040b290300d1040044e21841141407010900d039210882c000121074149003002c002e112000c103071000c00c040c80c0881c5080040e03000304100c81d119400c28001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 417929505 1250 417928255 417928271
    0xb04090509030409050c0a090e151203040906031109010b0c06010e06060409090317150d080d0912020d170c030f1906030f05010b0306100e1504060305030903011103010b0d 75
    0x840c210320503500321004d0300d400e0a040001d010401e100a104228240d951807144664800361645141e03030075114081c00390701c4280500e400746000d41d80760418402450030780c2d24095075000460102c4020303a104076116500b103117000b030403032410816040c01030801800d40c030325150b02c4403041070312800140220240140c02d54003080c5103856910545001c0d1000030410450b040300c0c1e04025210200f5103c241612107600000100452180a0301c24010034003e4240882c00c25142e0340d40f1525001300c2111100c03a80d42d00d02c100301090090321655680da16030740140c00800210310001300a2031122480054001c3c83c901401142c101e0801100d5110100b000e20340d502e500c03400080710b901604c50440c4c1900da42030100c04000d208a0001000500380300c3c100812400b0850002d250b120002111500c29480401a04100c501180c0c04119801004000c91804003030f44200054215904c0740c2083c0c406074004542e100d0380781000d1040004070345810700d4072411503240150380e0b401441440555002c282c0c4444030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 417930755 1250 417929505 417929521
    0x306182301020d02040308030405061b0a0e030c0405130515041205030604091407050112180312181202010c0305011401200a03030b09130201020a03030525090f0902040b040905 77
    0x1030307400c3d510042c003041d95a41c0d907d01380400c0980098506440e140500070104810703080b80307a030310300c0c000050184080c01c0910013241a80d03840303074003054580c05020701a017610b110f54483c07040501c04c1c805910044049101800c1c414079142d11031142c984d50096250922006c6104074a241c5400718080ca40b0030f81c1e030ba030f40401080191a1411008113550010313140c1d0150044080759010680e4803c1c1d8030f2054110260b50f504081c0c3c1c0c42442490b5a0304c140031680c0c00882c0c410068501d50040ac01e40209003002c6645101c1b1000054800603a5507201c014854008141d0a000d20f0480c90f400d881c0510007541000904c1036101d510740c9059040c000c50412030f955501c0e1600036882210304023016500303074480d9810042d000c2c3c000d03682c00da031260251303100080703010550180345141260103900600e9140d50710355098009000c0504242c82c1410607420104441098030550003440005549400b911440c19000da500090581c1001d204640141710074441c80f039004080e90115000f0081c049050784803206 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 417932005 1250 417930755 417930757
    0x5030f0610120903050a02010c05041809170708030a0506040b090612100f02030108150103050d0c0215070311011a0d171303060603120e1c06060506070606030618230102 74
    0x2100c0a805043c030314900141078004002d4450703503030710760000d20080c82220400c8405200d81d0017070101c0c40b031401081400c032040715840305070020310668260b40900c2c0c03215a80c81c1e0b25048140202c944220000030031016070640d000e069046032094030107110f4030000da0f0000c0c021100041145004400c01d07403101038100307800c110340c00000c82114010032035031a8188000c07000e580301b40114203051080390801950f1986642e0164102c0c0e0308500500394070503881000b01c2e02a1142d2a0990380b10400564401c1e489000c0c1c001011114441e80300c0b05414003840a00c02d094410110850034800720b40780e507603121501c07041c040002d5690f208008244610b00b265542d00940524141e1400c040e02e100000300030041568890300940340a40076145407075a0400c02101c3e03c51600000039003280e14620031103111041c000ca850b502034881d00307021550b140c0703840204403140c00c0894240c5115031608403c2051014512811450542c40307031401d04d5a2269455032550380c03421140610341c1002d403040c0c090a906081d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 417933255 1250 417932005 417932027
    0x150e0f03060604111c0b0a05060f0f03060316080a210f1101150e04060f021920031c060b030c090603090a15021803010e1b0f0414011505030f0610 64
    0xc064620b001115132180c9000f411049941d0b40079009000c3e010407a0700c1d001080e00c01003170f0400ac1461404880d8a80308115400282c42160188109540c03412440101a2080003a20b1680000d01901ca42c0342851641031a00351028511035400141d09048140d01105000080c80c07141042505500e420350440c0c0144215842c10b40311a600381000301c0c4020b00740100d0f81c05a400344005005503008143c40740100d00c2012070060036922110b1020020038010300300d00804c018428084041070050205a9045074043d0300b901c1401a079032124824290f040740300c0c00018011007a11181507180150b0340902c2480f850003514032640c408800940b400c142048103002895121032882003e0254102c8080650009902001c0b04107001d0074080a60605200790712105c620380009003041c040e000a811906c2400780c50780c0341c000300c071032803a000740da250340c010b6012008580305078051035850319041008401007001e01ca010032200f0400e0180580c545280560090740031241003801e40d4400d43c0940700c101d200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 417934505 1250 417933255 417933277
    0xa031107051902031c08060f0301091b17010504080403062403050a020109150818100509070603050f0403170a180c060e0a0807150513150e0f0306060411 67
    0x40d1040012058140c20b00c0e54194404d40889202400c595034452503050440e00c40000201c070400020420720703011041d0411a0382c05000010003081c9a01c0300107031140107400b11030b070701c001c3d0704020801c0c8a21881d118114004a0000b000b031410641d50f5070a01d4490340c440a040c16444081149070512080701030750041000300c540183c42c555a00c1c00365150716800c041a40032502d070304400030300c0c8001100c01c07142000c000d40d14420715565070800b070001240e29140286992040050000340ea001c1e5100e29805514200c2c020401c05103030100c0103080d16001098203404c803403104107110009811186800c0d0b000e0344450403011a81d1041d41180c0105944000c3c000211204000070051020b064040800d540c155640d0007036040f1141c0a0060030805881141c406600c00c81d4200308007020310010440400151070a90b1404c0100c400040c08881e09030003c28070001c1c56003052004642044004802c1c0342c00f6280d000c514259080000e8031028001e042d240129219074880c1d00018055044a00075041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 417935755 1250 417934505 417934513
    0x40c0b0c01060906050901050f150d06030c030b0109021c0207020303070f08090a0e15010509120d02060a06050913020103050a06170703030201050a0207050604031107081f05100b0a03110705 83
    0x2000d40040e010b414a44220b000b003130316100c1d01080d14202502954143d030300241078411a100c16a0500002e00d03041c0110f03419400c0e00340f0900f1220310707070b134003995000b18042c2e2a05448176007107007083e5440c008180e0160b010a1f01c10030060740302c908608454450710030000e0f0300580791032541c00030901303510a20800800b00d00246a1060030401e15101402c0c2d40f0a0a0321180241758a484403000d10001c240d4101f5650b500503440b075265503104800030700b418400603207a800b6048244114610301803010304840056046002004080345003481180b0052804490f1110355040c02e0b80d4036000360060000c082c0c10552175000140050003542c0000c801054440c0d2031030828a04078420303544500702400300320700550034140807400004481c02990403054000010304810303105ca540940340000782d000a4403141c019101d001842c0c000910807001d100b000c0d4254000319031402001c0c203049860081010b000b6035880c00c4e080c4111110b00c8103450900705c49040000700d02c8070310f440100c7c8602895500800701e00c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 417937005 1250 417935755 417935767
    0xd0503072f10021b1818101104151e02010204140f09270607023301090e1e151015080a0e030307111c05030f040c0b 51
    0x103040d4040c07039801c4045415a81c0103200408100d80b4109108078800164482c14045003030350038202610381300450040c00d01a25070340b04140d0450525049850130700e128605d1180700d080040a0080e03440010303494400b00107083c08001c40c0440d50107240221000480b48489107120b40340101d8485000c016400080524404100c500a001c0d40c0f150081030701c0940b02480381000c41c01c0071003440d20441d00c014801000365482020710b0000e02c0031408203421b04002c04402da404104c05200030b50282d01e0b02e40c041c0442c030302c50b4091400d40004030346d200e03c0030700000c0b000300702025803269100d41950400480800c50000d007081031464108128540882c58080d842200401240000d2200d0181014840d511466492040c402d81654551142610110100b5581c040e0180b049006070341c0044410340c00200d0f0300010b01c4040c9075810494910021500740700b8840075a00f02000301140e213603444400c0422480040d000140755001c00741c40e00581910390710108040050030160342c0042c00c0e030b850300340b61561 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 417938255 1250 417937005 417937043
    0xb070b10081c14090a030602090d200906090403020307060b1203120a060b0a05070602070507170c040b03191e0b090d11120a0e0a05100903020111010c020601050d050307 74
    0x20a0340b014004180c07070702c1d211100f10320918280e0300140760081907100380900e991941d0001c0c2d884807510f19804940c00d4160000600d15046089030b00e81802551802080c020702444038100c4050481c5109043d038000300400294000101d0b20007640c0701c0d101281c03020b410720200d1441801d00c030a41050780030100300e201c161a07000c0185171180c02c01c61010702596980d10030b41c2d0520310600509000280c000c00007400412012340041072258442c8040300e041d03a555032040208000c0b50200c1200e19000510780540500c0c01d070003024441c80048001d4070600f0b8201c44032032240001070500400b0354401c10000d060900d0246064000680c0005030180d051400030130305030b201c4059201d038401003450b0700e08001488000080f010811800c00346903e140501c03103401510002c10004850343c5c011040403022480b9201c08001210210136a150f10300c4050642c4000f4056036080c14403011a6031500c9400c034442640020460b04503002070312020f000385218100700b03040d44100d036406040a01c0441d4001148 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 417939505 1250 417938255 417938293
    0x806100b1204110406080318030601140a26030f07110a050105160c15081e040b0c0d0902040905060a0c0c050c0103020c160f060f0c15050601030f05040f1b0b070b1008 73
    0x204808800752b41c0e9a03a29490760100f81643c50500340c1e00309003d0780e02480901d0189070361082c5441c0700c840942030362519000c101e00d560301140120001a0001c04d10000b0041120640c2c811081d0031142c440c102030510300000c005025107100801c01020070b201581c01c0c40501d19a020140050a101c031000c51030100019056240540f2045156401c4e0498000b8001580e8400750041b81c1c0000e0300141601c5601c10220380c0d4105505d100e807404e66658400f801039072180310340166503202e40064500b51400c0040d240c1120ba03480b50102c14440c4110448000a90110b9040c4200304242070060329040d16070191450b00040c2ccc0007258603085030b0301011480000d03850140045840c50303030f58007801481c01102190a654181c20040803510032207002c2e85030112507004694801c40600d00041d000200d500c0c440c050f91030070780c2d042c0d803d404d083c00c42e80e081c058000e180480080d0032200c00500f5610300342c0c83c56000d00c1181c9002e80400014008103203102821804640105040300840b00c035900c0215403000c00d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 417940755 1250 417939505 417939547
    0x130603060b090c0717071e0b0f0601051e0c010b060d1b0516060c021c2a0f0f03030212010e1501030605180408130806100b12041104060803 61
    0x407501c00300c80001e000d8410501102d040aa000031140c11701d031044510545650800d1034116010309035104040e1000340d400881c241e00301c0c09000d41868500b440103005d84070020240400307042103020403128602074141c000340d0b807d242c15840541d07070318824901d0082c01011401207403035200d6800182481d880c2c1c0304e034010201c1c901080360b2101c021440000280c90b103206802203007540080343c403007a5003c00d00541c07203060150654016501c1114204184803004000c20507460040f0354a510004186800455400480f07071450a00d0003913501e00791111442c07020303480300c01080e001200b50702c60201880b940546e00c1008082403209503a5843e00048080194200d80001860b10034200c7c2d0b001399882400f0310401c4800c0075041c1da100b009030301d80100140750010402e441c0170b4410842691002d5082c82c060000348480000346c04141404140741540f4180d5034007000f5900c0050100d0716049501d406e00c15000f0b540941105030100040c808280504215404051749000c0400c24603030034064070f036030124 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 417942005 1250 417940755 417940759
    0x8010513050721060926040e010f06020a300e031902062703061006090608070f0f030f060b0a0315262e0608010c0e0f130603060b 57
    0x6540c544980401c00050907510451280140181c83d07000420502d5200c0c412040c09110352107000701d00c0e500c1c55414609218104101c1d80130005040101c0c034408240d0602615032041c200071070714500035000395288008072010300140c25501642e2620a00c1010748400341800c00040c4924060850001e410081074400c500c1c024010103940c03240e907880800c030840300d8660040a850138200807081541c0c1c400450402600d40d07201074036110074143c0c0c040140347d03c100307066030b40c010700141099002440c8480b194010030600c200e95046c80f8115407c1000d00211101c40e01d0302e08070034508210100c0143c142c166801d9002450003001049808450f0001c0c0305440d840e490502c000c0c075484101400a0712140b244030808040702c0c20981c28604486034030580000e5000403180d031210f4460b5000c009071002a00c040328440c2c03036081c0012012550007190020003150000b0031071100c0006029005040408260788681d805042d605441c1d6503010030b41c0e00326510301c0300401401e600c4e4a0080000e01c0510b001c02c3c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 417943255 1250 417942005 417942013
    0x250c0f05070611010b1e1302120402010906020a030e24030403020f07080c010e040c030209030303010e15040c0f080603010e0f0606040605091314030910050a0e030d020307031103040801051305 84
    0x2041451050117002c0d0b102c5c0000d850b5500c02c0b05250801e02d8996000480144d02c101140550310300400f4030300103044004040e042c4045281130510000d071084004d503010006541100b52180c000c45e0b0000d8481c01c20520556907560304000482c81c02c0c000328000909070340c1c59200801408181540081c07076004600c040c0701180c802d55120b0006958130600403400074001500c0b0b502c8031050381010380054104071420b0801605240c40c400000c1d007503030806d80000005184880801108402c5c01d00c0720503000d0800d542c01c20400002c00e1004200c485046c0c02c9005006181000c6000f41d14254058204103111b0700603107401450a6056030b8495109545040c4154201a400b20b044c0c0307425840540104902e8105003200322203982d990400b400c4110030401c0c107000610034030445459a0144002c0c00d102c035910706590b043c000c0009001c00b160301c0b200e00d000380d0180200c50712007074001045030720311038040c1011320f02401c0106600707103184181c0e040506554240740c2400350f05201e441c1800c0c006031041c0709036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 417944505 1250 417943255 417943277
    0x20c0108040b131509050c0f0d080c030d0c020a03090605030f010905090a0615062705120a0b0f040213060605030a020c0102040305013209120708130b04050f09250c0f050706 76
    0x22030500710b25000d99228107503081d11070010746084010680bc0302800e00703880c100404000410b0845031000600c0026800c850010001c0692100c04540908018202281507040c03d10010030690014003075001c5513984c6c2d02c041449098200700d480c2009a020b141030292038180350307040111060344e00c6100085940300d82000c070820304890014000440c00c01c0d114040354601010040310900b0f80b01038400c0d82c0191280b0170007040080900300c0c4103a00303001000384142400d00c10f0080b401402d4058920b0b051400f1000d01c81d4691040440e030304180c1d200c00260b110314441005034021301c2503900c028025072800f05030003102200e00800d000d81881d596841342e00d4005107040c6041c1070354222406162500031010300e40600049a001d003010340d00409280b8100801500408000c113241e811022000d000450104154035201040c008a038000782c40b00580350a111000c0c55402080c42c0d001117024820041d81c920f107520480c01e40c02420342010464803d00d0460800319242c000501959000948200c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 417945755 1250 417944505 417944509
    0x150c1e3614030a031b05030711211005180f0a290c0a14030f060f03030f0304080c03091003050402040c030506030a1704150e040b01020c0108040b131509050c 69
    0x200c1e110740000b90190201c02480d80d01181d180b00380c440c20040c1d80e000800c12a000c140104040d0031103a11032050f200204c48035034108450740300129800800c030084c0640f284640f0901046001c0e5800b10b1b00d5001c51940c503480c00e410005200706080403064810300c141e44100746400134801c7d8000307000d2404910700d1000c507034020300c4d03c4e40c0e5044091414808007000c00d40203103481008001182e031500c1d1021f001030b441c00c849207040c0d0040e10140c0c1c502507601b042c48603c1c0b6190788524081030046000718901180b04213054a20f010041000d0200100450a0500803809001700c03081084002e002c22583c4142e0140600201f200b0f82c0e0990003145000c000755021806031040c9402110000c0c0109610362040c1c2d03800144442a100c0c0750254107003030200040002030340a0052600069850301030b026000c0405000c11507041882c22811540b052694800c01d98000308015000382e044603c0d0011030340e403c6490300ca80712001d20f0041006941d00e499403915141580302000c000d104800343c0b1604824041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 417947005 1250 417945755 417945779
    0x41502070e13020603010b090d0803040b06010207081c05070f020406030b040611040b0906030406090209070521010b03010b0a030b0303040b0711031b040b030a0c08010603150c1e36 79
    0x10094004d807003080144000340102d0041c1104580040500071507154954031000c407904181c404859083c003207000c0c800c4940c0c05100420141603850004d01601040032104499001e4001031a8140a800612802840003114a81c0f18683c0c000d00240303c1144d5030715100c1582201140d00781c07285881c0c14404603240c2c0703423001114219002c002410f402c0104100400100781e00180c01160b950766036141190040e00c0741d030041d038440e642c0754591030303107031454610b4001d42500b8130000e6180f9010105c0040c07203802e6080041d641541d004024041e222615140141c00410140c10382d10384c503210114000903860100300040ca2520301c03440e0030440c0900790105155a500101e803d203c145410740312008a00d007080d41c481005144020100c44040c0d00944420841c4605600303c014140d44654060003440012103160f007074007107501000c012148034014000c00361421000f8040c10550403680c3c0c00324203071082e0700100504c241130031025840356001074503200300d00c8100d103130040c03d8940c40e800180c0c00120390 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 417948255 1250 417947005 417947041
    0x601170d021002090111060901051b160f03050d15031401020a02150c07020d111912020402031e0a0e070b0403170a020712080c211c02041502070e 64
    0x60001c080c2c528014520602941007031000c141007040c030100301c5140c58402c21000380502c10140001401e070400d0503880a0059594010034176080301000b10500d00c684078066100417a4020400d00c0c9044603e26044400d40300c0c040d1080300403820080e444036108121502002102c1c41002c00d40100300c48411321178240c0c05403124040140e000074409800a0814000042d400b44488a91900d441c6055000904c03000020314291030480541d8020002400c018055a04030358206c03206e804968035080d03c90030080c1c10010001e0145030080003040d4155420a10181e50b40040d0015010900c0c0080082004042903401800303d4840c0c107100045c0c258417075080f02e040d00d030006850300c140d0280404226041e400145503008502c1581400204070f81208040320341c691140c44210340c0d0744d00c1c2d00c03560f81c68003510000310705c01100c46681100c0c81048a00c02c0b102c402c0f403142d60149007425402035510080c041c1d03030b00c010f100352440303118842541d80c082800010f032241c19a845c109500c3d481541d02e17204c1c0c900c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 417949505 1250 417948255 417948257
    0x82106181609181401050a0305030d0b0402091002150106050f0f0c0709090c182a09030210020706020105090309010918060b16050d080c0405041a0406080601170d 71
    0x11010032001c000d100d010305481d0742a41410300d02e10340e442a107003805035903205000c032681c2e913111016800e91a00034011401460203c0f21114024155154680c403840f9006814900940c7c42c0c81e078100c2500c43d501038070804200180741c01c0501d03c201102944501082e80d554000805640010402c1c60081b01030711031000c074403894541040c8000603003402552004c1806146407242140001c0c0340000741c001c18081c0c07480b480301e80550754079100321f00100000e85190b080c4518280300035080811112035024a01441004802090241403042a01c10b007295801c00303504205044d0326410b074a60002a0881240c0c4a60300800c080e6440d6019103440f801409045400104c442c0010444045460200340c3c032000443c00006210b0743d02c09580a0550003150001e54004d00402103209108061107003072158141414454810b03d464207500d91a803180c0d005480c400c5a0703030700c00100c011103088001c049505000c0c10400c407851311a0031882d0344410900ca80009a206d20300e481d58030f444040350004d865801 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 417950755 1250 417949505 417949549
    0xe0708010f0b090d05100213090b1806190608180c0f1011030a03140108190611070611092707030f0b04140609070912020d0f082106 58
    0x2c10210641e903a0040300b0907640603040c42540f8021075400d0122141c0b03481c09082c01030b079952041c00c180080c40e20035800a040e15183c03411421647c0c40c0ca4880079601c05000010004035a58000001c000b00384007407580c040b10402c0d0300049403240d01301e0380040c02913280d031a1074070a6a03400d260103680c4140d000e98031074100300105c1401c081401d000320f0640016180d03007054480100781010482ca9034000c0c4148a0001e601d81400780100d80c0b0000f0402d026140c00303005005229990b00320071140d4810400b0007044595240000302c83c850551060b80d14540e800f62050000e081d90714081c070901e8003d03044852084041c80548401640d200078494038487c10b01f400644980d0700c18806038000c2c203d00d000c0100c0b160326541c0c884200d0b581e40c866002d02c2c0c01001c1503000b19041071001d00c030141500416900501156030414003880450b080c45181656048a150201381100c1c5003070a052554020003c103680c60200300700c070301d1070071b442c01282c050304901244400e07650382c40301001400386000004a80d6820 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 417952005 1250 417950755 417950759
    0x91a0c030412060e0d090303031104081b01030f0c0809070b040e0c0306010309150e01060e100e0c040302040501230904030806010e2107050102010b0f03250f09060e0708010f 76
    0x200c28600c4015843c01400d00051803c0d090105904004003810b102000070b240c00810b004248d094030808080d03001103100c45003020704200140341c1d01e0810711031340005548242e9041045a02c0380d005466406c81e03400080c42200d076241005012144152110300450203448400b040300b00304c080950f81200d200d40ca010000e6142c135030f0f045001e81d001070302a5040540390303407008000c16041c1b00c00301c0710000301420020303c2004440c415400c44160350010181030a041040c048034140d072005000c01c1c0c030b2500b00348a455450307141780c04d200b920699200940260801000168202c88440001e4850804074503100c401d418540800c0b208a00456009011802c1e07200410a1548980543c00ea40c5501a044103224405c220284070400500b10b08526240c0c48805e042c0190350b4280142c0007040d105451940c400c0b051040025120240c6c03560354055104440b2055900310403190354500108600d03401c0c103c916441c0d8a6000142519000b00400d070300448021612142c4210300e4141207a80002640d14114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 417953255 1250 417952005 417952019
    0x1e05030c031207151e0506040608070b130e0a27020625050109060e0f03030f151f051809060306070f0c0b0a092f0607030909050403091a0c0304 63
    0x1403c04030066416a101e1030452040d0162881126040c50000300510320525600d0207010a4417001000c0c603005a051000410105000142034015900d2010b038032603e900303144405604009036580480c9540600000340204080240e108504000b0a4044142d80d00d10302c5482884103410510001d40280b0104598440089205c0e0507400181c6403280310f403030344845502c0340d50a40b0000c43c1c064032002e41d144500d00980b6020456007488004880c051819860410404103c684e002010401100d8590500495503920704241c00e92052214000c8030340e070104801d00034000d400c048140d500c16419004d10100328a054480349216500082c003c1c152076654880031290441b0241d002802d010403000400002048910190b120b14070031000010842402d04040e1244001c42c000d4200d050110b21226419500c10003541d02c0c4c801c0207507000d550310b4100d0f141c00c03900305040e41d00009481d071a1400340b00070107134000d80c61022140c0309a100384001c0c1150350f041502e0b100d03030142c98107140d0041104020305 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 417954505 1250 417953255 417953257
    0x111180f131d06061017130f030206040507050105030105030a061a060409140f090727020d0b120c0d0611090d0c06030e060610080a060803041e05030c0312 68
    0x2400c0090220003000154950040668044501c5a1a04a51010341d55151401040360300d034032600481e00c44640c0c440310031010b44180520f5588007009101d2000183e184441949829045580401c4c40700c41c208103420000d440c0e01c02603801300e1390340c0690000050158450380559061303a60090240ca80a400c40c0d96020050502c9400ca040080d808145820542d8800c00a04010300c4402c3d004100c031409040e8840481340c00a11502c21419440107010200d100000c080003038610150560005040000c501c01151951441195601d400080c0e000c111010540003800300400986040103048204000b03207858141d0625400e8001000d0350042c004a0419004591200c080c3e10b42c417031808284001280c1d10b46004030054071403400312a02000f44991500c1440d1000429002500c2c407414000001000480050b0284003007007401e07004100f041c80e859000700014480c20301120380e61651215100d08455078641c01a400b00c0054600123964100031400b103031210002000b8101e141d4001035400c00e1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 417955755 1250 417954505 417954529
    0x9011509020d0b030d0e01181d040507120f12320d06080708060c190c060b030a050f0c04050f010b21011202090c07050a0809190308030108011118 64
    0x32a40c80300030030f000d1500c0c14041961110300e207650b070302d14a0820200251800950030156000071071100b808000e031104c28030303a990351064244524802d5445034142245480b550350090001119000070300300c10003a000200150088c810164260b840c4034290003030742c01c04184041402291b01c680c0e141e55645155025506460b0040030a10341030801c005050381c100c03842d540080381658000303007043c4041c00d010480164080c62000001c1c1c90709100d05007040c41d40d9402c030080300a004241490130708000302c1e13800203000407801604946070f0b090716003003a9039524000a0500e0341d500461301d04e00213505042c001d00e03200e01c0080080078620f034a010790b11107840d484103002d0065815214600c2c0750400030040528001e00c2c41c045800b421403040d004003d1b400320040c041c2382c1992030820148001500c04507141500035002601c1f90303155410f4001140070340d40d0208424a42005420020080260b2a070265050360101402000000340c14801c6600c184109602105100c135004001c1d201031500c4060881 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 417957005 1250 417955755 417955777
    0x40e0105040e211b0a1407050901080a0803060105070b0a0507031b0c020f0d080a1107050d030c2004090b190b0306041e061802040f050610110a12170901150902 70
    0x1046185031300e40342c140995014221100c40518580010984e010048400030348000c40754840154035245030242c0c1d9000e103070402000fa0700f0100008910b80c0c000c00c180d54505800400342c0c2d40b949080f44011004100865892012924054401409940400620907603c0341d5486e002070384a0160200310000071304106c41075000056000386400107c3c01c1b40540010240d80e2030302054a00342e101a0360030150603420081c092124501c4101c04264824040541035030000741c504071003c0019242d0408980c9c0c41c03000c0740c1081c180800d41c01005002548e09100c0c010324004052020344251805068610345c1e010203525912020101e0042030101c03049982c6440b4080d003a4001d1003442d900c520a0b50380080300d01e0160b565401c0da144c20b40c00c044c0500701c550603151108201902e410703c000303407441c0100310105007002043d041341c0498420801850001c1500425110000c00b0f00039401410340d204030740954050a805008180341c44014084c0c1c960f00031130155803e85c018286800c80000390030000100e1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 417958255 1250 417957005 417957037
    0x15011725050f0621010317130306020d1b0507110406080715110d0e0910030804090c020c03033f04030c030e18060102071a0702060a14040e0105040e21 66
    0x12985103200480c11031318440c504441c02e62550811803020112988400c0c81c40800300011100411860026011340f0fa000340b005845080203080ea030010840c9900d001e1120030300780e41802c11541c0041c05400e8041c811030b419040c2154050911040e180c451003100342991214100707008001414007003408030413040c80c106221807090030203246050100e1403801d000c9494252140c1480c01c040642e00e80c00002c4503418042c142c59540c03000c0081c42540301e0350030800ea0340c81891001c0703442400104cc1c1580028112034956148946c1401c24087c003017401c0d410465003d07030a5815580c911241a80404900f211005556aa490650707040d072000900720704002e803e0b61007900560b01c0d00b80c100c0d0204070b01c00d040070162628100181c41d1100a0b08103490810407410200000c880f04400c0318103c07907050b84c3c00b54541d00c1c0c40d0b00c00c4d50a0481c824041800c6103001c10702144003960195800e040315000c540500440c8640703c0c00c55114413240010040c0c0c0d00e5280000a5489168001015400d072120303951 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 417959505 1250 417958255 417958267
    0xd1b030c17030f01060905060a1215081006141509240a020705030c0d020f0f12060a020702191401030506150d02090901050102010e10090515011725050f06 68
    0x40803a82c8100d801c0c10403000d50b24018401d0507881500840607281c00d8036007a00c2c14081788000352001c40b020054003c19901d1b40314122a840310511010000c3c004101100c1c0c002011525107806000d07140120725000e000700d8008505172a255210a01d620000d29a062410340d812041c440080b000119000691902242810340c074000d80e03004001170b011560142400c541003c04240c00d01614228007031251442c80c9400c2c02580e00c0070301d24191244100c0e14000724841040c0801d0980c030703204102c00428011001003150780c0c0c0707186d0000c4c6141c601c00ca1340981c003c034004150a441c11400d0040d107001d0b000d940e10300c60065010f540a690041d400905c40c02c1c1d18800140d075461954040c001007149030741c0200c1c07412903508042c810940544024002803100044040c0d00c103540c3c0d214401440411038403041200203208060044074880e240480b08040c596845640129425000c0c4555140c60f20420f29900f44040c490055185480d240305000c0b0a558030f04010490b159058680c200d503c07117410054 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 417960755 1250 417959505 417959543
    0x40609211202060a0b0105041413090b10080c01080118020c0a0606140a08060105090c1b010c05030106081501020d03110c06070918060e06120f0a0c080d1b030c 70
    0xc00700859031940100058901880d0360429035170f40c107169505006c0203000070b1287c40c8408006080880058400304900d002c0007030490060040c40c50041e002d03054800030701005030002e00c9c0c007506807583d16089030f145908040045618102c00d2090300d846101e8162640d010003526001009800c55a4007211721070301c43ca0321650200c410640c8005100d04a8440084050801940880041200c4400307007002c1d6140030040342e040343c4020710001c0140c00010303c00c1c43d0801030130010a1030b00151002041308074451100079000790b00a00801000c45e540100084203101680f0303d444001e44107a0241281d41481c28054025204108a4a80022042c40301c503002e56410069140301d15807075a9001c3c509807901d80c81304045100111150708560801c0c200f0321100e607503120030940141065540102001600740d800e802c1c000f084403d8411800b81c0e0500310144004001407600317448100007a070300800e18100c01070f0f40c8480340c0009050110345d071045900c0480d006000392181203028049032000c0918640da = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 417962005 1250 417960755 417960773
    0x270608042a1811070b0415020c01020306010e0d051c030608120a09121e1403210a0b03060c2515050a0c0519030b03010c0c0b06010504060921 62
    0xc003104841c0c00c0c100041002c940e140c00d030840309000010003040f8400e240d0340c14152520594501401101d07403640414100721041d01c40070501c02c0d643c0021511000610070040c041c0d44140c5610b80010802c040010751407500820a2001a0f800381c01000c94810b09a440300600381c1d8000f0107824903955841c00101d03c0070500c5035507200800400403d40c3c0350103249001d020780c41c5540155600f024000c200c4400540d80b4005040c18900342400400309020502c0c2c980291908408031102c0d500004c035007055120644580703205001c0300041d034180240c4e40c85000f40115040c61003440d030305600c41c10115902c101e030117005104000390702c0710003c1c500c000314550380b4104502040c1112001400f000d820701e68100d6205076034101d440502c003449110030090000f00349005018229a4800b1000c0180310340b640a81d00c0060b001501600074030070200201070103009c011200740180c030458032550004900790302c030b50100c2d01134407481e171100c4056074145800300480d46812805420940740811400700400c0c0380794 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 417963255 1250 417962005 417962063
    0x1d0409050a14031e070611040602010f060b0903070b1c0603030c050d09060c0206090a0e010b0904050c1207110a17030a15030c120201020102160b010627060804 70
    0xa01c041800c80c41c002c20001000100d51280f504107110740440c90300b070b02409502000641e6480d0342c0303550150070984000c01d40040d400c3c504290008000130040c3d01904420122100c1000410105988507001001440340280443d41904624020301c2401010005810f8024041011001124a00d200c5900700e40440d00b0960128100d0908402040010004048480400c1c40c181c40030a24020024083d0341d0a038034024840c02e00442c20f0f140b50749900820134010320b00090341c0746495a4916011456038041c1c855140641c1c1030100003100c0021100071a50182c084120600407940c3e0900c0480d085488080b280c2202d004040000c00071a59021652300188180e20301c1960340e04140071083c04551143d050941074154850082000c06c100300014800c840082c101a070b4980c00314030040303009209070710706080d25400c80501d0409002c00c0c075140310b040e01c005d51034502080d071001d1800e0400358129090520070450550f07090050a100b104a140c00510489002a42004401c1140b100180c91 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 417964505 1250 417963255 417963263
    0x30819090c06050c0607110604171e2109071e032009010512120f12040c0f051509060a0905060a1d0d03021005060f1003050106200d1d0409 61
    0x4240201d00500c1404550f410441ba03050180c1402021103140e03031114401040604002d20714013421805000243c1110403007070422408100104440c0200802600150741d0116040c50001d80f06800341600d0103810b01621000008226061510080500350003540b03803580d4130403680c00800030024051401c2089181d03a0505542604017941050000c0503505920803403260156846002c11440f01103450340401d10030101c000ea842002900c240c014ec030468046240300030350b10041000340040d580c41c440c241c2c2c2c3c5e40c40310316601d02e0fa954104107060042c840c004d02c01110402001807903240c88401801c85007080d040c5617011075a1400029580d03080300349110049101c200200650b4558041048100034080781d49003008143c54500a645801103016045400c0d80e85000c202559240701c42c900f84580024140e001c8105541d00c000c000d0030083c071803000803a44401d2000303981100d1009241d1386250700401000f00d158840411104246c2c000c50b26038400c400e2040d001d4854440d4060420301c1c41c02 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 417965755 1250 417964505 417964507
    0x90309060c010603170301030308041b05030d020703022806030207060b060f07050106050103060b0f1608030c0c0601060206012d1e0e010b161b05031006061803030819090c0605 77
    0xa10f00b17000c0d040030f044541d400c0c0007000810043c00000d030002c000540094021489810100c8201410200e07045150030055242c030428001ca00241d41c006108000d0340d01c00d4880b4204034140d200400c0216400000d52054420026401e10a0511a13409801c0c040c2c016a400714003102d048010610300e80c031803500706c010704130b00181ea8818003000340a07000090100b0b02c0c04000c410315146907442c250040030707490104690009180507051016810007800a500182c0403941e03030800c002180426131040b11012610f0150400004081d800483c0080c12158982c8280340000d0001d8002e0601503010220880b070100d80b0310021620310390780842414001c40c000d0b03181c89034a06212000051290590007000742d81e20800070040302604e00303c800301c0140d074001010180320700c0c0100004460a4075800c140c0d0544680084001c089503150044801c030355040d200e14103859a001801c00c5202002e0001501054040380400c0400300001800d18100e070310848009030f0101280e4035030200020320f501c02070011324 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 417967005 1250 417965755 417965759
    0xc0d15020a0309050c01081618050306131b05010203030f07052b0b1909020c03160f0308010509070c12030b04020f03041b080606010804110d1208060411040e090309060c0106 76
    0x204105d40c0302c3c10003400c140c0340500c4c10100e4002002c1500c0c204104101e006426030004040407980900078000082c00d99010b89441880d0306880314035100c040c1c030022400300c0c1c507030f07004120038560324241c030b4040e409141f440d40e40e50004c00c20010098826400c0100800013012b0907440240c40701c9551428052110ba0903980202c4001a034840f41441485000c1107038010b0030300c1c503040d0310715011074202003070241e1990505a240790039401000240010840d02400309020000141192410b040c429141c2100c1640c0700c50034481004c0f0216480000f040ba2000c0b400045083e40c1c2c4a18092070a929012520160b0240840d05236002050300030040003002c400d20041040c012400361961641f0b0340d00c0c075455480c0a2a503682c0d2500685078a040c009100089420300c030000c241d580000401603c030316000302841c640302c3c00c0c60318145000000116241c1c0416170b54a4240140512103002900250809040c00d250082121000d0007140d054802001480425191803010b043c2120200c000042c3e024 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 417968255 1250 417967005 417967013
    0x40b1023060a110f100e0c030303040f02120318100813020904020a0b0a051803010506150706090c14090903210612070312080907050603070e0a0509191d0c0d15020a0309 74
    0x610406c05000c207504a0151078415840c0082030b2503015410095210050100d0700115840c4a410038040351a4040040c0c6040045400c1049400a001c10340d03510041c0302c10f0003000c407038502043d964050000314507404040545010903000f90028002819115529500c503011401e69100341d6200c80031440200d81c0c43d240003070f0202036170b540c900c05400030302942c50040c0c000341401801c0c0203000380d221030200d400828003090741e000b0204035510004c0006e80303548500c0c020003010a94580c80e84a818880b0004002d10408003e551010a911aa800c15104100c8004080d13003401801142c0100c0c1a0085054030101084000019400f800c612502e40d640350400074607442c4000c16001041c0e00c50340081203551169400c4a40c040c2c035615000c0c1c20404080001204840c071540300f1548000392000b4405400c2002c502e424048401d00010040840062003003550903411520154183d0411000b2403980c0c1883c1c07524451052240302c000705103a4a091100049130410404200040d071740f00c448030100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 417969505 1250 417968255 417968261
    0x280b120a0f020d06020409020a03020705101a2e050306091807210210020c0a050406050a05060a12090605010509060108040b0705090315040b1023060a110f10 69
    0x50044000d00036100403520390030812410901c0081c0502c40d03075500a414040a6410f85000e800c010609640d120a08070004010f0b4014004c2039480d80900c55050007050b601d80305003100d140b5001c1c58184421010001c1007900320141820112402041810034000403d202501c40404031649031141c8904140701032003c0454000d01d03d0340084801c6007001c40c1d1803070000300d00085030300b1180708212824980b000250321840c100c00c0250412900c298000c0c0c0e1540100c0c503c007848000340d450303c00156460003000140e0340e02d0b00c51f40d03802c140360b42e50511845c00d081d0010701c0151080c0c105076020100f2442c6c0a4200c0303079101e8065405c2c03946c40005004500c2c140c500550000700910304581541440d413915480400e003d000754050040005d0b02c0701040d00d080c010702281c7c01c01041c0309001850f20b41071114407031400701c40071300c0c1610110f00041140a240c05036054050f20395450340e81181c208006200007580056640c0081c40050119413000500c02c22184612000a101805100c80d50391281c17401e07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 417970755 1250 417969505 417969529
    0x509061c0e060403051602040b032b02010b0604090b03010b0a03050307060506040b0612040c080a050601050310180f21120f0c170a1103071d01080709060305280b 71
    0x1c0741c20200078000880d9100c016542e14072242078005040c3c1650f840080c00030260445155014094040380c4440c02400411440141d200001811030308c3e0020a0f0072800c0310b40c20207010768095024401400904d40aa014140a220150000034860724039000500340316155481140c8513840003900c2d104218007800340030b0b0420f100340c4042c0710300e4400100003500350099001c182001d654900004050001d2088410001c258460a5548186031824641d4a828090184a00910410381c041581c818a4803c001c10348a084203440800e907429910300c542b010b40110141d402c25444000000300c01c402c0108100704842c0380e01d40c00340c800c0d402c00c885030a4460740300c1070880302850030000c07401207500000040010302e07100940301d5269030361030011001007240a003a05a803038408000c001070b141d000003110348170340900005540300c04200001103816600c2180c1410010304802810407180c2d0280e04242e401c10301560480307078400c10000400d203410401c0c038909110151034001d404424100060300d00b01d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 417972005 1250 417970755 417970781
    0xe190c0902160b2e090608030403080316020c030102040608060f0405060a121704032406030c0905070c05061f0e0405061308040806040813150c06020a0509061c 70
    0x20410000382c1d01d02030b01e01600c64002d881924100002015800b02c803003141c80ea00f01d01500c1c401030480304d41e0809482d501c00e00a22844c58076208000c0340600c40041501c044039031000c1d02a24507901d0040031000d184001a19005512456400c904030f90f5084c000382c800b1380340b2980c411005140810410441300c1603014014001c4c0c0c5000203010302502c1d09454a400d41da540901c1c420031010625114981089584140c0065880400c0100802107244680c1c2c000580c002030b01d920b600c00524030107040780c5aa100060281c40781c00802c1002111030f401c00c0750300013160f0800000014032900c0304e40c1410b0007100c04260070300e4000140b41041040340a00000341131104c11a0070705191940d9415640c21000d0003404410407280c0f64501084415070480d00078000b1442900d0690070240f40456080c2c00103155955902e1455001050100440040454610050b0b940443d0000c0e6a1900300095015210007420840704000c4030310145c6440e4014440c410b80300540082508418130701404035055024015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 417973255 1250 417972005 417972007
    0x305041208070c0809010210090503090906031605091b130812040f0509060d0f061e0203040302064507060906050d050c04090501030b1501020c100309060e190c0902 72
    0x415603c0e800071200600a610440c2140e841c2c0740d085c0180e1400f146040012441801c0ca030138081044000f20150107003400554803c10f0ba911382004058803000c410540c04145032400700b0030806480c1ca1924203400c00084065142d403040000700713200f00d59112040c12680190801410045820204100002e400502169904007030034400c000c42140614403e5902c24915100030400030758a840c89030f0b601d00d41c021000c0744000c1045c6400d402501d50f01c0c208006007142111070810a4182c0d0003224800c56050703015081a41c0c464500980804650780740d4041c1c81c0c0442e04a000f0410069641c030012100418021617040c4810a05494001103400a80c100250361104224030ad0b040b205444190340c020780082100d0741c0d106503121050140e94409440d007801c2c58000000d10062800d49401114a1144071030b4041c0c1d0a07006981d2010519241c1e50010302181c50400440d01ca0350020140d103101e08004241d40f0382c00d41080f85810700c440d40d00611050b5039034284042001040c2030500400c0d05a23015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 417974505 1250 417973255 417973261
    0x1509060f06041a04150c03031109060901230c07080c040603080f0304061103010b0409050901140a0902010e030a0c1d0c0412050c090a152301032a0305041208 69
    0x2081a0b4019482408540c5a038043d1040722070001d10f058030003411004050214a42c1071000040c000000700d40107601092900038140340318120101162500c21000d0825880d0110071070044a105110001e070740d6101c1c0c11611010405c0c0e0040f4000c08841856400800045d4140f4007190b040c85176000300e451040e803903c0c1003003002640e40340550385420310305400c0340d03142ea403141030620180c4501005140300c17440000000c03c1c0e0a00c128080e105580b03402d001041b655442d10381e5075007203030301e01001640300d0243e003000181c18107010341064950030301c189845000c54043c0c40c042854001d00400c21240d0b551020400d20040504040d80c040102030541074071302030b040894607c07000d88154020f07034180c6104903c0800c00e110b0208116045e0750805009480203107030006040c4004d0001755442c0c80724400000300000c99607981009440780400c1d400384454800d01500040d00140f1001000041c91074494140c022a03481207100300c00d02c00031540300865030b403509151640184080c417856106101c480b0f028 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 417975755 1250 417974505 417974509
    0x1b0501020d180302040b01020a0c0e0f0a09030801150e041b02061f26060708090c030304030b0a0b0406050a0e090c0111150a02090406030f05100603260702091509060f 73
    0x504403a0155000105c045070140100c1c09c0402410028015801d0318200050010720940541e00c01d07141e08004200940f038081c01803050340c2100c01e0290000740000c005212160300d40148400c42c1280b8140213000b003800f00e02140a486c981c2e0f00c1c000b49641e0341d03142c2d030308001d805000c02607100f648904903141c8680e240803a015500582d008520310400000005a1000101024103030f4240a51007192440e01e014200109130b02c01c211049480d0b4020302c02038044034100082500c0540e988a20800c2c19075954401500040081ca580b4546c881d403684400104c1d51642c229070805008000e410031024641242c0461070305034544030150400105909404407000d02284040380403001c03000d0300c0c196440c2e504c078510181c0203910040d0303030092905a0010400900300c004130100c0f44180260317413580400705565400c8070b52074400540b1185680c64101500642804105c103076854207150070303040038600d4001c240b4207102110302c00f2181c107024040e0f620a203060007145510040440e0000204542e10b40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 417977005 1250 417975755 417975797
    0x20415030c0e09030d021204050c09010617060d060504150b030a0f03030b030735030a020a0f150f0506120c1315170303010e10031205030901091b0501020d 68
    0x2c55811038440c014041540900b00340225480031001313010940d12200c1201c0e900580c0801a5400c503250b02ca841942c409904298003124121a8183c480b126502580025510442c1004001503409561744120354000340705c07840b429008601035404000c0c440a40710b840000c1342d200c03c03a414442c1c0d01400004000558014034200810b40c18907021940244103000301e0301d84a13007030304400300880031410045020344109907021540c031403142e045240d5032414045581c880c4200c803070100068221010b0500400c04d00524034090601c15000803012083d5540180200d8001c1c007a8084416111402d00400b1f00d000c5002204042900b03002e021780d030001c40c0c001200c01088603000051141c4404003900a40900061403005245200051009034000b000194981d402405194100e050010200f2004841c00c0103282c2904c3d40702c2510142c12201c010261903581006190320a00e42d2215400740000e041003038043c024440320028503400364106000641002e03507050001007040300d00c0130140442c0d25409 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 417978255 1250 417977005 417977009
    0x313060c200d0b01030809010f03060302210a0506090109062921060a090201030c0206010b09060310080d0e030f1203150d021c03030b01111e070f06030207020415030c 73
    0x10070351404510050000c81ca0540e220103020700285a036100010900900f50000d0070513010036071782c19103c010001402d8048800900010f03400c40500700d030010035121080541171b1600b1891044440002d0603a680f145010011220540c09035114107100c410007134180109200016140c07405210641c1c0880c0c541c030000b103d80446031140300b0543e1201c500c1c03050278406204046d44070050321124a05204280c01408150504a000910300865007841c00c0c03010401d141a210b502c1992460618020b082200eaa08041c1540b81140203040000426050402100d000003480780c86011003c10441c00700340c184002010181c90320780105650080c0c03285000202c0340d110b084017030000c101020000201e08801000c490080d00503c0410814403c0324201e81c500304001d2003a035087c040d070684c0744011143d04408100b444600e60103940c1c50704600104005441c480700442081b038841983c3d8005809100d1100da2002d000f0a90000d1220154142401203208034040103e0350360000c3d01d140da810407001c440d8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 417979505 1250 417978255 417978293
    0xb1903110f01031104091a040b0105030a0c05090409030c0203100c09030303020f120f190902061204062a030f06060c080f0708030103060203010611010c0e10170403020313060c 77
    0x21460304000760b00a9002408000300e0f062560344071074851b410280100343c80c040307050265604105078000e0b850240110764426406a40f8582591900b5000d20003038002c4400c4c080600c4402c0c400c42000b61641c4c418045251f0080c1e94040701c0b954140141400d00b4481c00c2036046c0303d410000d4084100d80c05c070480d20100c99242c40c5c0140d844400c0003103c3c4407402803520075980d040b81e1400340051920802100317405110700c440794503071441c0f0340ea159100300da5024100070741100c0d0070721a56014448030180700e540a030007124003149000324a00c6070242c4500c0c3d00c0b10481401e140c0680b06d90740c1c03641445410110329980e00100701c0701d030038420080c1c81c0c2c03030707024000a000d02400583d1040e10990758081e03c00082c3d101042a443e035071607117008406500240182400141005403072100341e4414006c0c1c5042e8040c030780310002c18000700700034824802c6540507082d0600050840607102a42030b0b0048900c92800f950240d5120031409151940708151a800002001020021030000c04e0040011b09580e401c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 417980755 1250 417979505 417979519
    0x312020a02150c0f01020a08240f09041401090503030a0c111005091606020a14060601090308090d1b06031518021b0a051f14060d0f02130b190311 64
    0x2c0c200030f043c5000c01d41001c0341601e5001048110340380740c100007520b0003102c400d49200100708038601c450140b5940c3c4209164001c842c004601c0440c10007840f543d802034007034200b112080086450b010300f510b0980d05c040351241d100000b0071415a05078443d075014440039140c1000406400083c9959800304408110a801d9440000c141e009004000e071280c101d8140044107000c07550b5000194840d248090700b03a81c8050000f0300c840c251000840c1261040340140c450702456801c60b03c410960f034225202c183d0308081103c1026022400d401803800c2c8103091103400721700c0c0c5410680006e007656030668401185100d00e03101882200e44105000007520002c0c1070068a44900c00003021807140c005441c240d075402000440c00520801207012101c4507410a160f0b0255001c0d500b00104480c0085c100444090100c400b041345440c0c2103407076404450007103040d91403010054000803103207401482c01209065950b011400e0a00f0103d01151600110b5a0074849891868036280000d1a4125a1504c1446 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 417982005 1250 417980755 417980767
    0x60503061906030b070e130608060414010b04060909020f1804150b0a060507050d11030403031b0222050f04080a030b03100e0c03060105031606051602090a060312020a0215 75
    0x101c542c00710000b580c020960b20b24908104101800c40b522000f6a203025060a11078100b500c0d52a014880c1103880010060003a40d8642d01e95500c0840130000c1c072111552260682c001954480c010710700070b08038240000844122a05c1007165034030310119041d02030091b2800b56180040d45a06240d80303d03400c40f809245125078800003600030a0021421070b8014aa00340105106501c44050248603114000310741410300c44130b50544441075540403000181c0d004110500020b8842c02d01050b1040d204920341151400d95030004804641103500707a40b100c0c1601400e0a0301c8203481c09144d4101c081d000d400485410952034800d668030a198044c800d040e2600120300258a040004400c3c03c04030000c100000d800d14003580381c0f10020f10325254403a108040c00441c1c00e182c0402c0b2400120300114081c031980303180141c142e900d42c20440186034a210702c1810140503803114a03140b88501c100040010b982c0b811440c081134458100c1480e1421580106003410060302c0c2c4370700c41c01c03030400c1003190a03031908 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 417983255 1250 417982005 417982051
    0x2704031407020a060c0605060a0803040512070f06020d17040312051801051f0f05061209070f0b03070801120c060e270915071409010311030403180906050306 69
    0x4803540320000d40022032a44001344050340400300c015014400e00041c40141c580c503040210169460040c80c4050f001040108050300c0d00a074000206030451054a044c213035259100401c0c01c44660090300941c00407802154201c0c1d20280c000701100440d82c03482a01c3c00d00c1d80340207004039032001e8034000440d43c41d00403408112200300660800c10601009010710700d0b102001c04500c800024518840001c0c003d4045100450042a0703400d4030b00203882c0b41d0401c0304040303076484000001340c03d140c1071703024200c000314414000c055a140580141751109640782083c0c04001d006401c141c0c4800d490030254031110380017600209206040380d08524103a02c20034440c0c80002d020090528078100142a9140b0701020100d03116641d603c50114101602c0c0c0c42040d00e640307010a84022560103002500b002c44070505940d0060250210343d1042c034000509030200d03055034019a0050303d081d002b0a01d06010150703c50304522043c4040e1061100c2031008a03c1c4c440401d944003405004851071700ca0a480b41341e82a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 417984505 1250 417983255 417983257
    0x90402040803071a011703070b150d060204140f1807121d1207020a1203120509101b090509130804060801060809190f1505100527040314 60
    0x20700000c10940c1c2d83c8140b90314011520710408511081001c20260000845950086212403041031031805035282106507a140303007009400a010f0a8a2015480c0303680c8291214049200300a100d0300c401640c59003000d072800400d07442c8170130307252040d1100817654119840303e03418000c407107510400d100f40c581c845441c15102e916090008240701446d1400c400e0030074402040c0340060f070280400f507440e50300c05020300310f00d58800c81d1000794001540000420481c01c00c2e502d0a0034050282c038060140804014021040c2e4405840f10106c503404240304802d030041a2040d000217150000e0050001c016800c8050a80d0856104841c0b00b200304034000f42d07803803d20031012810243e10061003969940c50308009440302c0c00130b0142000040400d4005956410000b0b6110588224180d00c0740381c0100942e07851380c110f221002d080700e03508154055000174540da4040c00d40550946040740700300034203010a11040555040c00d40b003916004060942100c405201c0c9640c1090709072509807100c0048490320201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 417985611 1106 417984505 417984509
    0x51b0a0509040f14011203050705150609180d03020a0201020706110a090f0305120c16061d0a0f050904050a0b07020312011212050d0608010612050d0203040e0c09040204 74
    0x7030298007240141c47c1c440d16120b440c0016070b42e41c0d1401c14030380942d20a03140e240704003400700500d000c0c402640c0c000301084d01c00040707440042005a40d10803c002d540c1c00c0c15400500461075138401c0d0102c1c1d104030340001040c0201d02c0c1401c2a0046640b1100c03860000403004a00410340300c5191441d501182c2d0820001c16000c2c102e007840080d00e901205103c0003512400c020700b03d0001d040300c03025000740250740351540104150002101d1141410300500d119900e608018002c0c1021a0300c2d03101580d000340c076440c81680c1e603840e04a1901a038400041d210080000800c2a4164000028403603c0200c055644c2944d81e0360b45001403001d82010018503142d8417001c290715003031103540a02583c0f10740420228050360b0310702c541d60031504035070001840f48845075000d4081c8001044500203621451004511b840d00d080e0001c404070001804a9440c1c20700012036400700d82e039540581340 = true := by decide +kernel

theorem cover : BRFrame.Cov 417805755 417985611 := by
  have h0 := BRFrame.cov_init 417805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 417805755 ≤ n) (h2 : n < 417985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
