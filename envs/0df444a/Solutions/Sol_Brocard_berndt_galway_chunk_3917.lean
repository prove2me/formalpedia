-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3917
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:03:31.085767+00:00
-- url     : https://prove2.me/submissions/01631cc9-566c-4b1d-a8db-92e1660df1d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 704316546 ≤ n < 704496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 704317796 1250 704316546 704316611
    0x412030c020301110706021305010801050d121716140c0d050f0d0203010810050c0a05032806151101020403020609060a230703020c030c0a051c05100504050d030519 72
    0x8013072500200a522401d58174607030400250009c6829403040c01c4180c1a104040d0a0022a80040d104e801c410500154203a04009403055460451400310f02e000e030061109150b294005118044044c0103030708603441c07409503c42d00b03100b034a00e020780000d00103880ca030a0b800c00070380d192000311422199100358806103100600000000034010000503401c800c448081408008507280c0864013140e40c4a0360b100e03400040d4013031020030080303104246031142455048403c504d01451040d481c80c141c5159621903514a41c4400101d030002c1d800070001e60590910f01c1c000c600d002d0550380015124095808007078000c61010030081031395802010100440000d0328030000c0b90390b5003c009240103600c08a4220018010b9801000c50b5080006039640341a00080003921414102024040345079408864070b4030b5a9200540103010440600c4006a403004507100402d062820b41801880e080002c19002e007098030b4581005000950043c0a403004c4030300010100b24040d442da2940c400564100a0007545030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 704319046 1250 704317796 704317807
    0x190512030d091a0702060c0706020a110d03051501050c060f060a030812011802130306020a20071e030b0106050a0504030b0907030209010f0303050d0b01020a051b0a09020412030c02030111 82
    0x200d03c00c480d02c030348403120910034260348440080381c035030800f622040e507141c105100780400a4001d80243c0320540c058544908a40b6015180078640030509852102081e80d92045c0401c4a000d0702071456050000c0c00d01c2450701015003121660741d1802030410005100c0a80842e007690b031400401c80085400c41d0300c00ba10b07102d144c13904a0544000b0302c03c5503200d99070008201d11154403402560403076860084000009443c540303402000e9413203c000f1808002d41f00e415108040880680201e25040d04002032240070b0410072800c003480d014402502c949103100004200240071010700c141035604514015845080c42c050948007070146c1d800040001d1101410003600e03001c0007900c401140e00803a03006000f6641d640030225440458000a070005c0c00411402d1265542500719240d051810310481d403032205261142802d08a6034444111440d880f0103101d400c9242c10b40105000d482c0c2458114a020320b003500240c9000c0702140d000301070015814204066543c01e51204c11740c40c0c1c000310202d60781c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 704320296 1250 704319046 704319053
    0x3010e0c0909250806010905040f0b0702101505040b06190c031b03030c030b040213030b04171c050709050f10091502010b0117090a08030a090203030708030a0b190512030d09 76
    0x6150b50203400e4a45c8105c1e400003480d042e041c050b042c0296001620300740d80c40343c543c841d9000040000e080700300f58890341072150380442d5244205150329000f2082c807079145052a04000503194900e80240c4100014002e400d141e4100001d1000c0c0d16440e814107040d0600c0d180f40c19614402007141060b0b100701101d9000080c1034054005001e01d00f210303a810400920480100001c81c0136186544444070400207050000400c0b00610300d0f0098000c422201c00003d0460288103950700c0400100034900c90f404400b4248000782c00f8903500b00703880d4188040141e09000104194280c01c01660340b00d000c4444c204040c003130050a1100182400144c441c4020000c45001ba029080c1040300700d0001d5847c41c1650184a20f40070464010030b15034024100d40c042d1610b80b0411900b014082103811541c1e00b04410059030200001d1882e24400e0380c8103612440c010020314110f40c0109032090140c0c0d04810580d110642e072804c12416140f003121007000080c61411018a540541c9102003000c030b28040810051 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 704321546 1250 704320296 704320363
    0xd030302031f081c020f0d0f0215090604020927060601020d17130503040815040209060f0102120310080a0f2a150c050d180503010e0c0909 61
    0x80d4100241c019500c804150b0888240700240c03050f94000d0700500c0110090b01e40031500c07580b016600384105c901c20643c0c0e004207410801c0c00190b180106140040207040d1030303014840380c20200d441c1c01c03c0013510301d040b0b00001c0d244c441c0284024818094500041c0b0030001d180310102d03d288005007017246401011010503500c02d41540c90030302610814441080084c40340c84d00b900c95850301c4a142d0038a8642c4548100201134004d41103035240820311010030300100400041120100402810500b41400d005210550001a24480c018100c00b02240c402d0790f0005810603020041c00950f90303a9542d52007102c400000c1a400c90b102d2801100c81550030f1010f1740000d410410701440c03100405035444560501c41004580d1480c0e207410492004200b0301400c102c5003a17012040e81060b85049445035520b80c2441c01810000b0045543c940c030454206516000404c040c06055008000412448810f1540c0701c40071304485100f07400d0000000c0354080b09100682403960703544c50f120919000c40c0c06d080507 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 704322796 1250 704321546 704321551
    0x6180d08220905130c050405070e030f010c0311040602030a1d030d05070b060108060a031b090c0c20030304091508150f0f011203050706060503030d06050f0402070c170c0d03030203 79
    0x2e6190400002c902200c0c003c0a0340b4070050f034041081c0940a20745001e00c406850018210018052038094003c020b46003484064000c04040000080500d440c003409800c0704e034044c0b0341c181084401d000622045400104840085c029410280139202d25180c00e0b1201440c0450100e030140a40c0010090041d0008041c0400301c0c4610300b40f002c107980d001c004561251085484551082d85407204102048400c07080e41c1d000c4168892007100d03d612100b41505444030341c11801c002800c003881ca0018003d18a602560300003846070115819441c400c0002d0740e030300482c028401c0300e551b81c2e00090142442c04452b500200900003d5498071010030807103d840100465032a002c1c42294000904c01500d1100094166412481c000d116004c6a4900715a20340000a044903810358402c0089076643e010005041074000014001c00d0960401081c0420720128010480c02a8018050500001d000c81002015a103c0c1c40000303103104001a00f1a1900080600c1550440780808110081c0f643c113800652 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 704324046 1250 704322796 704322809
    0x60f0603050a051018090218010305060609040b06060903010609050c04260303161815030c14042709060b040b031b04020904060b040e040b0606180d0822 67
    0x215520301d0000002e6903c00c94015100d0148a00e05102c20000f20042c85507020700c414002900c02d0b030304e40c08921441403100b00004d0400007080100200882000803607401401940c08600741d003401d6403054500c82002c0e00c030a114040204041c100c80d02c0c254429001004121024402410005400082c0b54040d001e01c03002035000741d100303111600c060444120405814402180740d40d031204100f022400c2c4040b8024200030302e0012000b400b4554004000150100f03400036600e031500140080d00b11541c0c01899130601c0031f51103861220103000802e40d000c40c6c0003801011801d050741c0c400c407104110100c0016020925146804050005550002c088482d007038800300307d080300c1c002c00c040e50ba20348104140501c96580505031414200794014010307100e4050300c040703501511024081440e030001d03000504c1200d0301c0c1e410041444401d035583c64101c0025074181c0d00c2d0011940b00722107040000244c2c0c90050201500c00410804210121103a401413140c481c58032268030411403451603610f01c11036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 704325296 1250 704324046 704324051
    0x90605040b01171f0b0a1709010c091502011127040e102703111504021008041104061d01080102030105010509040f0603060207050a1403070231060f0603 67
    0x404480d401075141126400d00140d0b502c400340c2d80d0a00541082e40c41481c0c2084070f41c048180041c45d50303481c03005080f411341320352200c0c1075100045183c0703141d40c0304c003c2000b41c01d607041030b10403d40740e50029400000c0d10342046451520340103403034050f805464508180680004002120507100c080300b018804405101c0b202100c214030f080082000b5504184041081504143ca110140b8035059104801d02d034100158203150142d02c04030280c0201000b01c0540c0030071003603516514140c0741481020140020100034080da403e05402060032000700704075840910a0304070200d014480100d840c0c00d144540100709010249d1141c414100603c5208584600300400304004501c5507418001e99042e2141a1b42d8141001c0442c0c041001a0402b500801522a581c11010004c10001c1c0014000c3d107018000402d00001d1910301640c0401210312001155002840404016503943c02040407401800003407040d541c001500c0424408052044513562501e003102c009810310f5111000812118540ca04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 704326546 1250 704325296 704325311
    0xf01030507080714040216060f020a080f0f01051c050a030c23030315190902040e15010c03270f080c0a0312140f03010801050612010b0a030303110f0409060504 70
    0x2090b94a90f034501a40020030a0541003001d9401d10354003404034211455042d000400700c2d521048102c901140d82c1e18505600003c80312003054001e43c656400400700e0f41902460725040d00c462501140602a642c4189200c4803d40c1c1031180c00614140361035080420307074078906224175000e004018542c000b181c000081007218201881718403000e003140604440603610319910440c03201c100c2130b04800442d910065001c136081c1c040e0030100300a0051329850000581d00c3c0d00700000000f41c004010018040400b1000094903540d90000715001d85540c075051030302075824070080d60181c4d9403400c1d012010501c44580300181d12070880c861001114441c2c01039803a208510000e101d000b50060001505c10074861100c2900e540c46401241c003070043d41c0c2a00c03402d000c0d540135100c60550083e4003c1010b0303910b48040c403ca510b0100491282110b20200802610388400c000c59580d143c14400a0281940c2e2071010380c000c0340d00c030200c0305003045e80c020407980c403501c610600e0000c1069004250165160000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 704327796 1250 704326546 704326559
    0x6180109050d050c030d1803031b020a0f08040b0c0d0e0103090b0103020d0c0b03040c0807060e240c0a0b041106030903030f060105130b180a05180a140f01030507 71
    0x10303030364419811001401c1d02c0318000c0401c1d2034580c00000a500c2e248402c01a02c000d200da14814400746034a00280d1000da8401070a0050a03241c2c4c2422202840101381c2c005a140c640000e52002041d900050144060b5402c0c24020b401d801540d1184610080001d0b009231010b00c08108000d036070f01240c4900e00900145e600441c206d076180b601c0208544044801480545499008080240d2080c800f40c80d000d512014001a240c0080c0d4044404030701c100c005110440040c0300c104041e080c546015507400c84158000390a0000758017891681c8030304441441c510311910411030b20541d20203012102018094685480c03056002c0b201034428885460f040003241c50322034112405441120015405e58075000802c043c5c3e0b503009003016040c4a401c00000882540301d5003810010b00c4006c0700185c0710070001031690b0700a020344943c01c0c03041e40c54440c140856a40c2c60542c1a1500800340c01080c2075807807500740c0703000348280c0644070607103603076501001110301d04440c9850507280309a040c1d595803a81c03201c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 704329046 1250 704327796 704327801
    0x3030206072c0d1509050304081015060e0d0b01260c011707021c03140703050408040b180904050c010f0206070909180f0c05010e03031c0507090b0c061801 68
    0x50025820341c41d0107854005514010b1006081903004074181d20844140f516280e040300d80c2e405c4125000d40001c1002c1110000c103204039030032098000402d12807400e0900f2103060316101e0340038502c00e108945a1644080e101c0c2e22050014075404698900e081d61100704110b008800050000103820801d500910313445004103450f8925030341a11400102d402600c01000c07031000c0140b07008210b103d007018400b0351808550766006081682e4030001a29038030034a0030381c04420000d00103400d0509082c1030000103603494003101e00700c074203a070f00958542c41c40340c0703c4400c00d140c0344200541c4120b440c0c05020620001040000484409881d803c0c280002c0e00000d90302d50310708071034070b0001c16410801005050401d03085454500e21803400d00000d5203da5464a401802c20f08094400b1294608244500d5801682000c1a404110001c609000f00171540d600c1c00003045440d162130a1b19040410400390155080f1006003101182860715142400c1981c0c1e0ba94100712800c204136800c1810009002c1410b1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 704330296 1250 704329046 704329097
    0xb010302090f090903190503060a050d0308060405150301061e05180105040207060612060609060f030804090209030319020c090a06080606040b270402090105060f03070f0c08040303020607 82
    0x504200c0b808481d1900704040000700800074861404200000800102080140000000d40e03403100e07600c0c2d0910b4030a10500301c10b290400380c01782c0303086a40c080100c2e40240785503602100485000c50141e40e041089815085c145007950381541c245540400c07889410040e111684e504c14040e01c6d005c0342e641080040b94030b500090702211306080401446030b4107040d001450410b008900101d03d8a41d502010b66225002803025101035a46507401c2c41004041e004440040c40f000c014814010b0450f22926101d00c40c5124002c2c0d038650000d903500c1c04d030310203000742d907854070004503003844600b005200a5114030361460702900c90384600700081c0002c002d500c904000e071b4646000420203940c0300b1007440010440c0403180d039485516110b41041900000010700c3c40903040100c620307031904182c814800c0083c0103030403551281401b0301540403600380e0b20050f01e0f880601e903e018012101c01181c00c0d688641d203100060111280010040240750f00000e04e1400b80c442a0383e0810111a1044024103a80c40d6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 704331546 1250 704330296 704330299
    0x90c120705040f14040816080f030a05011514160c0605030f0108031602040b03101d0f06131e020405041a060a0b04090c0504080303010e0717090c01260a0605040b01030209 75
    0x40c140402c01240512000e04800d4110090311034448400c0e0b1602440c58211409d1081c03d90000170402002800328011180188030b01e61501100c3c1003036101c00f41096495007031480c4414408250741400800300b03240d040800b80c0004074500302c1a200e0300001c10710307841212680107480b040400011220400000c407040740b041e030035141e410703104282d08100141005162840d814810b080920340a81c01c90700c02c42644940107400038841035500491241464401110f500742500701104001c0a60014402d0204d45540900802d150340008030501d20011900b0344040c0d0002c0c0f40004200030485e081c1c400107050001050b201016507030700e400308070b5218998052103511000500c000c110b01400d54000e0071201c6200d06101d41015281c003025440c5030001d81c40b54848400300001c1c800c00a13041411008050b908584420f1035181110540c1d50399045440301c14100490b07140103003142d071a54031400d05100c011032094281070400c0600031000d043d1074040c60303104a00c1c081810080d0b601030700c21221001070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 704332796 1250 704331546 704331581
    0xf0806011701021207021e0105101401050f0a05041a0c100203060411180117012102010c02030d02011b020d021203041a0109091b0302090f090c120705040f 68
    0x24600001c4044036501c010103900d640901143c0c0d04203080b01005803007020310764020443e61460303405100c180702e100651100b10381d00d86014040c00702c090b00a05c5040ea00e145c47e00f0004c2c001c56400490b010320030030158451051000c580d550150354803800900446861036204d4011291142c2003e8082c851002d10700321552000105603080766143d000786612900c000c2c0001210b400020311041f050b84540d5102c40e082d101850340024668202c00350030640d420107080c0503425030400c0c8949944103440c2c0890041c1d6426134480c90116881600d0304140b00c0c2c0d001c1c098903844462501c001e40a080030915440c40209080d0400d440c00c3c1c4001420034606442e6030007851105048014003215a00280042d2b0301204c080c861400c0407104207424a008240b00140007a220419003443c1d849401c0c402290b08084064241c20000f40e900c81d28140c1c3c000480b81c01d90011a151170313158a14014105a03826044903403803500142119002c9116402c45005a03420b00c8002c004070014000c4400038062080d1440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 704334046 1250 704332796 704332799
    0x150c0604060b0126010f08010903020703031103270a14033705061909020108070f1206080f010e06090a290f0612120f0918040f020a0f080601 62
    0x2030381604150140d02d0181071090499841031400f0301c409030055804842c289000c40104030301450758410800406c017000003007010140a40d0020340350801b03440007908200c004480c9203070f00c0405000301c41c1004028480f01a40c141d070b0304440c5260000602c0c291344103c0c0d6030140020100809080c6001c080c1d40200549881200524a4a540745207a00900c04144940300e54003148085040616003440c02a0700074403032403404d5803d600b03461500384020715240c1c0c2440103550050340c012200320b40280070360800b00690454424122a0024641400003a5074106040050030f48c4010038059000801c40700244407003815950700e00e650f42e0301a0b6113000d083d0302c40103459000c0384a4102811803014910703400d0020058400c00741d0120700702500c401a500c0d1000083c00b201d1f18051081c034107160303400f102400c0306080a031106030050007540b000611001001560811650b241034008880015140801409046c9801e10b00110b1003a40002c9010f10059040442c540b18071b1341480c0121420302e4010501603 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 704335296 1250 704334046 704334053
    0x90905100606050910110a0516081207080d0f090b150915220203161e09060305070311070609060b03060f0a0b0a15020f1c0203041e0b040311150c0604 66
    0xd4402c40403003820000410420849080140b0080031f00501440c0240060042d01203030480c1441e01d580054441d9001c59030406203504000180c03210590403280c41c80c2c845a00301014409460b119540080c00b074a0700c2c0604082281800d64103005816000c0310550b0300003030030188004014103840c080000b02103440b03007015600e84a41c40c0118400c0b896400180e01c480c0c421402c00381d03001070780c08a03a0f42c0802d0300c103a038903980d01c1052501d1340210004803012410010102600d00001402050101901c0c0c0c00042c4609010ba0030041003c03194003110f40ea502c1207030400d0002170880900480e01281451300408a03803400140e414014074040b58803000b542c0750308074800001c140207034816800c052840c1000900c4100025840c4023a03070f0702e401070042c4c201101c10060414501c4c06814590340d4620306421203003036000095600b41c030b40304010150098440303880d0601480560f0301a0150b21000200441040440c2d0b24a8094003030940c1c0f0301e04e0045141605c2d520034010344070486030540c031840004011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 704336546 1250 704335296 704335309
    0x20f0705010c1401060f0305010204030302101131170606010903020112092103140f101a07081902070824041505090102070b090d14220909051006060509 67
    0x204008800002d9459640c030140c5d5246c140940c015507450758045410024560140300707801e10428440000c0283d1300c0000c06414060041001c220300180403004450340d4949980c00740e40301080a0000f280d09555980186400359400a00f448142c1c050080840c0b019402401104281c943c140c488030f00e0f889510749050010150703000c0c10356a0084018402c20020b211228003900d42c5003564020a18500280394444101005049060014030300801c012a40c607141102008cd0741c10240310348242c20031840541e08a02130303140e014181104c00100101b030300c803091031601d00d410342603001e9a408542e9400e440392502e0740984410070400d00940c1d90406d00199414050b070051145a0002a110f00d0140040803107104407203205042e98006111810300c0400d203541580200d00c04014801000e0b0890005c0882c0300081c03002120302130105211340f02054040c07410b052061a92032010485030380310013140107845007450035200f0740107010b000302c201d04843c000c4400780c400a0300c03524030705894141070040c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 704337796 1250 704336546 704336573
    0xa0501020d120603120c030f0e060d0207020d080a090501020712030e12011d010b04060b1e090105160308101d0105010509042009030c0d031704031b030807020f0705010c 74
    0xc2c26a80d1003011001401040003190074071101d0b07640c001070042500e0081c0c500d407002d42140c024041a0074203030115070b541400f1903500210100000d0380381c42c081e2000c40c079202c1101030018114500070416400059010740b01e0320440b80241e08031a0b8107995201d40440181e18804090700080114208250904207003e80141f800002c000000c0c40c21031001022050a85070111112140d441d24a08251031816028020191030464030140c0741182c1110b01c00c040107000055110a2000896040f003140e010f901074079200907143d51144240246854020002d1a04481c8141061600c03a0003141920880f40c540c6103518a004902101e0703401c1c5801527446d600410707503041e4016164000aa81104460420015810341224007070322a2400401c1605050340d5202c01401480f1400e0b03d00d000c0b9500c19507400186098000144040d122402c04407140c1803401d40380c02070601c2c00c8440f01d0415a025803561b00c1103d041d420360b1045904e40c20110b03112080d0f8410580040c83d440c6803040401c071701c42d00619 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 704339046 1250 704337796 704337827
    0x604060e0705070b06120d08090c010201022508041509031a150d140102040e0103210801030602070f080a1206090506130e0118030c0512091f1422050a0501020d 70
    0x221400325400c258504180103041000081000c810300270b400c0f80401800c0c0c15110300340002d5050038540030a07140c3c000007005800c9a000c080c0c644003414480004202c42c00340806e11280361032000b14a2010b000c44115101c01c444600301528800072110706140070602a03d54040ca0110300303030174a0304100d01990010802d5811080d032910105003e9802d200a10003030129003191041907166042803901402e481c22031400e002c10303c890900072564001c501606603503100ca401030316810039013020401c0a030108401000e0341c0c00000d5108a45800010380554a01c806006104080e1180003002c150b81055503500d412644540c2d0305400b0782011b4010045030705803003000042d9240c0c4c000348a0000303040c0b11400e4010900b5410040306000090046d460101e291055181c40c20210700082800b04908c00d54420f0541e010714080d00400e40f003400c4814001805034203843c3c40f101c01110008103c64080b068804002c4c1c10361002440c0c0c2044c0318080d040725816005020309110f2a0800d80b04a4054172544 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 704340296 1250 704339046 704339059
    0x190c0b120106082e05010806040608070e0a020702040c120f11040501030f09051608100612020d080705070f151707050304052506030e0105151c0209010902030604060e0705070b06 78
    0x100d107520481d550004402c0e404d11000003e03483d110015107003400181c0f01750300590600c0024417020000107000000c44100450802c010349d55006101c0c000d0081e018003d40c0a0b00701007e06501a034810202840005412001c10246907100e09100417a4a000f0004881c908280410805c0c1d6009602c41002603031804008500ca82141d40c03400d05203240789400d080f803d0240a0180300501c401c01005c0006c00e001034003002468205488018003103000700300248034100c007200f800c08000280c404d4900c1194041c00311407099844080001288840d40100c01d01542d1001150590a210300d10f0703050b00a540b140c0d6003030b258980740c000b102c20764402002901d8511502002d0b1000c0c400c20400040d1401c6416481c5040780d017410802000c0c2c8980b8520640309031704140034001407411010f401e0420300d904031a000c451618080c40c00541c4000070001031f40c4410000e00000324002242c0086100b020219000c0014584400381c3c039000d220203485480024906100001c00116400c40c056005440140030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 704341546 1250 704340296 704340331
    0x2309091e0a020f07020a09020d05060a0602120918070905032112040602070807030c02030114091509010e030d06090b03150f0403051b030a0306080309130518190c0b12010608 76
    0x45911410f841e4803500647d0741c0000c000b0408166445016008007007242e072962460314100e0001d607210312080d2044c01c003803c0001e0140341a91101040103120b40f03100805e0160386441030000e8400701d07076880b44501034002c80c0c48490400000c110704400c0e84624031595400c01250300102c1c2c1c80404014030454040e03500300500404220342d11301900505120707540d43c0d021404103206041c20f44001c80706002c854805582400304000700408c80d040028000280400156500382e801409000507451088250000050040da1809541c01070800d0f03030002031040c440c0c211102c003450359803d24120125030030602c03a00845c0d020f4503503161140c1c109000e4609141840c036a82c2190706001c3e86003413142c1460340002900280749400d130103101e0050040101960a002d40e00c030200e400010742500b64202ca607529030014121410812096030307100550000c9a88a00045841190b0380b0220383c010703105600304c100009064520a001c41d49400500c2c606001141d00e00700e400d840003800a400c0106000c03541c0711 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 704342796 1250 704341546 704341549
    0x1701060b0c0a0303060503060105060d0b04063b06030309060d09021503040b06011713030201060e090303010f081b060f0702130203010609090203040b06102309091e0a020f0702 77
    0xa00000300207500a440c940c2d42919000d070484100d0340c4824000d41000c0c00400c5075603100380075109031150380305001c203008440100290003032186400404e0001c01d07260107403910190b0030140070b0b1088145000041c18201840c0c4280171104212030180d4141e004110081c0c0c0b03030074080042d0850307a92245020a08900725400a041d161985a2100344074902104000074080d0720307941150483c0007070030700d4490340c40044414040500c004015046518070441c2c0c0004140c401d51280e40100b0520b540750f510b50422400064480d1700038466041105103180001c501000086403440340325607196a4028050307408810300a594000740c0c609001038406108940c00b580740c2c0600880e041c0080c0000691781d42c10300340301500c0030720719030010120a80306108010000d9000c0ca0300d103402070b00803154042240b0942c00216080c110020101103070048550b079801e842241100544a107804c2240d115495070317900c03d1540c100b00c6040401405e281104e00204101900315130043c004401000006841c1640c07070f40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 704344046 1250 704342796 704342819
    0xf06210e010c0e04152303060a05060f0307121502091017070c03051c060b0c060f06090702030315010210060e01030204050c04030f03030e0c040528050c04170106 71
    0x1000c440359454180582080e0f91000030038240301c508490070070010100c4003098070f1003c414060b80c030f0400182044200700c003520361240c14291000504454a92401c80c0168000d041c096500074003526240524074414a0049000002e442903524036000c101459240d104c1d030900c0511031609407650802c0304418a4580035400c0b5401840c48d101d0400c103000d0107001c040c40302c03001817800040003a403c110b000001c3d40101100c4c044416048030300c005640300d00500d0002c08850380099088080040d00881095010451a109400124801c501551664140801907400b254a100180c00070400540710300c1c0c0e42000c52031035403818411540030388481051542103480941189000c0401c5400410440c50503005890340810301c1610719003018510303070b40c609803202d001c02c0090a150b22201d1010341544104a41c21800310001c1c030900c0303242171070020280101c04500c26280710004442e2000441ca4290207298054140c08000394074182c40c19507440740300c101020b003010095481d1980090640100c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 704345296 1250 704344046 704344061
    0x30109050a240911010f1d04020f2b051608130c051c0606080a020f012a08030603010e1209101e080f0108070806060607080702040908041e0f0621 64
    0x4504105644681d000003401a646c3c240c0548204030703000c0d420400c024580f6401c1542d00308256000f5131100c0440b10105220b00581d0891440c5082c001c90a4600c01c44d8829140002c04089604010315140c1a607200403a504541801010405140c007058100c070318042c901716401e02400d085100280c403a0700040208901480d6902001000340028082c85818410180240070304002070840010710b80c08512120020350043e41031000b4404030380d4046410560b10403400c04000610740012507a8906a44142c03c142c5900e402903107055000e00c07680c000000c459024407a44801c0301e040030310007410010b221401c607490008016524201cac048840d12180003a90f000210349998101c0d1070010b00381501c2442c140d00a410070760240d5400c120427800412441e80180c0203440e4180d1b00c04203814554100d1103800c00080d00a890543c41034107100400c0041c00076a003000d500085402000b0341590800c1c8454014042e40c1c1d90b5035102041501c4c002c00c40d041c50049540c1c05400c0d03c0285003c98000c84012 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 704346546 1250 704345296 704345303
    0x5030a090b0925080d230c0d03180b0417040806240a240309020d11030705042703110303150109050a0b0a0e030705060a020307060605030109050a2409 66
    0x1e5914800628021009521a50000401c0a118604405145d840d082084c40d00709200c483d504140441605083c07199081148420303c50f5165143c0324070543d103d50383c0c140200001c0c5010f0b039a1700d000400e09652100030f90000940007c0d9140da440caca803051b00d03201e2030000707414800f00703c00201d0030000c3c000548100c0701c003040318081e200d00801204147c80c0c8414002d200384407d02080c401c020350790714007414020546c40a080308c404601010b400400034000d029601011240300e8034100325410107021488070080e41a901c3c8661707510207000c2501d49200e020081807103d1844e071100000881221500d16001c1d140003982c8403c2201560b007503500c01d85401640410300059012039580040050000b020700351181c44105250141111280c05450342c280204000714030500819a81000740b1405001c0040c0802da0343c5160b080065500c0c0d001c0b440484040d400d000c000200d030726040c410068443e130031901034482c008281d60f1f074000c1010140c0035104801c5a0030301242801c103040c811805107510 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 704347796 1250 704346546 704346553
    0x506090108030301051e0406031703090c03190b061801030506070206130b0f040507030606180501170309010f0302041e050f0f01091403150a02130b0a09050105030a090b09 75
    0x51100a10404850581100009a2003003004005507114108111380c440202000610000850300000700985100da1000d071005039076a04070182c5404400086019680c454200c40800c504032091517100c0f003070200150110030003003d502d4007103504c04030f65991108000340400800c80e1680383c00c4503698801e8000b61441c0d4091420060060b80401c15a41c02c02680c5604512a80b090303598004030a0009000762240780c0e20300040f40400100300086805180c0c401002c0c40482d80b0b450070150f41d0740080101d0002d282c08d000001a0031080c2d812108120080c942c0a90314001e04140107444d84070502a004080642c00c00001856004003807580070032017030341c038421180c081c036000030408240405400079220301d200401000c00ba84e04282c54000712241030290543c0f0b00980000a0b00b004101e004540e64280030408210b140101603004211003528024030154080d15034815054034041d085500d0045802020248059800380300a154403400f148400712b030a00c01d43d07075500034480044d81c14143d03503407 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 704349046 1250 704347796 704347801
    0xc0504081b130902010e150a020714060d181202011401061e0813080301081e0a08030721020a03060609141e0f120c01030c170417190305 60
    0x981408068900c0318810704905406001d840060800c5400250500303090f640c0390180000c40e4001c54480080c1d420007007031000f145020000c00706095205003071200041c040c500e400302d07600c18502a256130410024048609206641d0b036100010942000e108030f8550f02c804181d00050030341d40b81803100c0070596001080380c011076000e8104500303041e0440d0080c061140605080b4103420400d070580c0c002e00745440306260301c80c0e403801d8000b20100c01e00904035640010000c140303100c0014400940144465000005861b025070158448148080041c0341010400100340c840f8400e6107101d50158816903240250484400540c0490740484181c40c00700c0e03119042000f8164200701600300406810b1028494100c2e0103002030034003194508800081e062410090f001519042620080b10b1409000304d04800c05010345c450751a11000402070000342802c0030803d46511844001c0102c0040d80c1140c07d40d52500c0d86d42140315034260f80e84803854103041c0007000d84402e0510007a00d0481c000d4a0004060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 704350296 1250 704349046 704349059
    0x170f060402124303050a0303110f040f1503110711150403240b0d0b0c130321020102070b1812030106050a0306090504030f11010e010f050f0f0402010e010c0c090c0504 73
    0xc0d151010304003c900541c0804102161021400e14500d83c0d25107000101c49800c001c904910340100c2012205819011801141c03e080403a00202a600c1307984a6240000010000302d09580c4030b80c2000d07451400c140500710010f0b48010031150511801004550700707484280000c0c2c015000355100340ca002400796440304c450042c05020500c0fa43d045e070401d0100e0201e000100300b1301603400030014500e1000030000b900c860214816035903914080080c2e010480d40e2818140b203c050243d1120024100c10380d050f161880c01442200d400e43c1d03105908448559849600c084091003070079210100d809105045e40b00a60408000c5001e0080d07a12805c1d00c44c847c101000b002c44000b0b8100903072041c507140c140300c00f10350001c044002c20320207450b2400144200c034400c10b02410b044284001c0315803c045280c00c904540d500064402e1151150b000025500e13071015104442d41030f01c000e40800d500c402d1207042948140140c41c0602d010721507500038150f40310b1041044521000c0c5510008901180a0083c1e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 704351546 1250 704350296 704350393
    0x312090e0a0515010207030b0c0d0213140a090207110607050309120f10150e060d1b060809031905032a030f010807060509040209010909050f01170f06040212 69
    0x20b030100780300600c02c686c1541c2c8c2d54002000090902c0380003141c0407071355404008094044400399089c444850054070390b204418040494400f05403840b0750128680810310300114800d80c1ea05a81040d04081c50501200a1004a902015099699000c20050445640c807500004034860f56910020b00b80c02d171817400014140700d43ea0320300348105414440b03115002840713401444203840440e003c0e0f10581e00e440f00005e07040d0758841002041c01d00c400308245104103c1c40d0100044501d036031182480e50f80c0e03001d00d0948920070480e03800e00202e103510156031030714840c60180d544400c11610b94600022300c2c040031080c0c0704184030480c0b035501002041142028242100c40c3c0182000401402903a05000014185010b5114094096a40440c00380f40c981c1c8500070601c01440d07100c41c20080e60078030055021900c0c20034021062650400100d040405000168242c20007007e8005058142c0711a070030450f1100603101a40d03242c0c821490b240e03807101c8920b40a080c03129501c00c115000300c030141661014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 704352796 1250 704351546 704351581
    0x1030209091003060b040b0a15051903140709270b120f10020c2e02220b03101703120f040606050108060d062a1805030a0c0312090e0a05 60
    0x140d0704141c21509981c40b040182d105540c44274045194140d9008401c907800d000d1148514500c13440741c05401e550503015030140f901452007944104181e51110400c1d11546424452802040e40c480c2e0903d8808100380b910748142c1c40b01100c0030076448a8540010f001c150f0504d100201030700030b1081070101040c100700e00d41042c00603d00c29401d1001400c040c0c2d031100390180840c030400300300c9900440303820b506101c000900d0f101a00b086464001c0341c00040940c098880544200ba02611400f045075840d48060b030b4030451700c00e140034100b130f401d11082c4105c03880f51071481803c52000f0b0212900121200303220500c03441c0c02d000e8041043c42c050400101755092584840d060040000a1003000d80741c144c2501d009a800c070304041800030716540360406004282c0009040d80341c0210340011019400850449051452280055981c1e155020140c0301c96071000000c1106c1c0100e0360030000500b861805030050f0605083c4420102c1e42d46110f0b10803c0011204642c8081c0d0769420004849103026184a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 704354046 1250 704352796 704352799
    0x1906170f1e030909150a03031115040c05011110140717010608070c03180602060a110405090a1e02070804050a08010911130605062109030f12040201030209091003060b 73
    0x80c8001550300195440380310340100071340140340c02c01c0010301009550034000003200029240c008400d42e2070400811240034064914914010f003130541d404002d013049a180110b0300810260995031400005480c00341b003030301e07030301076035014a1840707850b030303d441d44160611100070040d5001c0e030749001c87c001404010b580200c525501400340043c03204d15400f8101a610030494202446000603900302940d1215070b03000451181c01c8221400700b109039000c80c00c1e5025a401c8070003400a441115460981801140101600031003c0c100160441c0180d4000c00c4210f6072070898825560441101c0c441aa440382c103040d5900b620018040000c0e041044504d07000380440c82c002c1140d6842d56550020402c90a44c5440c030840e0882201d400508080d8010b174004c1c6001000203a0751808c00011001884001148a5030512204005400d443e0301000301c0780c0614051031010719080d400b00d06401c0800c0040c0c0700782e04169007440b03003508075202d0a10107401245051700180d002d500c1c0d4a07002c402d035002404542d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 704355296 1250 704354046 704354083
    0x3020409140d110a020108060402040801020c0a060b0d0201140d090b0907031709060a0e0f030102040617010e09031603020304050d0609061b0509040b030a02060a09030c050a0e1906170f 81
    0x2030f101c0c40109212840c1c40c0d09286c0662162100400078001e40a10f42002525510000d0310000404000442820031032290700244420140d2500704000100c2d035078000390118042040101c22301c0c5141d0001c00e02e14180b88000503a4581a813600c0b0140b8108a44542c01c5900c060802e0050143c440500e444101b181003c0501d003420030004a1903c4c0141c803c82c00501000c41900583c60350744440c2c82500d003c02800071915966201d2000348201507014922070b00d850b02c0000812000c88000505c0e00c500e04200c001d42c901200340001d40e400b510444c0703040e81140400d10000c1040d585a03107560000d1406968007003114842d60400d0011618424036030400b1003101174032402d00c90b8010f03007940e80c1007004036030008500007402c010900f07207405040025030016001800301c5403590011184025a070103105611013264462080c00b0000075640949081c40c494000001d8812901c250421440c600802c4080740155442c4001d9042041e0900a40c609802c219101503023401c041045103160032228180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 704356546 1250 704355296 704355317
    0x21020c1c0f0e041a01030506031f020403020108060634120906030c2a050f16150302162a06020714040506060409050714180924041503020409140d 64
    0x200c2c4003c1390000500341410b44480c0060300c5030303609010401d00351100450340510041c07440035000003940a400101d0205070004042845801d2035030070b6070307070510b0700c060040f20114001c0485115500b4890f9038040c0b600843c1d01041c00241440c0300380140c04200d0b21144983d17030802ca80030f8203039081800c50804000342010309084184041c542c0303c0d01c00c0311041c407a252000075424910704285002c4014804c92080c229440441100c06003503100b1502c030300d14045a20031890390700f2000d91060702e030100c0c0c282240049101c040741421045508030381c8078143c0c016210000d11030340070f01e900043d0301c19400350304203030710400c0001440741d08070403100b004032020001c1c2e203018000201640100d002c2d5001c103d45d00c07400500140d00510181071034010b409a81a1109000d0303000c24102c40440000a0003401d0020100351104540d41010500039076002804000100001c1448001c040035440c0600d094010400040075850328400c035112140111030085089008a085078a003042e0390055400300b0080018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 704357796 1250 704356546 704356571
    0x112706041107020906090603010906020f0406020706090f0905180f01090b1b031b040b0d02090307090c271805040501050c04060519050918070f21020c1c0f0e04 70
    0x40c1c0c41e9015004441031b411580b41c500c04203004000c05c050040546200003402115204050b000e04200e481c82d6086079501503c03213008654203102441091880b4182074014021441c03160002d03a0b00c903400030003401d0349445184040e8a0040d00c0020351030565500d420308400e11410140d6a0360028132101030100b104e1f1840c1c42c03000c031840000c0822041c0030202c2d10210408003408101c1e0000c11040750100d8544008052010080d4044e9220034441e2240050004140d00c4500500c96102d4071507c0f401100400e15000c250922400704c0d40220a9540743c0c808150030031007041300e080003100c61400240b1071500c0c1c6009800c692001c2e04c5102c0700355050208111840d40711040320000e0b955041500d00c80c41c00010160b581e4003821401651140d2042c0c40d44c4008140d8a1046105d0540e555174a15141040300058541d03c245000018000404407841c44500c0044d400800c0c0301c48603801110541040302e03c000380011802c64a10001845030303c0d40074400e80c0d01c106000c80c80c84084408004056120a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 704359046 1250 704357796 704357809
    0xf0706080a0915090c050609060d27120809070506040611101d0105012108341a06100536030607030c052a0a0b01050111070308030411270604110702 65
    0xac802030026501c940b10158045400340348215252100e20000000b10704501d40b080e0381c1400c0b40d02000c0014000c3d4009403540e01e00080b0304040744c1001d40350b14a000d0400204555000c002110b50b02c0511070100d14401e241d00a1045c43c01c81c01d0704400444852403050001402d490040c3c1c0720104800303003220a10f5905008011b9490302540c031124160f03545014414110580c0020155410f10303101183c1c0000010209000001c07120348142072022204043c001e10b0f90311008140c0b4420307000403289400e01c4481e4011001003e03000404c00b0201030124010850358001031a1540003840c4103606000c03407140d802d040080c180c101440d070a09001403248407000074900c0c01841e086c50400c4c590624400080b02a02c41600c410f006080b0660f00441080d0800c10300c000c9003842403500003048064002c0003110041082e0007a40d60218101d803854486807162802c002912002607440350210740c6d0b0604000c82502030f6482401c20900380d00052404108020480c0c05501310070300d5200e81006540700590750350 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 704360296 1250 704359046 704359057
    0x60c03060111070b160303060e04031e0201020903030304110109061d060a031d0708070605070f060c020f0f1b090c03070c241d0f0706080a0915090c05060906 69
    0xa1a081c803050002e010600d02d0700c0c1d0280d002034070101d40000d507000846400c0c080e910302a1301170748080c820b042d0348440e009000001150f003c0d002818010020400e4080e240219030380c10b00b03502c00582800e070500002411540145c070200e40054005aa00c84256080f00402c0010322140c18000c3c03012503107d410000221640650500c51080040d41511240c0030b07074001c00c4070302e083c05161100e0381c0340c0b649030a40d034100368002e00d241c0707204807040080c401703202c0c104603503000da0710a00811312103140ba6a108040c2440d01460010b5008007940c001c1801c40410a85110103002c1000b0700204c8841c24408180d038441000751070140034020100702c8a102c0440440e90021114609030466032480c1c24441d1510b006258000700030351f460072019804603141d030050004c011911240030389520343e0210315590ba00f240c100580d05130b0018801002454050301c41140d20885204000c210f4040c95564003009812000004000e10740c0c0712021000e000301743e02040040c007130a8844500d4220080700040d0b080c000d6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 704361546 1250 704360296 704360299
    0x1031205130b0f0d020301030f05060a06060c0212150702070609090b0f1014040b040906090e0c19030803180f28031e02010203091207023d0e030f060c0306 68
    0x220902038400c1d2404039802104c1c0100115104d5840c0c0c5030240000c0120b55003a591441010b000c0703110100107102d603000711115601c0788030510705158203100038841c2d0724540c0e500c5d90240350f000c0c444002c800042070b481002c03207034060001603003400c201400040150b042802210302e0072a640401d925401c03e100102c0108503290103000c1d211400483e825518a00443c0c40898003040000302c41030240042c1041e030700140b00610120b600c40e05480c00b1a4104501119140d00400d10329110b410300810098441a00301c000707000c2c032a282c1d102e4544d25801683c0500e50091519003603078a03280284440a4aa000d040140000c810b10254800d080d86a070720b0140329045202c0c0001080500520700904100b4000d01c00c0c0045903c04100a8001c2d04129940d400c14040c445401400c4034800040321070b0158010540d20f05001c1918101d003010741c0090601c1c01451000348101031004c9110110305205111340e80e28090040104141810840c0b42c1d0380a1185074001014002c0b890201000d607a0311020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 704362796 1250 704361546 704361569
    0x5011407081b010f2016080408030a0f0f020d090905060a1a04060e180c0a03020c0303240406030b0c0d11210105090106080f060102070812030103120513 67
    0x51400c107026207218607541d5254444081440310054041134001407511456444100002c42d03444207010400b0b80c540003034042e0150100704640d00304000c00d9503581c1c07041c000c1410b01e080646400982d03240d6484184901f0202c1c1814031401c10151380024001c0744141c0620180c14400307070341000070b803440105005604040340c4034000141c0c1625504e1941008180140d200e801e40f162907540740d5410750003401841c00107286101e154609040c00400c160103098504480f902030794a681d07070a90b480d0001d101c2441059000c0240f05014042003000c0c0d402440a88070855410710003010200c24408600080e034000d506060341000407070316a015240c0e00050000c0059510500d844181d0014404004028101400403036201800720b41500c5540390030f041403120142d41d0340c80d2010040f1200c400d10506000031664000103d000e6600c0c0d8403142c10101c10300403101c0c10b80e2554001c03420b00508500c0050160408801002032080b103041189600115042151a000e20a07103249145005401281c81005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 704364046 1250 704362796 704362807
    0xc12030a29180a0b0d0f0c0e04021f0216170606030c210f010510060f170a0906060b030a020c0111190c0c0801021c0b0a08250f06031e0501050114 64
    0xe503203400c40c00130200c0040918513045031528001c07445911082c81550360a403031718004100010420b600c18042c030703002441000481e12000c0d95201005030300b030080e000c5002e00c2d00301c0040c1c0c3c04002d000750041d29400d0443d80d249002510011702e00b0310000e001611a41c0b100c2910fa0b02d035240e40c4011140b82c040105c556804107041c42c04c00d440c005800c0883d000c290300e05010059040e0210300903c0c140e58455a50340c84103a109401100e01001c40480e042101c6c0600c0c0c089696450740d9407081d50080c2c8100404070f041907903200e0f2000705400448815200307075000034103400d0101c020300c50041e0303000080284604000700c20404089441c2c20148250a1184010104082c40500e281d2503004000c0e150080d5070f100c3c0441108402c0715406100e051110341030140128951925124210544843d1002002e046100050482000c4000e40504694003104c01011420601e041c0800c8058450b5032004142c940d803442e80001c2144000c0e500c080350a240a0040c0290b03a448103213800890100300009440e407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 704365296 1250 704364046 704364061
    0x1b0b030a0b0a05120a0b13080414040f0f0c0f03141b070606080a02011101141612090609022701090b0609090702061602010b0102120c12030a2918 64
    0xe80e042d402680d4441c90f034a0100c0c0034401c2c0007906401711480750111131065100c1207003d4000d51041180204406000c4c0320074001c1221345c1e14100d14010700180041500400303003104c3c00c1101c100500242d102502c1d84841c80807240c100345001d0301807600d8902000b0151a00100380c0e440e10019041c40454421091080d4101c08041c0988580503042a000c00000d903480310b0240d900d0200003400c038003060542c03c9100714104180b1407040768103c00f2080c5115540e4950090440725000b5101d2800c0c44425418840655a02c0c031500e40303190300c50800083c8c10015401008900c001c4410150101d070071b16406a1601c0d6180341c0c500c1e045402c4100041010801d0000180f0280134442020382c002020208010100358000b03103023400385042003414800b0042c0540201e0903610340c4440765015034080600e001e0b0811080c4005c003d411ba1181c1510381128010600c100c10b58015290b10100c19128510a03c1d00c0300c00c1021180305076000c014100040c11100b02089041000720780760f618502003440080e150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 704366546 1250 704365296 704365309
    0x305060a080c0f030307020a0f0302034e1308010f0b15030604060b070f06050601020610050d050f01060608012d0504051305030d090303050f01050105070b070210090305071b0b030a0b 80
    0x103c41c7e006100800301602c442495043d52001c1c441a0300c648140300583e01401c2c003554281c941059504102000b600500455080520f00d4203403590620031344a920200e2141840050600328096050218889290640c5a400e459040c41c501c1b110a00e403000c51540303a45d0700021603056003800030390f2030344039a1441f00240c01040258051070507000300103046010451044608540ea41c804c0a080086480d10001265078000c05c944091208200c100d042c4181d10b00641e0080c010b86c070500480d44148041c441050943d01c5907486a0081060140144030300c0180341580e9007003114540048103d8140078801e034440c99000c1c8501405a50b84002007010320034624903058882d80c000d41141d5452081012083c01414400e400f540000d00c1c3c41d01240c148000054014100c8105035280c0e0300741700e03030340e103450150900141c00354042d8030450201360300c00040e5000d0150100c2c0a038460320f448410604000340b0040403010502c10500340707101d05004006000c0d066a4016250560008800310190080707000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 704367796 1250 704366546 704366557
    0x115020312151305090d0c0506221a270c04050a09060606091806030803060f1c08040e071806031a030102030f090d050a020a020d03030617010504030305060a080c0f0303 74
    0x400a0410f115030f0399401c0c86400c52402144500304070350b011096000e0407100c454403030000130f1881d008074000c0f803a5002c2c0b11601c0c0c1d00c108002c4032074440800550f80c03401c1107403c1014001c0a005010410099280105816105840c1c01e16014204d014105083c464481840f244043e103c0ca980d04003044100766154406c03c1801c0e40200108034054882e00043d001e5a010b208080114400c801c9601e8a10101e0050340200c03544181c40d1421602c8035400c104105420b004003642111040c2d5102100145d5003911071105801019010b54031414081e20040d0b034840284000140709e20146c041c1401ca18540040e01150303c9450005800503000890440c1114400c490303561540c0044148a00302c8203604229000d0405c90044030351031a4000c0d019100c500a05100702e02603000007040d1409410500c00800c140383c40391a00049141d01c84201780b440740410050308060360354030001c0204041c4c040c455107400c82ca046424017401882d02e0001c540d18a0007814960007050303002000c08440d102082030b00d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 704369046 1250 704367796 704367799
    0x51507030525020622120503180117040614252d02011a04230c040b04080f0f07080c13060b030408120a020412140c030f010204050108011502031215 65
    0x1e590342018024081032603a26445441020741e401000a20929054880c5200540c007c000d1418a896218600d851204000000b814801c0b84500740c0d60300583c102c00d291050b03201c0e0b0f000080c1c8122000b40c1d600a048024103603c0c036940343d880038001d00c100e0b669114100040343d283c640f1864031203d50050541c240d0b0303000c0b200d1016115201d80c01107501900080c1480c1c807140707195a10030203d03c5c2008142d40d490f40c3c200705060841d09410991415680f200c0d9400340d010000d4510b01583c5c3e800c940f80640c41684a2103240d04440340586900406101c15041000120300408219091a40310358580351418092841144143d100000303031302c01a0481c41c01040307407000c10760302e034505410191101d90181110000c1c1845250005030340400510944041e10210340b4108540c0e0850b035942044130b01c9410407000d091203110240d0b44c0030f90341007007c00c5611500c00000344c1c83d2854280050403e582c113821020032070703150302c10521003039600105a030364600c0346541c0b03004141c56101c4c4042c01041c16010030f6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 704370296 1250 704369046 704369059
    0x40201020c092e0308030601050c01090b0114090916120c051f080a1a040c030b040f020d0f051303030207021503070203130b090f1005090909010605150703052502 71
    0x3c840154240324000f5024a281140c0012101c0000400c1c900c00783d0000500e0f0042c103001055055110b180a41b10072429030000007a40c0c000c0c0c3c4c4030441d0b241c009a0103d24001c3c03008a8045a44c24617031542a0001c40000007002e251441407022000b0144a0142001340b6044100d45010300610741d00d0380c00142005003400c1525210b402025070003c24140407180030170a0f481c0412031508161141c0d0000c8500f5081d9440c0c2c840840003000058554541d41400301074441c400700706180c4e9148120019523041c400d0042c0e650700b100c6981e20a4a84400e05800b551b442c203800c02c18805521030f41485203581c10b1030010f988504501c001500114540b014004444003c010400c242d80c0004c0103008414030105105040ba6a40d450b4401d1840782c004501e0700207403c40d44007180c605010b07650082501644c144141000d81c4c80d0049601014200c504a005a44449040040d801e2100b11002c403100030b0001e0501d4850591000360083c491499100715004059400d551f421010007207183c2d1440d030041c4403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 704371546 1250 704370296 704370301
    0x71202030f0121032111030f0604060501090e010b070f05061504060509040203031207020c030f070302120d0c0b04031b05010914070812090d060e16090501050901030b040201020c09 79
    0x101d0520500c00d00035803071583c6421008000045010040341d889503410340e44c05840c2080d0002580ca820300240342c034845141c64000100594503420003642c0f04802c07a000c60708452805400300301c241d9826500c01ca0622200784024070007852001c20b2541580e20800c2d241c1d51354580703450820b0707a50340d084002030a82d0040409102410b80305407a41c0d800702c4030844080c40b0181c2c684041209407070b019940254558010800e2010200c801d400890b4010000d005560a40c0e181501007030421050044901c50b40e004441d003402103140c16a4221441c0c00309100511404035265005441c1d21a50b40003e410051280c1c0060100351207024501c2110010206422030100396241403400f800394002e08454020310782e154208942000200d420407680454018844e1440190341c1404c280d00514140344c00021500720340000c2105400b502d44500e030a10018940540e9103044005a116560020303006075003007000400055441e0703000541900c4d0000303011012510307203100607443e01801401e01d54000c1e103903004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 704372796 1250 704371546 704371561
    0x203040515010b0d0b042306010e0a1214010c0e12030c12040314010b1507020301140103080c070618050103050702030706090b160206090304060c05160b181807030507120203 76
    0x1d0310302030b9101034060010040c00e8003000103403506134048110031f050303c403816141c61103403891003600108107050075010b013084003000c281c68071011341048100b420300248690401c480f0071800c0e85484280002000040c0700a18011302c0054092040c03446098074512000181341d0a104544103944820100c405420315070100268503006031000f03542a4141c5c986822203168180100ea4411030010107072408205009140710307480d0000f0f03000780e80641d690554451105103046144d40a94001c80800f51500c42d0002514500f0106401110070841800300c01032a49501080a50640d0f2017400c0114a40d664044103d1540c012000d026005506020710314040c040c0080d0b0041c001c01c110041d003414040802c8050382d823040306691a02441e03104000400072544140740710307000d15109005850001c0204041d032030112216822488800e800040c030640890450001a045440103440000d00041130070800080171400901c0705e4241900c40c000146010f105011a050031900d2920440d12801c140342e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 704374046 1250 704372796 704372819
    0xf2e1701050a260d23030601080a110c0f010e0d1e031d0307030314061c0f082206090e0403021c03060503030f0403110607020d29011d0c1804020304051501 68
    0x81c080421002c403c01d00c4117106061008507071245006842d194020303180c190894000340b0b010024032127034035018020441d61003814440e0300402c81901d4008104075282001c0e5900700042d90038804d00b444200102211404040c00d00d801c407080460800003440c40c2e040303007002c0ea540b002c420b1030006030000040f1441011380640c0044002141c04103020199074034002844641022541110044015640c809000400b903000c0ca111080c464400c0340d090a008182c0c0340d40d140000074042d40c49600789242408030651003402c034001411003002c800d071035091030b86029440703072100f40c90408040d00302141c00c40014002c0d084100288005030440e40c1e034560600c2941e203684c1050000f1120706481480e0301c2ea25180031000d40d1106074000303000c00c02c0401c1a960311000302e40c1944040404884022801c0200c0f045440c06600130099540300107a15100d5252454003800d009050100031401444450308410b900110074038118400c3d5401680ca032a1130405034a0258076694000c2c0c1400c0703c0001003100f64180307 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 704375296 1250 704374046 704374067
    0x70204090803190203090703140f0a03050c0d140f090406030c150e041a1009050a0e04050f0604031b110405040c080d020d0e0f2e1701050a260d 63
    0x7004100d0840c105000b0343c02c00d9110a5401945a0380004014808240890641151813003e071040382c1c0800418405241001d00600c0180c0c0030031008105120100014040c0b820001d5451411070010010000014807500600040d100455004074030591140c0ba40d5100201a5400c90411680c50765102c00904004040d0060313140020002c104220039800d26010b01c05000401c0c4070701003910b0340782c24107005182860789002c500300714400c0d600080c3c3d074a40c140d0120240070b1030400b0803ca8501414440d16000e940900114194004400c000129a000400030390854904103000703101c11403403c01281c503800704603210368840c0c68442400200608041001b04036810f88064900a45400c2400d0380c03680300e0843d007900824560400070715503142151640082102c014809032010304070034020320800325610340d4040704540e40c81c0e0551606412092040402900d6007249800c2d40c186008901040740c90310411194402e001d01d8442d8500f00121804000d403802011034204001e00d000040100124 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 704376546 1250 704375296 704375311
    0x4051e0105060415050a03020d1505090106030c150815062a1941010c1d03030f07050102070f0501050f0a02070b1b1b0c1f0804080d02070204090803 65
    0x1810703160f20b50907943d1410013089a00c01040c0c030344040e10303680034400c42c000e0701001105d9850105c04001989142c601c10035018009201c00002c22070704520b880081c00320300e41c1008460b42c0408a0341e044440c1e00c0412190300140c0d038942022101e601c0d90108a84e030107000c05982d50328402c42e0f1400750141c840000c080f2503c28400031503d40d10303030444031240c1032500d10381e01a220141c80980d0401d10080240800000c142a41017034a800d8000540000707280820041000265112460841a103501451510740c04d0540f04d50501c0d240900c0000a55034803c6d45040603101001041e0301007030201c20340c107486c402ea802c445482c20302070f000e123800c80c0201000c844802d030100d041404104d016199109880302280c1c0501c50390010380b10b0000c070031348900c20140070314091501000f6080034155851441910600c4c000002d14154a42c1410003009601072200065103d550541540301541c1c000354103900240c01503051550392444240060183c460148041d4106003420020b00c100500280110b106440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 704377796 1250 704376546 704376551
    0xa09021201140d0602130e010b07230304120f1a07020f0a020904060e1608010608010b03030c031905091806010201051501090614120a06061b020604060804051e01050604 74
    0x80351154540d240e0a0050401e03000004980c2c00f400081e03183d4003c0003900407250000250340d42d902442d9040381e0f070907005442201c03c007003801310801c0401c0d0207280811040c080065803851580014941da400f6904c01c0c18940c10f10112000d060260075220400b1954000e0801144040304a1100c54241c0c0180c40c2c41c001882446000100300c10301040900c040c0b98010040603050725240c550801500076666040e51038018490702c02d103244100d2214400400c5014000314181d0b281c038040d142152030191400340240c00421012142c601c0100c00c84d0f07202d1a05001402580805120031203d501601c801ca503001b210881005101b61a40301f40729100312800d900a111581d07859880022442c1d102500c1030218072041002e0044600410340743c40c001312071411040c24000f07140f0200c0c841100030755821046076650041030100756804030a50030380f10b4140303000c4107800015901103410307440b03944189400c020255000c142040010320140810074944001c4010811a03429898000c10307003525020320851 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 704379046 1250 704377796 704377799
    0x105090f0f0a15020d0209130e120306030312130507060302190c020a0e0703141303020708120301090203100815100504150e180706090303090f2d050a09021201 70
    0x40007400303401c0da9901950003c901420300c501c0b04040e4000140b68101d181d02172003d88032584803130b034400c100c00642510100d01820041c0a09d424990b25450081680d0403c10810603d910000110788028400c1401d801440d611825842d9941e1b240d041c2c020010701608800003071041d815006011a0403690080ea1108104110280e950044030b410003900070407184020041440800c1449600005500b001315003c2051704600c82e00701401c4400449240039503025409041d810403442015084003802800341792040d529504082c041403140c0c80c030f0190000300080340000e400a0b01001040031501312410a510784214100c165021200d0000200002000094a10386030190252400e0101c01803d049420b003680c0080300303a0b0007000d0300050801124010f451440800400c802850107903100d120403800c1d841c00030400d042d00d40c070440f031814102c04188000c006001c5512010600502050202541c0e00c003441c010101a2b4845903010041c201c1c00148c000194004213006002d214640500d43e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 704380296 1250 704379046 704379073
    0xc0e040204061b0c09090609060e0a0c090b0d02060c060f0a1505150412050318030106030c0e06011e02100b0a06022e020316020d020a0302031903020c0105090f 70
    0x7801075119000000d03081030140301e00110040c24004690380284d84590650b03031a08031400c251120703060125803990307581c3e51503400d000c02841060030303c062401c00b42c5003580c09500e80840944c610301070b000303c0903500c0784034a855036038410703000c40c051340d0140685441d503668603069a215035003284e20304a40d1740c0b4170000808502d0740d84912812140f140c04943d44882c14401400782c0c440f080c14a200b01c179101040044ac14020031104031485510a100135030f0b50701c1d03001d402003809440f452100e0340641e0600304184001401c10300c11f041604d000349444400d5170780700c400480d611001480da0300100d00880480d4034003a6408140b40c4496180c80780c0500c101503944081c4400e40c0750340e104030b00058002201540454000301034000c803141c10584140c005031170002c0e0030703401c0f81c0c82924080302203d0b640f038460100d2074061009030f034428030b01c3c000741a4a107880c2d100a5120b220740791189020030020400f0300c6a190280d410b581c14541440020801d43c071309400c006944001c08002400079100d0282c100c200ca = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 704381546 1250 704380296 704380301
    0x110c010e030d0e0f1503010609090203160e0105120a150b1c051801050c1b0f06061504080a15051018090303090b1920091212040303030c0e04 62
    0x203000c00030340100322040721114112090316501d24010b81c00308030301c89800c81603a01e03580010522035440c0c04030b603604d5141940141a213040340d800074a001c2d005008204840c1407228002c16030748000c5c10007a480101540040307c2034454000040103101102d0306200d0b11080a43c001d0517807913000c8500900f00b41e1281c210211301d020380b0030604500300303107101d0340b000018003a000306402070060800c50001d02d0f01c0422190a60313004660840b03e80e031010a6444024030184402c1d901040e2000142580343c406c20149912510700501c160301034404654854103262024045a000348035030070949000d0b040c0c51605c1c11050780c11400d400001801d000119a068048202c1c1e4411141d02801d6010301c4032191680310090594000e056040c10382d21100c50020400303107003215205070f180035441079007000001c5007102201e100700c1c0f600480c1191146405040310340c132000ca0340080c0003100e100301c10440020607a460510ba10240c0042c03010082000010035806403c8185000c078551a4442400d0009081c41f04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 704382796 1250 704381546 704381567
    0x2120d1b0b012c09060f010609030f030e12030c0c1504060c0323030f0a0c0f14030402031006061715060f0a0908120a090b03010e0105120307060507110c01 68
    0x2000c8010001c54208070080d6222401481c3e410512400d802100b2840250444c1c3d800e9641e0003c0c0c0070841035040d03001e00240545501c3c203003042a182141c0303841e0008e0b0000e0b4001010302402c0c144007116559200c0e01390a42000003021281d84079101140141c43d0789080c84854010180c04001c641e0440c0780c0016601945d01d507640307030800402d1940341140d190701c014040506240748941404d610358080b60040d407040320328a200906031300b09070b0900c20840d180001c04000300481400c2403640a54407603006a030380f0b40000c50554503030701c80303000107030400381820001c0780580d24060300001c00701c1d08500240c0f543c444442801c1042e90b1075008102400800483d00b0b40c1c440001c010041d070758060507018240c0301140b072415070703035080c1c498a513686000d031384451081407114080b4900200940c403400c0b44006d003440944890455140c112613101c5024107002d654802c00382030340b040b000c4d0101041a54800d0b03801100c28820b50070484006002954442c280805c58061140d00c81421350040302641c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 704384046 1250 704382796 704382803
    0x801050d050604150b04021215030a11040c03020405030601080606090c1c0f0b3001060b0313020310020a05090a0806042d0b0408030f0709060507060f0902120d1b 71
    0x80300c0d81d43c660f500b402030041124038601c4143d0340c00464402da1643e20180c80b448080445000c0e1500381000c2c481a440032414089110743c3c41902442c0020b1030001c82c0c0311701c002042c0c5003c150b1040c00c00702503005c0c1c090703504096018031810000054800c00003904a024038010b03107115015440e070701400344041c810742000126031640f000ca51902c1001c5640503500c08003030030400080783c40110f000500075042140a0428044811480c51106144040b4001782e845692000f006200c5c940800200c107070100415081c403001001c120f207010b5480a00c000c0c02990750610b011940c40105c0c400113400790300010070490040c951b061010030400b9000821900a82e00449a2021140c03104041c3c225503084881d0401c4010b070080240000036001031640d400349115901040c0c40b845d01c01207005104400814071401c00c009402d040080740c0c0c211040350009900324a000c01d030308808040c45009403525102c0250001c6500115682c1c0390000704002051280607541c1c0c1030a440b4992070190804039404000c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 704385296 1250 704384046 704384053
    0x3041406070b0c1e071a13020d02060f070b0a20040528090609090b090106061e0203121305060c030618040c080d020d080106020712110f060a0e010801050d05 69
    0x51010364140060050f00d140b041d01e0420700303003c8041d020b000350442d003170440f00000c01b6410002c1c1c81c207090444c580d11040403844510b0b07011291300044c3c0344010a250184c018100040c034403242c42c80c010211014660000380b595054204081032000412240520071a01117510140c0c12010012404407011158010603100301c9007028078002c07406400c43e442905140384054000200c0901034080d07000101a1104005010140350030841d200c00002071210031203034904002804003d0700419031803040c0116a1700568a071030300c102c003a4590703c60310402130440340c01030b010032640c4804101c1400c5610300c510107903040d58481e280282440d02090718450782c04001040b02201c1e02c424644219400790042d610222a246c0e0350f0003281c1090b02c0d0a8180700144c02520380d8011481c1c008441600402c0f4902c01002c60318a0002d0340140d20754525001802040d031840c494046944180e8103000300305005100a58800e143d4030701410a004018003035000c250001d00008040c80c4c40304072410140e400a024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 704386546 1250 704385296 704385301
    0x1803080609040c090e0a15020d1104260a1709010f091404090305270915010e0d020f10080718150c1b180f230601090302090903041406070b 61
    0x100005031410b00c1c0d80341701c64407500507a50003086944072803018241c66100c00503603401111088500781d03426408480600d0208100c100101060f040c880303010030301d031500a2001740340a690001d050140355000501107041c594075001010b12500e00800c10a2001d8035200040c0320b040b8020b541e92240ca200710380c602e1600f0802541e032401c00d904002130492013032400b10b20b0301e802a018040c40c207000117821003085800601030701040c28a0150340760800c0c074030960041c0200d080700000b00340d0b800003c1078074082d54202d0b070100f0071925544003051078008020a900085036660800402012040391800001170820844001502050120310151100e216004030950640302040d1190500c1c94022251380c52050504080c0340f08021a0342c005d007158600d480010341c80d8240d041c0985002403592030764540b4128a6041d082540020107001c13070545032a0345500e645000c0143e440e42520351001e5084841e4000b00100e02c24040020300c262006e070b0700c0070000320300c0300c4043c082c1c41e0003202002081440000003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 704387796 1250 704386546 704386559
    0x615040b030c0a03120507081c0c020a08040501030902121504060609090302100c1b0309030203070b0324040e01020c011d1f02030a06051002060411150406211803080609040c 76
    0x9040f117901801c000380344c0226540d404138a54403e40d8040e9240800341c600105c0c4048070301941e80595054801003e25200e1030300e94060f248114880c040c145a9114190320031504d0754030100da0502803100075148a0500240c014840c0c2d00700f118101c85542c030700074010443c05403d1144580054242d4024804030b104918848000c26010300b41e01c1c10301c8203010790500b201301c2031010803e00391b21036a240003140d803562041c5441c1040c1a0010b00c01c0038000d1042004584020458500c4072800411410303040c0c25034000315004080d544a6842c01d5400003600381038901054101d01ca810441100e1958050a16075a840d1110001d05500010040e032100060085240350003030f5400c120100b100190b00e947d80d038001549842003850800143c0c0154080005201c51410105010b04040d07506054113840510101c54510807405030b1824010301c1c582d4840e28030001501e0b0306103141c84020400044200d0b6401d045200355138442200014406c9002030715608242d01d055000ea540421034405180c00c01c43d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 704389046 1250 704387796 704387813
    0x30b1503150405150f0f090408040f152a0506010b09150a02120a0201060536040809010c03030f0501080105090d02010c0c17070f081c23070507050615040b030c0a03 72
    0x2981c165206c0c2c22003a000b046551000c942a02075132180306010754880c40e2204588542c6501c4e440841045014820b512a031504100312401d6462814a11070292602c8503003988541d840c800302501501c100000440da041c0c0c500001c0c075024100300c5840c443c415841103081498403480039044016000b540d035401c2c440544002400020001d03000220f901e42c0c8403030100c0c980240f141350071141c2801c3d12070704a000744141020f000c90a103240191203241c0ca00742c3ca40b015140704d1241e01504124000407044281131003a400302e0f5001c40c40c51014889035946004aa02910042d034001c0f80a002d40c07242c01e003000340140b24050603103075036440ea80040440f94a880b806490a03a040c0a02071804004150014a800c03080044562060b500c09450305a1902c0041408121016014942d4070b800c074050801095441c0305150300b1041d02000c2e082d84e4801e402182d440c02901c41c01400d512442c0300703028018401a00d103201c018000d9804010b40c02001040503960003140800350f8100003030754001d002080040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 704390296 1250 704389046 704389069
    0x10e030118030804050f0a0602120610090b0c12070809191202091012030215060d03080a020d0b061c05060402251707061d0102040b0406050703030b150315040515 71
    0x52003511214894046d400c0e00744030300550100e072215400100e20602c1ea5045c0e02e26034103c101a20700c1c030f000c241802d03006441041c03680a0003401410216003094013450412070502e01200541c030729900c504082c1303000b10b05504800500b512850049080d91098007202c0400c4046071251017988480300350a0b0244003c04c280a0b0030300944a0f85000d0200c0d000080e407225030240c40c0b10742d000303105c0b005c0c503145d0f031210100c2c000d8015441a10b058110344080f0341e11182d441d4226020f07490050f558a40090f40900400308506100d802c4040070486c075507040700c8460b0805c4880c10110080c0215503444042000b2441144a6003400886e005020740c1e0a064203a032900c1424410900317070901190307055440303006400240c012100340e40c648140141414008a4001541d00564001e50a06041500b05005e600490003000300b0440e01040070428103109130132209030458041c10105030362640310700303129160740300b10b521105185e081d12542c500c07810a441910300c60001d50002070600206c440c01c00c041054071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 704391546 1250 704390296 704390303
    0x70c0b13090e01151e06080613020306031c12050105010201050c070b0402030a06050c091203070201020d11070e01030624060f030c0c0b0c071a0103031e030f0e0c010e030118030804 79
    0x26010640600c032003141d00713000903207a00322a45100d10700340440b0407140445504050208034000040c0709458440c1b42d880c401c5902c040307402507207070f5540c40007081ca0000300410300c0d00d030b04504802c4146115088038592005481c405014809680c0712001a8241c6005a0703010000b8002040064085102100240d4000d407000f001d50b22030100d02e4542c40180c40e01034814541607240040d408809203080c01e40c041c403a46465010b14104102da0b00013039101c018072115502071056003881742c00801000d0200fa13020b401c0000d240d10184d42c480c2001c100a024a2655641c3c042006100c9243c010351031601c20202e400316607458003050f0103003200b1405006c220101000b809620300d2a00c000800d080005441148000503403a150386d564140410b403031682600205540025400510100798001e4011240308403c0e04140c01240010000710300038001c01c403454504501d8203203075801b12600070864100a00307090b690380403800b0084e0304041c200d41a801c80b40c8101e0f40e0900d001e80000740254206a4083d00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 704392796 1250 704391546 704391551
    0x2708160624050a0302091906140102010b0301140c0a051c02070c0b0702101218050c01080106051809180a060b1212040909020d080a17010f151107080a08070c0b13090e01 74
    0x8564050700261121f5401400030b0900340850302703000d035078248107231010103504400a10207541075010103258800c0c06840380030300820008142001c907009a040321050303a1403280303030b940c50341c1900c507a10029044004e04485081604000003802c0590205460f8041d80007000c02d00460a2158242c0d030504904004824182d00c0d40d69105544200c180c02c00c070001c3c000c40c060640201350f00001060002c0580001080c040180840744c4800450510f034060040e059031240d0144d103031603642e04043c5040c140c02030310500c03800085600b00480341d00a010108010b540201007a03658803c12a100da41c1d0400410340402e040c0000c01c11003069820019425001908600c00d0029a4a80c850036622008204011914404140e07450a08080c5818010484180c46010030790400c0d00100ca003043c43e20440c1308115008161301c1d401d02c070a1103184002e00740b95040301e048240d94036000c0707000e400100b42940c41c090f42501c00924641c40d42d0444403640f5014844410142c200190817004100c84030740709003e0365 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 704394046 1250 704392796 704392831
    0xc0609060a200d020a11010201150b09130f0c02010f022113020904030512061828051e09010902090613062303102708160624050a030209 60
    0x10000d00031040100025130103000b00e800c07582030000d0400d8000440d0340c11a89031200c044c0308541c1c580a19402d0300c031290850703507542c2e0003c400a40041c02488421100d075140c808190b08001403640015880300142c1c0083c021038a08000b44030880c001d0002801c403400ca1b6420f10303013150240020040d03010904000c3c03003403101c140340c010801e00d0b0000c0b101100032440024640c410010300b10000da500603804c40300e11203148100d02c13020030160b00242c40b10441ca11602c00703171603060a0490107480040175405042240d89800c400050808400d200031441792204240419034000041c0680404e003070700503000c6450390b200d42d403d10001605401409814030342d105000315203142c01111900006a500303004100034095902014200141c05445e000c03040c1c5003058509507540310740c0d07901694aa4441041d0a0300d42e850500c00c40611844e000d4800d200004203c0004020603035020440e070701c00030304100c0c0250010010a1016550a01a0075400168280d0800061030260400742d03004d00c0142d490b605030b0703 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 704395296 1250 704394046 704394107
    0x100302210312040b06180112120509030a081855060f02010c09060e120102131a0304081c020910080402040e0c0109031511070b0105030c0609060a 64
    0x582c00d48088030448089010b014661500d282c1a21804804810048041d403600b880707101440020000182040c02c5110200900c42c042d01c1a80d030789140141c151204100c882c44c1002d00c503400310148000c807120a0480c0041800c1c041488041426508003c0400361030a034252102a0040c04d140f410a060032034120400d050b100c1c00f5400404035042e00030380c4e4542004400307003851113096049421a80b5040072100001e0380540d03100220b40c0780e0b00b0302003401e4000d40d000c100e80c5081f410981c40e03a5800050882c5201e1030703c0c84d190080320800f41580c07036070030100c1034940c165100555028045030010b00045090340b1503c00841468086440300502c3d00010f400410f0040c403001c04804041030000342040103600385805150617083d42240035258107110103001070702c0442c1d070b80000341030342c00b05086a1400da20140c2c09441c12040000c030f1141c581071a4642805502024001d4502074014034640c1c0c481c9007001c0058a08440004000da03040803807404046880314100075941806030a07881200141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 704396546 1250 704395296 704395327
    0x14060f161506090908030f0702120a050912030901050f210a0902042a140c030309030403060b09010b0912070b0313020405090a0b0711120d0e061003022103 68
    0x19a10070300002900701014141d03482110055031107450a1403c1042080004581e40d0859a0003010302d0005052a1a8044100d2412481000c40c0c00c6100c00041c5003100640c0120180c00002000c0f00c065506600da0a01d1a48a009500d543d501046092009031050300d0001d018040031101c003003000e0451000c003001010040e80075a0500385659583c11140c0642c1080d0003014130075003c0280c4118101241d000440f03c40c82d40301d008504024020103070209058104040b903440c8a103540889449051050101e61252301500c41103403990301e4210000707030324149417440324121058101d030a0305040380e5000380b04950740310030640d0080d80124800461042c041601450040ca400321052134519542d105000442e40d0142c85c0e0000703988481c81c02c100280e2000b01ca00e82c8603949107003625203c80c110f03081c1490712201e0a644114500e000c60503101203085036000008030820030088038000d80740c0e0f6400c40e0b0745050600000c1e411003101c0d25078828007102480e800003e030721404126440d106070104000320 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 704397796 1250 704396546 704396587
    0x40b0c0d0606053013051c0906080a060803030106050a11060115030e0a0b04060b03030409050f0709060f0e0f010903050105040b090d08010b0a0f03060e0901090b1014060f 75
    0x115201040000b81c4d42010002c4041148410001003039030b815510000e02c041d80010081c00401041c1172400d41000717070030b001d15455100710b44c45591544070220f8000c1c006040318012000000c26a100040c0355a01d180030351401c88248c0009076155909008048a03140d101d90140300c24440086214a002076082103214024100241c44040f1001601401001d49021004142c640d5000440050104440c2203803990841c3d40004000394030401200400e0a5005580c0000411403030442000800344040d42068840c070030945e208046203840364015209100c1d1040c82000003544c0d802050b0301030824456140e40590141031445011342d0340d640c0e0074295102110200c81c00780c2010b0601180710010000c0c00e01c000d0403030030071404940c102030341500240a521400800c10801003184070341d00d40030354040809002020008a4503180c805030650190803110412030f0700c43c50350b600281101c5114103020046c0c030203c442e2060a610a04100141e60b0000c0c203a10340215400c100020b0000003502a254 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 704399046 1250 704397796 704397809
    0x60a081f0b0d1d07180b0d050a031707111c0302040f080102131d0a09060b0d0311070602010b0f040f14040c06030605010c02010c0204020c010e01050c04030c05030a0b040b0c0d06 78
    0x1c1c2d44940fa21140c4210700407852a91003c0d4402c0782c082c030814a03000c0300d09502c2071500100103020489100080c0d4544035080c005000b90044000b100e050560150301c5295403d10210f40d540303540c0750004101c881003c02d8413511a136820100e500b40360301074010702c2103031000c010380b03005800c16442d00c415054100443d0b014503820307903000a00306a40c08408609000401400300101107041d098009425410741c001c22600ca040d0799003c100d010015150302c0400b00020203006000340703000900d0043c222446011095816124030800082c0407841402034688000c00031384030070010400b02c1c0a210284c01101e90402180c0e4581001c82558141c1c11b464a01c550b00541d1030200b40307880c080e40a001c4076001c0d001030781048200ea10342c0002d030741c1210700303240d03c01d40c1600c00681e1401c03114115401031003c000007541950034031040c4002d0130020f5020b0826a4026444040596624000c260391810041c1d0f0041a50b01500000383c042420300001c203900041c00042d8926003400e50050000b101c0346030300400c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 704400296 1250 704399046 704399051
    0x63723060c012408060a11091c0503040f0e0a050105060412150513120f08040818100e03010f1413051c08010e06010e0d080f1b030307030b060a081f0b0d 67
    0x201325203907003000210f03040f0340342d00380401ca110348410105841c0d218140800380540c140c40147c10100c2700d80325851041c941c0207420349846507150240e030400a0820300c6000c4c0070020321004551a000980304403070407210020310040c41d0610708601d10110741e14451040c3d500ca04283c0200c01c8800d0b003030081d54456401d040d443c8440c042d036482e200310401ea02c144401c04100308007500d109046e03040501140c110303800660603a1a145000d003140119040b1403151600445c0d070008028000f904241f00a4902d01708030001e00000301c000e480b8030100d9011040000c214820040800c0030080310070000c00301280204166100410b05203040b100c040c5000c00f0b000002201640100140c0015124045c1c200310240b03003000728240c128001803050104004080d21241c40041c0e044400501c00701104c3d4030307048060781c003044054150702498885e007085030004003290520306105020303c1c0000031139002c0c005986a400d0a9150106000909407191002103034500c80b50310045098a5442e02400e401d04c0c500130003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 704401546 1250 704400296 704400299
    0xa140a03121704062705060403140c0f0c0301180b04080904061d09070e1603051f0b0409050a0b06030406090c03150f0b011e08063723060c0124 63
    0x41c0c0304401111910342c5c0322016090424006040840c0d55038200f600361a08803841020285440e426101e07412000e4058462000c081000110108050601200c2100204002c002c4410003c81403261084014000070035240018001901305008e03000390500900002909500d900c940550300f8103110f08002204821780400400349010407104010700010002c0745600d042828a854500da1403808000074142c0702c0b80020300c00c60381010340301c0c2e4003031404c4031607440745580d80500d0040e40d00a0140d04d070720f10704040010760b4006060080130220203019050501c0c56441e40c484000500c54140c0440e401080080000049441a14015500070084600003651803512142c1000c0300d809204a40c180303c0c91051401c070268541d95405400c00180c1000c401170703030310103000a00c0c0c5c90000010110441d6030501707d14a513a5103a04039101c1211580720025690b80b9044c4251201c01c2e00200f02d94860302441115095080190141081c041094000f20b4002100350649001c550000501c84009007807980 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 704402796 1250 704401546 704401571
    0x20309160e040b09030a090311011e09032108190b15041d0c030a020a11030c152503090206121f12080301031101140a0e0a140a0312170406 61
    0xb500360085500c400131460310046c04400b5004c4c0d42d1a200c094101098080e003141c01e030340121400f02c18082100d4050a21400f64a070103071810300341c2c1c00103466003445208060b241c0002c58941e21400d05141d10340b40225507600380c04c952101500c82d40b4071b15180e20b800072008503480301400305c4458442e0502468071681080410b50340d000c901d015110741c03500e112090010302d07003051007120780044140300056540d001d107c2055540d8010f40c5600c900134400045c0740d426048012410295001040c603103560161540103814002400403d0841c880107416a40c80340d00c03c2c0242d00201d40103101a00b20303410180301440101c1201c1c0c0403104000034941d1400c0c08034410100308816409410f1148540e00c0300001601c4880c42400140402058500040c00c01ca000782c5c029030402e8501c0c070840704070994540428000034007081c1880c3d05140039604140020071181c407043c20002c1c40c0507001e40160005469a11900003000310400c1200034402e10800c00701c1740306141944284144e009103004214030b40300c000f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 704404046 1250 704402796 704402813
    0x10c020c100c03080f2d0609010e010f0b03101e0e0a14010506033303160308190e280b2d1902060415021903020309160e04 54
    0x14032008208141c00b55000094010f00c41da90420403010382561199111140807860640c0085c030401c0181c012801160000c241c582e8035032041c2020344d06884280d80c1d51a503118200300038010b8040000000070240301c0315041e0380180d41c4c0305414008100200b80d0303803505400100c2d131201c00c1002d80540301405000000c2d480040a0700001400b104000104844c214050907841c1802214420b240c0003020031204800000c011a103002c0d00254084001080c09822003400d0052030605d00034040c0c42c0d0011500241e40140c0c80840340c104004528184016940201101e1040612028001000164011030700e6251490040f0401c1001d030300c9160200c00341052480105a01001090b40108142c9854a00000c82484914200c0101841c0c00c400c3c0403004c1014080c1789100c0314402420350000d510590300203001d900650041220240301913542c202c22042c3d00c5170b506215064200341d601d8000451280d801950b004071071505490705040c0c01c04281c0303e900da60b9400182e42d54240c406100c2486403030b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 704405296 1250 704404046 704404069
    0x5030402030115050d02060c01111b060601050717030615030a0606020601080714060a03091a0601030b151605100e060601140a08060616020a06020102180607051e030408010c020c 78
    0x1000d89a900501c0c10002401c00c01390205d0082c05600046030501d541c08094100200715158418400d403038500348222000c3d81400384108984511400010a40550041c002c4501c00d81d0050090342c40ea4002c44803410b8a036101034246a00314055080c2494102034802c05580146000d4101087c000d203841402403070100107030042185900200ea04100048010b5850360f042c0c0802e03502c0c5a05d9080c4001d05400500000601403c84150401041641c0b010729107924401d000036201001044520400d00601283c051943e298500c0200035102c086400004000c036a10700c0350048034a814003001203007013075032001a009046548000c00f8000c0d07643c0c02c5009004001d410600c02130a21100035402040d000d0301421007806040c0000c0c00c0e200100090303a0855449402404007040903650b041c2c028004c1d4420264103042408048020241c0c3c6883c400320344d00c258219006040c600c041d50360000802511a1070546c00307210402c4001144030081c09503000f5031501c0e801070984101800140316480818 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 704406546 1250 704405296 704405321
    0xe010206010e130c180c0314060f19051804060b010804080403110109081506010305060103150510030209132307021b06090604030b01051f0c0f08040312050304020301 73
    0x240040c07100c1240b440c1c0c01507002c1c0300e904150ba01d030345107030070800001a2140c004070030001442c502524501d1194000302241460ba41d42000829061001c102e01d204095850079808120001c4040e010718128444204491441d000903824698540014106c0c0416203032056065500c0c0c000c06c002d002d918410141d40c400c0a0904001e1880c040d51034521300d21683c040101481041005a8126407140000704045c01111003154882c0815190b010224042240c8550001c1e0038180081d82d02c1d4840c0c0030306040c072816096030140d0941481c4c10010041b400f0400101056030900103100c855440c48803e0007000c014001c006440f1141030b2034204181d0310b000340781c45406010018080c48943c0058105038000d5134928642600303207494005115413103446800d642c052008203010090210010085040f1081120002540808065090714031001012101e0100d5205141640410000040340808600c11480c2074a029182e40e2103241c4d5105c00f459034800204080200003c6080c24440d1702c0c0309548 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 704407796 1250 704406546 704406553
    0x2040c09030b19090f1a0601020c130b0607020a121e030c02011d120309011b031e110102040927020a14040615030b011404030b060409050309120d0e0102 67
    0x15902c031211032070301c040e10390b80b6400c009454482c0d8000c0d01d0350040030b02179030256060720401142d040c043d081c4118070850171402d128030b00c0414481d41c00083c0703003840300001410010110440c6032040c070042042020b2290084001c00c203c40050341c0b003420100c0680003500c01c0c541382142030f08000080c1c4005031030050900d02884410b81c0442d4100c54841e4803540c0c2440c0c4012412210705002e9016020038404640155506401151113100400609400c00d0282e9580060820109000040d1502440050041000000107008034510050424520316071400c007001207450b072426060880e0301980c80900507550b5194401030b202030316004505031f02885440c50b4410a03039034000903010a0310307101c0c100c45039400001e403503601d442d035030001130003803034582540c161a103481c00015002d40f421001d13050001d407076003e5920601103084280c0b41500d80000040c50641d45100601c80107007040d0344142c0d0248021311140c90340e070740d0341240e52000014480c090003c40328540d40103480c002000106070306540 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 704409046 1250 704407796 704407799
    0x30309030c082829011514040303030b01020304120813171f09050a0f11090f01060f090302120703030809070b16080c07030305121608070c08091003060302040c09 71
    0x1c0700310b038001660500e0720641060707114280740407000c80e1010341c4c55420402013101d1000c0001a4021024102e84210035424000a48060210746003000c6c0e85400100070003c0c0010f20119109a1020340d2844060046900d0035407202c0824005504030380040b16240000680c08080907415118440201000060000032460960703000380c0782d0a209070040ca5400580d2a1120300e10502e421028040340c100d02643c04c258118201b000d0010025041542d5001f280289910103040c230030f4805101d0220841c14030441d908040c4111600030524400c402048907001000c00583c1d910462a082401080c0c020f01c003481c038500c0c0180c00114028003164a071b03000700c942000183c0b507480440769414030340800411228210700d42a102030007020310014080c441d2440220030035030800000c00c800c2c0e469032844142503490b041c0c18203c1448000018001401d25004280c07890f000d900d0440442d4890303200241403082c09004981c01c40e00c80b221440020741ca0380c808105600740351003180d640c20080e2030302d80e0301c29 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 704410296 1250 704409046 704409073
    0x506010e01030905071a0306040506090f041b17030d0b01050a052d0a020f010f0c0e011107031e03090504180b091c1709010e1c18030309030c08 63
    0x390030825515050540b82c881510411005100300c9000c1e10340e0240307041050386280d03d03200039500200d034910700491500020502c0303450089030700c034415504170b0740c8010287d0341d07030b61074061011070400b00c0c1d149409680c0c0007044081e08109850010031a0000841d00d46072108000382c2512540c154031414858100201e0b035107a07610078119030b0504080d0040c1c0c2207110307043c204175840a0b91092000062007001c03480d00036459010038915181c00100e4002d01c00c40c0300c0c4100c9001103c030043c215801107006291550065402105945820081c0000b919415641da4440d0728100c00c2c1c014003048003500200c41442015000740446018000c2520104149a1110380c60b5800100215010302404520000206007070010407145000001e4091040021400c1007005410f580c02442001d402e40700c80000242160340c14415415003508070001130a01c40440300c890014081034054000030005044184608202144451700055220381e03a01c01c03011b8950b0400000e080b4240d00000c40917044004c0c1c0250300e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 704411546 1250 704410296 704410307
    0x3020c01080907170703081902070609080604021012140105191a03130c03030201020301230312090612151503070f0e12190c060f021c11030f040602070603050601 71
    0x365010f1450458004c0c03d00c0010a1504509030700003000b0f00c40003c1d02e44c0da044130340188440d80700801d8084808098a600c01603c2c900e94a000714402c55101c2800100940352100d4842c2c0c1744216030402500f40045424041c0556010440e02c8500040d400010080350400451454550810f18403420150741820b1035104100207200f4024042c06000c404188040707214050703018229030245100c15840c0e507038603006c1c2c080e410910071010409180040c41c08500038402c2c0740c03480d42c800100074044000b503100c0c0880d100d401070790345c0540000703040c0301403000c000648900714000d41840007549149050070301080507101903c5da49560200c3d050013070021154100d10b0b084070001c1541408950682e140c0c011076244501d1302e1012081d031041d20450f01880e0031a03001045020b014a03800c200d425101c140c161040c00c0104c01d0a00164000307100809120700e0b801072601e50100e10710b02502c00c031007100482481c5420891600341c9113a00014200702c2c554041000c40000c054505040c01985000c2e00081c08 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 704412796 1250 704411546 704411549
    0x207061b060908040f09050a0c110606101803060e0115050d1401020d020313120206090d0c0515010305030c0c030c010806040c031d0106050a21021e0d08030403020c01080907 76
    0x407500d58504008200d00f050946015000c0141110b80480e913820450303002c0c02c42514071013802407074180c142c400d40d84190014002d035200d8100a01d0140c0b03840081c0400130304255219402c0049580c003004d400030610079480019406018040f03102c032010103940d802c68801032f000301c0d03520101400c10000c94a0700451600303820341012040320310310565403805019100350b0340c8000c0414800810004007405038089000d426010700d4440c1030b10701200c1030507030f680c82e03050b1140b04040c0c2c400740d10540c126205006a1a4007449a01510000c4028400260039a502a001211940c001150210707403400c003000304001d40e603801c4009201e040c1d001c1002030207245000c0c00c00e60140c1e0300c80e20500701040c0641c00007904102140101d500c2d01c449416001c0c02013095008640c4607501000001420529000740c1000f24601200c60b00300a840039400c01c00c5e40c404a45a00c10440d0100b80c58805554900181801c550700a19200d0f54a2a1600c0c1c028205400304c5075132818003146100344468120001050f80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 704414046 1250 704412796 704412803
    0x60509090c0d03120606081f0602060a0f0b030a030f140313060c02032206140309070b0a0915170c0309060a0c020f030f0d06080a05030f09150c0109030207061b 70
    0x5501030b11828204c560400d400d4540038503606018000551692014071140b140c0b0038800c0c010002d81d8900c80000012070203126250040c0d0100000c9840080507900009603181000b40020b42d00c000b06001c241003410351030056002c90b569290b10008260484000d921f20000c609215240d80780442c0b041c6180a1005000303042103a07507581007070002d4004c200315040f1840007000c510354402032400f15034a09000340207003070024510800c1c080b250000c40042c2c03030042100c0000b030040e00e8140506a14541c0080c0c042c4c00c20131038803000008184c9103511080941070303607075560100ba103e0b0702c0b0801e120180e0041c0440c41c01d050100308120440002188190b00b0070003c0c40003003030030714524000b01e20b0601134442072071036030000068640303038121040002c12441e040d00800307000c07482c0e4410503207480d00c062a1001c0c0407500100421440d940d129001420341020043c5022a8080325241c629660380051112041c81e030f649140740d2042c0354040019600070406417402d500b9200301001d841030901e003034a0004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 704415296 1250 704414046 704414059
    0xf010b030106210318050d050f0c0102010204030c050d02030703080c010f110c0c090c0c010c03050402091602030301030f0303021b010f060b09010504050913050111030703140106080711010f020c030c01060509090c 93
    0x4507201035040170041c00800c4020100311422460f410681d8403046042da00d00528414078610704104d50041c006e403811680c100c0f90010f4a2880e24040c4016000001001c9900d405110008400682000003506900740e20f8000091403041c3d80d212981121004084003a070f58909205800200c04c000815650042c1d0560f100a8140c5440192240a0060341c0d0f07845595400c100c142008513925905c0144a103000300c0b14000f0607120700850405904040c61a4401600304000500107e1018441c19107200e1007441d0040c9400c0d078004801c1c22440560199000783d075121180000311003010301510001e0f0140030751062800e042c1c40006040b034440c903c2040d004100031000200001810060009101d802000038085100448009030281c0c4c41110301d80086440d01009465175501032040c141681d0b5980c44a1800fa00c1c1d810301583c00d49000112110300350f480e181150102d0880b800645030001e810340003151550b21502d03006080d141150461401010020208502c0d68000200340d035980d8401d441d00d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 704416546 1250 704415296 704415317
    0xf15060415050406080309040609140c180a0e0103151401051905030303100f090b0f0d0203010b100302190c0c1716031505010504050402130b01050702030f010b0301062103 75
    0x251280c020562096900c00c2c0b5007600040c1704c0708040010002c21000701e404101c4d69403556841d10407600c180a00c54000643d000002c0c00804080c13000784007509100c14a4003c04a0900000b40549020340118072700d8845500100104940128036050780c400c0b8640910a4400e084054030081d4030510506100d06d946000f299544d8180321401006880003405490b540e01e07104504043e018028032070b940e60f28240120000c0e005200b441440c1c1f030454000c144034007104203007003003104079049030344c00f0799141d582c51030310080d56500c04034440882026500d0240c1c8805c505580010040c0e0091030400601c0a000031103400503559281920650701440810002078041c031303007050300d41014072040032184c00301d0020200c28881c40b0107403501c40450041c01804941c5e211000c1c80196117050300c1c025041906441980128110354001420404040c9000c40c100051500042d141c030107407001d0074400e655a1070395681e40342401c0c0115406020702200701c032241c03941c0f00c441048410040d00d014080000c44c200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 704417796 1250 704416546 704416571
    0xc02030309060c1308070b09030c010503150d1a0403080405070602120f0a2021070201050922140f010e131b03020a060f3005130f0b07020f150604 64
    0x5200016103901790807180701d152251203100e1158030040c2050700c45e21801310412201e602c214101c91260000c004800d0752011a50709020800703505171710850310403560201000351008200d139128801c43c020798943e070281c03c0c11300b0710354281152500404119088540060031105c0d914044682515800440e1a61038169201c1141d8490007921404125602102d1005055200151881070121541009150805441c1040c071032841188402800310b5010b004046280ca440b800c612401c2462140c0039081440f4140550200e0b400865070031580e085010070f10074220381200c0d00c14054000c200c860b110b42d060090021134035024501c0c00a00000f14070134050403000b50300c4415002194050000d03c0c6040e00c0d00d2000d4003900c014400200002e004504c1e160741d108113244a00c1620b180d0140d60700120310105042005014000c003d50030840d4091800d100040d400d46001c0040b13800340c0621300d018101a90300a09144540c01d801039140c0c801c1c540c0392142c080880c005908240d0445000a140d01c0001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 704419046 1250 704417796 704417827
    0xb0312040e1012080c010f0c0903290112150203011d1b040b3703020c071701020403020109080c090105010e010e10030b0a27180b040c090c02030309060c 67
    0x30014215496540c00103c100030810001e0489458020001d00c0012907184202007143c443c6c814003400070300032000801c0407401380c1c00710850342d4032a025170120461040e15001c405410a070701001c0b40c5040d00e0f0b840010700040070080d51601c3c030035880c15881c45d45010840f580520ba4062207010558081000c98400703c0b001e140c0342010011801044c1d2a41d0340d0307018914180c1c10207100d10b0124102902110029a2407840c03114a000c500b0103085070000400108600030340140c10100d826206114011819102070b280700020402045c1c005a80c0d04e082d840010580005503000c8046a48064101032295480da01854151082840c003091410110740040301ea116101c3d1085030030207021615550301641c0768214801103501031f030300c500d00d481c0d58940e0502800500060541c076400c0b031000702c801031010741d0404081d542d82950440b640030744644800b0f810000a807001c544d072480450040080c40483c0c001c1c0446484240081c40c21172800800043d201d00008000401200c00041c00c10441c40254 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 704420296 1250 704419046 704419049
    0x180c0603011a041203020a11010309051e0c0303030901020a11060c0304110d120903020a1d04060c020a02130c0f03020c0d080a020c010c0809060f071202160f0302030d0b0312040e10 79
    0x15000e0303000c0c0c3c01340c01c02a4030f035110a401555a00082e07044000321354000d014901446500c40000c1c0302c50317181c0740c00c0a00c4400b06003248070040c0c00f0f034201040e150f60301000511300810f4003000050f550924850050030040c5040c2d08507485030401c00402106032a01c030152948941c020480810780c201c0240010407800d8810401130540d402010484002540701c460402a248207865140901c1c0d110340280b5009486244054080300550b40002c000920036008504501000d004440408110360700180e119401c01c0401d00e0060b6440d403454041a520007600c45032590720382801c42c076040c20001d900c0e0310350f4121024007050094080100300e200c940f5130304403180c0c5158800200101b1210440080c04c2c0c0405442401280c0326040c0810000c541e4182d501e40600c10302d03140c181d40b181680003c1d07c065000400b581c2e03c41c25403880d414001c281c4142d515015148603a0141d030391490341c8400c4004075201c1d03013404d034041c1d0b00111009000c00b060303404450039100351040e04045655a48898040c03241c05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 704421546 1250 704420296 704420309
    0x20c0a0b0f0a06060306050607140f12030f010506040b07020d11120705030f03131a040801090312050a1a01050f07140c1002010c02070b0714060f180c0603011a04 71
    0x4400400940403007090354980a41d440740c600b032104a80d1080d0032130594805000f800d0b84100704101300d01c0010340d1005a10080000350044d038944044040d0500e0900100340c079500340030300b800000c100e0382d140740b01040c030301508040714a00e0406040c01c80e038107014052003000a000b4410007141c0d006000e003400c4482d4003a0001002441d103820b1010315640c480019203e914000d200b16180c07446031700c40101c117446414800b05041013a003481c00440710b0211129420350550782408000c0440c052000b030140790001070094480c2600441020750b400b0440d030008045040301403918040344208107850b6000422184240f80c200d8448420007072080e45803241301130040c04007103241c035010000000842c4054019004440c0a40c5100d000d0400ba42600d0400510a0040e08400f1040c01480704003c007610060b0300403000c2154041c50700c03140d540b07060300540f00104010740604c00c03c4420601c01c0c22120001d54540c010b01042c02100300402d02500060095096842111000081d0030000501341c4e00203000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 704422796 1250 704421546 704421563
    0x20702120a1221150501020c04050118051902070506011a0a08010b090319050106140a1505030a1410050307120305041403030c030f0304150506060d0c110111031905070c0303020c0a 79
    0x5600c0c030450104c04c07144100d81c05401f0b105c40c0c040403880e0610602e03040b54010101e000004501e10400070040078002d00c40181035206144003880c0d90954806420342601c00c40041007603505054289003010441c0180e200601001c200320041035a01440c1541100c5603000826100c5072028002030a100e5480050780850b4144030340f01c400d010b0305401900c11640540c1d01d28031168418000d0001840c4640540068280850002c1c0109403003040116070240070200e002901c107aa40c41150301700c0d1019586021411100e240601062a0511108000308440400c0025440745641c01404600552082461602911160351039035103003031084401407425681a42c0e503030105010702d044950070548080d80d2014190740742c040c2100703062181c00d008080c001d04041c1007008003d94000604124a59a02000074185040444034002d00880307001c030810201154407440c2100002d4640303140b842d90102c0d05e505010034842000d8102418244140c1c051402680e151481d0599516117103080800034450304 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 704424046 1250 704422796 704422811
    0x1b1202131b030f050702060105010f0e06120415061403210705060903180f0603130c080d0903110d1218150507020111010c0203042306030901020702120a1221 69
    0x1d51540c041c50490f503110108012035165205c00300c0ea5180c00b4090325000c160185900940a400f9555070350301c2240040285150015180b030034a00031000b5070781180c045002c000040e04a280741e0040c4400742070050300c1820480c4806001959811140c0041400300f0107075400300004160b55401c640c6120b80000c115240703401c040442039504d41c80421140340b045500148450383e8a0040c190400d00600203040508607101c014007142140c420507002c5482c000420750000b0b614000703000e49021020240c0350481603074030318240035000803d60f032401d5200d00080300142000901c200c03200c5600081c1c51034200722030b1400c04614400c4003100c0e0000342034034400c1500c0c00740c40c0e40d0000080288034400c1e42c1711030003440110302c01400e03a42034000c4400580c1080c4010701850034000014a0300340d4010380005182000c44005c0f54203544140c4d030500c1e441e50001600010760400442c000d22011010340140540718603a00d4040c2d1482e4800405000c01c04c4119000316442900c104403c0742c6501810704202c080d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 704425296 1250 704424046 704424101
    0x50d110f0c060f1501142b02030108011410030f0311010e0d120c02060105060f04050901030f030e1f03020a05040302040c0807081e0412031e091b120213 67
    0x129012200340710986140c00c00220568450b0313841e50006001038692102d03061209070002c60310f80001000f8240c6510400090035104501e050040041544e000010b0780c070750614101034291007808540c030b0000410031040c001c10300c8404400d901203d801042e10348003075001c0d140485d101c001500c0540355940c00c4c01ca54a52445000c6441d64418115450b24241c1895824016042e90f0044030140c0c00360300800d0041019003000c00c020017812040c4c2034902d10703047d04d0b0350010f8500e00f030a07023050b102c81141c208072078200f54004410384540242210b01c40002c60803941018007081c494000d5104050700400c554aa01d4029015074001d160b00a00902000030200d600074004038003107511000041e0581e01140d041200710603200700149000e010070300641e0765a121821a08141c00c0c2035401c05a603039101c0c254403504a02e0f0503121140c0344001260742d40c1d450402d0a07a4682101040c0784000c40d103a002c11441c4811520b154500707505682d0402102c00040e0003400404d40030301c0508880000802c940100c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 704426546 1250 704425296 704425303
    0x5040218040c060e420d0203060301150e012112020604020f01050a0c0201200607020a2915030705040e1e0a030e0112110703031d0a0201050d110f0c 65
    0xf514001e0341e608520800c41c00801000b4519108134408820110401795014000c50001903054400300941d80492040c00508070029400b031625105410fa002c02408501c0c50280034840d1499100710400c103429013070484102c0f140d08180b14400403400e00342080314208079a801e1500c0c02d50b80089400c410314a81c840041e40340d1004403001c038803c03d15115a00c019602560969610001c07940d03c00340300c0c0d04103500546408034100451030100307003c03841c1c601d4610010070202c2c0c41107101d070703000d0103d24000d0b190010b0004182d0002c0e02e00025500400901c50300054406540304040341710b422040e210308070109041044581040d07402c18202070f083e42045030001010f1010301c0d40d000c886840010007803903580d1034454140c0000c000030081ca5190f80e040d84103201444240030603040004020182c0843d5003400d910466003140825111840c0c0c500c1c000809040b0740262138080040c203075801d1590300003000e80c442c0d14100304105648132400c0f4a40c144460588002450003414640d881820303003986640c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 704427796 1250 704426546 704426549
    0x402010e01030905060613020c0304121401050903090d060f05072a021509130e07050a08150403050a03020c030310050301050924060d080a0801030302100c1205040218040c 75
    0x41654160400c5295200b40f20710251941c03c00050b04280e150f0f5004c1142124954588a50b604d1302400144104441400180f00610240c4410041034050740703400002c07203000071741a03c22645060100001c492000c0200c031420101220184c18140c0c083c903215004009d60940c1c46890b61074403081040e480c0c0c00012124010210700018202291150138001400940b518001c0d046102d0710f09940400040c0b1019000f0280c009200c0c0301c099140c0e108207411121140e8600a155015400c100620b0508000c40d60250841c4400781c00314449044000d80320f131002520040400400003480d20440d442507042c2c8442c0c0c404c140580c1c1d640c0c10300c1d0700c8040e42034000b80140391081d46002d000c25444070b000a203158071451141c1203004111901b80c1c6844c40c00d0402809103400240c40c6030307050002481c210040085401c15191040c2e154190f0500910b00801e0414410b082d41c50a12040310742d541000008050519110010405030350303e201150188083d201d800402c1080702c2c09000821603890305480 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 704429046 1250 704427796 704427799
    0x40302070f05041104030206070809090c03040215042103121508011a101101061a0c060105010e0a091d010905070311040606090905040c030b19110415081305150402 72
    0x807950b0311601080300700c8482c18003090545904110030801402c140014124060040300310605045c0c400c8040303111060211280600550008100000c510340b451000c0750b03400b07803616201d06080c01c0c0091440e00785210f440d541104070004001c0c1c0c04240c442d80c000e8071084901c0c002030004515484594041d01640d02441000e5401c184a0083c2040c030181c0107220448018000403d41011120564445400a20444455480b46404203c1d003100041d600310700000340c41201c0e42d82004503980d5003061010381080e81009210034140a40e0354a40c0400419142c8080001810091403c0c3c0070385030030303800c0a80c801107500b013175154014014003140703a404880c0911014044401c0f007c0801c0100c4100d8010540400c1d10040180a9200154040b9030700a200302a2051120b44036280c0c0708070036004840a4101c100d00c80d030030000c604100d00546500c10807001d11142080d080104550f00c0c0055800784a0400445000090310a00488480380010b07802c401030f50600c1c40283c0c0781a100301c03001c40d0180d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 704430296 1250 704429046 704429069
    0xe06040f06150e120c0d03020c03161e2312250803040f0306020708161121060408071e03031b020303160e0a051518100c020f150304030207 61
    0x2803c1c54281810300b0805244d4000c00761020f03905034410440007202c004001c0d0214070404000c4642600c08001c158100f17900100e04580030307840d103100c1c4000240c1003407800030505013500c0c0c204001e2140b240d08000145012000080054662001c250801068584664a4401c3c400d0442001040c0c03c140c0554841014000368815180c074500d554a1050307201c1c4040e4034201010800100f02c440e80602004c92040d40c00c03502e802012034040102c0b464032030080d00e0015002120410a00c0d100d80c207030310720207810350120043d6000c0000d01074850760300600103001400b00140d5241004585a404403081c40c02c180c015400c0301d030600f0014000d0000c40e8041110304008600b4035101c034000802c5d44e109070031800d9941210040001304031040c0c0c0c01a0b50300b9801081c0800c000c0345980d9901009820102104041e0b9240c1e40c2582054400780304d00b40d09039025018000c403100c07100c0e46c4031010141403031b015102000c145200c0c1001c40d001e1949042c050a12640100c14001090742c042140d50850310404000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 704431546 1250 704430296 704430317
    0x1903111e030402041d2508010203090705040f0b060720060307030504112e020712030c060501050105091e0a03120f080711100e010207120906020607180e06040f0615 72
    0x50914045408400c00380c1b0742c08250801c5403100d5900009032002e1011100c3c08600e13594149003420383e0000d036400d403000c0c2c000883c184094100b61051400c075a81c1c41405010300b16800b030114840d4403915001400e43e0000c600008800341043d6441c03081c440016040319501d20f8217450080003050300707680868016034800c80d000b000707227440b00c4a40d80d810130801c5022131218600e000c0f5080181041900350560050381d00000755020301c1a0174000c114041d4881c0f0f10801094900b44044620581040f41400000e101c55a030703075100c0c20b044540c1c415806100240d41401c0c20001007603c089640300814602c034101c4401540c07540b04500e01c3c14444240c0b5100f90688410400781c61000246600343c0b4580e0020030741c0700c0408074a41100d8018030300c103030005203004c10940750010002c581001810105030160780405c10103034104000c540c41822881d00c0a08500b0b450500d810048491040d142050b015001040c0143c1eaa6440000e03802115203040242c01c1c0d85210340c5041040c66541c2c0300116440341d56 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 704432796 1250 704431546 704431571
    0x50d0e0a0b0a0e0114010b09011e09050d0501060801051305010b0109031e06060302030d0503071707090b0c01140405010b040608011416050d11041403031903111e03040204 75
    0x46030203149901080408403a036032590080d00a001980c803245080d9200c0740d030050003030225482140070b00382c038200c8290b4440000002420440c0108091700846400312000800c4651002c07815081d61011922085070250b0f03400c0c2a400342c0403d03003160885502c0c00080c415805014081d03001014400c0d4002d00034400098010340304500030b444042c0906080a40d00c0d01010908009549250b11805001900f6601da8020074900580501960b0100d0400400d002c685074101481c107015000b5100403842924215000600c2958140314071000b1000c0402c1540d201d640030b400110420001d4030208030203140504005000e0250481103a00440c540040890b0128060207082c5100e10b442800341c1d00c90b2286400848602031806000c020800e00f44a60305900c4840e00482c140f00c4003000391103442d42c0c10000b825109900d6013035198030030f130b01c01c108902c81c000311405030300a5207086080000d086c400003284495544188000d40d00c400403581e80d00541801ca01c800303076014074021344040104011222 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 704434046 1250 704432796 704432803
    0xa09030503030a09060c03020309071e0f0308030906090d0c02310605090705070f022115010602070f030f0b101226030c0f074202030c090402090d0c06050d0e 69
    0x81d0b4856990700302f94001c1c04514812014904082c800c0d42c407154202d0f944486c440d8032040d081c1c2040340e0001e000401e10814400803c03199800c0340340b140c050000d419101d580640301d01e0090900a00a4440205502c03541c0d200d8034280038071540f40842542c01c0f4618980c1070008020038010300d84074240c0c000100f00c0485c031030307025155010b40c04034121841c0605602003203510748a41d04402283c8180700111041d240050000007601d040689560220754140b48000e41420000d4200610741100b4140810102d04041c569001140d084206800d850322130102e01089080c941d002609000c0c9280c051104124100080c0b00985a50980103002c5420441580e0214841a100703191014014060500c446002c0c03001403002c03612810070117a040d841c40042004c00d000040c10002580e4002622480015040000252100c0088021855844c04400040450144143d50350080b0303404280b559036612342c9200c400c54141c10264001c0e03001c0e940c401c024810381c03241140030b03096820070903420903040000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 704435296 1250 704434046 704434051
    0x20f0606010509040218101206060c0b06010e0a03050f0a11100509120c0a0f0e0601030903020303180c090a02190c020d03050702010e040905030d0b0609150a09030503030a09060c030203 81
    0x142e4035140b80c00306140412002c4d4000c034044445042103007500381c50a64425100508007403c0b600e49548200240352800c00720394940e803180c01440401e0000700c00107031032652044c0d400242400d04004102d080004601c0d044000e8000800c01c1c451403076440d07140440050a192080c0c03080a040b04078202503814860100480700c00c80700400d8050007200039500e030070b118424507143c5540444603c0124200015410b03c0150302400500381d420000740400c1d100700c03107619889102800e0522151100e0341e002982c0788802402210700840d251401c1c1d2203a10103102c070702c80e2940700808051103400d000d800f60000b540400c800c01d080f812150300d05022180a040d030702c40c15a4005007001c00601141d1401c1d541903101044c220304015605c03982c0080741c0d94a00c00c000045004000840e107468030246800b0440e80103c0c3c025108410621101410342d807901600e226186c000d540d0300b915250091400d40790310321a604018494000030007044000b42d041c3d4040404e02c0d01030401808010200700c03096003244804d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 704436546 1250 704435296 704435299
    0xe030306031b03030a2d0302070605060319060c1205040602120112030212090a050301020a09031704210f0c0305061e0108060619050d05010b19180b01091703030403020f0606 76
    0x3401400c40c402d0046d5402d00700b10030b803180c4c203c02440f0115104540748209440c00030100780e0100d80398040c0700030340c8a003136400282600104403d02c280e0314900000b29900000401150300c404503003400300c1c031500042c401024025800d0007035080c140fa00c4c40c041d4018103030040b614600c0c10000102640e0701c0e006242001c9c0c060300a40b458905a0b81400c500d40c1c4481440e41d0403c180d014000b9481d00c0c03d02c011b00d07041d0344503500e242d4101c1c00c529008510400f9003d80320046002408140045c421a81c0d000d141d511203104907041c03d0340189422004456201d0020700031803007a0000105004c801f203689841381c6519020207107020070840080d101d50900b07000c0d4403403c0c0d0181c40013903014103000c1c4807400307070f411403031036940601d1b68450000d8804002c0e5a411142da0351200b4904100d403c11416448040d800681e0000103107042004290b07100114003889003080c0d0315a00364405e16401540031a01802021079543c203010029103900f0765950003542e08800512881a1480e02c0c4040030492901a0b40c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 704437796 1250 704436546 704436553
    0x12030c14190f06092103060b09012001110715060501031104091e0f021e0711060d0b130c0e04151a0f0a030c02070e090303010504090809040e030306031b03 68
    0x1454640c00d4202840b948215406a900c403520f8004c52100c1e103500b000c0d003011030001c901342c070b000c018000d0a8806d50350103c9a482818803100b002130780c000400580c4008100ea940d0540c00d10884001e02501105440b1080c400000900c0401e00c070b4185400c00c0751403418402845110754603801101225180c1c008100551070521007401200c0403500140ca007200170b50214901c91255112070300460b0038074401c3c4414113600007180f410303503100546000c5500030001d80290030000d1a0b19544030600c4401c00152058800042c1300c1500b022607400728504003006041d170030903041d0322483d180044c5160610040820706109015241e0700e03250003820040c03030000341d91505007890b2200010a8080c0c41004400c8164244100f40000e200d1402804652101e0365020480707800c8918040d06095050b0004418184901c04105418100200710390444405442c0090301c0c040361304000701709005128000364000e0801c1c51039880e0213000005075020709030440c180c3c5c808803820000900c50145c1592314942680 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 704439046 1250 704437796 704437843
    0x10f140904020111010c0809010c08010510080912040e0114120a030302030901020705030c011a0105030705091003020702030f0615060406091205010b0919050109020423030712030c14 80
    0x101003120a410502c18140b5991040c00c2242c443d09545040000c031000900030410012006400d00644481901c181414070840d41490041800c00761036000000500105c040484c60a4108010340c11043c46808295a100d0b9101c658040d0110700078800c030503003968180a0615607203031414050341c500c1040d100402d00b00040790707004d4019410042820740c081d542030250a000c2482800101151032240d8000a012040da45a02c0e400b01c04040205040110030b10030080c181d41c100c400c80c0c011807411110700c11a540782c0003046010f8840c041c030080d054001e1054001702040001000d90141c40300700c2400c1070800409050004602039840340c4000108107280401001c600d149142400d01d028400108001d0f00040120b59041c100341c1d950006564508240e14159103184165030140600103019850319180c03002100c001001003180101c01c048400c0041d07403598040150b00003c00c0040090034411455007809000c001c910201502c4007034034400e07030b440c014101090320100c99015040712503140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 704440296 1250 704439046 704439049
    0xa030c03050c0a11030d11030420090a0506060d2904022d0c01020310061106060f09131403070510140117120f2101081c0e0a0603090308010f14 63
    0x1580d44040a030711401704012840e40d6240e02d00591000e15070b6440c0701c5070f0340e041030300d001d040700981c0e841000b0540c5c0707508094102c1580c41e008201e801041030b11020440e074031041e00050642c8141040f070f49440c0c2c60040d068140071240220003038280b83c1388004551000a0005110a901c104031001c06030f15000c800c0c00b071a0b120048014161911010078041c1006d11030300035075007280c3c0b0a881c409204c9070401d108008080d0300c81c0181e1210359003030b0047e240a003024808114001004444d103481445c4610020b403101c07442c6018001c00b00d400007040307162181d03a1a680d94070390380300310003d40d41c40c05207d80c012800119401107117007150b140d066424185e840d040700d546140721280400f41c1e560159030145046003494001804403002c948240c1c5030b07580940600c0c107a00b01c2c1070201001811043c03400420200d00041080380319407000446100307440f40400700858001d03190040565220189901c00304241d0390660040c62418442c0e2104c0c001a607d0701d500d0302d000d8604d07202d072911000d61489019110b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 704441546 1250 704440296 704440307
    0x60a06030f060302030d051215100c110306040b18010e060106140c030a051201121106090406050d0f02041d071208070f11040f02070215030907050a0303050a030c03050c0a 75
    0x4101c405000028016280e60019080140390045840041c8000c996201e07121100d10001c0d0f0440c2880c1c032111f609401d0b0f5400f28034488028800d4000b840585040302007406040c0a502d410380300d005050f01e41d507290600c0d00c0f964000c401d551608002466000814002005200e248407420030702e802800e450380b81c904211180018050b400e54095000d0003a000c0c1d0b2003007000034114521060b25180d494183c3e944a45910003030503407100700d101101c58000c1010460304e0742c401c004e10000f1b644580d900c084410104015281e80c0d404a41c101034401180b106100180c200242450310071503050000395000300a2011171003240034421798681101e54200000d25403d001a1001c030306c5800c00301d05200403a00c1c0c06021492080080c0c982181c46d0403a407c55181511410b50b5611481804500b803104a4010a120660740d4044605415001010945214040158070002c14004103282c035020380320300e00240150022100030780070074142040c030341559020340a018840d9440482031410200d0711203080300d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 704442796 1250 704441546 704441561
    0xa06150c21021f0b030d0c0206031501050906120406150617190204170106051e0d050c06160b161202070c0e010f08060109111209010e010212060f09060a0603 69
    0x7544036203a058000c4a002c2e40fa507080003c8003c80c0000c1003940b080c00c0c9030a01c000e8010900070000b07818000b10040e69a10161b03034002c501c61226a040b2410040185c0d4103124a61086911100228448000f07003100d5440074401c0384138480038002002e1804420003c2406c0e40541c6c400b0a6030400c1100307864007000071050344028202145402070001503c26000c03031b03200b90003018421383c0c11410181c0c214024019040140000d64000040e83c0d2a45a40a4071000d22901280300d040000f40d24018488100811101c000e40108540d545940c2c081003510300c0907205c02c040700d0144009001424159020821b201001d005403520501e0011084a050080d4051f0307808850054030910003241c4220900d0210b03000e082e02c0500041641e04042046142c100142d0080da062411b0031314989450b003490007540c00440c14500004e41c0341e200c10340864050101d0400c060383e00c0d84003080c0f110001d13000c00071440c02440c0c141d03513010101b0000010f0012007142111034507004500240c0030044103200342e12442 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 704444046 1250 704442796 704442863
    0x20a02070504090b180102071b0e090a0503031311031603031805100c08070f05071a04050609152106100e0d02100215010e010f0e09120304020103060506030a06150c 72
    0x146001c81c1c5030b2740c411f40c944c2e1b0b01000380141102031005201f04041802082c0d08142910018000a08603540c3ca940c4e901c0018200b81c5d00324060307540b41303080090916141400341c60007820740e0542901011310000382200b40c40f050340022100c4141c600d02c0014611480207a42e005001c1c520740e42061b08056a007002101422075441c601040114003142206c0140b060b481d00c0b800181a0381d45c500340c1e08241501000c6044104641c007000200200e569403000c072803940c1e5080c3c9590b684507818542d080c205002c0ea000c2c0d61000340b14001c4130542140d4114000f4800c1030304680c00000c0b1381455804945001d0302c9021160891415070a400140c0740181c1c4440e012461481215000341c2c640b02c6110303807040280d0003400c45040841c010301058110050340c201600b1050645440c038505445015900e201c601c500c06031000c00040424190391103600201e01420015116960742d040c1240018020003540c842c4a9002036654144280d5605c0b41040c030203203a8001c00f8040714a1164403010b1a107121443c041e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 704445296 1250 704444046 704444051
    0x250207062f070611070806060d030203040f080706120506030d030f0b06041412120301030f1a131124030903040905070507030f0504060903060c2001020a02070504090b1801 75
    0x500c0c1d031015114510001e8440c40160560901c0c090014001d1400800d119000d50480f540920544100041065011408a0715071011030b91600701a0700f14482c0d504402000b503403600000c640002c0000b0084100d8002da0384103109444021040b408840b015558076131300d600500514104144a60042c0c03d000552840001d007415600001400781d40c001d6000018400440c1c01d034104915000b5101181c201d4404060680640f65640000c1c991205000080105c0100d107402c0c01403001c40c030103a101001c030581c0711400508107941a509a0042c4410440e1001c4141040b104035090589041001071160409010b01031000c041034900c54000420490051200b03200001c1c0c0e441e20ba01805000f00c2c81c545a5955401c400c0c00c000b001003801d40b103a0301c103004003000200b1407150b114040c00c0880e40c004a0000c0c15810b65181199111400003a298140c103008298111880040d4028485c0c0b6280350201c0c2c141559640900090755002c90000d0400845900056002c03200101d2540c160080030000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 704446546 1250 704445296 704445347
    0x51507120f1121010f03020d0b09100617010e0d021b01210b030d030c02060601080a18080408010c03060b0d0e0a0804090204170a020d23010f0525020706 67
    0x144210740281c54580600c00c0481d0300c0251a206003c01039024203004c40156618a08503001b28040001c00d003401488020080700281d50b8072400d11289084d070780005400d1000c1c1d907444540070401c1250354880c03031540d4a03121803d00a02c41c00501c0b1070007003895401818800356075540c90203519501d81505810300417103202200208000e5582258003123110b100024950340d199040c145841c00001c800024189003407421400290009410750b0301a02c01d10b84682c869981c0c50081001e0107640d14030b501d08401d0703a0300600402000d82e010380180d58507580208210711400d00700300c0585009101e0001c0106c070410202c5801c500a4000c0004c010f4030500f1210304000c6566480170741e5105a00c400c030490750214084c40280c000c100e2a007101245400180800911600014941c100c0c1100090121600f5040c081075004070030310481415610030000c001180408482d14041c0908481c0d002e241d46140407458541c11464824811f01c103150350040a0071800d02000b65580b540c0c002c908801c2d40c400020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 704447796 1250 704446546 704446571
    0xc0306040b18070e01140919050c07050a03120b010309080906030c0415020a060c0e090a090203010609020a02010f050105011404140103020f0408011401053f0303090604051507120f 79
    0x1e514020001a46510583d62509202c50a9800086c40d92841213100c81d091006a00d10a42c11240b030001c410350009094031495903540041c800d15100600601466201205158001000820040c0c00150034084030b85808011000c0340d14040c0020450030742440001154245130340a5507204e5102c4800c039281c03548551090981c40301649110006034424603030f50041041d1401346485803080c90424405041c5288000b440f00d040040c0142043d543e942003440540d0f03800d410035002404144030455441c01c1020000f4007031b06d0b803401950300c20b40c04c10000041c1e43d44500d92111001c03c600300c1c41410305091070154500c05081d200c102d410940c080c04107602d0400e508004100401c0114000189284032042c00c8884c00016031001d489002190710022052000e40324100c111012141c02d50003186403941032009c49880ca6401012a200110400c803e8030000610580a540204210f0b2160310001c0d0b1400d80200003240c41c4c000180c0e103031134080c0c10403500781c014401c00c204d001c00100d060003403800c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 704449046 1250 704447796 704447803
    0x5090303130e0a2d0c090b0d021b060603030a050a14030a2a0f050906040e041103101a100c020405150a06030603081602060f0d140601020c0306040b18 66
    0x1000426070703004100501503540201d1086400c451010f071107402c8080040c4d100003280c0d018060800d007507a905d4401c0207445903c580c45100c0034100c802e40c515222030b00d40e65544020342000408104104407904600740310180050080d05c190001001985003026541e0204d419402c049008418026001b10640c2d481100c5c002075441252004400180220b204400981e5101e841c801d23988140c0081c0b0000e0f520303a0740140b0324200000c40b4100141d86001e41c101184040c41141c1c89040c0d86480300c82800f0070031104014507074014800f14211081445e4407036036074003294840c000380c2c400b40c02070b1200e038401030a005011091100e010704188000b80402c2d000300d019502c0c102c03500b56100300426606282c0d03203030200040b00902024134003040054255038414186119030700d071069200748840075404c11565070100729150603519018150316040155080340151440b80d1081300a101f055001030b0345548001580442504000d00801301b5403620340300d1680e00f82001c1c04012031400d0203c50a51011002c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 704450296 1250 704449046 704449049
    0x703022202280f0807180503010911150a081504110307120e0c010207090209040605060408010209030123070309060e0307110a0609060f1b020a0e0f0108010606050403030509030313 79
    0x4892110301c8040c0c090b1003010302c8908034482e042c025540801d0740015032149081364421001d0800340d1803840149200581500300b03a00a56043d8209000741c2d0401082d802c08461600050f40c17106c1c3d10751130105401400f03009208460700001c3d42d4500203000e0390f400a11101022201910000340c500d40c140665807540d000301c80d040c002c01c503609042c04054201d44592002208510050103c600340400000d46400c8584107280215402141008041d52160310640083c0300090080c0d66580c8d075001028040e4000000c0c040c400d510b130584651181003a080c107960005510000c15005e82d4865005800810402e5000d450181d900d94040c00040c03010802840080d02820048554071a080100030351211990420300800c01e03410b001300151034100d581d0090124035400e0480c4240e0200240c8032410700912006940582030000000d221801078007010f0164000b89019031060fa2100c4105080e07c881d403080200041c0304010400201c2d00c40c10250290301c100509603031034100f80380b0484105070701c103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 704451546 1250 704450296 704450317
    0x70314030f0f07050415050d0e031603020115030f02010c05160909060b04020a0f0807120518010b030d02340303021f0c020706051c050115020c010804050703022202 72
    0x4001d2000504020780c1d19540f294992902c030385881d08000e405041c141c64030b0740b48814401c0100c3c0d400c200090070b8110001c00840d0704200c07900d82a284a0460414911400c141e0141d407030302c03100c2c40c00840b0045c60f038030903640c00102003a0541074aa00440d001884500103a0303180c007a01e0503040c0a90000311002e8002c2980c0b08010075600c500d401c15000301c46419019038031561042020154158200d0021a264001c43c1450b0800d503030b4101080e11040c402002d0f03034205515010070408c84282401300140580c61480003041003510b91000e042d81c0e034040c865448007507800504124030b205040aa851280070400b01caa030700d4a032011515005c4152960812000b5801840620500050024000001400075401032100101e140d102a44640d42c2c1d0213050308014000400d1100c08c01440914614581030b10300400c43d56035140c55590500d28983c0b041070060240524904081d0710a0038081e01a1750449d000d880004d20310350030052000380711a08050000b03030315407540c040c0c0c030b0b62440504681e001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 704452796 1250 704451546 704451571
    0x131101200a0507180209150a0c1b0614070201021506030705030f03120705070c05061e2106121905010603080a0f0e10020a030f0203220e0a05010b0a030207031403 71
    0x821381100d00f0a8842d440801415206200348245d0743e41c0d0304012482e03c1201c00d102641c1d00d0310a072048480e0310404801402d0700c0341c00080e04100c0c01c415040d0008540495441d9007901c802d00b0851200780c416000041c1c01139010b00003410081c86a0b26490360400001822a02c01c1c584d1040480d00300190110600120f420100e4502286a034902e88940d01c14154a0902d11380f96260b0754040780d01403240074084c01424081079a1111071200c102d103002941404065945a20384070381d112511030050301300b60702c0201d4620041001030500051018940b64024080c10f0794810035400c0150b0035414030010f0740e0f02d640721500040070400700401040d02c040300e60342d1503541880c4100c001d003c40f00744c240d040d40600325084100c629241d0108a03080c4980d414501846640c11901c000c0346180200340319101d5201039041103101e441e9440c0300340c5048a1241c11500c119030f560724559011503500748150406214100406c00c05544251300034260280310f8203000d51609003840e00d00c0c01d00d0700300b19801e0b007c065 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 704454046 1250 704452796 704452799
    0x3270d110c01181503061d1b0a0c0611040f03030f0201180f03080a0905030301090b090f07090e2a0318010c0e130e1b0108131101200a0507 61
    0x95081c007403040240c20a00348807250060b0102c140c403030319400c1d201d01483c0302e000140c1d80044d41d1103034110314000c2590302c18541c0803644144224001e20011395010b580c481080040510185541c3c0584907000c800391140c00f6a05859110301000e03104410414000480402c4081021420761441c0e2001e10300a03038644071048400c1c00301a00711032000481081c0b601c048010172002170110b0550070f800d03e61500c0c5c1010152124101c2c24042d0010100080041c00040004076069080350f00c1444128401c46103280141c42e40b05140380b810b8810fa034000b001552081c0c0c14041c24004040080d040a0640040000c0260344450f0032124a104c503242401b521001040c40740c03140300e1204c040ca5200020008100b000c59000000d088040b405071110300030800360f0b000554207045980030310340c2c0203040001d40300400c8580f08400c0100c0c0722160f00601251700b041c0403e650040c041c5c400807502e940042804081c9000d000155070264040310f54030905a421700d800304900301c0900c0b081040e0f07845017009201d201d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 704455296 1250 704454046 704454077
    0x204081009051e030f0a030b0d05030a02010b09010f0506070305071401060302090f070f031a04060801240303050708070f02030a0b1b0a0c0602090a1511070f0b03270d 73
    0x540070104810103083c5890089851004401c80d03001541d134401d00c65070344007882404e03000f403c4080b04440e800300c0090302250a1241c007000034a4095010781c0200410001c610170010303502000c3c01034100e040300006090146090040041405500909100d42040c0b0180d459204042d049007011107a03075110743c4208214144103904075000018049500400d1601c8000101a815962400c404041c0c030b42c0380b080307842c0c4c00e410f0aa84144c0000340c010710000c0c0d19100e0440c040c220443d264841c03030105400400d52110280728482c192541a0364440c6828655123941070290021076090340c511440a110301d0059904018540c0000d00c0f8a0f114141413404400010029408100f40810b44038100140c3c4940780e4410340c2d03180010741c0b00b2001a1141c16281c0400c0d6101e4080d04070f900c03103101e00070304001505c2d000741020340318960071022503a0081d141c140100c0e0690542c4680f5515020600101d09406030700c1640b09081c544043c5030008865980d280c5c0d51038003503541c0030140410711081d10038189 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 704456546 1250 704455296 704455303
    0xd080a1407080403110106090b09010605070f060b011205011d060f010c1e05060907090b060702090103140c220b0a050105070311070b072d0b06040e01020408100905 72
    0x41044500208200d4810468004088600a0640d01040000400141050301440440c1c003912103910003000026100c910038001007002e0880c06100c0c0134440700025a0394890b0b011201200c0d800052201c2c0d051540d55484060000f6018440c18018040c80c88910107906105033030081c2404840b0030020071310500c1003990490060001805180b83c48900c0090b03076000110040d01650209440f903030401c144103c021290803003800200280640402e0260054000542c0700c16503004100c20810040b4020401c072075842a590000d4124051b900100f01040d0400c1103003100704d040c50283c691181d000400182070300c040503148030405110b00700030340f904141031181120012041d03d007180e4050500c030001e01107000d4082d0050030052018125284020240071b00e4000386210313091143c450001d46031081c102e80da8021408481d00717200c000c43c405401e00401a45085030045900c0004d5102d20701840040c0c42c0c1d0790501546590200000110050208400d400c0d803c003121001503d4900303442e10714203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 704457796 1250 704456546 704456551
    0x1b0e010314060f030f0a05010606111f050901200409060515030103060203040201050c0115090516090611070e0a02070c08030304200f100c06060807030515040614090d08 74
    0x42600c1e051011400c000c01e21102600804126803400c0c00c43c5400001034134012121103406080d0040a00310700c1001815045074090301c1a64403058844011101c00c1540c56a04485100c5010040d6a201c03000d419241d111a8001d203ca07400071821800f014504918070951221108030701c01c0010302080344031002d00c1000083c210032124903496043d0104600a030b40418000500440ea0001c049011680031704111074400301c82000030701001107000d0701c502003c1500d21076024400e090100080002907010f2806000c0262511103074045030400104a8204840b1882540c0300d01ca91000481c03454074031120340344150040034003d6500c0c0031524140d0f0452000354480009070f8028400e000c0041c1c215241c01c0001d01c248444200701480c407200094042150540036074000c028610100d10090f031100c00d01000500134102442250740d9034800e141e90b51050f1002800c160841c1d843d07a10401d0820303030011b0300b0034010500810b03503100c0902011148a000d4400b00213541c0006000c49545422511240d07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 704459046 1250 704457796 704457799
    0x9150302070305041e080d050304060f0603021f0323040611030105031002090312040303020124050d1b050616050c0306010b12190c02070e0f04080a211b0e 68
    0x50518903240d0b4007608602543c0030349000742030010400340c45c5a482802000003810351008488000c03803480000f0704039078015102500c00a041003003a0805c1d120b54000c6004980c3e01a140d14004078807000b2460340341044a024008158480f100c2900c58109542e54598455040707143c00020304180c9000c0c03040315214080700c0031458040c00108113940e07000c50341c1b006911280402680c1c400403400060300b000e0f400740001c4103918002c2804010f155055120140780307500290401c03d180c0d00303010f1001800d443c5104465019041407640800111a030061440000b03a12240c011105e0302d17500013800300d030008015101c155864005100a0000030801c2d0000c1c0c141c01e0340035241da03505021001c035842c880c40840408180054000c00c260780d008100c080b0801000d28820005c80c4000c8400030744a4803280f00d506200d106281c04039000b007040044a50140c0d40c02004149440d00001041c0c1c0c040c5059043c1400b61491004800d580181e01d000d0003800300421030b05000c121b0740504001c1c0c41003000c102d049 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 704460296 1250 704459046 704459051
    0x11100e071a0f030406020409050103030e09090c090c09040906060803070b160504060c02120d120e011b08041a04080301090c05180906030102040f08070306060510050d2703091503 78
    0x45000240c0c0c1045400341080811259030f207542c3c9091410203132090b6841424028075100001080c940d1010890240034021075015005480300c0d1480707a074426000c1906036004620380c01003039080c211200100070b42400a480420440303510b0310707a03a04072070290380103540d01d8000090800c2000220b0740500e0b800103074901c06a6800040c0c1e5070003040c078060340c040c000c103000032046007005543e103507803128885125100896410000c0610020b00c1030050425103405141001c010300d0f044079041c050031942d10781003894584006204501202ca40c9000340c0700741c4211044484941c000445282e07058807680c000c0009682d0f0b07525002d41c0d402120404003450702084402c3c0008140d40101034170071110010100c0e065000c40d00c1d0711000a0080c4140c0e030000c480e94016440000d06450702240c2001102d0003800100710243d0383d0428460032080920b05080021410811411508a9644039a400c2409501d8054042c4011500d208030b071943c5c441e050300490b102078001c012a14105003500c89400340c1c4c2c03806 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 704461546 1250 704460296 704460329
    0x1d0a050601080f0d09030b100902130302190605030c032809021804020603040f0309050607030c020312280e06070b10080d0207170c0303040e1b070b06060a11100e07 72
    0x2020f401040c04020b00450600000c508c51042e105400300c05040d444104568803101400b6079040d076041440101e0082c08085243e40064088281650841c0e031f0302c0d100e0301c1c44d41e5200704000000d40d000601e046065001910411442001d14041050004918030300180b64115401000407803c5003a141182880d583d00070840140c90b0482629000741e4071401c2c2100c1c1c03121916042d944108243c006681011000c06c12905050303110b8800a0181d00950654460300f000003c8001c5d0351007140c0b0b5003515902c03840f082c5008003034040d44400314005145850700d0111070200010304554040d80b000c4e12928035a2080c0401490b080b0300c00402030103480010a24000c1480d03000c0e4070303a00c0c9841012483e14842c00e414550a500b0302c10038484c0e600050940e031307546844419a0964100a403000200c0841501145804089030021180401e810026801407a034910b0100304040c1e0000b1a401d08200c1c01c1c520640103410100301c2c9603095002ea01c00803d42074ac440ca9400d2400380035500c000c10301d4054020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 704462796 1250 704461546 704461573
    0x130b0a2006071205100510020703020111150c1b0706030212090a031d0111060703020703021c0c02040218130209030111090d0605040c0b040303020303100b0a121d0a050601080f 77
    0x610070000b9642e001003402d5540c0b00020840ca800d1b503018640090f001d405000705039602140c0d0300e045ea0700c00d80b10f42c284220074400e442d075136031001c00c0711240030a11100480c01082265014118440c05c00901031116894200020304280c0709600800110343c020a90900481c031018032113501c440240020708040340e2503100140340b98181c0c0d1841440b000b0491740d0782c5199110b540e03888214210712048600c5802c2c0030200034029402400140c0040c01041101e0541c101194560204001c0c0c9507641910a0940c0c0c003000001c0d4008900c4041c882c44100442207a604c0b00c140b84050000180001a06d4010602c00e150a46904165017801007404102a820a40d80d02048a10640d00a107000078150b45600d00380740021000d40241304500c0c00424000100340e800001544980844015104c4140d60780316601c0180c01a070310785201140302c400c0d5854289101d50701c41c2002d01556580100031040349032140d0300307000c1c1c000c909442c60b8200400602a01c14100030b0820145003030b400800349041d4554 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 704464046 1250 704462796 704462807
    0xc030204051008070b19090605120a02220603060602010b061204170304050105010f05060309060723040f0f0611030d09030309150902030705030708070506130b0a200607 74
    0x4000d10440c0e0301c001003448031218542c540094103e210455101c6a00d500c2012440d802c60201d04907102da800503605c1010f07100b50707210000c4a01c5600d4080c2002850216804040401070801003400d17404c0c4070290500009503044000c1c409440110854141010002026600c241d0007210075a810212404802d45940084a1a9022215680714261a00e16100f20f002001e5440107204030000f10074403062103010b511050485042601590b1616a60300a10030349003c00c030782c0741e2800d4018000249180340500043d03614883c001660780501281c28109900036042034008820a04a482041c8014919801c0c12009001d280c14460600700d09400103581d00d1007011030000a03151244060401c05001307822040800750700c403a041c5000c1c0f20360982400180a0684140d100740301e07800c400122401c000c542d500513a003803000903100d0b00781814148085a44000000c0c003100008010004200701d0440240006031441d9a4002e034607808504291284094680100019001442400035194000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 704465296 1250 704464046 704464049
    0x807030e070810020705070306060b0429180a0b04090c02010e0a02030d120228021c02060601180302030708070e1f090c120906020c0f03030105180603120a0302130506070c 75
    0x1c0f001603910780303841c5001d5050135801ea00041c8501c2c100700c40855080c511501800a899a01c1c00003451a0b00e034469005000302c0403c07030801481000c1000d598526001e41250049103000f424039102c50340d40341c03d0840c036030f401640040c90311030303031500e414010590a006041411900324014094202c135030300001d84419880182e1810b024440c1100701c10212306070140e030040b1101b494050183d440080c2041500548403900c980140546040c0b000365000c41c40c1c001d4080f20281d802480340c2e035298401502c400188203042c0040341c106141c00001a5010000c072005080c002000d00107481c46e2019903148940d0142070307030b0751100c1600f03070442404c183e0311003040071224405808038420103100e505a40140e040d521215140b820305050000348081e6400500250f1801d03011070780da5001c0000c4090700e80c0000e000c2c0b2903000c1115080b40066065030840c0982207130004041d00c540c1d00c911303a51f1524584c010940c1d080400d40104550980060341c100c40f10041001781c070740b54038101c00c0d40d40386000420903 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 704466546 1250 704465296 704465323
    0xc091e040f1109010f17010906031a28090b04051c050307080708070c1e0302060a1802040b121501061b03022d0706020c0928021c06060807030e0708 65
    0x40380c9910451724404c611040300f4002c400d1003643d295031a401c4410103005d140c0800d644455a84940e00042100c90030040c1c070541c2c020f50202100214041c0f8080d054820303608494039261183c8400b80850350240d04a8000d40c03040c0d009007540804016a00c00c0340d54410115401c0c007a082c01001315880d000b0080a17880061b61400c0b103101c0e41ca0746016120658652809404e260f81800c400c0a4480d0f03407001000c0c042e00a80840d021603070742d400c0b02020b0f41c01c0c07070701d07070325001c601c3e0498200050909800c04806042c00403d070810001600140500d403540c2038141203c5200403500410103203422100801c1ca4000d040d151a14180103910040c1d0340300b01604001c4802205601080303015020201c610300383c84204402d9818003035890703800942d502c04140050f4840d5513090049000c000140380035000d1401260700d0301c00ba4046003410540250844030014140039002c0d580c0741700c81c4607607100d00d07805400d140d1141081810400d00c020101e411010804036031780c2c825130050248000000d02080540348 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 704467796 1250 704466546 704466557
    0xa0803070b0f071b080a0e0604061202160f0507321e041d070503010e0a0b0408070602030420040e190201020a06020a021f02090f04050c091e040f110901 67
    0xc44100444810f0341c10000f1152044d034034121074042003c64002000ba40c1129920800500a02410010302d840303584110705c04164200c0707500100e001c09030040c11294031702000d140500ca010b5110140420501c00f0200c0f0b00360410b21090160561074940c550070b14101041441c0405284407014041c44801541244206855130b00d032045d90503c69003149000901400900c02e4150000c4002e5020102030030001160046000200b00f0307040520a0000c1502e8010040440d0107480e19200d580140c0917005507100181040078078042003a500066003c2c0e440f800401d510382070a464400e03003030702c1c05841c82882207007459903120030305100240a462075003c4803a00c0c00307501c01070b20040c0d250030140c410050002d400442d0b400e403e0390700440c81240d40c40444c180407082003502c12983d0124851101c06683c4100010807030019800c166220503804202e000c0010310b003c480c00300041c02d291ba5000c00340c0b14110302040c0c0c0401d500b424040e048105c1070004007480458245c04480c001030042100140c104003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 704469046 1250 704467796 704467801
    0x4030311150114060903100e070602060f0a020a0519120f05100303050c010f05090c010e0a03080a121404050610050a060801050415050d080903160602190503091306050a0803070b0f 79
    0x296213a0031164201002011120b000150030f408002401d8015881d09141c02100e03000154a07001040051042621801c952039540c0d034007a50038000d40100110004000c028003040c0b406840c0d003c2c0d01351012003aa2207002c540340034039107910155940890f0803c045400c100c1401a181310b02c1603d81c00396580340c20410b448105001d581801045910b00e001075080c101010701c2107810000c240604000da0a136500c0e4012000b00060004d0070714188001071502c0d10400a9040440c45001c0c0360341c0b585140300020910b410020b1032803021590503201503602d6001042488400c207170110000005003016160300301c010b072078800d01400380c03101481113601544d16000700b81c0011010b010741c00c001e4940103000d031114203840d0400800c640c0040300000e00910403c0141552640e120640d20111507103a4000c2050040c0c81040c003032207a80c030507421200c5120030301c680f900030303581c21b62844483c0c502c100001a2040c64101006400702c02644480c81d1034208100810108880e40030032980501050400400758 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 704470296 1250 704469046 704469049
    0x506210402041113080d0810060c020f060f0c0606151608040b031006030c0216031b092d0204060f110304090c0509010806010806013f0204030311150114 67
    0x2003240f00b15503d07200c800000e0290350003d00c2c129038004d41d4510b80c1210044040b403103058802000079900107101088050042084a100300306c10310050348060040307001e650441010480079040005240e85540d00131507500d0020800b04a81d680c40b10701110300c8407141c50450980096442009040200c00ca50110714805114802c4100c40c000e00c09890307929561325104000030600b1038980a4170380042d0802802c802c025200050b091605501c1c0301006400600c3e580d9407058400b0321001c1a01d65a40710071001500644038440d0f030751400c0007800000641801401c2004008802ea82080c00c3c80b84140802d000c0300342d00c1040105003040506058080a00c00f004462650040c1d900182c0c14500f4142c25800d02a8848054076580e1004e0322a101070b61500710040d10300400071210715002440360020740c02c1d100038100c0d002000240984846981d041402070f0940e040302d680c40c01c1e1108a40018080003011340c0902c011010024a0f000b5083c0d540c5910003881e4203080c184115840d0300c002c0048107005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 704471546 1250 704470296 704470301
    0xb0711030412060b0108010b030c0f0702010309024513080403060501030303020a09051206070f03021201170d05030108030901051803030d1a120c190806010807030507050621040204 79
    0x2030b1924100d205040392061900f28068440c2d06038160004003008000034401944406490103041d0280141c5e045c040b814000318060340020000b03a0400d5161b40d218409605d565410315a02103c01030b02001070100b000a000c0d0720140e14080403581e5410080c0303c44107070748003d006a00840d900e880340640d5511818a6502405a9040541110710303220000007090f0f010f0307009003041d0003140c49030048250350714204040d02c2454004100075070803610005441a00c01c0b041004407540324200107080004202a0141060098100308004038403421400108141000b201606a02031b2070300342e20315070410384069100c1c0038100050303050002c0800d040b800400c0c244025075420102500b2281c80f581c84004280240007585c45012203800c680c40041e40f5810020796515004034408000c08200c0c0001c3c00307002441e819000d0308070b8414100c50700865a23341c02d10444c0c0c02854540010444207065007415410006c00c0d500592107490300f0044602030f0a04501c14030840c55400c000a4410365990011801 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 704472796 1250 704471546 704471549
    0x6060c030408010203060a0b18100908030f030f09030c1b0117130201110309010c030c08070206190f09060c081c0608251d0915040c0e10030b07110304 66
    0x30301000c50042542d902c154060752203204120f4403c1d00a556a00c2d18018500c038001c000e00c01d00c40303822042c42032400c11003500072200f90149010640d1541d62a4202d040d80c11400c42c18480c1440002400151511100c03019000351a12020b5440c00d4090003020355588840e0312000a5410b145144a480341e015a503a0400c0f0a04040c2c410028504102c11681c1481000d208a0101e0f555030001c448508001058445265040c1c56070f1603c0d40301d94030f094440c030080300c900b160102010001600181c603400007038a822005400740116070f403d00c600182081084404170b000b0046444c804211182d400f42d074011666401c2880c0f189d90f24042e500084075070700d60301071007d5403500f0800000341b0101d0002d8411400111584000c0030f00680001410412a4520903c03256040a200c4201c1e44250f00881d1038002c3c0e8010116040c489505007900c40340b060880d4152617810a1090400c4555402c6401541c0440201c0c2103282990440c2d980d07074400c0c00040c1110b010400303100050021400308000b00c40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 704474046 1250 704472796 704472817
    0x12030304150906320c03070c1511040302012007090b0301090507180f051303050a0203120a0506040501050405041208130c18060b0c0c04020d0204120605060f0d0209010e0606 76
    0x3d0700783d80444905131880440c070110b40307642000301603002e2045092a03240107250f26401d031461500c41c40e00032610308240ca802610149411207403400c20040398442d10903a0400c45105070303225403540c00003414079140c100c03040b090081c0042c40707024202c0c1c0208800060f14595100011050520000309004156120700105a40308100000c10304400401130321450440803030051100c080324203201801e5840940e4032448501800c03600e500000e02400140c0706a640c41c2c81207908080400c48140902c0106484417540755640d00107010050a00d80902c9015200548090141e42002e075165101441e40c000207004004000700400c00d041c000740d04019007540c00c0040b1580c80e40d150080e8000201e58604188029442c01500240f4400f03e2006c0c2c40a0a400002400720942294103100196006110884210f6401c100218135810703200c284501d014061038000542d440c240d410700500c110729075016445058081c41c2c2400507500e1040f400d040d128a007001c1c038840d455540c04035405024440918 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 704475296 1250 704474046 704474051
    0x20103021b030a09050f0a08060402060d020723100204140904061d0114090610090203070e09190b04060b0904090510110a0f0e060703031802040f02071112030304150906 74
    0x2072581c40c4d100e2000c0080c0e0300c0481c2c0c2c0b411500c03444810003030444000c0c4582c1c0401e41044000401500d004d0002d070100c0d0464000c091b10301010b5503103806444d0078074144075450300102e20394240f00c007000304248104c14050307083c1145490305103200904e00249840782c0900c0380c9070100c0006d041101d240c00900d401d03d80c0704d2002640e100008141e601829454034500000c00b142c400141001000040d42d07030040d0222140c0d55041428584280003940c070061100c030900c202c00d00c030300760551030f0320000502c44d085040d1208e51100041081c2c5065844080c200c501c40c0d0f08044e02481101c8003c03044805c43c0404483c001120059494030604000c080304503445080e24200f082e0780141c1034400140456546542c03044158035110700c068504400c051030080d04070405011810000740242d00070f034000440c3d8021107824040b07903030004c0c094038100900d020790550042415010444407640180c02000100d5400101020792018503559003c000d20250800c0e200380c000d1003110340b0550040c0c05468100c88203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 704476546 1250 704475296 704475307
    0x1b2303010b12060a1a071b031e030512010b0c1b01080106110a0f03030204150906080a0506180109020a02120403051009290f0903090901150203160c0e071b020103021b03 74
    0x514480c0c101003003e0368440440c0f41031800e420643c0c02001d048c2ca0f8404101800c0308079080094a980c4403100b4120b00703201003017100041c080075401c9018024100444078542d240ba110140c1d86c142a80c1042c00e40340c44c40f040c1c042e00740300e03a0010091415504146031511481c9610500d95252170010400074242e110390400c1042416031580040c000c0c1c0f0f2034400400822204882d0851350500944140b0b80003400c1d174800320320703c040c990b00b120b904040c0c02090302d0104408a41840f030610000e074440400c036a40001e001d00035075014008075030310150341500d00e820f1601d951502508c840100070242e040b207a03104030703460405c2490700d60494503032680da07003810741c50700088425000030800761400c84102d0413000c006080312800104407818940c002c0d2100c040c07641381117014803a0345510368249040d80000d00031900e16002a5166032482d60051003644052440e08426030342d0148064180e10400484148220300c1c00c480c0c5900c06841982843c2c0165070791a0440c40c0010300b480d9034250304160100088 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 704477796 1250 704476546 704476589
    0x201080a110f2508040b0d06050619020f0706080105120f0a060f11160609170705010209040b06040608070e01020309120a02210a0b06041b2303010b12060a 68
    0x7502c0410200002c40300700030210401c80d040481460030040500301304000074000020240003406c204007454001050745601c50780010020741122181c0b140c24007000c0f074420611581004104601c4034078802504010303003004001402c100d0140100c40c000d080300200001e80d07800401401803114043c0f0700303561400c000345c036106010305000d40b41c075000c8600f001449642c056084003250b020300f1031200f142c0400241a81c40c20043c04501c08240d60105210756681c101e4803401006205a900c03d00005a541c0c0c2241d08010481e03502019072402241c09000078040c3c117402c20b4510350860060300703103c0b504000c4000101c0c40d5108110300550001400e401d100100c0800042e81250300744222040b2524017100018924071010211101600340e02000a00020604c0240d2054000c0b0700540040344805114442594640d2211003010026082480d00d88101d24014130100c600380a1a403428a15490304020804500889140d014104030384804250b0350750b02c825111b002400381c004400b052201400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 704479046 1250 704477796 704477827
    0x50f0d090b04260403110109050a06170f040f020603150a03060e06070e0a1502100608060405061b071221050a0b01030b1305040309080102070b061305070c0201080a11 73
    0x2e41c11a800080aa4024410381515040d0001c41c0c41440d0300c03500380361030341d2100c0c454010356099450500594100114140c4c1702c003807107000540520b40301d0a056082c04000401d60301801044000e00d21041c90500000421000344071031201e4044807015160b481c3e00b011748114400400240354400c40da5100002000302c81d8020010589400040e00d4003569816826141c1c240c02981982d0720580c0c4440902071828200e40782c48502440f481103035410300354210408105c1c0c0a51b0084181684100d00700300400804001e084d80c80282901c20750400040ca0002294a0203504001403021807503c0600d51160300c01c007082502403402c011100140365042c0908402448107403040e49885061410000055010740103070810400042c02d200c1118042141007001000c01803c01c8041048520002800300801d0015015540c0214260380041c24520f0800c034001503840ea410350940e0925003000300d4942c221000e480d40e80d40a00300030860340d6401161200406401c000701030303000000700c2c0c07090180d0001c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 704480296 1250 704479046 704479051
    0x2181f140405010519032a080c030705240f0d09060c110a1a06040e07091a040e06040f1b03030201091704080d050f1c150f050d03050f0d090b 62
    0x381c03000c001c9a41c0328005c1c04449002c02510809281c4065010800120700b0540305030318005605201640f19800907140c03407555120780c4140129440701c1c422038114981882480000d0100300e9000c0c03010211030841003084650000100510040842d00040038140102210900d00003040208840445c4d0b2810030000c000070480400007448944908071400000603d0101581d080004038800d128462980000241c00a148035040750300c03400002012041001484040e02001c4030120302200010001d42d01902c41c02c107072790300ca94204654004550b0300820003d40042d0880a4545a00d445050a0061031041e0064031086588154004107169065200c0f030504ad00c14100c0c84040000c02c0400d200314041d0f405141d1250b00105d90280c5898000d4008010f0b40d403180c0100c2e410551900100003421034004518884279403290203540042c58141032503005081021000d1010b1800c0c4800710b004e800b0f100d50005d060007000142c0068542441090759070b000041c100900900855292201307034090203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 704481546 1250 704480296 704480299
    0x312050d060e0105030c1c05150106300c020703140a05060105060a050405010f1205181905030405130908030709031a010e040320162102181f14 63
    0x5014000c61212090400039048500050042404407421000c02c4210103441000a1440707d5000952000070401d020416038014005600c03038081d03240500c0a003000d0107004201110300866588071f08401c0080300441c0119084540000360010f0280069103010307240d070005000f030244020203501078100010038034681c1c1d108805a0784aa40d0322010300445004080608000ca2000d02080c415548104071100301888070740341c58018540d44810107801c450b802e48038850120710701c0360007e8480d401005484800f48001806603200f030010380750146c0701d0080e40150351003091002c2c0102c00e0040700d80c005203402c07900803081680da81000c45001d080c0006030720089403260104042c0340c2400b011400a00d0403685000520742c41740c0c1d21030364100d4a15035200c5040103a246941c21010719802c042201000c01000030041000c4281082e200542001504000950b454581c00540006849980301c0326240c500241900c1107039203c0d018035072001c503450030403690310b21a1070700d0000d43c1145107001d041c1c4c10b080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 704482796 1250 704481546 704481551
    0xf06140307030c0302120304030b10030209150907051c0204080a060c05040305030304060b010c211e050f0702030111030a0f0f05041a06130e0601030203011a0102071502070312050d 79
    0x1404091640341c40980c88003030040700e0070035004c00c054240800312180c102d6032103003540c1c642502c0360f844461801c001d40e01041800a1100240b0031810100354003500718807008902e040e1820007400054101600502c100c040080100d0a550030303544130706030f10507295181c11b819522940c946940c1991585046415a8444d05001c9100701c0c6501502c2214140ea800c072000c1d519550711038403403401070085501c203941001250803150001ca0f080c0030303c141242c1a103801e0b40d541005000c0004000c41418000700c00201e660202c0054525081401c075981c8600044d0210f80751549400040e004040d0080b5841800000100700140d00a0319840f25009000d803000410454810304240802c0340c0086030700401249032900d40440b501062080d16038070100050980300801040b90001040c2e034141700c0f14403000c3d80070b40b006004501c2c0a004081a0007860007051842070b02c4400000d6480365948200704140031140e4407841120300c2404801c0145800c1062946445015040180320360311400d2000410761 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 704484046 1250 704482796 704482829
    0x121031404081513020d1403090a030807020a0e0907260303010e071803110105030411060a0c0b06030a12051612050702010e03012c03040312081e040c0b030a0b040f06 73
    0xc0200701d1341c4003e98005d400c0c054000c15a581d45030f0f09801148201c0c04511050204c15182d91702e18100801031403040982903226640c03072050140040e00740c0c003c12458000c80b02000400540007940b102219000c2c2658104110443d91152105032080902550381c00004008100d0017080040c107402180c03955030b06074a420140c0c05a042015403800000c051004000703150010398450f6008e141c2003401020982c508803a10800105150300150300540412040da035854240203c01d5202036101038150094090103207a942c40001031540c54441c0d800f03000c4040b4440d0805e48011415204080d8002d00321303804d961601c40058101d80000348124002036142040717070180e08041c000c980b40741c5240c01d880c421480d003101e0140140c0865224803c4244030600000005c1800401ca46500c02099203400781c05081c4026000c070103c64600302a10500b4180b018440015011568201124a10b40031291640c950100c4000601414041c03154000d08105014a07440156400707001100c030544846030bc41d0303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 704485296 1250 704484046 704484061
    0x302030d211a0d050619060e1810050a05040c06030e060624040f0905010f0305071a0c0616030c0207050f060a030b03100902090a020301210314040815 66
    0x60111200d14180071040e010308410654854200c4001442036500b50045980300801180507240c03402070545a0b50301000c140100302d5103420310030000c149008000c0c003846080c000880d20b01d85001d40301801c1d0030305140180440340350910120710702110201d018895420a91a81d001600081d201a15407d03800000096514040c0c401e0300d4061220001420301643e810b8204280c0c07035090f141e0300c4404455000020440c00c0703070341c000300094a00c411603400c1c4141003100b0103040b034805811410345618100014070120300002000300860340c0c004410300302d580170000c126149009a5804907910f204450038407490200840c1071502d01c02e07040e94100481807803003208903580d81d864801c0c15080f0694540c3c01c0070500b0703c5c07801055861101e081c0031400041c050040303494501c2004212812030780e03880014046250408916030001804601981154101507082291080d00c0b804852070342440a500030070103020381c007420f40c403407840038000d80c50710740d1103c0c1d05480308644a0000070400f03400d400204603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 704486546 1250 704485296 704485307
    0x1709190f021302030403020a260a03020c070b0c03030a150e0901020a0f0305071b0203012301030c0923100905190513110910090c1101290409030504051305010302030d 73
    0x85c0f601b6500901c500405502d0702e000c4000f528054886541141c1940c0b844d480340c440c010b14a9400960300143d40350750f10318181d07003401ca054110701e507500c03010400503400d54400000d6980080b48444001110202e08804c60b240e02581d0b840807004099a0b400c010720010107501403d000151078440208010900c4070031400c40f002103401d030740480e101d0301c80700b0360b40003860340300f60a894030140000030820f000d2600c00e054481d95101c5042d495190500600801c0107900f1420010014040c1c140038000c0500c080f504205c4c2c446080303503d1402041d0004455600ca81d5540004289280003003025003046400700c41e82e4003601c07001080c0c8506003000b0031445c494024500c9426508003540c280c130301010108204002401400d1403861848030240410600350074031076002580c41940310021079030280c02d09a400d460124402540120a851a420b190440000c0307000d4012022200064003240624040d10039000d16085613401c14039002d03180340d40a4040e17000c60b069030b0086086400032030803034504840 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 704487796 1250 704486546 704486551
    0x5041b2304060c080f0403240e03030c030a090b011e0506040f090207140105090303040209070206090c011b06140405060105100f08150616170a1709190f02130203 71
    0x650403400c100400000707102c0c50781404030714865640d8038904140a058420075401c650002c0c0c9584a012040c0c1e040b14114039070880c0c0d4a5840705051201c410b40c504281d849000080510030354100010005207140b41c542d0140c00c015501c9880d900c040d586615070071103d002c19040030f0900d020110004240e900d0030000b91801c13144424424495242083d0310340020350810602194005032214204050480a003d05071184110300300554813464140100705403e08060121030a64000c14103101600c10041020083c014081c00d108030726484031201c0f100f44284002020788003e1509030000d032000b0759901b44c1030186005108440c490798890007003100480070000d902c0086150554195485401442c400d0361154580c4c03203402c0000314260106240c4e910200850600900d81c0e00000e003004501c220012680158840090505001420141c0120316992031180301543c181d00248015404000b0f1548407070f4002c08800e8107112524128540e40b407c100c00724401d20740001d901c5040182842a0307072 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 704489046 1250 704487796 704487857
    0x92304060f050d022808010207051002030f1b0d02040806010305070f050d0303050606070b010305030703031b121d070803180d0b0a09020a091104081b030a170405041b 73
    0x11104040383c0d00b004201810b2000005c801e040e200111312482c0f140800032001824a0000903030340d08001d2405909000d00f0b80c580103000341c170500c2809070301d0346501502d035480402c05a1848141002545298040c0128140c0140c003a00014000c62081e0700480c0e0241200e1142d012100c910340c0301c0a040030000260301800d90000040c101000c04070707201741c0007250003580103089140792605544a081048100740c0050380d007503000160003001c042d0b15214100d50b006041c01114070218a25200a0070b03003440855020b00f0b03640b540d47c6080e585107000c0d010002d20303120000310b400740380d82e510100b0b03200d420000a81403000d80d45c80f02280c4d24101851029180c50307011841c03801c01e6131108000001003c0115080e41c00000e00103010810595034030404040c0044c80003481d440350f140021441c60480d4625911a41c40b08102d01e621854500050702d440190388180c0105107440c154880341c115001e43c0e480213521078140300044c980121f80c5a2004608440b540e43c042032a900c3c181d2a90750b00b4005030200e03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 704490296 1250 704489046 704489059
    0x6161403040c12030e130c0923100801030201140f090105160501060f080c010903230a080d14070503060a03080904020706050a050a0c0c03020703030807092304060f05 73
    0x461414902001140c1c030a02c01c41c041d04107a40c4422424003040100079080300070900c1c2d8554820540707000740f03411348000380a48007070190800482008188040031710404050f80507600d950b1844101e4440078500c08900a8240301481c0400c1360700a0402c41e003032200b41d01080396100029034042c80481121081c0002c1d4000390700e40421540115140da01c0704004105242004c003c00c3e0000d542802104000c100c042c1c800d4009034100000b281c01c0040c02c1482a0500c0b03021001080040c00e80c0c0301485861004403005a004a0080c04250600c050003900038004030000818a041c0301455001082c106d40c855101115a59400c2081c0c800d8441951000e170b1260b5103140400005000f040101880d0201810240c00c01000307582e400d00b600c3e4240c0c0d060324015124010040403080b01e2051030b4074400c1a20b0000c0700303216940c502a403075041c01c0c08082c0412482900007480c041c00381030a03c0040480f03000246220306100c100070741702c02940202c60300c12401e00c8400141407141540c51820350704008d004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 704491546 1250 704490296 704490317
    0x3031503030c1c2007091a0913050a02030304060c0b010611030702150d06030c0e07081b031005060d020c1507090e0a0e0a12030f02030c04060302031305011503050616 73
    0x2d0740316640c460b1500034100b00032140140b02d04401c9504c801000741d9000000d02840d0b00b0412201c00b6600080f10601d000321804130720700c56030750b51003111540046419800c0d81c1140c60a041440c20700f24420000394140c44001070028003940e0144183d84454082d00e024242d60341c80d03140803110301240081501140c0d0052002001610341541c400040009222086140c10000681e03402913600c21f0340182c842c0c5613051340400c41508040e644036401a285e241104591411b41c00030070448a1000d603030510140e0100006c0c61101e02c802091b0054400200120340310220004118007a510003100001c2c40d000d261054095100070f00701c11401b50300c554544514480c2446034420717080c50001c0201c565143c0710340c1c1080703202d1418030440525500440c00012401c0c0e82c40c1d006400c1e60014001c0c286020b1042003000070910075507042d030b41990841d107400759490301e8042c207038884409800d8010300302c0d52030f0001e8583d0f80e85240408404480c4550151074030b507640c2520b9a01c84014a86106000c038180c0f010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 704492796 1250 704491546 704491573
    0x2161d01030816061a0103050a050f011503110403060501051906052517030f07090614070204090209091b01020c0a05010c050f1f05060d050d0f03090f0503031503030c 73
    0x3d080c6070303800000c01014003011522000299000000d00500d10707410440030310125641401140c0c1d011900a0301401a0700304003840c1850450b052007160300240c40c04056083c0b940c480d0b0131101d030900828400c03035100ca132241445c074000c25080c407e0a100311600304629200f0400c428180045034000c0c0ca0306400e02883c0c80d0011094441c0c1c294000d100c0d40182d000034002501d44107000b0001400050841c1c8a2504444180f03841002034058407e00c62044020800a9880100300c10112055800540c5500451000c10050100f071000290b2001410f810440908000560100c00c00d00d000b14080300d40307000c4401680c64201080710a40c025040d11402d100650103910f81d200b80503c10350445420814684e0b001d402c0c40c901001c1082c9407000030b84200e000414500800d44c100004454035121107220381d40d8a0b9a03810f222200e031051000c1c004c2d034100304602a9224085c3c064010409844000311450800e032a40d10450350072040fa070380366013142e400d0b050000903203441c1a1000020451601c0255 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 704494046 1250 704492796 704492813
    0x13150513200c100f0903020601050d080304020d140a030c0203010b012a020307050d0311011508061602030f07030504080706180905091609050f01151b17030702161d0103 74
    0x244140c0144192078034404144a00d00c02c074604c0144d01c0c400010315074603034503000b810a007041c0e2056100d049092800c8020461140072603400540c100c4400500358120b03d00341d2a161079103c03589595028903192501419003040c0e62806140c801c80081040f10020801911441810001c00000c15410382c1c20103a07c0001140a0a02600040880c4c031055555000100c03501c5070400228005000d440308211516824068005038803214460114030342d0600c24000d541d03d00050030ba038201107a0f40b80408146d8000c2c0f04940c401c40c1166071095a81079141400340c8140c0c003e210703009040c8101540001c00ba071003804940c940d80000b10005030100c1c40c0c04c05a80160002600c0c16046010b407090011541c1c10f840c0403c0000e00b01d003040840c9611745810100c4080d40140d008007032589050751000c0c1032070761090300e149a030540c07012410900b60745410001d860521034000640c000e24004103004c00160005090030100c07610443c0342010a45079100d54000c4404074090040000c2e122006100150055 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 704495296 1250 704494046 704494057
    0x92709050c03120c01051b030a090f1401060e0109020a0f0f090f090605030f0a05030d0c020703080403230d0e01081e040c061d0d0f021315051320 64
    0x1681240c0c99406203078006810408003446603041e0310320010340c03080b05020038000c1c99441036290442c00580d2801c00c500c614a48001451f0002d11546c520128042145c42601d40c0d40e92604903618080d83d142d032040941c02084180150941a520000009080c80f002d000711400c654695981c41d000540351341080d0b84110301c0010f0030303050044074a40440d40120051032000204408400441c06d1450001814205021003c10740d0790390b000030314402d0200314000308607400000b9121001a0039014820100d09280d00e03074000900244001500005110654103032211b104c82d1101c1800180b402d401d156070b80c032100d006504000c52800455032841e0340c0500030103030f4044500e40320b10341c003d44400c810411550f000c40301110745104418040c0b000a9126a00e0204000c2c5407182169141410b03000820207403841000620107180c103503003802151603146040c1c648155020781801400030500d20200301d040e403801898058903600900180307510680c011151070300c2c1001d000707500d0003510340000d00321580305c0b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 704496402 1106 704495296 704495303
    0x30d05070e1806030703050f1005070c030801090b041b0816090b090405092802031c0f0806010e1206010e09010c081f24092709 56
    0x301e6040100c0c440c00300d8818a92a0b07500c100017483c000c1540c00003005c03802880400c000c58207000920f4481015030140600c419a180f11088400c1c0c004240e0207030000e4800c0d00100a0790680354400340082402400c042030f050028980c0304030a03c08106600c000412150420080312180c80280b01450350501e810282e07117140c00c82c2c0d40326031300507140300e02d110302e9844000c02c0d5240343c00c01c51044425061031100b801510845520303072101005200990080c0a1019224001d00d400c41c8225510005a10b603c3c036501a04001103c200d517008015a042c00151540000d407540c07030751096a0f40289100080255604101240d841c010004d4443c1041e81c1c1043c5200704091781203828141d200203580401080301045081000301c154030b40c0d0001c440078414051089000088a140f130800e02182e4641084c40f5681d1001c51440c003200624590041c115401540b50703002d00f581099004900 = true := by decide +kernel

theorem cover : BRFrame.Cov 704316546 704496402 := by
  have h0 := BRFrame.cov_init 704316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 704316546 ≤ n) (h2 : n < 704496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
